//! Capability-protocol registration, coherence, and requirement
//! resolution (`rfcs/0009`).
//!
//! Protocols and extends reuse the existing generic machinery end to
//! end: a protocol's own type parameters are ordinary `TypeParamId`s
//! (`Ty::Param`), an extend's own type parameters are too, and
//! `crate::types::substitute` is the exact substitution every other
//! generic declaration already uses. What is genuinely new here is
//! deciding, for one `uses` requirement at one call site, which
//! `extend` (if any) answers it -- authority and overlap are checked
//! once at registration, deterministically, before any call is ever
//! resolved against them; resolution itself is a small recursive solver,
//! memoized and budgeted, that never trusts a caller-supplied
//! requirement to already be satisfiable.

use std::collections::HashMap;

use super::codes;
use super::{Checker, RecordInfo, VariantInfo};
use crate::diagnostics::Diagnostic;
use crate::hir::{HirExtend, HirModule, ItemId, TypeParamId};
use crate::limits::{MAX_CAPABILITY_DEPTH, MAX_CAPABILITY_RESOLUTION_STEPS, MAX_GENERIC_DEPTH};
use crate::source::{SourceId, Span};
use crate::symbol::Symbol;
use crate::types::{CapabilityRequirement, Evidence, Ty, substitute};

/// One declared protocol's own type parameters and method signatures,
/// each method's `params`/`ret` still in terms of the protocol's own
/// `TypeParamId`s.
pub(super) struct ProtocolInfo {
    pub type_params: Vec<TypeParamId>,
    pub methods: Vec<ProtocolMethodInfo>,
    pub source: SourceId,
}

pub(super) struct ProtocolMethodInfo {
    pub name: Symbol,
    pub params: Vec<Ty>,
    pub ret: Ty,
}

/// One accepted (authorized, individually complete) `extend`
/// declaration, ready for the capability solver to select.
pub(super) struct ExtendInfo {
    pub id: ItemId,
    pub type_params: Vec<TypeParamId>,
    pub protocol: ItemId,
    pub protocol_arguments: Vec<Ty>,
    pub requirements: Vec<CapabilityRequirement>,
    /// The underlying NIR-bound `ItemId` implementing each protocol
    /// method, indexed by that method's own declaration-order index --
    /// always fully populated (one entry per protocol method) by the
    /// time an `ExtendInfo` is accepted into `Checker::extends`, since
    /// an incomplete extend is diagnosed and excluded instead. Not read
    /// anywhere yet: `nir::lower` independently re-derives this same
    /// mapping from HIR directly, so this is currently only
    /// `check_extension_completeness`'s own natural byproduct, kept for
    /// a possible future cross-check rather than discarded.
    #[allow(dead_code)]
    pub methods: Vec<ItemId>,
    pub source: SourceId,
    pub span: Span,
}

/// Collects every `TypeParamId` occurring anywhere inside `ty`, recursing
/// through `Ty::Applied`'s own argument list -- used to decide whether an
/// extend's own type parameter is actually determined by its protocol
/// head (`rfcs/0009`'s exact-forwarding-only requirement). Depth-bounded
/// the same way every other stage that walks a type application is
/// (`MAX_GENERIC_DEPTH`); a hostilely deep hand-built type simply stops
/// contributing further occurrences past the bound rather than recursing
/// without limit.
fn collect_occurring_type_params(
    ty: &Ty,
    out: &mut std::collections::HashSet<TypeParamId>,
    depth: usize,
) {
    if depth > MAX_GENERIC_DEPTH {
        return;
    }
    match ty {
        Ty::Param(id, _) => {
            out.insert(*id);
        }
        Ty::Applied(_, args) => {
            for arg in args {
                collect_occurring_type_params(arg, out, depth + 1);
            }
        }
        _ => {}
    }
}

impl<'a> Checker<'a> {
    /// Resolves every declared protocol's own method signatures, before
    /// any function/extend body (which may call one) or any extend
    /// (which must satisfy one) is processed.
    pub(super) fn register_protocols(&mut self, hir: &HirModule) {
        for p in &hir.protocols {
            self.source = p.source;
            let methods = p
                .methods
                .iter()
                .map(|m| ProtocolMethodInfo {
                    name: m.name,
                    params: m
                        .params
                        .iter()
                        .map(|t| self.resolve_named_type(t))
                        .collect(),
                    ret: m
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_named_type(t))
                        .unwrap_or(Ty::Unit),
                })
                .collect();
            self.protocols.insert(
                p.id,
                ProtocolInfo {
                    type_params: p.type_params.iter().map(|tp| tp.id).collect(),
                    methods,
                    source: p.source,
                },
            );
        }
    }

    /// Converts one HIR-level capability requirement into its canonical
    /// form, validating the referenced protocol's own arity the same way
    /// an ordinary generic aggregate reference is (`resolve_named_type`).
    /// Returns `None` for an unknown protocol (a sentinel id from
    /// `hir::lower`'s own recovery, or -- defensively -- any id this
    /// checker's `self.protocols` never learned about) or a wrong
    /// argument count; the caller is responsible for skipping a
    /// requirement this returns `None` for rather than trusting a
    /// placeholder.
    fn resolve_requirement_ref(
        &mut self,
        requirement: &crate::hir::HirCapabilityRequirement,
    ) -> Option<CapabilityRequirement> {
        let arguments: Vec<Ty> = requirement
            .arguments
            .iter()
            .map(|a| self.resolve_named_type(a))
            .collect();
        let Some(info) = self.protocols.get(&requirement.protocol) else {
            // `hir::lower` already reported an unknown protocol for this
            // id; nothing further to say here.
            return None;
        };
        if arguments.len() != info.type_params.len() {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::PROTOCOL_ARITY_MISMATCH,
                    self.source,
                    requirement.span,
                    format!(
                        "this protocol requires {} type argument(s), found {}",
                        info.type_params.len(),
                        arguments.len()
                    ),
                )
                .with_primary_label("wrong number of protocol type arguments"),
            );
            return None;
        }
        Some(CapabilityRequirement::new(requirement.protocol, arguments))
    }

    /// Resolves a `uses` clause's requirements (shared by an ordinary
    /// function/extend method's own signature and an extend's own
    /// head), dropping any entry that failed to resolve rather than
    /// aborting the whole list -- one malformed requirement must never
    /// hide every other, valid one.
    pub(super) fn resolve_requirements(
        &mut self,
        requirements: &[crate::hir::HirCapabilityRequirement],
    ) -> Vec<CapabilityRequirement> {
        requirements
            .iter()
            .filter_map(|r| self.resolve_requirement_ref(r))
            .collect()
    }

    /// Registers every `extend` declaration: resolves its head and own
    /// requirements, checks it implements its protocol completely and
    /// with compatible signatures, checks authority, and -- once every
    /// extend is otherwise valid -- checks pairwise coherence (no two
    /// accepted heads may ever match the same concrete requirement).
    /// Only extends that pass every one of these is inserted into
    /// `self.extends`, where the capability solver can find it -- an
    /// unauthorized or incomplete extend is diagnosed and excluded, so
    /// it can never also produce a spurious "missing capability" or
    /// dispatch error downstream.
    pub(super) fn register_extends(&mut self, hir: &HirModule) {
        let mut accepted: Vec<ExtendInfo> = Vec::new();
        for e in &hir.extends {
            self.source = e.source;
            let Some(protocol_info_type_params) = self
                .protocols
                .get(&e.protocol)
                .map(|p| p.type_params.clone())
            else {
                // Unknown protocol: `hir::lower` already reported this.
                continue;
            };
            let protocol_arguments: Vec<Ty> = e
                .protocol_arguments
                .iter()
                .map(|a| self.resolve_named_type(a))
                .collect();
            if protocol_arguments.len() != protocol_info_type_params.len() {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::PROTOCOL_ARITY_MISMATCH,
                        self.source,
                        e.protocol_ref_span,
                        format!(
                            "this protocol requires {} type argument(s), found {}",
                            protocol_info_type_params.len(),
                            protocol_arguments.len()
                        ),
                    )
                    .with_primary_label("wrong number of protocol type arguments"),
                );
                continue;
            }
            // Protocols over affine (resource-containing) types are out
            // of scope this milestone (`rfcs/0011`, `rfcs/0012`): an
            // affine type used as one of this extend's own protocol type
            // arguments is rejected with a dedicated diagnostic here,
            // rather than silently letting an affine value flow through
            // capability resolution as though it were an ordinary
            // observable value.
            let mut has_resource_argument = false;
            for arg in &protocol_arguments {
                if self.is_affine(arg) {
                    has_resource_argument = true;
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::RESOURCE_PROTOCOL_UNSUPPORTED,
                            self.source,
                            e.protocol_ref_span,
                            "a resource type cannot be used as a protocol type argument",
                        )
                        .with_primary_label("resource used as a protocol argument"),
                    );
                }
            }
            if has_resource_argument {
                continue;
            }

            let extend_type_params: std::collections::HashSet<TypeParamId> =
                e.type_params.iter().map(|tp| tp.id).collect();

            // Exact-forwarding-only symbolic semantics (`rfcs/0009`): an
            // extend's own type parameter must be determined by its
            // protocol head alone -- there is no other mechanism that
            // could ever bind it. One diagnostic per unconstrained
            // parameter, in declared order, and the whole extend is
            // excluded from the solver (never silently dropped without a
            // diagnostic, and never registered half-checked).
            let mut occurring: std::collections::HashSet<TypeParamId> =
                std::collections::HashSet::new();
            for arg in &protocol_arguments {
                collect_occurring_type_params(arg, &mut occurring, 0);
            }
            let mut has_unconstrained_param = false;
            for tp in &e.type_params {
                if !occurring.contains(&tp.id) {
                    has_unconstrained_param = true;
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::UNCONSTRAINED_EXTEND_PARAMETER,
                            self.source,
                            tp.span,
                            format!(
                                "extend type parameter `{}` does not occur in the protocol's own type arguments and cannot be determined by this extension's head",
                                self.interner.resolve(tp.name)
                            ),
                        )
                        .with_primary_label("unconstrained extend type parameter"),
                    );
                }
            }
            if has_unconstrained_param {
                continue;
            }

            let requirements = self.resolve_requirements(&e.requirements);

            if !self.check_extension_authority(e, &protocol_arguments) {
                continue;
            }
            let Some(methods) =
                self.check_extension_completeness(e, &protocol_arguments, &extend_type_params)
            else {
                continue;
            };

            accepted.push(ExtendInfo {
                id: e.id,
                type_params: e.type_params.iter().map(|tp| tp.id).collect(),
                protocol: e.protocol,
                protocol_arguments,
                requirements,
                methods,
                source: e.source,
                span: e.span,
            });
        }
        let excluded = self.check_extend_overlaps(&accepted);
        self.extends = if excluded.is_empty() {
            accepted
        } else {
            accepted
                .into_iter()
                .enumerate()
                .filter(|(i, _)| !excluded.contains(i))
                .map(|(_, e)| e)
                .collect()
        };
    }

    /// The authority rule (`rfcs/0009`): an extend is legal only when its
    /// own declaring module owns at least one authority boundary -- the
    /// protocol declaration itself, or the outermost nominal aggregate
    /// used as the protocol's *first* type argument. A primitive first
    /// argument has no declaring module of its own to lend authority, so
    /// only the protocol-owning module may extend it. One file is always
    /// exactly one module in this project layout (`rfcs/0006`), so
    /// module identity is compared here by plain `SourceId` equality --
    /// never by re-deriving a dotted module path.
    fn check_extension_authority(&mut self, e: &HirExtend, protocol_arguments: &[Ty]) -> bool {
        let Some(protocol_source) = self.protocols.get(&e.protocol).map(|p| p.source) else {
            return false;
        };
        if e.source == protocol_source {
            return true;
        }
        if let Some(first) = protocol_arguments.first()
            && let Some(aggregate_source) = self.outermost_aggregate_source(first)
            && e.source == aggregate_source
        {
            return true;
        }
        self.diagnostics.push(
            Diagnostic::error(
                codes::UNAUTHORIZED_EXTENSION,
                self.source,
                e.protocol_ref_span,
                "this module owns neither the protocol nor the outermost type of the protocol's first type argument, so it is not authorized to declare this extension",
            )
            .with_primary_label("unauthorized extension"),
        );
        false
    }

    /// The declaring module of `ty`'s own outermost nominal
    /// record/variant, if it has one -- `None` for a primitive, a bare
    /// type parameter, or `Ty::Error`, none of which have a module of
    /// their own to lend authority.
    fn outermost_aggregate_source(&self, ty: &Ty) -> Option<SourceId> {
        match ty {
            Ty::Named(item, _) | Ty::Applied(item, _) => self
                .records
                .get(item)
                .map(|r: &RecordInfo| r.source)
                .or_else(|| self.variants.get(item).map(|v: &VariantInfo| v.source)),
            _ => None,
        }
    }

    /// Checks that `e` implements every one of its protocol's methods
    /// exactly once, with a compatible signature, and no extra methods
    /// -- returns the resolved method table (protocol method index ->
    /// implementing `ItemId`) only if every check passes; any failure
    /// diagnoses and returns `None`, excluding this extend from the
    /// solver entirely rather than letting a partially-checked extend
    /// participate in dispatch.
    fn check_extension_completeness(
        &mut self,
        e: &HirExtend,
        protocol_arguments: &[Ty],
        extend_type_params: &std::collections::HashSet<TypeParamId>,
    ) -> Option<Vec<ItemId>> {
        let protocol_info = self.protocols.get(&e.protocol)?;
        let subst: HashMap<TypeParamId, Ty> = protocol_info
            .type_params
            .iter()
            .copied()
            .zip(protocol_arguments.iter().cloned())
            .collect();
        // Snapshot what the solver needs before mutably borrowing
        // `self.diagnostics` below -- `protocol_info` itself borrows
        // `self.protocols` immutably, which this function must stop
        // holding before it can push a diagnostic.
        let expected: Vec<(Symbol, Vec<Ty>, Ty)> = protocol_info
            .methods
            .iter()
            .map(|m| {
                (
                    m.name,
                    m.params.iter().map(|t| substitute(t, &subst)).collect(),
                    substitute(&m.ret, &subst),
                )
            })
            .collect();

        let mut ok = true;
        let mut by_name: HashMap<Symbol, Vec<&crate::hir::HirFunction>> = HashMap::new();
        for method in &e.methods {
            by_name.entry(method.name).or_default().push(method);
        }
        let mut method_ids = Vec::with_capacity(expected.len());
        for (name, expected_params, expected_ret) in &expected {
            let Some(candidates) = by_name.get(name) else {
                let text = self.interner.resolve(*name);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::EXTENSION_MISSING_METHOD,
                        self.source,
                        e.protocol_ref_span,
                        format!("this extension is missing an implementation of `{text}`"),
                    )
                    .with_primary_label("missing method"),
                );
                ok = false;
                continue;
            };
            if candidates.len() > 1 {
                let text = self.interner.resolve(*name);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::EXTENSION_DUPLICATE_METHOD,
                        self.source,
                        candidates[1].span,
                        format!("`{text}` is implemented more than once in this extension"),
                    )
                    .with_primary_label("duplicate method")
                    .with_label(candidates[0].span, "first implemented here"),
                );
                ok = false;
            }
            let method = candidates[0];
            // Read back from `self.functions` (`build_signatures` already
            // resolved every extend method's own signature there) rather
            // than re-resolving `method`'s own AST/HIR types here --
            // resolving the same possibly-invalid type twice would
            // otherwise diagnose it twice.
            let Some(method_sig) = self.functions.get(&method.id) else {
                ok = false;
                continue;
            };
            let actual_params = method_sig.params.clone();
            let actual_ret = method_sig.ret.clone();
            let signature_ok = actual_params.len() == expected_params.len()
                && actual_params
                    .iter()
                    .zip(expected_params.iter())
                    .all(|(a, b)| a == b)
                && &actual_ret == expected_ret;
            if !signature_ok {
                let text = self.interner.resolve(*name);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::EXTENSION_SIGNATURE_MISMATCH,
                        self.source,
                        method.span,
                        format!(
                            "`{text}`'s signature does not match its protocol method's declared signature"
                        ),
                    )
                    .with_primary_label("incompatible method signature"),
                );
                ok = false;
            }
            // A protocol method has no `raises` of its own yet
            // (`rfcs/0010`'s own honest limitation), so every
            // implementing method must be infallible too --
            // `hir::lower`'s own `lower_extend_method` already rejects a
            // source-level `raises` clause here and lowers with no
            // raised-effect metadata at all (R0031), but this defends
            // against a direct caller lowering hand-built HIR that
            // bypasses that gate: a fallible implementation must fail
            // conformance and never enter capability resolution, rather
            // than silently satisfying an apparently infallible protocol
            // method.
            if !method_sig.raises.is_empty() {
                let text = self.interner.resolve(*name);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::EXTENSION_SIGNATURE_MISMATCH,
                        self.source,
                        method.span,
                        format!(
                            "`{text}` declares `raises`, but its protocol method has no raised-effect signature to narrow"
                        ),
                    )
                    .with_primary_label("unexpected `raises`"),
                );
                ok = false;
            }
            method_ids.push(method.id);
        }
        let expected_names: std::collections::HashSet<Symbol> =
            expected.iter().map(|(n, _, _)| *n).collect();
        for method in &e.methods {
            if !expected_names.contains(&method.name) {
                let text = self.interner.resolve(method.name);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::EXTENSION_EXTRA_METHOD,
                        self.source,
                        method.span,
                        format!("`{text}` is not a method of this protocol"),
                    )
                    .with_primary_label("unknown protocol method"),
                );
                ok = false;
            }
        }
        // A method's own parameter/return types are never allowed to
        // reference a symbolic type parameter this extend didn't itself
        // declare -- true by construction for anything `hir::lower`
        // produced (a method never opens its own type-parameter scope,
        // so every `Ty::Param` it resolves is already the extend's own),
        // but this checker never trusts that invariant to hold for
        // hand-built HIR bypassing `hir::lower` entirely (mirrors
        // `nir::verify`'s own `check_type_param_scope`, applied here).
        for method in &e.methods {
            let Some(sig) = self.functions.get(&method.id) else {
                continue;
            };
            if !sig
                .params
                .iter()
                .all(|p| type_params_within(p, extend_type_params))
                || !type_params_within(&sig.ret, extend_type_params)
            {
                let text = self.interner.resolve(method.name);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::EXTENSION_SIGNATURE_MISMATCH,
                        self.source,
                        method.span,
                        format!(
                            "`{text}` uses a symbolic type parameter that does not belong to this extension"
                        ),
                    )
                    .with_primary_label("escaping type parameter"),
                );
                ok = false;
            }
        }
        if ok { Some(method_ids) } else { None }
    }

    /// Pairwise coherence: no two *accepted* extend heads targeting the
    /// same protocol may ever be able to match the same concrete
    /// requirement -- checked structurally (does there exist *some*
    /// instantiation of each extend's own free type parameters making
    /// their heads identical), never by enumerating concrete programs.
    /// Two exactly-equal, fully-concrete heads are reported as an exact
    /// duplicate; anything else that can still overlap (generic/
    /// concrete, generic/generic) is reported as an overlap. Comparison
    /// order is always accepted-list order (declaration order, `hir`'s
    /// own `Vec`), never a `HashMap`'s, so the diagnostic is independent
    /// of source/import order.
    /// Returns the set of `accepted` indices that must be excluded from
    /// the solver -- both an overlapping pair (only the later one, `y`,
    /// matching the existing diagnostic convention) and, for a pair whose
    /// overlap could not be decided within budget, *both* extends
    /// involved (`rfcs/0009`'s coherence guarantee cannot be claimed for
    /// either one, so neither is safe to leave registered).
    fn check_extend_overlaps(
        &mut self,
        accepted: &[ExtendInfo],
    ) -> std::collections::HashSet<usize> {
        let mut excluded: std::collections::HashSet<usize> = std::collections::HashSet::new();
        let mut by_protocol: HashMap<ItemId, Vec<usize>> = HashMap::new();
        for (i, e) in accepted.iter().enumerate() {
            by_protocol.entry(e.protocol).or_default().push(i);
        }
        let mut protocol_ids: Vec<ItemId> = by_protocol.keys().copied().collect();
        protocol_ids.sort_unstable_by_key(|p| p.0);
        for protocol in protocol_ids {
            let idxs = &by_protocol[&protocol];
            for a in 0..idxs.len() {
                for b in (a + 1)..idxs.len() {
                    let (ia, ib) = (idxs[a], idxs[b]);
                    let x = &accepted[ia];
                    let y = &accepted[ib];
                    let outcome = heads_can_overlap(
                        &x.protocol_arguments,
                        &x.type_params.iter().copied().collect(),
                        &y.protocol_arguments,
                        &y.type_params.iter().copied().collect(),
                    );
                    let (code, message) = match outcome {
                        OverlapOutcome::Disjoint => continue,
                        OverlapOutcome::BudgetExceeded => {
                            excluded.insert(ia);
                            excluded.insert(ib);
                            (
                                codes::OVERLAP_WORK_BUDGET_EXCEEDED,
                                "checking whether this extension could overlap another exceeded the maximum depth/work budget; both are excluded rather than risk an unproven incoherence",
                            )
                        }
                        OverlapOutcome::Overlap => {
                            let exact_duplicate = x.type_params.is_empty()
                                && y.type_params.is_empty()
                                && x.protocol_arguments == y.protocol_arguments;
                            excluded.insert(ib);
                            if exact_duplicate {
                                (
                                    codes::DUPLICATE_EXTENSION,
                                    "this extension duplicates another extension for the exact same protocol and type arguments",
                                )
                            } else {
                                (
                                    codes::OVERLAPPING_EXTENSION,
                                    "this extension can match the same concrete requirement as another extension; there is no specialization in Alpha 0.1.5",
                                )
                            }
                        }
                    };
                    // `y.source`/`y.span`, never `self.source`: by the
                    // time this runs (after every extend in `accepted`
                    // has already been registered), `self.source` is
                    // whichever extend's own registration happened to
                    // run last -- unrelated to either `x` or `y` -- so
                    // using it here would silently render this
                    // diagnostic against the wrong file whenever that
                    // last-registered extend differs from `y`'s own
                    // module (`rfcs/0009`).
                    self.diagnostics.push(
                        Diagnostic::error(code, y.source, y.span, message)
                            .with_primary_label("overlapping extension")
                            .with_label_in(x.source, x.span, "first extension declared here"),
                    );
                }
            }
        }
        excluded
    }

    /// The capability solver's public entry point: resolves `requirement`
    /// against `own_requirements` (the *currently type-checked*
    /// declaration's own, still possibly-symbolic `uses` clause -- always
    /// checked for an exact structural match first, since forwarding an
    /// existing requirement is always preferred to searching for a
    /// concrete extension), recursing through conditional extends as
    /// needed. `span` is only ever used for the diagnostics this
    /// specific call site's own resolution produces.
    pub(super) fn resolve_requirement(
        &mut self,
        requirement: &CapabilityRequirement,
        own_requirements: &[CapabilityRequirement],
        span: Span,
    ) -> Option<Evidence> {
        if let Some(index) = own_requirements.iter().position(|r| r == requirement) {
            return Some(Evidence::Forwarded(index));
        }
        if requirement_is_symbolic(requirement) {
            let text = self.describe_requirement(requirement);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::UNDECLARED_CAPABILITY_USE,
                    self.source,
                    span,
                    format!(
                        "this use requires the capability {text}, which is not declared in this function's own `uses` clause; add `uses {text}`"
                    ),
                )
                .with_primary_label("undeclared capability use"),
            );
            return None;
        }
        let mut steps = 0usize;
        let mut path = Vec::new();
        self.resolve_concrete(requirement, span, 0, &mut steps, &mut path)
    }

    /// Resolves a fully-concrete requirement against `self.extends`,
    /// recursively resolving whatever further requirements the selected
    /// extend itself declares. Only a *successful* resolution is
    /// memoized (`self.capability_cache`), by [`CapabilityRequirement`]
    /// identity -- every failure this can produce is either
    /// path-dependent (cyclic, depth-exceeded, work-budget-exceeded: the
    /// exact same requirement can still resolve cleanly from a different
    /// call site, at a shallower depth or a fresh step budget) or must
    /// still produce its own diagnostic at every call site that hits it
    /// (missing/ambiguous capability: a second, unrelated call needing
    /// an already-known-missing capability must not fail silently just
    /// because an earlier call already reported it), so none of them are
    /// ever cached. `path` is the active recursion's own concrete
    /// requirement stack, for a deterministic cyclic-requirement
    /// diagnostic; `depth`/`steps` enforce
    /// [`MAX_CAPABILITY_DEPTH`]/[`MAX_CAPABILITY_RESOLUTION_STEPS`] --
    /// a budget failure is always its own diagnostic, never reported as
    /// "no matching extension".
    fn resolve_concrete(
        &mut self,
        requirement: &CapabilityRequirement,
        span: Span,
        depth: usize,
        steps: &mut usize,
        path: &mut Vec<CapabilityRequirement>,
    ) -> Option<Evidence> {
        if let Some(cached) = self.capability_cache.get(requirement) {
            return Some(cached.clone());
        }
        if path.contains(requirement) {
            let mut cycle: Vec<String> = path
                .iter()
                .skip_while(|r| *r != requirement)
                .map(|r| self.describe_requirement(r))
                .collect();
            cycle.push(self.describe_requirement(requirement));
            self.diagnostics.push(
                Diagnostic::error(
                    codes::CYCLIC_CAPABILITY_REQUIREMENT,
                    self.source,
                    span,
                    format!(
                        "this capability requirement is cyclic: {}",
                        cycle.join(" -> ")
                    ),
                )
                .with_primary_label("cyclic capability requirement"),
            );
            return None;
        }
        if depth > MAX_CAPABILITY_DEPTH {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::CAPABILITY_DEPTH_EXCEEDED,
                    self.source,
                    span,
                    format!(
                        "resolving this capability requirement exceeded the maximum depth of {MAX_CAPABILITY_DEPTH}"
                    ),
                )
                .with_primary_label("capability resolution depth exceeded"),
            );
            return None;
        }
        *steps += 1;
        if *steps > MAX_CAPABILITY_RESOLUTION_STEPS {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::CAPABILITY_WORK_BUDGET_EXCEEDED,
                    self.source,
                    span,
                    format!(
                        "resolving this capability requirement exceeded the maximum work budget of {MAX_CAPABILITY_RESOLUTION_STEPS} steps"
                    ),
                )
                .with_primary_label("capability resolution work budget exceeded"),
            );
            return None;
        }
        path.push(requirement.clone());
        let outcome = self.select_extension(requirement, span, depth, steps, path);
        path.pop();
        if let Some(evidence) = &outcome {
            self.capability_cache
                .insert(requirement.clone(), evidence.clone());
        }
        outcome
    }

    fn select_extension(
        &mut self,
        requirement: &CapabilityRequirement,
        span: Span,
        depth: usize,
        steps: &mut usize,
        path: &mut Vec<CapabilityRequirement>,
    ) -> Option<Evidence> {
        let mut matches: Vec<usize> = Vec::new();
        for (i, extend) in self.extends.iter().enumerate() {
            if extend.protocol != requirement.protocol {
                continue;
            }
            if match_extend_head(&extend.protocol_arguments, &requirement.arguments, 0).is_some() {
                matches.push(i);
            }
        }
        if matches.is_empty() {
            let text = self.describe_requirement(requirement);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::MISSING_CAPABILITY,
                    self.source,
                    span,
                    format!("no extension satisfies the capability requirement {text}"),
                )
                .with_primary_label("missing capability extension"),
            );
            return None;
        }
        if matches.len() > 1 {
            let text = self.describe_requirement(requirement);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::AMBIGUOUS_CAPABILITY,
                    self.source,
                    span,
                    format!("more than one extension satisfies the capability requirement {text}"),
                )
                .with_primary_label("ambiguous capability extension"),
            );
            return None;
        }
        let index = matches[0];
        let extend_id = self.extends[index].id;
        let subst = match_extend_head(
            &self.extends[index].protocol_arguments,
            &requirement.arguments,
            0,
        )?;
        let nested_requirements: Vec<CapabilityRequirement> = self.extends[index]
            .requirements
            .iter()
            .map(|r| CapabilityRequirement::new(r.protocol, substitute_all(&r.arguments, &subst)))
            .collect();
        let mut nested = Vec::with_capacity(nested_requirements.len());
        for req in &nested_requirements {
            nested.push(self.resolve_concrete(req, span, depth + 1, steps, path)?);
        }
        Some(Evidence::Extension {
            extend: extend_id,
            nested,
        })
    }

    /// A human-readable rendering of a [`CapabilityRequirement`] for a
    /// diagnostic message (`Equal[i64]`) -- uses this checker's own
    /// registry so a cross-module protocol is always named by its
    /// canonical qualified name, never a possibly-aliased local one.
    pub(super) fn describe_requirement(&self, requirement: &CapabilityRequirement) -> String {
        let name = self
            .registry
            .qualified_name(requirement.protocol, self.interner);
        if requirement.arguments.is_empty() {
            return name;
        }
        let args: Vec<String> = requirement
            .arguments
            .iter()
            .map(|a| self.display_for_diagnostic(a))
            .collect();
        format!("{name}[{}]", args.join(", "))
    }
}

/// Whether `ty` still contains a symbolic `Ty::Param` anywhere in its
/// structure -- a requirement built from such a type can never be
/// resolved by searching concrete extends (only forwarding, from an
/// exact match in the current declaration's own `uses` clause, can ever
/// satisfy it).
fn requirement_is_symbolic(requirement: &CapabilityRequirement) -> bool {
    requirement.arguments.iter().any(ty_is_symbolic)
}

fn ty_is_symbolic(ty: &Ty) -> bool {
    match ty {
        Ty::Param(..) => true,
        Ty::Applied(_, args) => args.iter().any(ty_is_symbolic),
        _ => false,
    }
}

/// Whether every symbolic `Ty::Param` in `ty` belongs to `allowed` --
/// mirrors `nir::verify`'s `check_type_param_scope`, applied here to an
/// extend method's own declared signature before it is ever trusted as
/// implementing a protocol method.
fn type_params_within(ty: &Ty, allowed: &std::collections::HashSet<TypeParamId>) -> bool {
    match ty {
        Ty::Param(id, _) => allowed.contains(id),
        Ty::Applied(_, args) => args.iter().all(|a| type_params_within(a, allowed)),
        _ => true,
    }
}

fn substitute_all(tys: &[Ty], subst: &HashMap<TypeParamId, Ty>) -> Vec<Ty> {
    tys.iter().map(|t| substitute(t, subst)).collect()
}

/// One-directional structural match: does `pattern` (an extend head's
/// own `protocol_arguments`, which may contain `Ty::Param`s the extend
/// itself declares) match `concrete` (a fully-concrete requirement's own
/// arguments), and if so, what does each of the extend's own type
/// parameters bind to? `depth`-bounded by [`MAX_GENERIC_DEPTH`], the
/// same way every other stage that walks a nested type application is.
fn match_extend_head(
    pattern: &[Ty],
    concrete: &[Ty],
    depth: usize,
) -> Option<HashMap<TypeParamId, Ty>> {
    let mut subst = HashMap::new();
    if pattern.len() != concrete.len() {
        return None;
    }
    for (p, c) in pattern.iter().zip(concrete.iter()) {
        match_one(p, c, &mut subst, depth)?;
    }
    Some(subst)
}

fn match_one(
    pattern: &Ty,
    concrete: &Ty,
    subst: &mut HashMap<TypeParamId, Ty>,
    depth: usize,
) -> Option<()> {
    if depth > MAX_GENERIC_DEPTH {
        return None;
    }
    match pattern {
        Ty::Param(id, _) => {
            if let Some(existing) = subst.get(id) {
                if existing == concrete { Some(()) } else { None }
            } else {
                subst.insert(*id, concrete.clone());
                Some(())
            }
        }
        Ty::Applied(pi, pargs) => {
            let Ty::Applied(ci, cargs) = concrete else {
                return None;
            };
            if pi != ci || pargs.len() != cargs.len() {
                return None;
            }
            for (p, c) in pargs.iter().zip(cargs.iter()) {
                match_one(p, c, subst, depth + 1)?;
            }
            Some(())
        }
        other => {
            if other == concrete {
                Some(())
            } else {
                None
            }
        }
    }
}

/// Whether two extend heads (each with its own free type parameters,
/// disjoint from the other's -- `TypeParamId`s are never shared across
/// declarations) *could* ever match the same concrete requirement: a
/// real, sound structural unification, not a "bind once and then compare
/// by equality" approximation. Conservative by design -- this is a
/// "could these ever collide" check, not an attempt to enumerate every
/// concrete program that would actually call both, which is exactly how
/// coherence checking must work to be sound (`rfcs/0009` has no
/// specialization to fall back on if it guessed wrong).
///
/// Since every `TypeParamId` is globally unique (`rfcs/0008`), both
/// sides' own free parameters can share one substitution map with no
/// risk of collision -- there is no need for two separate namespaces or
/// a rename pass first. `unify_head_args` is the same one-directional
/// matcher `match_extend_head` uses for a concrete requirement, seen
/// from the general case where *both* sides may still be symbolic.
/// The result of trying to prove two extend heads disjoint: a real
/// tri-state, never collapsed to a plain `bool` -- `BudgetExceeded` must
/// never be silently treated as `Disjoint` (which would let two
/// extensions that might genuinely overlap both stay registered) nor as
/// `Overlap` (which would reject two heads this checker simply couldn't
/// finish analyzing). `rfcs/0009` claims both a depth and a work-step
/// budget for this check; both are real here, and either one being
/// exceeded produces `BudgetExceeded`, never a hang or a stack overflow.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OverlapOutcome {
    Disjoint,
    Overlap,
    BudgetExceeded,
}

fn heads_can_overlap(
    a_args: &[Ty],
    a_params: &std::collections::HashSet<TypeParamId>,
    b_args: &[Ty],
    b_params: &std::collections::HashSet<TypeParamId>,
) -> OverlapOutcome {
    if a_args.len() != b_args.len() {
        return OverlapOutcome::Disjoint;
    }
    let free: std::collections::HashSet<TypeParamId> = a_params.union(b_params).copied().collect();
    let mut subst = HashMap::new();
    let mut steps = 0usize;
    for (a, b) in a_args.iter().zip(b_args.iter()) {
        match unify_head_args(&mut subst, &free, a, b, 0, &mut steps) {
            Ok(true) => {}
            Ok(false) => return OverlapOutcome::Disjoint,
            Err(()) => return OverlapOutcome::BudgetExceeded,
        }
    }
    OverlapOutcome::Overlap
}

/// Follows `ty` through `subst`'s own chain of bindings until it reaches
/// either a concrete (non-`Ty::Param`) type or a still-unbound free
/// variable -- the same one-hop-at-a-time resolution
/// `typeck::context::TypeContext::resolve` performs for ordinary
/// inference variables, applied here to this unifier's own map instead.
/// Bounded by the map's own size (a real substitution chain can never be
/// longer than the number of variables it binds) so a malformed chain
/// degrades to returning the last-seen type rather than looping forever.
fn resolve_head(subst: &HashMap<TypeParamId, Ty>, ty: &Ty) -> Ty {
    let mut current = ty.clone();
    for _ in 0..=subst.len() {
        let Ty::Param(id, _) = &current else {
            return current;
        };
        match subst.get(id) {
            Some(next) => current = next.clone(),
            None => return current,
        }
    }
    current
}

/// Whether `var` occurs anywhere inside `ty` (after resolving through
/// `subst`) -- checked before every new binding, so this unifier can
/// never construct an infinite/self-referential substitution the way a
/// naive "just insert the binding" approach could (`extend[T] P[T]`
/// unified against a hypothetical `extend[U] P[Box[U]]` `U`-side
/// re-entry). Depth-bounded by [`MAX_GENERIC_DEPTH`]; past the bound,
/// conservatively treated as occurring (rejects the unification rather
/// than risk an unbounded walk).
/// `Err(())` means the depth or work-step budget was exceeded while
/// walking `ty` -- propagated straight up to `heads_can_overlap` as
/// `OverlapOutcome::BudgetExceeded` by every caller, never coerced to
/// `true`/`false` along the way (which would silently misreport this as
/// "occurs"/"does not occur" and let an unsound overlap conclusion
/// through).
fn occurs_in_head(
    subst: &HashMap<TypeParamId, Ty>,
    var: TypeParamId,
    ty: &Ty,
    free: &std::collections::HashSet<TypeParamId>,
    depth: usize,
    steps: &mut usize,
) -> Result<bool, ()> {
    if depth > MAX_GENERIC_DEPTH {
        return Err(());
    }
    *steps += 1;
    if *steps > MAX_CAPABILITY_RESOLUTION_STEPS {
        return Err(());
    }
    match resolve_head(subst, ty) {
        Ty::Param(id, _) if free.contains(&id) => Ok(id == var),
        Ty::Applied(_, args) => {
            for a in &args {
                if occurs_in_head(subst, var, a, free, depth + 1, steps)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        _ => Ok(false),
    }
}

/// The real unifier: resolves both sides through `subst` first, then
/// either binds a still-free variable (occurs-checked) or requires the
/// same nominal head with recursively-unifiable arguments. `subst` is
/// shared and mutated across every argument position `heads_can_overlap`
/// unifies, so a variable bound at one position is correctly chased at
/// every later position that mentions it again -- the transitive
/// chasing the previous, unsound implementation never did.
/// `Err(())` means the depth or work-step budget was exceeded --
/// propagated straight up through every recursive call and out of
/// `heads_can_overlap` as `OverlapOutcome::BudgetExceeded`, never
/// collapsed to `Ok(false)` ("disjoint") along the way.
fn unify_head_args(
    subst: &mut HashMap<TypeParamId, Ty>,
    free: &std::collections::HashSet<TypeParamId>,
    a: &Ty,
    b: &Ty,
    depth: usize,
    steps: &mut usize,
) -> Result<bool, ()> {
    if depth > MAX_GENERIC_DEPTH {
        return Err(());
    }
    *steps += 1;
    if *steps > MAX_CAPABILITY_RESOLUTION_STEPS {
        return Err(());
    }
    let ra = resolve_head(subst, a);
    let rb = resolve_head(subst, b);
    match (&ra, &rb) {
        (Ty::Param(ia, _), Ty::Param(ib, _)) if free.contains(ia) && free.contains(ib) => {
            if ia == ib {
                return Ok(true);
            }
            subst.insert(*ia, rb);
            Ok(true)
        }
        (Ty::Param(ia, _), _) if free.contains(ia) => {
            if occurs_in_head(subst, *ia, &rb, free, depth + 1, steps)? {
                return Ok(false);
            }
            subst.insert(*ia, rb);
            Ok(true)
        }
        (_, Ty::Param(ib, _)) if free.contains(ib) => {
            if occurs_in_head(subst, *ib, &ra, free, depth + 1, steps)? {
                return Ok(false);
            }
            subst.insert(*ib, ra);
            Ok(true)
        }
        (Ty::Applied(pa, aargs), Ty::Applied(pb, bargs)) => {
            if pa != pb || aargs.len() != bargs.len() {
                return Ok(false);
            }
            for (x, y) in aargs.iter().zip(bargs.iter()) {
                if !unify_head_args(subst, free, x, y, depth + 1, steps)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(ra == rb),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::Symbol;
    use std::collections::HashSet;

    fn param(id: u32) -> Ty {
        Ty::Param(TypeParamId(id), Symbol(0))
    }

    fn boxed(item: u32, args: Vec<Ty>) -> Ty {
        Ty::Applied(ItemId(item), args)
    }

    fn params(ids: &[u32]) -> HashSet<TypeParamId> {
        ids.iter().map(|i| TypeParamId(*i)).collect()
    }

    /// The Fix 4 regression: `extend[T] P[T, T]` and `extend[U] P[U,
    /// i64]` both cover the concrete instantiation `P[i64, i64]`, but
    /// the previous "bind once, then compare by direct equality"
    /// implementation missed it -- binding `T := U` at position 0, then
    /// requiring `U == i64` (a literal term, not a chased resolution) at
    /// position 1, which is never true even though `U` itself could
    /// still become `i64`.
    #[test]
    fn detects_the_transitive_overlap_regression() {
        let a_args = vec![param(0), param(0)]; // P[T, T]
        let b_args = vec![param(1), Ty::I64]; // P[U, i64]
        assert_eq!(
            heads_can_overlap(&a_args, &params(&[0]), &b_args, &params(&[1])),
            OverlapOutcome::Overlap
        );
    }

    #[test]
    fn reversed_argument_order_still_detects_the_same_overlap() {
        let a_args = vec![Ty::I64, param(1)]; // P[i64, U]
        let b_args = vec![param(0), param(0)]; // P[T, T]
        assert_eq!(
            heads_can_overlap(&a_args, &params(&[1]), &b_args, &params(&[0])),
            OverlapOutcome::Overlap
        );
    }

    #[test]
    fn a_fully_generic_head_overlaps_with_every_other_head() {
        let a_args = vec![param(0), param(0)]; // P[T, T]
        let b_args = vec![param(1), param(2)]; // P[U, V] (fully free)
        assert_eq!(
            heads_can_overlap(&a_args, &params(&[0]), &b_args, &params(&[1, 2])),
            OverlapOutcome::Overlap
        );
    }

    #[test]
    fn nested_applications_overlap_when_their_arguments_can_unify() {
        // Q[Box[T]] vs Q[Box[i64]] -- overlap at T = i64.
        let a_args = vec![boxed(100, vec![param(0)])];
        let b_args = vec![boxed(100, vec![Ty::I64])];
        assert_eq!(
            heads_can_overlap(&a_args, &params(&[0]), &b_args, &HashSet::new()),
            OverlapOutcome::Overlap
        );
    }

    #[test]
    fn different_nominal_heads_never_overlap() {
        // Q[Box[T]] vs Q[Wrapper[T]] -- same argument shape, different
        // declaration identity, can never be the same concrete type.
        let a_args = vec![boxed(100, vec![param(0)])];
        let b_args = vec![boxed(101, vec![param(1)])];
        assert_eq!(
            heads_can_overlap(&a_args, &params(&[0]), &b_args, &params(&[1])),
            OverlapOutcome::Disjoint
        );
    }

    #[test]
    fn concrete_heads_with_different_arguments_never_overlap() {
        let a_args = vec![Ty::I64, Ty::I64];
        let b_args = vec![Ty::Bool, Ty::Bool];
        assert_eq!(
            heads_can_overlap(&a_args, &HashSet::new(), &b_args, &HashSet::new()),
            OverlapOutcome::Disjoint
        );
    }

    /// `R[T, Box[T]]` vs `R[Box[U], U]` would require `T = Box[U]` and
    /// simultaneously `U = Box[T]` -- an infinite type. The occurs check
    /// must reject this, not loop forever trying to satisfy it.
    #[test]
    fn occurs_check_rejects_a_self_referential_unification() {
        let a_args = vec![param(0), boxed(100, vec![param(0)])]; // R[T, Box[T]]
        let b_args = vec![boxed(100, vec![param(1)]), param(1)]; // R[Box[U], U]
        assert_eq!(
            heads_can_overlap(&a_args, &params(&[0]), &b_args, &params(&[1])),
            OverlapOutcome::Disjoint
        );
    }

    #[test]
    fn exact_duplicate_concrete_heads_overlap() {
        let a_args = vec![Ty::I64];
        let b_args = vec![Ty::I64];
        assert_eq!(
            heads_can_overlap(&a_args, &HashSet::new(), &b_args, &HashSet::new()),
            OverlapOutcome::Overlap
        );
    }

    /// A pathologically deep pair of matching nested applications must
    /// resolve without overflowing the native stack -- and, since this
    /// exceeds `MAX_GENERIC_DEPTH`, must report `BudgetExceeded` rather
    /// than silently guessing `Disjoint` or `Overlap` for an input this
    /// checker could not actually finish analyzing.
    #[test]
    fn deeply_nested_matching_heads_do_not_overflow_the_stack() {
        let depth = MAX_GENERIC_DEPTH + 50;
        let mut a = param(0);
        let mut b = Ty::I64;
        for _ in 0..depth {
            a = boxed(100, vec![a]);
            b = boxed(100, vec![b]);
        }
        assert_eq!(
            heads_can_overlap(&[a], &params(&[0]), &[b], &HashSet::new()),
            OverlapOutcome::BudgetExceeded
        );
    }

    #[test]
    fn deeply_nested_non_matching_heads_do_not_overflow_the_stack() {
        let depth = MAX_GENERIC_DEPTH + 50;
        let mut a = Ty::I64;
        let mut b = Ty::Bool;
        for _ in 0..depth {
            a = boxed(100, vec![a]);
            b = boxed(100, vec![b]);
        }
        // Never silently `Disjoint`: the depth budget is exceeded long
        // before the differing leaves would ever be compared, so this
        // must be reported as undecided, not misreported as proven safe.
        assert_eq!(
            heads_can_overlap(&[a], &HashSet::new(), &[b], &HashSet::new()),
            OverlapOutcome::BudgetExceeded
        );
    }

    /// A head shallow enough to stay within the depth budget but with
    /// enough sibling arguments at each level to exceed the work-step
    /// budget must also report `BudgetExceeded`, not hang or silently
    /// guess -- the counterpart to the depth-based tests above, proving
    /// the work-step budget is real and independently enforced.
    #[test]
    fn wide_matching_heads_exceeding_the_work_budget_are_undecided() {
        const WIDTH: usize = 4;
        // `MAX_CAPABILITY_RESOLUTION_STEPS` worth of sibling arguments,
        // all identical concrete leaves so every comparison would
        // otherwise succeed -- purely a work-step budget exhaustion,
        // never a depth or disjointness failure.
        let levels = MAX_CAPABILITY_RESOLUTION_STEPS / WIDTH + 1;
        let leaf = Ty::I64;
        let args: Vec<Ty> = (0..levels)
            .map(|_| boxed(100, vec![leaf.clone(); WIDTH]))
            .collect();
        assert_eq!(
            heads_can_overlap(&args, &HashSet::new(), &args.clone(), &HashSet::new()),
            OverlapOutcome::BudgetExceeded
        );
    }

    /// Fix 1 (0.1.5 follow-up): swapping which side is passed first to
    /// `heads_can_overlap` still reports the same `BudgetExceeded`
    /// outcome -- the T0047 diagnostic this drives is deterministic by
    /// outcome/code regardless of declaration order, even though (like
    /// T0036/T0037) the diagnostic's own rendered span still follows
    /// declaration order.
    #[test]
    fn budget_exceeded_outcome_is_the_same_regardless_of_argument_order() {
        const WIDTH: usize = 4;
        let levels = MAX_CAPABILITY_RESOLUTION_STEPS / WIDTH + 1;
        let leaf = Ty::I64;
        let args: Vec<Ty> = (0..levels)
            .map(|_| boxed(100, vec![leaf.clone(); WIDTH]))
            .collect();
        let forward = heads_can_overlap(&args, &HashSet::new(), &args.clone(), &HashSet::new());
        let reversed = heads_can_overlap(&args.clone(), &HashSet::new(), &args, &HashSet::new());
        assert_eq!(forward, OverlapOutcome::BudgetExceeded);
        assert_eq!(forward, reversed);
    }
}
