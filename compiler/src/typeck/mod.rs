//! The local type checker.

pub mod context;
mod cycles;
pub mod exhaustive;
pub mod unify;

use std::collections::HashMap;

use context::{TypeContext, VarKind};
use exhaustive::{LiteralKey, ResolvedPattern, VariantSpace};
use unify::unify;

use crate::diagnostics::Diagnostic;
use crate::hir::{
    ExprId, HirBlock, HirElse, HirExpr, HirFunction, HirMatchArm, HirMatchArmBody, HirModule,
    HirPattern, HirStmt, HirType, ItemId, ItemRegistry, LocalId, TypeParamId,
};
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
use crate::syntax::ast::{AssignOp, BinaryOp, UnaryOp};
use crate::types::generics::GenericInstanceKey;
use crate::types::{
    CapabilityRequirement, Evidence, Ty, TyVar, display_ty, is_integer, is_numeric,
    primitive_from_name, substitute,
};

mod capability;
use capability::{ExtendInfo, ProtocolInfo};

mod codes {
    pub const TYPE_MISMATCH: &str = "T0001";
    pub const ARITY_MISMATCH: &str = "T0002";
    pub const IMMUTABLE_ASSIGN: &str = "T0003";
    pub const EXPECTED_NUMERIC: &str = "T0004";
    pub const EXPECTED_INTEGER: &str = "T0005";
    pub const UNKNOWN_TYPE: &str = "T0006";
    pub const UNSUPPORTED_FEATURE: &str = "T0007";
    pub const INVALID_ASSIGN_TARGET: &str = "T0008";
    pub const NOT_CALLABLE: &str = "T0009";
    pub const FUNCTION_NOT_FIRST_CLASS: &str = "T0010";
    pub const LOOP_CONTROL_OUTSIDE_LOOP: &str = "T0011";
    pub const INVALID_MAIN_SIGNATURE: &str = "T0012";
    pub const FIELD_ACCESS_NON_RECORD: &str = "T0013";
    pub const UNKNOWN_FIELD: &str = "T0014";
    pub const FIELD_MUTATION_UNSUPPORTED: &str = "T0015";
    pub const AGGREGATE_EQUALITY_UNSUPPORTED: &str = "T0016";
    pub const NON_EXHAUSTIVE_MATCH: &str = "T0017";
    pub const UNREACHABLE_ARM: &str = "T0018";
    pub const PATTERN_BUDGET_EXCEEDED: &str = "T0019";
    pub const INCOMPATIBLE_PATTERN: &str = "T0021";
    pub const TYPE_ARGUMENTS_TO_NON_GENERIC: &str = "T0022";
    pub const MISSING_TYPE_ARGUMENTS: &str = "T0023";
    pub const GENERIC_ARITY_MISMATCH: &str = "T0024";
    pub const CONFLICTING_INFERRED_ARGUMENTS: &str = "T0025";
    pub const CANNOT_INFER_TYPE_ARGUMENT: &str = "T0026";
    pub const UNSUPPORTED_ON_TYPE_PARAMETER: &str = "T0027";
    pub const GENERIC_INSTANCE_BUDGET_EXCEEDED: &str = "T0028";
    pub const PROTOCOL_METHOD_NOT_A_VALUE: &str = "T0029";
    pub const PROTOCOL_ARITY_MISMATCH: &str = "T0030";
    pub const EXTENSION_MISSING_METHOD: &str = "T0031";
    pub const EXTENSION_DUPLICATE_METHOD: &str = "T0032";
    pub const EXTENSION_EXTRA_METHOD: &str = "T0033";
    pub const EXTENSION_SIGNATURE_MISMATCH: &str = "T0034";
    pub const UNAUTHORIZED_EXTENSION: &str = "T0035";
    pub const DUPLICATE_EXTENSION: &str = "T0036";
    pub const OVERLAPPING_EXTENSION: &str = "T0037";
    pub const UNDECLARED_CAPABILITY_USE: &str = "T0038";
    pub const MISSING_CAPABILITY: &str = "T0039";
    pub const AMBIGUOUS_CAPABILITY: &str = "T0040";
    pub const CYCLIC_CAPABILITY_REQUIREMENT: &str = "T0041";
    pub const CAPABILITY_DEPTH_EXCEEDED: &str = "T0042";
    pub const CAPABILITY_WORK_BUDGET_EXCEEDED: &str = "T0043";
}

/// Which function(s), if any, must satisfy the executable entry
/// signature (`main` takes no parameters) -- `rfcs/0006` scopes this to
/// the entry module's own `main`, identified by `ItemId` before typeck
/// ever runs, so `main` declared in a non-entry module of a project is
/// just an ordinary function. Single-file compilation has no concept of
/// an "entry module" at all (there's only one namespace), so it keeps
/// checking any function literally named `main` -- the legacy Alpha 0.1
/// behavior.
#[derive(Clone, Copy)]
pub enum EntryMain {
    ByName,
    /// `None` when the entry module has no `main` at all; the
    /// project-level `M0010` check reports that separately, so nothing
    /// here needs to also flag a missing entry point.
    ByIdentity(Option<ItemId>),
}

/// Whether `check_match_exhaustiveness` actually completed. Kept
/// distinct from a plain `Vec<usize>` (which an empty budget-exceeded
/// result used to be indistinguishable from "analysis ran and found no
/// unreachable arms") so `check_match` cannot accidentally treat a
/// failed analysis as if every arm were proven reachable.
enum MatchCoverage {
    /// Analysis ran to completion; `unreachable` names every arm index
    /// it proved unreachable (possibly empty).
    Complete { unreachable: Vec<usize> },
    /// The work budget or recursion-depth bound was exceeded -- nothing
    /// the analysis might otherwise have found, including reachability,
    /// can be trusted.
    Failed,
}

#[derive(Clone)]
struct FunctionSig {
    params: Vec<Ty>,
    ret: Ty,
    /// This function's own generic parameters, in declaration order
    /// (`rfcs/0008`) -- empty for a non-generic function. `params`/`ret`
    /// may reference these via `Ty::Param`; a call site substitutes a
    /// concrete argument for each before unifying.
    type_params: Vec<TypeParamId>,
    /// This function's own `uses` capability requirements (`rfcs/0009`),
    /// in declared order, still in terms of its own `type_params` --
    /// substituted the same way `params`/`ret` are at a call site, then
    /// resolved into evidence for that specific call.
    requirements: Vec<CapabilityRequirement>,
    span: Span,
    /// Where this function was declared -- a different file than the
    /// call site's, in every cross-module call. A diagnostic pointing at
    /// `span` must always use this as that label's own `SourceId`
    /// (`with_label_in`), never the caller's `self.source`: attaching one
    /// source's span to a different source's id renders it against the
    /// wrong file entirely.
    source: SourceId,
}

#[derive(Clone)]
struct LocalInfo {
    ty: Ty,
    mutable: bool,
}

/// Every diagnostic produced by checking a module, the final resolved
/// type of every local binding (parameters, `value`/`mutable`
/// statements, and match-arm pattern bindings), and the final resolved
/// type of every expression. Both maps are what let NIR lowering
/// (`nir::lower`) know a local's or an expression's concrete type
/// without re-running unification or re-deriving an approximation of
/// it: by the time checking finishes, every local and expression that
/// isn't part of an ill-typed program has a fully resolved type
/// (literal defaults included, and never a bare, still-unresolved
/// `Ty::Var`).
pub struct TypeckResult {
    pub diagnostics: Vec<Diagnostic>,
    pub local_types: HashMap<LocalId, Ty>,
    pub expr_types: HashMap<ExprId, Ty>,
    /// For every `HirPattern::Variant`, and every `HirPattern::Bind` that
    /// resolves to a payload-less variant case rather than a fresh
    /// binding, the specific `(variant, case index)` it matches. Not yet
    /// populated (`match`'s own checking, and the pattern resolution
    /// that fills this in, lands in a later commit); NIR lowering will
    /// consult it, keyed by the pattern's own stable `PatternId`.
    pub pattern_case: HashMap<crate::hir::PatternId, (ItemId, usize)>,
    /// For every generic call, variant construction, or record
    /// construction, the exact concrete type arguments this checker
    /// resolved for it (inferred or explicit, always fully resolved --
    /// never a bare `Ty::Var`) -- keyed by that expression's own
    /// `ExprId` (`rfcs/0008`). `nir::lower` reads this back to attach
    /// the same instantiation to the corresponding NIR instruction,
    /// rather than re-inferring or re-resolving it independently. Empty
    /// for a non-generic call/construction.
    pub call_type_args: HashMap<ExprId, Vec<Ty>>,
    /// For every call whose callee declares one or more capability
    /// requirements (`rfcs/0009`), the resolved [`Evidence`] for each,
    /// in the callee's own declared order -- keyed by the call
    /// expression's own `ExprId`, the same way `call_type_args` is.
    /// Empty for a call to a function/extend method with no
    /// requirements.
    pub call_evidence: HashMap<ExprId, Vec<Evidence>>,
    /// For every explicit protocol-call expression
    /// (`Equal[T].equal(..)`), the one resolved [`Evidence`] answering
    /// it -- keyed by the call expression's own `ExprId`.
    pub protocol_call_evidence: HashMap<ExprId, Evidence>,
}

/// Type-checks an already name-resolved [`HirModule`], the same as
/// [`check_module_with_registry`] but with an empty-module-path registry
/// built from `hir` itself -- correct for single-file compilation, which
/// has no project-level module path at all (`rfcs/0007`): every type a
/// diagnostic names is just its own bare declared name, with no prefix.
/// Kept as the stable entry point every pre-existing caller (the
/// single-file driver, and this module's own several hundred unit
/// tests) already uses unchanged.
pub fn check_module(
    hir: &HirModule,
    source: SourceId,
    interner: &Interner,
    entry_main: EntryMain,
) -> TypeckResult {
    let registry = crate::hir::registry::build(hir, &HashMap::new());
    check_module_with_registry(hir, source, interner, entry_main, &registry)
}

/// Type-checks an already name-resolved [`HirModule`], naming types in
/// diagnostics through `registry`'s canonical qualified names
/// (`sales.user.User`, not just `User`) rather than the bare declared
/// name every `Ty::Named` also carries -- what lets two same-named,
/// differently-declared types produce a distinguishable "expected `X`,
/// found `Y`" instead of the same ambiguous text twice (`rfcs/0007`).
/// Project compilation passes its own already-built project-wide
/// registry; single-file compilation goes through [`check_module`]'s
/// empty-module-path wrapper instead. Checking one function never stops
/// at the first error: each expression is still visited (so later
/// independent errors in the same function are still reported), and
/// `Ty::Error`/`Ty::Never` unify with anything so one bad expression
/// does not cascade into unrelated type mismatches.
pub fn check_module_with_registry(
    hir: &HirModule,
    source: SourceId,
    interner: &Interner,
    entry_main: EntryMain,
    registry: &ItemRegistry,
) -> TypeckResult {
    let mut checker = Checker {
        source,
        interner,
        registry,
        ctx: TypeContext::new(),
        diagnostics: Vec::new(),
        functions: HashMap::new(),
        locals: HashMap::new(),
        pending_defaults: Vec::new(),
        current_return_type: Ty::Unit,
        current_requirements: Vec::new(),
        records: HashMap::new(),
        variants: HashMap::new(),
        variant_display: HashMap::new(),
        loop_depth: 0,
        expr_types: HashMap::new(),
        pattern_case: HashMap::new(),
        call_type_args: HashMap::new(),
        call_evidence: HashMap::new(),
        protocol_call_evidence: HashMap::new(),
        pattern_budget: exhaustive::MAX_USEFULNESS_STEPS,
        entry_main,
        generic_params: HashMap::new(),
        generic_instances: std::collections::HashSet::new(),
        protocols: HashMap::new(),
        extends: Vec::new(),
        capability_cache: HashMap::new(),
    };
    checker.collect_generic_params(hir);
    checker.build_aggregate_info(hir);
    checker.check_aggregate_cycles(hir);
    checker.register_protocols(hir);
    checker.build_signatures(hir);
    checker.register_extends(hir);
    for function in &hir.functions {
        checker.source = function.source;
        checker.check_function(function);
    }
    for extend in &hir.extends {
        for method in &extend.methods {
            checker.source = method.source;
            checker.check_function(method);
        }
    }
    checker.finalize_defaults();

    let local_types = checker
        .locals
        .iter()
        .map(|(id, info)| (*id, deep_resolve(&checker.ctx, &info.ty)))
        .collect();
    // Resolved the same way as local_types, and for the same reason:
    // an expression's raw recorded type can still be an unresolved
    // `Ty::Var` at the point check_expr ran (unification may settle it
    // later, or finalize_defaults may only just now be applying its
    // literal default) -- this is the one place that's collapsed away
    // before anything outside typeck ever sees these types.
    let expr_types = checker
        .expr_types
        .iter()
        .map(|(id, ty)| (*id, deep_resolve(&checker.ctx, ty)))
        .collect();
    let call_type_args = checker
        .call_type_args
        .iter()
        .map(|(id, args)| {
            (
                *id,
                args.iter().map(|a| deep_resolve(&checker.ctx, a)).collect(),
            )
        })
        .collect();

    TypeckResult {
        diagnostics: checker.diagnostics,
        local_types,
        expr_types,
        pattern_case: checker.pattern_case,
        call_type_args,
        call_evidence: checker.call_evidence,
        protocol_call_evidence: checker.protocol_call_evidence,
    }
}

/// Resolves `ty` through `ctx`'s substitution table, then recurses into
/// a resulting `Ty::Applied`'s own argument list so a still-unresolved
/// `Ty::Var` nested inside one (`Box[T]` where `T` was itself inferred)
/// is collapsed too, not just the outermost type -- `TypeContext::resolve`
/// alone only ever follows a `Var -> Var -> concrete` chain at the top
/// level (`rfcs/0008`).
fn deep_resolve(ctx: &TypeContext, ty: &Ty) -> Ty {
    deep_resolve_at_depth(ctx, ty, 0)
}

fn deep_resolve_at_depth(ctx: &TypeContext, ty: &Ty, depth: usize) -> Ty {
    let resolved = ctx.resolve(ty);
    if depth >= crate::limits::MAX_GENERIC_DEPTH {
        return resolved;
    }
    match resolved {
        Ty::Applied(item, args) => Ty::Applied(
            item,
            args.iter()
                .map(|a| deep_resolve_at_depth(ctx, a, depth + 1))
                .collect(),
        ),
        other => other,
    }
}

struct Checker<'a> {
    source: SourceId,
    interner: &'a Interner,
    /// Canonical, module-qualified identity for every item -- how every
    /// `Ty::Named` this checker names in a diagnostic is displayed
    /// (`rfcs/0007`), never a second name lookup of its own.
    registry: &'a ItemRegistry,
    ctx: TypeContext,
    diagnostics: Vec<Diagnostic>,
    functions: HashMap<ItemId, FunctionSig>,
    locals: HashMap<LocalId, LocalInfo>,
    pending_defaults: Vec<(TyVar, Ty)>,
    current_return_type: Ty,
    /// The currently-checked function/extend method's own capability
    /// requirements (`rfcs/0009`), still possibly symbolic in terms of
    /// its own type parameters -- how `resolve_requirement` decides a
    /// call inside this body can *forward* one of these rather than
    /// searching for a concrete extension.
    current_requirements: Vec<CapabilityRequirement>,
    /// Every declared record's fields, resolved to `Ty` and in
    /// declaration order -- the layout NIR's `record.create`/
    /// `record.field` will follow.
    records: HashMap<ItemId, RecordInfo>,
    /// Every declared variant's cases, resolved to `Ty` payloads and in
    /// declaration order.
    variants: HashMap<ItemId, VariantInfo>,
    /// Display-only `(variant name, [case names])` for rendering a
    /// non-exhaustive-match witness back into surface syntax.
    variant_display: HashMap<ItemId, (String, Vec<String>)>,
    /// How many `while`/`loop` bodies currently enclose the expression
    /// being checked. `break`/`continue` outside of any loop is a
    /// diagnostic, not something deferred to NIR lowering or the
    /// interpreter to discover at run time.
    loop_depth: u32,
    /// Every expression's (and block's) type as check_expr/check_block
    /// resolved it, keyed by its stable `ExprId` rather than its span
    /// (see `ExprId`'s doc comment for why). May still contain
    /// unresolved `Ty::Var`s until `check_module` does a final
    /// `ctx.resolve` pass over the whole map, mirroring how
    /// `local_types` is finalized.
    expr_types: HashMap<ExprId, Ty>,
    /// See [`TypeckResult::pattern_case`].
    pattern_case: HashMap<crate::hir::PatternId, (ItemId, usize)>,
    /// See [`TypeckResult::call_type_args`].
    call_type_args: HashMap<ExprId, Vec<Ty>>,
    /// See [`TypeckResult::call_evidence`].
    call_evidence: HashMap<ExprId, Vec<Evidence>>,
    /// See [`TypeckResult::protocol_call_evidence`].
    protocol_call_evidence: HashMap<ExprId, Evidence>,
    /// Starting work budget for each match's exhaustiveness analysis.
    /// Always `exhaustive::MAX_USEFULNESS_STEPS` in `check_module`; a
    /// smaller value is a controlled test seam for exercising
    /// `MatchCoverage::Failed` deterministically, without a fixture
    /// that actually consumes 100,000 steps.
    pattern_budget: usize,
    /// Which function(s) must satisfy the executable entry signature --
    /// see [`EntryMain`].
    entry_main: EntryMain,
    /// Every function/record/variant's own generic parameters, in
    /// declaration order -- collected once, up front, from the whole
    /// (already name-resolved) module, so resolving a *reference* to any
    /// one of them (in a field type possibly declared later, or earlier,
    /// than the reference) never depends on processing order
    /// (`rfcs/0008`).
    generic_params: HashMap<ItemId, Vec<TypeParamId>>,
    /// Every distinct generic instance (`GenericInstanceKey`) this
    /// checker has resolved a call/construction against so far --
    /// central bookkeeping for the compile-wide instance budget
    /// (`crate::limits::MAX_GENERIC_INSTANCES`), never an independent
    /// counter duplicated per call site.
    generic_instances: std::collections::HashSet<GenericInstanceKey>,
    /// Every declared protocol's own type parameters and method
    /// signatures (`rfcs/0009`), keyed by its canonical `ItemId` -- built
    /// once, before any extend or function body is checked.
    protocols: HashMap<ItemId, ProtocolInfo>,
    /// Every extend declaration this compilation accepts as coherent and
    /// authorized (`rfcs/0009`) -- one that failed authority/overlap/
    /// completeness validation is diagnosed but excluded here, so the
    /// capability solver below never compounds one error into another.
    extends: Vec<ExtendInfo>,
    /// Memoizes the capability solver's own concrete-requirement
    /// resolution (`capability::resolve_concrete_requirement`) by
    /// canonical [`CapabilityRequirement`] identity -- a requirement
    /// already resolved once (successfully or not) is never re-solved,
    /// the same reason `generic_instances` exists for ordinary generic
    /// instantiation.
    capability_cache: HashMap<CapabilityRequirement, Result<Evidence, ()>>,
}

#[derive(Clone)]
struct RecordInfo {
    /// The record's own declaration symbol, carried so `Ty::Named` can
    /// always be built with the declaration's own name (see
    /// `named_record_ty`), the same reason `VariantInfo` carries one.
    name: Symbol,
    /// `(field name, declared type, is_public)`, in declaration order.
    /// A field's declared type may reference `type_params` via
    /// `Ty::Param`, symbolically -- substituted with a specific use's
    /// own arguments wherever it's read out (`rfcs/0008`).
    fields: Vec<(Symbol, Ty, bool)>,
    /// Where this record was declared -- compared against `self.source`
    /// (the module currently being checked) to tell an in-module field
    /// access/construction (always allowed) apart from a cross-module
    /// one (only ever allowed for a `public` field).
    source: SourceId,
    /// This record's own generic parameters, in declaration order.
    /// Empty for a non-generic record.
    type_params: Vec<TypeParamId>,
}

#[derive(Clone)]
struct VariantInfo {
    /// The variant's own declaration symbol -- e.g. `LookupResult`, not
    /// one of its case names -- carried so `Ty::Named` can always be
    /// built with the declaration's own name (see `named_variant_ty`).
    name: Symbol,
    /// `(case name, declared payload types)`, in declaration order. A
    /// payload type may reference `type_params` via `Ty::Param`,
    /// symbolically (`rfcs/0008`).
    cases: Vec<(Symbol, Vec<Ty>)>,
    /// This variant's own generic parameters, in declaration order.
    /// Empty for a non-generic variant.
    type_params: Vec<TypeParamId>,
    /// See [`RecordInfo::source`].
    source: SourceId,
}

impl<'a> Checker<'a> {
    /// Collects every function/record/variant's own generic parameter
    /// identities, once, before anything resolves a single type
    /// reference -- so resolving a reference to any one of them (a
    /// field typed with a record declared elsewhere in the module,
    /// forward or backward) can validate its arity without depending on
    /// which order `build_aggregate_info`/`build_signatures` happens to
    /// process declarations in (`rfcs/0008`).
    fn collect_generic_params(&mut self, hir: &HirModule) {
        for r in &hir.records {
            self.generic_params
                .insert(r.id, r.type_params.iter().map(|p| p.id).collect());
        }
        for v in &hir.variants {
            self.generic_params
                .insert(v.id, v.type_params.iter().map(|p| p.id).collect());
        }
        for f in &hir.functions {
            self.generic_params
                .insert(f.id, f.type_params.iter().map(|p| p.id).collect());
        }
    }

    /// Resolves every declared record's field types and every declared
    /// variant's case payload types, once, before any function body or
    /// the aggregate-cycle check runs -- both need every item's fields/
    /// payloads already resolved to `Ty`.
    fn build_aggregate_info(&mut self, hir: &HirModule) {
        for r in &hir.records {
            self.source = r.source;
            let fields = r
                .fields
                .iter()
                .map(|f| (f.name, self.resolve_named_type(&f.ty), f.public))
                .collect();
            self.records.insert(
                r.id,
                RecordInfo {
                    name: r.name,
                    fields,
                    source: r.source,
                    type_params: r.type_params.iter().map(|p| p.id).collect(),
                },
            );
        }
        for v in &hir.variants {
            self.source = v.source;
            let cases = v
                .cases
                .iter()
                .map(|c| {
                    let payload = c
                        .payload
                        .iter()
                        .map(|t| self.resolve_named_type(t))
                        .collect();
                    (c.name, payload)
                })
                .collect();
            self.variants.insert(
                v.id,
                VariantInfo {
                    name: v.name,
                    cases,
                    type_params: v.type_params.iter().map(|p| p.id).collect(),
                    source: v.source,
                },
            );
            self.variant_display.insert(
                v.id,
                (
                    self.interner.resolve(v.name).to_string(),
                    v.cases
                        .iter()
                        .map(|c| self.interner.resolve(c.name).to_string())
                        .collect(),
                ),
            );
        }
    }

    /// Rejects an infinitely-sized direct (or indirect) aggregate cycle
    /// -- see `typeck::cycles` -- once, before any function body is
    /// checked, so a cyclic declaration is reported even if nothing in
    /// the module ever constructs it.
    fn check_aggregate_cycles(&mut self, hir: &HirModule) {
        let field_types: HashMap<ItemId, Vec<Ty>> = self
            .records
            .iter()
            .map(|(id, info)| {
                (
                    *id,
                    info.fields.iter().map(|(_, ty, _)| ty.clone()).collect(),
                )
            })
            .collect();
        let payload_types: HashMap<ItemId, Vec<Vec<Ty>>> = self
            .variants
            .iter()
            .map(|(id, info)| (*id, info.cases.iter().map(|(_, tys)| tys.clone()).collect()))
            .collect();
        self.diagnostics.extend(cycles::check_cycles(
            hir,
            &field_types,
            &payload_types,
            self.interner,
        ));
    }

    fn build_signatures(&mut self, hir: &HirModule) {
        for f in &hir.functions {
            self.source = f.source;
            let params = f
                .params
                .iter()
                .map(|p| self.resolve_named_type(&p.ty))
                .collect();
            let ret = f
                .return_type
                .as_ref()
                .map(|t| self.resolve_named_type(t))
                .unwrap_or(Ty::Unit);
            let requirements = self.resolve_requirements(&f.requirements);
            self.functions.insert(
                f.id,
                FunctionSig {
                    params,
                    ret,
                    type_params: f.type_params.iter().map(|p| p.id).collect(),
                    requirements,
                    span: f.span,
                    source: f.source,
                },
            );
        }
        // Every extend method is registered exactly like an ordinary
        // function -- it shares its owning extend's own `type_params`
        // (see `HirFunction::type_params`'s own doc comment) and
        // `requirements` (already resolved into `HirFunction::requirements`
        // by `hir::lower`), so `check_function` needs no extend-specific
        // path at all.
        for e in &hir.extends {
            self.source = e.source;
            let extend_type_params: Vec<TypeParamId> = e.type_params.iter().map(|p| p.id).collect();
            for m in &e.methods {
                let params = m
                    .params
                    .iter()
                    .map(|p| self.resolve_named_type(&p.ty))
                    .collect();
                let ret = m
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_named_type(t))
                    .unwrap_or(Ty::Unit);
                let requirements = self.resolve_requirements(&m.requirements);
                self.functions.insert(
                    m.id,
                    FunctionSig {
                        params,
                        ret,
                        type_params: extend_type_params.clone(),
                        requirements,
                        span: m.span,
                        source: m.source,
                    },
                );
            }
        }
    }

    /// Converts a type reference already resolved by `hir::lower`
    /// against its *declaring module's own* namespace (see [`HirType`])
    /// into the checker's internal `Ty` -- an aggregate reference is
    /// already an exact `ItemId` by this point, never re-derived from a
    /// surface name here. A name `hir::lower` couldn't resolve to a
    /// locally-known aggregate is checked against the primitive
    /// namespace; if it's not that either, it's genuinely unknown and is
    /// a diagnostic at the type's own span -- `Ty::Error` is only ever
    /// returned *after* recording why, never as a silent wildcard for
    /// "some type we don't recognize".
    ///
    /// A generic aggregate reference validates its arity against
    /// `self.generic_params` (collected once, up front, for every
    /// declaration in the whole module -- see [`Self::collect_generic_params`])
    /// and resolves to `Ty::Applied` when correct; a non-generic
    /// declaration always resolves to the same `Ty::Named` it always
    /// has (`rfcs/0008`).
    fn resolve_named_type(&mut self, ty: &HirType) -> Ty {
        match ty {
            HirType::Aggregate {
                item, name, args, ..
            } => {
                let resolved_args: Vec<Ty> =
                    args.iter().map(|a| self.resolve_named_type(a)).collect();
                let type_params = self.generic_params.get(item).cloned().unwrap_or_default();
                if type_params.is_empty() {
                    if !resolved_args.is_empty() {
                        let text = self.registry.qualified_name(*item, self.interner);
                        self.diagnostics.push(
                            Diagnostic::error(
                                codes::TYPE_ARGUMENTS_TO_NON_GENERIC,
                                self.source,
                                ty.span(),
                                format!("`{text}` is not generic and cannot take type arguments"),
                            )
                            .with_primary_label("type arguments on a non-generic declaration"),
                        );
                        return Ty::Error;
                    }
                    Ty::Named(*item, *name)
                } else if resolved_args.is_empty() {
                    let text = self.registry.qualified_name(*item, self.interner);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::MISSING_TYPE_ARGUMENTS,
                            self.source,
                            ty.span(),
                            format!(
                                "`{text}` is generic and requires {} type argument(s)",
                                type_params.len()
                            ),
                        )
                        .with_primary_label("missing type arguments"),
                    );
                    Ty::Error
                } else if resolved_args.len() != type_params.len() {
                    let text = self.registry.qualified_name(*item, self.interner);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::GENERIC_ARITY_MISMATCH,
                            self.source,
                            ty.span(),
                            format!(
                                "`{text}` expects {} type argument(s), found {}",
                                type_params.len(),
                                resolved_args.len()
                            ),
                        )
                        .with_primary_label("wrong number of type arguments"),
                    );
                    Ty::Error
                } else {
                    Ty::Applied(*item, resolved_args)
                }
            }
            HirType::Param { id, name, .. } => Ty::Param(*id, *name),
            HirType::Unresolved { name, span } => {
                let text = self.interner.resolve(*name);
                if let Some(prim) = primitive_from_name(text) {
                    return prim;
                }
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::UNKNOWN_TYPE,
                        self.source,
                        *span,
                        format!("cannot find type `{text}` in this scope"),
                    )
                    .with_primary_label("unknown type"),
                );
                Ty::Error
            }
        }
    }

    /// Records that `key` is a distinct generic instance this
    /// compilation has now resolved, enforcing the shared instance
    /// budget the first time each unique key is seen (never once per
    /// occurrence -- calling `identity(1)` a thousand times is one
    /// instance, not a thousand). Returns `false` once the budget is
    /// exceeded, having already recorded the diagnostic; callers must
    /// not additionally trust the (still returned, best-effort) type in
    /// that case.
    fn record_generic_instance(&mut self, key: GenericInstanceKey, span: Span) -> bool {
        if self.generic_instances.contains(&key) {
            return true;
        }
        if self.generic_instances.len() >= crate::limits::MAX_GENERIC_INSTANCES {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::GENERIC_INSTANCE_BUDGET_EXCEEDED,
                    self.source,
                    span,
                    format!(
                        "this compilation has exceeded its budget of {} distinct generic instances",
                        crate::limits::MAX_GENERIC_INSTANCES
                    ),
                )
                .with_primary_label("generic instance budget exceeded"),
            );
            return false;
        }
        self.generic_instances.insert(key);
        true
    }

    fn check_function(&mut self, f: &HirFunction) {
        // Local IDs are unique across the whole module (hir::lower),
        // so locals from earlier functions are never looked up again;
        // leaving them in place (rather than clearing per function) is
        // what lets check_module snapshot every local's final type into
        // TypeckResult::local_types afterward.
        let sig = self
            .functions
            .get(&f.id)
            .cloned()
            .expect("function was registered");
        for (param, ty) in f.params.iter().zip(sig.params.iter()) {
            self.locals.insert(
                param.local,
                LocalInfo {
                    ty: ty.clone(),
                    mutable: false,
                },
            );
        }
        self.current_return_type = sig.ret.clone();
        self.current_requirements = sig.requirements.clone();
        if !f.uses.is_empty() || !f.raises.is_empty() {
            self.push_unsupported(f.name_span, "`uses`/`raises` effect and error clauses");
        }
        // `napitia run` always calls the entry point with zero arguments,
        // so a `main` declared with parameters can never actually
        // receive them -- that must be caught here, not discovered as
        // missing values at interpretation time. Which function this
        // rule applies to depends on `entry_main`: single-file
        // compilation has no module boundary to scope by identity, so it
        // keeps checking any function named `main` (legacy behavior);
        // project compilation scopes it to the entry module's own
        // `main` by `ItemId`, so `main` declared in any other module is
        // just an ordinary function (`rfcs/0006`).
        let is_entry_main = match self.entry_main {
            EntryMain::ByName => self.interner.resolve(f.name) == "main",
            EntryMain::ByIdentity(entry) => entry == Some(f.id),
        };
        if is_entry_main && !f.params.is_empty() {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::INVALID_MAIN_SIGNATURE,
                    self.source,
                    f.name_span,
                    format!("`main` must take no parameters, found {}", f.params.len()),
                )
                .with_primary_label("`napitia run` calls `main` with no arguments"),
            );
        }
        let body_ty = self.check_block(&f.body);
        self.unify_report(
            &sig.ret,
            &body_ty,
            f.body.span,
            "the function's body does not match its declared return type",
        );
    }

    /// A block's type is `never` if any statement in it unconditionally
    /// diverges (its own type is `never`, e.g. an expression-statement
    /// `return x;`) — even when that statement has no trailing tail
    /// expression at all, which is exactly the case
    /// `func f() -> i64 { return 42; }` needs: the block has one
    /// statement and no tail, so without tracking divergence explicitly
    /// it would otherwise wrongly report its own type as `unit`. Once a
    /// statement has diverged, later statements and any tail are still
    /// type-checked (so unrelated diagnostics in unreachable code are
    /// still reported), but their types can no longer change the
    /// block's own resulting type.
    fn check_block(&mut self, block: &HirBlock) -> Ty {
        let mut diverged = false;
        for stmt in &block.statements {
            if matches!(self.check_stmt(stmt), Ty::Never) {
                diverged = true;
            }
        }
        let tail_ty = match &block.tail {
            Some(expr) => self.check_expr(expr),
            None => Ty::Unit,
        };
        let ty = if diverged { Ty::Never } else { tail_ty };
        // Recorded under the block's own id too, not just the
        // HirExpr::Block wrapper's id (check_expr's caller-side
        // recording): a `while`/`loop` body, an `if` branch, and a
        // function body are all plain HirBlocks with no wrapping
        // HirExpr, so this is the only place their type is ever
        // captured.
        self.expr_types.insert(block.id, ty.clone());
        ty
    }

    /// Type-checks one statement, returning `never` iff the statement
    /// itself unconditionally diverges (so `check_block` can propagate
    /// that to the enclosing block). `while`/`loop` never make the
    /// *enclosing* block diverge in this milestone — proving a loop
    /// always executes at least one divergent iteration would need loop
    /// analysis this checker does not do — so they always contribute
    /// `unit`, matching their statement-only (never tail) grammar
    /// position.
    fn check_stmt(&mut self, stmt: &HirStmt) -> Ty {
        match stmt {
            HirStmt::Binding(b) => {
                let value_ty = self.check_expr(&b.value);
                let final_ty = match &b.ty {
                    Some(ast_ty) => {
                        let declared = self.resolve_named_type(ast_ty);
                        self.unify_report(
                            &declared,
                            &value_ty,
                            b.span,
                            "the initializer does not match the binding's declared type",
                        );
                        declared
                    }
                    None => value_ty.clone(),
                };
                self.locals.insert(
                    b.local,
                    LocalInfo {
                        ty: final_ty,
                        mutable: b.mutable,
                    },
                );
                // A binding whose initializer itself never completes
                // (`value x = return 5;`) means control never reaches
                // past this statement either.
                value_ty
            }
            HirStmt::Expr(e) => self.check_expr(e),
            HirStmt::Defer { expr, span } => {
                self.check_expr(expr);
                self.push_unsupported(*span, "`defer`");
                Ty::Unit
            }
            HirStmt::While {
                condition, body, ..
            } => {
                let cond_ty = self.check_expr(condition);
                self.expect_bool(&cond_ty, condition.span());
                self.loop_depth += 1;
                // The body is still checked for its own independent
                // diagnostics even when the condition itself always
                // diverges (making the body unreachable).
                self.check_block(body);
                self.loop_depth -= 1;
                // A condition that never produces a value is evaluated
                // exactly once, unconditionally, before the loop could
                // ever run -- the `while` statement itself diverges,
                // the same way any other strict use of a `never`
                // expression does.
                if matches!(cond_ty, Ty::Never) {
                    Ty::Never
                } else {
                    Ty::Unit
                }
            }
            HirStmt::Loop { body, .. } => {
                self.loop_depth += 1;
                self.check_block(body);
                self.loop_depth -= 1;
                Ty::Unit
            }
        }
    }

    /// Type-checks one expression and records its final resolved type
    /// under its stable [`ExprId`] in `expr_types`, so NIR lowering
    /// (`nir::lower`) can later read back exactly what this checker
    /// decided rather than re-inferring an approximation of it. Every
    /// arm below must produce a `Ty` and fall through to that recording
    /// step -- there is no arm that returns without one, so no
    /// expression can reach NIR lowering "unseen".
    fn check_expr(&mut self, expr: &HirExpr) -> Ty {
        let ty = self.check_expr_kind(expr);
        self.expr_types.insert(expr.id(), ty.clone());
        ty
    }

    fn check_expr_kind(&mut self, expr: &HirExpr) -> Ty {
        match expr {
            HirExpr::Int { .. } => self.fresh_default(Ty::I64, VarKind::Integer),
            HirExpr::Float { .. } => self.fresh_default(Ty::F64, VarKind::Float),
            HirExpr::Str { .. } => Ty::Str,
            HirExpr::Char { .. } => Ty::Char,
            HirExpr::Bool { .. } => Ty::Bool,
            HirExpr::Local { local, .. } => self
                .locals
                .get(local)
                .map(|i| i.ty.clone())
                .unwrap_or(Ty::Error),
            // Functions are not first-class values in this milestone;
            // only Call special-cases a Function callee directly, so
            // reaching this arm means a function name was used
            // somewhere else (assigned, passed as an argument, etc).
            HirExpr::Function { name, span, .. } => {
                let text = self.interner.resolve(*name);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::FUNCTION_NOT_FIRST_CLASS,
                        self.source,
                        *span,
                        format!(
                            "`{text}` is a function and cannot be used as a value in Alpha 0.1"
                        ),
                    )
                    .with_primary_label("function used as a value"),
                );
                Ty::Error
            }
            // There are no first-class/dynamic protocol methods in
            // Alpha 0.1.5; only `Call` special-cases a
            // `ProtocolMethodRef` callee directly (`rfcs/0009`), so
            // reaching this arm bare means one was referenced without
            // being called.
            HirExpr::ProtocolMethodRef { name, span, .. } => {
                let text = self.interner.resolve(*name);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::PROTOCOL_METHOD_NOT_A_VALUE,
                        self.source,
                        *span,
                        format!(
                            "`{text}` is a protocol method and must be called directly, not used as a value"
                        ),
                    )
                    .with_primary_label("protocol method used as a value"),
                );
                Ty::Error
            }
            // A bare (uncalled) reference to a variant case constructor
            // is itself a complete value only when the case carries no
            // payload; `Call`'s own arm handles a `CaseRef` used as a
            // callee, so reaching this arm bare means the case was
            // referenced directly, e.g. `LookupResult.Missing`.
            HirExpr::CaseRef {
                id,
                variant,
                case,
                type_args,
                span,
                ..
            } => self.check_case_ref(*id, *variant, *case, type_args, *span),
            HirExpr::Unary {
                op, operand, span, ..
            } => self.check_unary(*op, operand, *span),
            HirExpr::Binary {
                op,
                left,
                right,
                span,
                ..
            } => self.check_binary(*op, left, right, *span),
            HirExpr::Assign {
                target,
                op,
                value,
                span,
                ..
            } => self.check_assign(target, *op, value, *span),
            HirExpr::Call {
                id,
                callee,
                args,
                span,
            } => self.check_call(*id, callee, args, *span),
            HirExpr::Field {
                base, name, span, ..
            } => self.check_field_access(base, *name, *span),
            HirExpr::Cast { expr, ty, span, .. } => {
                self.check_expr(expr);
                // Still resolve the target type name, so an unknown
                // type in a cast gets its own T0006 diagnostic rather
                // than being silently swallowed by the unsupported-cast
                // diagnostic below.
                self.resolve_named_type(ty);
                self.push_unsupported(*span, "casts (`as`)");
                Ty::Error
            }
            HirExpr::Try { expr, span, .. } => {
                self.check_expr(expr);
                self.push_unsupported(*span, "postfix `?`");
                Ty::Error
            }
            HirExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => self.check_if(condition, then_branch, else_branch),
            HirExpr::Match {
                scrutinee,
                arms,
                span,
                ..
            } => self.check_match(scrutinee, arms, *span),
            HirExpr::Block(block) => self.check_block(block),
            HirExpr::RecordLiteral {
                id,
                record,
                type_args,
                fields,
                span,
            } => self.check_record_literal(*id, *record, type_args, fields, *span),
            HirExpr::Return { value, span, .. } => {
                let value_ty = value
                    .as_ref()
                    .map(|v| self.check_expr(v))
                    .unwrap_or(Ty::Unit);
                let ret = self.current_return_type.clone();
                self.unify_report(
                    &ret,
                    &value_ty,
                    *span,
                    "the returned value does not match the function's declared return type",
                );
                Ty::Never
            }
            HirExpr::Break { value, span, .. } => {
                if let Some(v) = value {
                    // Still checked for its own independent diagnostics,
                    // but the value itself is unconditionally
                    // unsupported -- unifying it against `unit` and
                    // accepting a unit-typed value silently would let
                    // `break unit_expr;` through with no diagnostic at
                    // all, which is exactly the kind of fake acceptance
                    // this checker must not produce. Loop-as-expression
                    // is accepted direction, not implemented
                    // (spec/0002), regardless of the value's own type.
                    self.check_expr(v);
                    self.push_unsupported(*span, "`break` with a value (loop-as-expression)");
                }
                self.check_loop_control(*span, "break");
                Ty::Never
            }
            HirExpr::Continue { span, .. } => {
                self.check_loop_control(*span, "continue");
                Ty::Never
            }
            HirExpr::Error { .. } => Ty::Error,
        }
    }

    fn check_unary(&mut self, op: UnaryOp, operand: &HirExpr, span: Span) -> Ty {
        let ty = self.check_expr(operand);
        // Every unary operator strictly evaluates its operand first, so
        // an operand that provably never produces a value means the
        // operator itself is never reached either -- the result must
        // stay `never`, not whatever this operator would otherwise
        // produce (e.g. `Ty::Bool` for `!`).
        if matches!(ty, Ty::Never) {
            return Ty::Never;
        }
        match op {
            UnaryOp::Neg => {
                self.require_numeric(&ty, span);
                ty
            }
            UnaryOp::Not => {
                self.expect_bool(&ty, span);
                Ty::Bool
            }
            UnaryOp::BitNot => {
                self.require_integer(&ty, span);
                ty
            }
        }
    }

    fn check_binary(&mut self, op: BinaryOp, left: &HirExpr, right: &HirExpr, span: Span) -> Ty {
        let lt = self.check_expr(left);

        // `&&`/`||` short-circuit: the right operand only actually runs
        // when the left doesn't already decide the result, so a
        // divergent *right* operand must not force the whole expression
        // to `never` (there's a real, reachable path that skips it). A
        // divergent *left* operand always runs, though, so it does.
        if matches!(op, BinaryOp::And | BinaryOp::Or) {
            if matches!(lt, Ty::Never) {
                // The right side is unreachable, but still checked for
                // its own independent diagnostics.
                self.check_expr(right);
                return Ty::Never;
            }
            self.expect_bool(&lt, span);
            let rt = self.check_expr(right);
            self.expect_bool(&rt, span);
            return Ty::Bool;
        }

        let rt = self.check_expr(right);

        if matches!(op, BinaryOp::Range | BinaryOp::RangeInclusive) {
            self.push_unsupported(span, "range expressions (`..`/`..=`)");
            return Ty::Error;
        }

        // Every remaining operator strictly evaluates both operands
        // before doing anything, so either side being `never` means the
        // operator itself is never actually reached.
        if matches!(lt, Ty::Never) || matches!(rt, Ty::Never) {
            return Ty::Never;
        }

        match op {
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem => {
                self.unify_report(
                    &lt,
                    &rt,
                    span,
                    "operands of this operator must have the same type",
                );
                self.require_numeric(&lt, span);
                lt
            }
            BinaryOp::BitAnd
            | BinaryOp::BitOr
            | BinaryOp::BitXor
            | BinaryOp::Shl
            | BinaryOp::Shr => {
                self.unify_report(
                    &lt,
                    &rt,
                    span,
                    "operands of this operator must have the same type",
                );
                self.require_integer(&lt, span);
                lt
            }
            BinaryOp::Eq | BinaryOp::Ne => {
                // Equality is not among the operations proven safe for
                // every possible type an unconstrained `T` might be
                // instantiated with (`rfcs/0008`) -- `left == right`
                // must be rejected here, symbolically, the same way
                // `left + right` already is by `require_numeric`, never
                // deferred to a runtime comparison against whatever
                // concrete type a particular call site happens to
                // instantiate `T` with.
                let resolved_lt = self.ctx.resolve(&lt);
                let resolved_rt = self.ctx.resolve(&rt);
                if self.report_unconstrained_type_parameter(&resolved_lt, span)
                    || self.report_unconstrained_type_parameter(&resolved_rt, span)
                {
                    return Ty::Error;
                }
                if self.is_aggregate(&lt) || self.is_aggregate(&rt) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::AGGREGATE_EQUALITY_UNSUPPORTED,
                            self.source,
                            span,
                            "record/variant equality is not implemented in Alpha 0.1.1",
                        )
                        .with_primary_label("aggregate equality"),
                    );
                    return Ty::Error;
                }
                self.unify_report(
                    &lt,
                    &rt,
                    span,
                    "operands of a comparison must have the same type",
                );
                Ty::Bool
            }
            BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                // Ordering is exactly as unproven for an unconstrained
                // `T` as equality is (`rfcs/0008`) -- rejected here,
                // symbolically, before any instantiation.
                let resolved_lt = self.ctx.resolve(&lt);
                let resolved_rt = self.ctx.resolve(&rt);
                if self.report_unconstrained_type_parameter(&resolved_lt, span)
                    || self.report_unconstrained_type_parameter(&resolved_rt, span)
                {
                    return Ty::Error;
                }
                self.unify_report(
                    &lt,
                    &rt,
                    span,
                    "operands of a comparison must have the same type",
                );
                Ty::Bool
            }
            BinaryOp::And | BinaryOp::Or | BinaryOp::Range | BinaryOp::RangeInclusive => {
                unreachable!("handled above")
            }
        }
    }

    fn check_assign(&mut self, target: &HirExpr, op: AssignOp, value: &HirExpr, span: Span) -> Ty {
        let target_ty = self.check_expr(target);
        match target {
            HirExpr::Local { local, name, .. } => {
                if let Some(info) = self.locals.get(local)
                    && !info.mutable
                {
                    let text = self.interner.resolve(*name);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::IMMUTABLE_ASSIGN,
                            self.source,
                            span,
                            format!("cannot assign to `{text}`, which is not declared `mutable`"),
                        )
                        .with_primary_label("assignment to an immutable binding"),
                    );
                }
            }
            // Field mutation gets its own dedicated diagnostic (T0015),
            // distinct from T0008's generic "invalid assignment
            // target" -- the point being made is that mutation itself
            // is unimplemented, not that the target shape is wrong.
            // `Error` already traces back to a diagnostic recorded
            // elsewhere and needs no second complaint.
            HirExpr::Field { span, .. } => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::FIELD_MUTATION_UNSUPPORTED,
                        self.source,
                        *span,
                        "field mutation is not implemented in Alpha 0.1.1",
                    )
                    .with_primary_label("cannot assign to a field"),
                );
            }
            HirExpr::Error { .. } => {}
            _ => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::INVALID_ASSIGN_TARGET,
                        self.source,
                        span,
                        "the left-hand side of an assignment must be a mutable binding",
                    )
                    .with_primary_label("invalid assignment target"),
                );
            }
        }

        let value_ty = self.check_expr(value);
        self.unify_report(
            &target_ty,
            &value_ty,
            span,
            "the assigned value does not match the binding's type",
        );

        match op {
            AssignOp::Assign => {}
            AssignOp::BitAnd
            | AssignOp::BitOr
            | AssignOp::BitXor
            | AssignOp::Shl
            | AssignOp::Shr => {
                self.require_integer(&target_ty, span);
            }
            _ => self.require_numeric(&target_ty, span),
        }

        // The assignment itself is strict: it evaluates the right-hand
        // side before ever performing the store, so a right-hand side
        // that never produces a value means the assignment never
        // completes either.
        if matches!(value_ty, Ty::Never) {
            Ty::Never
        } else {
            Ty::Unit
        }
    }

    /// Resolves the type arguments to use for one generic call or
    /// construction site (`rfcs/0008`): `explicit`'s own resolved types,
    /// validated for arity, when the syntax supplied any; otherwise, if
    /// `allow_inference`, one fresh inference variable per parameter (a
    /// caller then unifies each argument against the substituted
    /// parameter type to solve them). `what` is a pre-quoted name
    /// (`` `identity` ``) for diagnostics. Returns `None` after already
    /// recording the diagnostic on an explicit arity mismatch, or (when
    /// `!allow_inference`) on an omitted type-argument list for a
    /// generic declaration -- record/variant *construction* always
    /// requires explicit arguments (there is no infer-from-fields form),
    /// while a function call or a payload-carrying variant constructor
    /// may infer from its arguments the same way.
    fn resolve_generic_args(
        &mut self,
        type_params: &[TypeParamId],
        explicit: &[HirType],
        allow_inference: bool,
        span: Span,
        what: &str,
    ) -> Option<(HashMap<TypeParamId, Ty>, bool)> {
        if !explicit.is_empty() {
            let resolved: Vec<Ty> = explicit
                .iter()
                .map(|t| self.resolve_named_type(t))
                .collect();
            if resolved.len() != type_params.len() {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::GENERIC_ARITY_MISMATCH,
                        self.source,
                        span,
                        format!(
                            "{what} expects {} type argument(s), found {}",
                            type_params.len(),
                            resolved.len()
                        ),
                    )
                    .with_primary_label("wrong number of type arguments"),
                );
                return None;
            }
            return Some((type_params.iter().copied().zip(resolved).collect(), false));
        }
        if type_params.is_empty() {
            return Some((HashMap::new(), false));
        }
        if !allow_inference {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::MISSING_TYPE_ARGUMENTS,
                    self.source,
                    span,
                    format!(
                        "{what} is generic and requires {} type argument(s)",
                        type_params.len()
                    ),
                )
                .with_primary_label("missing type arguments"),
            );
            return None;
        }
        let subst = type_params
            .iter()
            .map(|&p| (p, Ty::Var(self.ctx.fresh_var())))
            .collect();
        Some((subst, true))
    }

    /// After every argument has been unified against its (possibly
    /// substituted) parameter type, checks that every one of an
    /// *inferred* call's fresh type-argument variables actually got
    /// resolved -- a parameter appearing only in the return type
    /// (`func create[T]() -> T;`) is never touched by argument
    /// unification at all, so it stays an unbound `Ty::Var` unless the
    /// caller supplied it explicitly (`rfcs/0008`).
    fn check_inferred_args_resolved(
        &mut self,
        type_params: &[TypeParamId],
        subst: &HashMap<TypeParamId, Ty>,
        span: Span,
        what: &str,
    ) -> bool {
        let mut ok = true;
        for p in type_params {
            if let Some(ty) = subst.get(p)
                && matches!(self.ctx.resolve(ty), Ty::Var(_))
            {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::CANNOT_INFER_TYPE_ARGUMENT,
                        self.source,
                        span,
                        format!(
                            "cannot infer {what}'s type argument from these arguments; provide it explicitly"
                        ),
                    )
                    .with_primary_label("type argument cannot be inferred"),
                );
                ok = false;
            }
        }
        ok
    }

    /// Like [`Self::unify_report`], but used specifically for an
    /// *inferred* generic call/construction's argument-vs-parameter
    /// check: a conflict here means two arguments disagreed about what
    /// the same type parameter should be (`choose(1, "text")` for
    /// `func choose[T](left: T, right: T) -> T`), which gets its own
    /// diagnostic distinct from an ordinary type mismatch. An
    /// *explicit*-type-argument call's argument mismatches are ordinary
    /// mismatches (the caller already said what the type is), so callers
    /// pass `inferred: false` to fall back to `unify_report` unchanged.
    fn unify_arg_report(
        &mut self,
        expected: &Ty,
        actual: &Ty,
        span: Span,
        message: &str,
        inferred: bool,
    ) -> bool {
        if !inferred {
            return self.unify_report(expected, actual, span, message);
        }
        if let Err((ra, rb)) = unify(&mut self.ctx, expected, actual) {
            self.diagnostics.push(Diagnostic::error(
                codes::CONFLICTING_INFERRED_ARGUMENTS,
                self.source,
                span,
                format!(
                    "{message}: expected `{}`, found `{}`",
                    self.display_for_diagnostic(&ra),
                    self.display_for_diagnostic(&rb)
                ),
            ));
            false
        } else {
            true
        }
    }

    /// Resolves every one of a callee's own capability `requirements`
    /// (substituted via this specific call's own `subst`, then fully
    /// resolved -- a callee's requirement can still be symbolic in terms
    /// of what *this* call itself is generic over) against the
    /// currently-checked declaration's own forwarding environment,
    /// falling back to the concrete-extension solver. Returns `None`,
    /// having already recorded a diagnostic, the moment any single
    /// requirement fails -- never a partial evidence list, matching the
    /// same all-or-nothing contract every other part of a call's own
    /// success (`ok`) already follows.
    fn resolve_call_evidence(
        &mut self,
        requirements: &[CapabilityRequirement],
        subst: &HashMap<TypeParamId, Ty>,
        span: Span,
    ) -> Option<Vec<Evidence>> {
        let own_requirements = self.current_requirements.clone();
        let mut evidence = Vec::with_capacity(requirements.len());
        for req in requirements {
            let substituted = CapabilityRequirement::new(
                req.protocol,
                req.arguments
                    .iter()
                    .map(|t| deep_resolve(&self.ctx, &substitute(t, subst)))
                    .collect(),
            );
            evidence.push(self.resolve_requirement(&substituted, &own_requirements, span)?);
        }
        Some(evidence)
    }

    /// An explicit protocol-call expression, `Protocol[Args].method(..)`
    /// (`rfcs/0009`) -- the only protocol-call syntax in Alpha 0.1.5.
    /// Checks the method's own parameter/return types (substituting
    /// `Args` into the protocol's own declared signature), then resolves
    /// exactly which extension answers this specific
    /// `Protocol[Args]` requirement, recording the result for
    /// `nir::lower` to attach to the corresponding NIR instruction.
    #[allow(clippy::too_many_arguments)]
    fn check_protocol_call(
        &mut self,
        call_id: ExprId,
        protocol: ItemId,
        arguments: &[HirType],
        method: usize,
        name: Symbol,
        ref_span: Span,
        args: &[HirExpr],
        span: Span,
    ) -> Ty {
        let arg_tys: Vec<Ty> = args.iter().map(|a| self.check_expr(a)).collect();
        let any_arg_never = arg_tys.iter().any(|t| matches!(t, Ty::Never));
        let never_or_error = |never: bool| if never { Ty::Never } else { Ty::Error };

        let resolved_arguments: Vec<Ty> = arguments
            .iter()
            .map(|a| self.resolve_named_type(a))
            .collect();
        let Some(type_param_count) = self.protocols.get(&protocol).map(|p| p.type_params.len())
        else {
            return never_or_error(any_arg_never);
        };
        if resolved_arguments.len() != type_param_count {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::PROTOCOL_ARITY_MISMATCH,
                    self.source,
                    ref_span,
                    format!(
                        "this protocol requires {type_param_count} type argument(s), found {}",
                        resolved_arguments.len()
                    ),
                )
                .with_primary_label("wrong number of protocol type arguments"),
            );
            return never_or_error(any_arg_never);
        }
        let subst: HashMap<TypeParamId, Ty> = self
            .protocols
            .get(&protocol)
            .map(|p| p.type_params.clone())
            .unwrap_or_default()
            .into_iter()
            .zip(resolved_arguments.iter().cloned())
            .collect();
        let Some((expected_params, expected_ret)) = self
            .protocols
            .get(&protocol)
            .and_then(|p| p.methods.get(method))
            .map(|m| {
                (
                    m.params
                        .iter()
                        .map(|t| substitute(t, &subst))
                        .collect::<Vec<_>>(),
                    substitute(&m.ret, &subst),
                )
            })
        else {
            return never_or_error(any_arg_never);
        };

        let text = format!("`{}`", self.interner.resolve(name));
        if expected_params.len() != args.len() {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::ARITY_MISMATCH,
                    self.source,
                    span,
                    format!(
                        "{text} expects {} argument(s), found {}",
                        expected_params.len(),
                        args.len()
                    ),
                )
                .with_primary_label("wrong number of arguments"),
            );
        } else {
            for (arg_ty, param_ty) in arg_tys.iter().zip(expected_params.iter()) {
                self.unify_report(
                    param_ty,
                    arg_ty,
                    span,
                    "argument type does not match the protocol method's declared parameter type",
                );
            }
        }

        let requirement = CapabilityRequirement::new(protocol, resolved_arguments);
        let own_requirements = self.current_requirements.clone();
        let Some(evidence) = self.resolve_requirement(&requirement, &own_requirements, ref_span)
        else {
            return never_or_error(any_arg_never);
        };
        self.protocol_call_evidence.insert(call_id, evidence);

        if any_arg_never {
            Ty::Never
        } else {
            expected_ret
        }
    }

    fn check_call(
        &mut self,
        call_id: ExprId,
        callee: &HirExpr,
        args: &[HirExpr],
        span: Span,
    ) -> Ty {
        if let HirExpr::CaseRef {
            variant,
            case,
            type_args,
            ..
        } = callee
        {
            return self.check_variant_construct(call_id, *variant, *case, type_args, args, span);
        }
        if let HirExpr::ProtocolMethodRef {
            protocol,
            arguments,
            method,
            name,
            span: ref_span,
            ..
        } = callee
        {
            return self.check_protocol_call(
                call_id, *protocol, arguments, *method, *name, *ref_span, args, span,
            );
        }

        let arg_tys: Vec<Ty> = args.iter().map(|a| self.check_expr(a)).collect();
        let any_arg_never = arg_tys.iter().any(|t| matches!(t, Ty::Never));

        let HirExpr::Function {
            item,
            name,
            type_args,
            ..
        } = callee
        else {
            let callee_ty = self.check_expr(callee);
            let resolved_callee_ty = self.ctx.resolve(&callee_ty);
            // Callability is exactly as unproven for an unconstrained
            // `T` as every other capability nothing yet guarantees it
            // has (`rfcs/0008`) -- rejected with the same dedicated
            // diagnostic every other operation on `T` is, before falling
            // to the ordinary "not callable" message that would
            // otherwise suggest `T` is simply the wrong concrete type.
            // Error/Never already trace back to a diagnostic recorded
            // elsewhere (an unresolved name, an unsupported feature, a
            // divergent expression) -- piling "not callable" on top
            // would just be noise about the same underlying problem.
            if !matches!(callee_ty, Ty::Error | Ty::Never)
                && !self.report_unconstrained_type_parameter(&resolved_callee_ty, span)
            {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::NOT_CALLABLE,
                        self.source,
                        span,
                        format!(
                            "cannot call a value of type `{}`",
                            self.display_for_diagnostic(&callee_ty)
                        ),
                    )
                    .with_primary_label("not callable"),
                );
            }
            return if any_arg_never || matches!(callee_ty, Ty::Never) {
                Ty::Never
            } else {
                Ty::Error
            };
        };

        let Some(sig) = self.functions.get(item).cloned() else {
            return if any_arg_never { Ty::Never } else { Ty::Error };
        };

        let quoted = format!("`{}`", self.interner.resolve(*name));
        let Some((subst, inferred)) =
            self.resolve_generic_args(&sig.type_params, type_args, true, span, &quoted)
        else {
            return if any_arg_never { Ty::Never } else { Ty::Error };
        };

        if sig.params.len() != args.len() {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::ARITY_MISMATCH,
                    self.source,
                    span,
                    format!(
                        "{quoted} expects {} argument(s), found {}",
                        sig.params.len(),
                        args.len()
                    ),
                )
                .with_primary_label("wrong number of arguments")
                .with_label_in(sig.source, sig.span, "function defined here"),
            );
        } else {
            for (arg_ty, param_ty) in arg_tys.iter().zip(sig.params.iter()) {
                let substituted = substitute(param_ty, &subst);
                self.unify_arg_report(
                    &substituted,
                    arg_ty,
                    span,
                    "argument type does not match the parameter's declared type",
                    inferred,
                );
            }
        }

        let mut ok =
            !inferred || self.check_inferred_args_resolved(&sig.type_params, &subst, span, &quoted);
        if ok && !sig.type_params.is_empty() {
            let resolved_args: Vec<Ty> = sig
                .type_params
                .iter()
                .map(|p| {
                    deep_resolve(
                        &self.ctx,
                        subst
                            .get(p)
                            .expect("every declared parameter has a substitution entry"),
                    )
                })
                .collect();
            let key = GenericInstanceKey::new(*item, resolved_args.clone());
            if self.record_generic_instance(key, span) {
                self.call_type_args.insert(call_id, resolved_args);
            } else {
                ok = false;
            }
        }
        if ok && !sig.requirements.is_empty() {
            match self.resolve_call_evidence(&sig.requirements, &subst, span) {
                Some(evidence) => {
                    self.call_evidence.insert(call_id, evidence);
                }
                None => ok = false,
            }
        }
        if !ok {
            return if any_arg_never { Ty::Never } else { Ty::Error };
        }

        let ret = substitute(&sig.ret, &subst);
        // A call is strict in its arguments: every one of them is
        // evaluated before the call itself ever happens, so any
        // argument that never produces a value means the call is never
        // actually reached.
        if any_arg_never { Ty::Never } else { ret }
    }

    /// A bare (uncalled) variant-case reference: only valid when that
    /// case carries no payload, in which case it is itself a complete
    /// value of the variant's type -- `LookupResult.Missing` needs no
    /// call syntax at all, matching a unit case allocating no
    /// fabricated payload. A generic variant referenced this way has
    /// nothing to infer its type argument from, so it always requires
    /// an explicit qualified application (`Maybe[i64].None`).
    fn check_case_ref(
        &mut self,
        id: ExprId,
        variant: ItemId,
        case: usize,
        type_args: &[HirType],
        span: Span,
    ) -> Ty {
        let Some(info) = self.variants.get(&variant).cloned() else {
            return Ty::Error;
        };
        let (case_name, payload) = &info.cases[case];
        if !payload.is_empty() {
            let text = self.interner.resolve(*case_name);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::ARITY_MISMATCH,
                    self.source,
                    span,
                    format!(
                        "`{text}` expects {} argument(s), found 0 (write `{text}(...)`)",
                        payload.len()
                    ),
                )
                .with_primary_label("missing constructor arguments"),
            );
            return Ty::Error;
        }
        let quoted = format!("`{}`", self.interner.resolve(info.name));
        let Some((subst, _)) =
            self.resolve_generic_args(&info.type_params, type_args, false, span, &quoted)
        else {
            return Ty::Error;
        };
        if info.type_params.is_empty() {
            return self.named_variant_ty(variant);
        }
        let resolved_args: Vec<Ty> = info
            .type_params
            .iter()
            .map(|p| {
                subst
                    .get(p)
                    .expect("explicit substitution covers every parameter")
                    .clone()
            })
            .collect();
        let key = GenericInstanceKey::new(variant, resolved_args.clone());
        if !self.record_generic_instance(key, span) {
            return Ty::Error;
        }
        // Never leave a known-generic construction to default to an
        // empty argument list downstream: NIR lowering reads this same
        // map back by `id` and, without an entry here, silently treats
        // this construction as if it applied no type arguments at all
        // (`rfcs/0008`).
        self.call_type_args.insert(id, resolved_args.clone());
        Ty::Applied(variant, resolved_args)
    }

    fn check_variant_construct(
        &mut self,
        call_id: ExprId,
        variant: ItemId,
        case: usize,
        type_args: &[HirType],
        args: &[HirExpr],
        span: Span,
    ) -> Ty {
        let Some(info) = self.variants.get(&variant).cloned() else {
            for a in args {
                self.check_expr(a);
            }
            return Ty::Error;
        };
        let (case_name, payload) = info.cases[case].clone();
        let variant_quoted = format!("`{}`", self.interner.resolve(info.name));
        let Some((subst, inferred)) =
            self.resolve_generic_args(&info.type_params, type_args, true, span, &variant_quoted)
        else {
            for a in args {
                self.check_expr(a);
            }
            return Ty::Error;
        };

        let arg_tys: Vec<Ty> = args.iter().map(|a| self.check_expr(a)).collect();
        let any_arg_never = arg_tys.iter().any(|t| matches!(t, Ty::Never));

        if payload.len() != args.len() {
            let text = self.interner.resolve(case_name);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::ARITY_MISMATCH,
                    self.source,
                    span,
                    format!(
                        "`{text}` expects {} argument(s), found {}",
                        payload.len(),
                        args.len()
                    ),
                )
                .with_primary_label("wrong number of arguments"),
            );
        } else {
            for (arg_ty, payload_ty) in arg_tys.iter().zip(payload.iter()) {
                let substituted = substitute(payload_ty, &subst);
                self.unify_arg_report(
                    &substituted,
                    arg_ty,
                    span,
                    "payload argument type does not match the case's declared type",
                    inferred,
                );
            }
        }

        let mut ok = !inferred
            || self.check_inferred_args_resolved(&info.type_params, &subst, span, &variant_quoted);
        let mut result_ty = if info.type_params.is_empty() {
            self.named_variant_ty(variant)
        } else {
            Ty::Error
        };
        if ok && !info.type_params.is_empty() {
            let resolved_args: Vec<Ty> = info
                .type_params
                .iter()
                .map(|p| {
                    deep_resolve(
                        &self.ctx,
                        subst
                            .get(p)
                            .expect("every declared parameter has a substitution entry"),
                    )
                })
                .collect();
            let key = GenericInstanceKey::new(variant, resolved_args.clone());
            if self.record_generic_instance(key, span) {
                self.call_type_args.insert(call_id, resolved_args.clone());
                result_ty = Ty::Applied(variant, resolved_args);
            } else {
                ok = false;
            }
        }
        if !ok {
            return Ty::Error;
        }

        if any_arg_never { Ty::Never } else { result_ty }
    }

    /// `TypeName { field: expr, ... }`. `hir::lower` already resolved
    /// every field name to its declaration index and every field's
    /// presence/duplication (`R0007`-`R0010`); this only needs to check
    /// each field's initializer against its declared type, in source
    /// order, propagating `never` exactly like a record's fields are
    /// evaluated (RFC 0005).
    fn check_record_literal(
        &mut self,
        call_id: ExprId,
        record: ItemId,
        type_args: &[HirType],
        fields: &[crate::hir::HirFieldInit],
        span: Span,
    ) -> Ty {
        let Some(info) = self.records.get(&record).cloned() else {
            for f in fields {
                self.check_expr(&f.value);
            }
            return Ty::Error;
        };
        // Generic record construction always requires an explicit
        // application (`Box[i64] { .. }`) -- there is no infer-from-
        // field-values form (`rfcs/0008`).
        let quoted = format!("`{}`", self.interner.resolve(info.name));
        let Some((subst, _)) =
            self.resolve_generic_args(&info.type_params, type_args, false, span, &quoted)
        else {
            for f in fields {
                self.check_expr(&f.value);
            }
            return Ty::Error;
        };
        let mut diverged = false;
        for f in fields {
            let field_ty = self.check_expr(&f.value);
            if matches!(field_ty, Ty::Never) {
                diverged = true;
            }
            let (_, declared_ty, _) = &info.fields[f.field_index];
            let substituted = substitute(declared_ty, &subst);
            self.unify_report(
                &substituted,
                &field_ty,
                f.span,
                "the field's initializer does not match its declared type",
            );
        }
        let _ = span;
        if info.type_params.is_empty() {
            return if diverged {
                Ty::Never
            } else {
                self.named_record_ty(record)
            };
        }
        let resolved_args: Vec<Ty> = info
            .type_params
            .iter()
            .map(|p| {
                subst
                    .get(p)
                    .expect("explicit substitution covers every parameter")
                    .clone()
            })
            .collect();
        let key = GenericInstanceKey::new(record, resolved_args.clone());
        if !self.record_generic_instance(key, span) {
            return Ty::Error;
        }
        self.call_type_args.insert(call_id, resolved_args.clone());
        if diverged {
            Ty::Never
        } else {
            Ty::Applied(record, resolved_args)
        }
    }

    /// Ordinary `base.field` access: the base must resolve to a
    /// declared record type, and the field must exist on it -- both
    /// depend on the base's *inferred* type, which is why (unlike
    /// record construction/variant constructors) this can only be
    /// checked here, not during `hir::lower`.
    fn check_field_access(&mut self, base: &HirExpr, name: Symbol, span: Span) -> Ty {
        let base_ty = self.check_expr(base);
        if matches!(base_ty, Ty::Never) {
            return Ty::Never;
        }
        if matches!(base_ty, Ty::Error) {
            return Ty::Error;
        }
        // Field access is exactly as unproven for an unconstrained `T`
        // as every other capability nothing yet guarantees it has
        // (`rfcs/0008`): rejected here with the same dedicated
        // diagnostic `require_numeric`/`expect_bool` use, before falling
        // to the ordinary "not a record" message that would otherwise
        // suggest `T` is simply the wrong concrete type.
        let resolved_base = self.ctx.resolve(&base_ty);
        if self.report_unconstrained_type_parameter(&resolved_base, span) {
            return Ty::Error;
        }
        // A generic record's field type may itself reference the
        // record's own type parameters (`Ty::Param`) -- substituted here
        // with *this particular value's* own type arguments (from its
        // `Ty::Applied`) before being handed back as the access's
        // result type (`rfcs/0008`). A non-generic record's `subst` is
        // simply empty, so `substitute` below is a no-op for it.
        let (item, subst): (ItemId, HashMap<TypeParamId, Ty>) = match &base_ty {
            Ty::Named(item, _) => (*item, HashMap::new()),
            Ty::Applied(item, args) => {
                let type_params = self
                    .records
                    .get(item)
                    .map(|r| r.type_params.clone())
                    .unwrap_or_default();
                (
                    *item,
                    type_params.into_iter().zip(args.iter().cloned()).collect(),
                )
            }
            _ => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::FIELD_ACCESS_NON_RECORD,
                        self.source,
                        span,
                        format!(
                            "field access on a non-record type `{}`",
                            self.display_for_diagnostic(&base_ty)
                        ),
                    )
                    .with_primary_label("not a record"),
                );
                return Ty::Error;
            }
        };
        let Some(info) = self.records.get(&item).cloned() else {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::FIELD_ACCESS_NON_RECORD,
                    self.source,
                    span,
                    format!(
                        "field access on `{}`, which is a variant, not a record",
                        self.display_for_diagnostic(&base_ty)
                    ),
                )
                .with_primary_label("not a record"),
            );
            return Ty::Error;
        };
        match info.fields.iter().find(|(n, _, _)| *n == name) {
            Some((_, ty, is_public)) => {
                if !*is_public && info.source != self.source {
                    let text = self.interner.resolve(name);
                    self.diagnostics.push(
                        Diagnostic::error(
                            crate::project::codes::INACCESSIBLE_FIELD,
                            self.source,
                            span,
                            format!(
                                "field `{text}` of `{}` is private to its declaring module",
                                self.display_for_diagnostic(&base_ty)
                            ),
                        )
                        .with_primary_label("cannot access a private field from here"),
                    );
                    return Ty::Error;
                }
                substitute(ty, &subst)
            }
            None => {
                let text = self.interner.resolve(name);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::UNKNOWN_FIELD,
                        self.source,
                        span,
                        format!(
                            "`{}` has no field named `{text}`",
                            self.display_for_diagnostic(&base_ty)
                        ),
                    )
                    .with_primary_label("unknown field"),
                );
                Ty::Error
            }
        }
    }

    fn is_aggregate(&self, ty: &Ty) -> bool {
        let resolved = self.ctx.resolve(ty);
        match resolved {
            Ty::Named(item, _) => {
                self.records.contains_key(&item) || self.variants.contains_key(&item)
            }
            Ty::Applied(..) => true,
            _ => false,
        }
    }

    /// Builds `Ty::Named` for a record item, using the record
    /// declaration's own symbol (see `RecordInfo::name`) rather than
    /// requiring every call site to thread it through separately.
    fn named_record_ty(&self, record: ItemId) -> Ty {
        let symbol = self
            .records
            .get(&record)
            .map(|info| info.name)
            .expect("internal invariant: a resolved record ItemId is always in self.records");
        Ty::Named(record, symbol)
    }

    /// Builds `Ty::Named` for a variant item using the variant
    /// declaration's own symbol (e.g. `LookupResult`), never one of its
    /// case names (e.g. `Found`/`Missing`) -- nominal equality only ever
    /// compares by `ItemId`, but diagnostics and textual NIR display this
    /// symbol, so it must name the type, not the specific case a value
    /// happened to be constructed or matched through.
    fn named_variant_ty(&self, variant: ItemId) -> Ty {
        let symbol = self
            .variants
            .get(&variant)
            .map(|info| info.name)
            .expect("internal invariant: a resolved variant ItemId is always in self.variants");
        Ty::Named(variant, symbol)
    }

    fn check_if(
        &mut self,
        condition: &HirExpr,
        then_branch: &HirBlock,
        else_branch: &Option<HirElse>,
    ) -> Ty {
        let cond_ty = self.check_expr(condition);
        self.expect_bool(&cond_ty, condition.span());
        let then_ty = self.check_block(then_branch);
        let result = match else_branch {
            Some(HirElse::Block(b)) => {
                let else_ty = self.check_block(b);
                self.join_diverging_branches(
                    &then_ty,
                    &else_ty,
                    b.span,
                    "if/else branches must have the same type",
                )
            }
            Some(HirElse::If(inner)) => {
                let else_ty = self.check_expr(inner);
                let span = inner.span();
                self.join_diverging_branches(
                    &then_ty,
                    &else_ty,
                    span,
                    "if/else branches must have the same type",
                )
            }
            // No `else`: the implicit false-branch is always `unit` and
            // always reachable, regardless of what the (discarded)
            // then-branch's own value would have been -- an `if`
            // without `else` is never used for its value, only its side
            // effects (spec/0002), so this is `unit` even when the
            // then-branch itself diverges.
            None => Ty::Unit,
        };
        // A condition that itself never produces a value means neither
        // branch is ever reached at all, so the whole `if` is `never` --
        // regardless of what the (still-checked, for their own
        // diagnostics) branches resolved to.
        if matches!(cond_ty, Ty::Never) {
            Ty::Never
        } else {
            result
        }
    }

    /// Joins two branch types where either may be `Ty::Never` (a branch
    /// that unconditionally diverges). A diverging branch contributes no
    /// information about the join's resulting type at all -- it must
    /// never be allowed to overwrite the other, real branch's type, the
    /// way naively returning "the then-branch's type" would. Only when
    /// *both* branches diverge does the join itself become `never`.
    fn join_diverging_branches(&mut self, a: &Ty, b: &Ty, span: Span, message: &str) -> Ty {
        match (a, b) {
            (Ty::Never, Ty::Never) => Ty::Never,
            (Ty::Never, _) => b.clone(),
            (_, Ty::Never) => a.clone(),
            _ => {
                self.unify_report(a, b, span, message);
                a.clone()
            }
        }
    }

    /// `match` is an expression: the scrutinee is checked exactly once,
    /// every pattern is checked against its type (binding locals to
    /// their exact resolved type -- never `Ty::Error`), every reachable
    /// arm body's result is joined through the same `never`-aware join
    /// `if`/`else` already uses, and the whole arm list is checked for
    /// exhaustiveness and unreachable arms (`typeck::exhaustive`).
    fn check_match(&mut self, scrutinee: &HirExpr, arms: &[HirMatchArm], span: Span) -> Ty {
        let scrutinee_ty = self.check_expr(scrutinee);
        let scrutinee_diverges = matches!(scrutinee_ty, Ty::Never);

        // Every arm's pattern and body is checked for its own
        // independent diagnostics regardless of reachability -- but the
        // *join* only ever includes a reachable arm's body type: joining
        // before exhaustiveness/unreachability is known would let an
        // unreachable arm's mismatched type produce a spurious "match
        // arms must have the same type" diagnostic on top of its own,
        // correct "unreachable pattern" one.
        let mut resolved_patterns = Vec::with_capacity(arms.len());
        let mut any_pattern_invalid = false;
        let mut body_types = Vec::with_capacity(arms.len());
        for arm in arms {
            let (resolved, valid) = self.check_pattern(&arm.pattern, &scrutinee_ty);
            any_pattern_invalid |= !valid;
            resolved_patterns.push(resolved);
            let body_ty = match &arm.body {
                HirMatchArmBody::Expr(e) => self.check_expr(e),
                HirMatchArmBody::Block(b) => self.check_block(b),
            };
            body_types.push(body_ty);
        }

        // A diverging scrutinee is evaluated exactly once, unconditionally,
        // before any pattern could ever be tested -- no arm is ever
        // reached, so the whole match is `never`, mirroring `if`'s
        // diverging-condition rule exactly. Every arm's pattern/body was
        // still checked above (for its own independent diagnostics), but
        // none of them are reachable, so none may contribute to the
        // result type or be analyzed for exhaustiveness/unreachability.
        if scrutinee_diverges {
            return Ty::Never;
        }

        // A pattern whose declared shape didn't match its scrutinee (an
        // arity mismatch, an unknown case, a mismatched literal, ...)
        // already has its own diagnostic; the coverage matrix built
        // from a fabricated stand-in for it can't be trusted to prove
        // exhaustiveness or unreachability, so that analysis -- and its
        // own diagnostics -- are skipped entirely rather than risk a
        // misleading cascade.
        // Exhaustiveness/unreachability analysis is skipped entirely
        // (never even called) whenever any pattern is invalid -- and so
        // is the result-type join below: an arm whose own pattern is
        // already known-invalid tells us nothing trustworthy about
        // which arms genuinely belong together, so joining their body
        // types anyway could report a second, misleading T0001 on top
        // of the pattern's own diagnostic for what is really one
        // problem.
        if any_pattern_invalid {
            return Ty::Error;
        }
        let coverage =
            self.check_match_exhaustiveness(&scrutinee_ty, &resolved_patterns, arms, span);
        // A failed analysis (work-budget or recursion-depth exceeded)
        // means reachability is simply unknown -- joining arm body
        // types anyway, as if every arm were reachable, could report a
        // second, misleading "match arms must have the same type" on
        // top of the budget diagnostic for what analysis never actually
        // proved was even a real mismatch between arms that matter.
        let unreachable = match coverage {
            MatchCoverage::Complete { unreachable } => unreachable,
            MatchCoverage::Failed => return Ty::Error,
        };

        let mut arm_result: Option<Ty> = None;
        for (i, body_ty) in body_types.into_iter().enumerate() {
            if unreachable.contains(&i) {
                continue;
            }
            arm_result = Some(match arm_result {
                None => body_ty,
                Some(acc) => self.join_diverging_branches(
                    &acc,
                    &body_ty,
                    arms[i].span,
                    "match arms must have the same type",
                ),
            });
        }
        arm_result.unwrap_or(Ty::Never)
    }

    /// Runs exhaustiveness/unreachable-arm analysis and reports its
    /// diagnostics, returning whether it actually completed. A failed
    /// analysis (`MatchCoverage::Failed`) means nothing it might have
    /// found -- including which arms are unreachable -- can be trusted,
    /// so the caller must not use it to drive the result-type join
    /// either.
    fn check_match_exhaustiveness(
        &mut self,
        scrutinee_ty: &Ty,
        resolved_patterns: &[ResolvedPattern],
        arms: &[HirMatchArm],
        span: Span,
    ) -> MatchCoverage {
        let resolved_scrutinee = self.ctx.resolve(scrutinee_ty);
        if matches!(resolved_scrutinee, Ty::Error) {
            return MatchCoverage::Complete {
                unreachable: Vec::new(),
            };
        }
        let variant_payloads: HashMap<ItemId, Vec<Vec<Ty>>> = self
            .variants
            .iter()
            .map(|(id, info)| (*id, info.cases.iter().map(|(_, p)| p.clone()).collect()))
            .collect();
        let variant_type_params: HashMap<ItemId, Vec<TypeParamId>> = self
            .variants
            .iter()
            .map(|(id, info)| (*id, info.type_params.clone()))
            .collect();
        let space = VariantSpace {
            payloads: variant_payloads,
            type_params: variant_type_params,
        };
        let analysis = exhaustive::analyze_match_with_budget(
            &resolved_scrutinee,
            resolved_patterns,
            &space,
            self.pattern_budget,
        );

        if analysis.budget_exceeded {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::PATTERN_BUDGET_EXCEEDED,
                    self.source,
                    span,
                    "pattern analysis exceeded its work budget for this match",
                )
                .with_primary_label("match is too complex to analyze"),
            );
            return MatchCoverage::Failed;
        }

        if let Some(witness) = analysis.missing {
            let description = exhaustive::describe_pattern(&witness, &self.variant_display);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::NON_EXHAUSTIVE_MATCH,
                    self.source,
                    span,
                    format!("non-exhaustive match: missing pattern `{description}`"),
                )
                .with_primary_label("this match does not cover every case"),
            );
        }

        for &i in &analysis.unreachable {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::UNREACHABLE_ARM,
                    self.source,
                    arms[i].pattern.span(),
                    "unreachable pattern: already covered by an earlier arm",
                )
                .with_primary_label("unreachable"),
            );
        }

        MatchCoverage::Complete {
            unreachable: analysis.unreachable,
        }
    }

    /// Checks one pattern against its scrutinee's type, binding any
    /// fresh local at its exact resolved type, and returns the
    /// `ResolvedPattern` the exhaustiveness analysis operates on
    /// alongside whether the pattern is *valid*: fully consistent with
    /// its scrutinee/case (no arity mismatch, no unknown case, no
    /// shape mismatch, and every nested sub-pattern likewise valid).
    ///
    /// A `false` result still returns a **structurally well-formed**
    /// `ResolvedPattern` -- never one whose `Variant::args` length
    /// disagrees with its case's declared payload arity -- so a caller
    /// that (incorrectly) fed an invalid pattern into exhaustiveness
    /// analysis anyway still could not corrupt its row/occurrence-type
    /// length invariant. `check_match` uses the validity flag to skip
    /// exhaustiveness/unreachability analysis for the whole match
    /// instead, since a fabricated stand-in for a malformed pattern
    /// cannot make that analysis's result trustworthy. Also records a
    /// `(variant, case)` resolution for `typeck::pattern_case` whenever
    /// the pattern (a `Variant` pattern, or a bare `Bind` pattern whose
    /// name matches a payload-less case of the scrutinee's own variant
    /// type) actually matches a specific case.
    fn check_pattern(
        &mut self,
        pattern: &HirPattern,
        scrutinee_ty: &Ty,
    ) -> (ResolvedPattern, bool) {
        self.check_pattern_at_depth(pattern, scrutinee_ty, 0)
    }

    /// `depth` counts `Variant` sub-pattern nesting only (matching what
    /// actually grows the call stack here); at
    /// `crate::limits::MAX_PATTERN_DEPTH` this stops recursing into
    /// further sub-patterns entirely rather than merely reporting the
    /// overflow after the fact -- the whole point is to never let the
    /// stack grow past this depth.
    fn check_pattern_at_depth(
        &mut self,
        pattern: &HirPattern,
        scrutinee_ty: &Ty,
        depth: usize,
    ) -> (ResolvedPattern, bool) {
        if depth > crate::limits::MAX_PATTERN_DEPTH {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::PATTERN_BUDGET_EXCEEDED,
                    self.source,
                    pattern.span(),
                    "pattern is nested too deeply to analyze",
                )
                .with_primary_label("pattern is too complex"),
            );
            return (ResolvedPattern::Wildcard, false);
        }
        let resolved_scrutinee = self.ctx.resolve(scrutinee_ty);
        match pattern {
            HirPattern::Wildcard { .. } => (ResolvedPattern::Wildcard, true),
            HirPattern::Bind {
                id, local, name, ..
            } => {
                let variant_item = match &resolved_scrutinee {
                    Ty::Named(item, _) => Some(*item),
                    Ty::Applied(item, _) => Some(*item),
                    _ => None,
                };
                if let Some(item) = variant_item
                    && let Some(info) = self.variants.get(&item)
                    && let Some(case_index) = info
                        .cases
                        .iter()
                        .position(|(case_name, payload)| case_name == name && payload.is_empty())
                {
                    self.pattern_case.insert(*id, (item, case_index));
                    return (
                        ResolvedPattern::Variant {
                            variant: item,
                            case: case_index,
                            args: Vec::new(),
                        },
                        true,
                    );
                }
                self.locals.insert(
                    *local,
                    LocalInfo {
                        ty: resolved_scrutinee.clone(),
                        mutable: false,
                    },
                );
                (ResolvedPattern::Wildcard, true)
            }
            HirPattern::Variant {
                id,
                name,
                args,
                span,
            } => {
                // A generic variant's scrutinee is `Ty::Applied`, not
                // `Ty::Named` -- its own type arguments substitute into
                // each case's symbolic payload types below, so a bound
                // sub-pattern (`inner` in `Some(inner)`) gets the exact
                // instantiated type (`T` -> `i64`), never the bare
                // parameter (`rfcs/0008`).
                let (item, subst): (ItemId, HashMap<TypeParamId, Ty>) = match &resolved_scrutinee {
                    Ty::Named(item, _) => (*item, HashMap::new()),
                    Ty::Applied(item, applied_args) => {
                        let type_params = self
                            .variants
                            .get(item)
                            .map(|v| v.type_params.clone())
                            .unwrap_or_default();
                        (
                            *item,
                            type_params
                                .into_iter()
                                .zip(applied_args.iter().cloned())
                                .collect(),
                        )
                    }
                    _ => {
                        if !matches!(resolved_scrutinee, Ty::Error) {
                            self.push_incompatible_pattern(*span, &resolved_scrutinee);
                        }
                        for a in args {
                            self.check_pattern_at_depth(a, &Ty::Error, depth + 1);
                        }
                        return (ResolvedPattern::Wildcard, false);
                    }
                };
                let Some(info) = self.variants.get(&item).cloned() else {
                    // `resolved_scrutinee` is `Ty::Named` but names a
                    // *record*, not a variant (e.g. a variant pattern
                    // written against a record-typed scrutinee) -- just
                    // as incompatible as the non-`Ty::Named` case just
                    // above, and must be diagnosed here too: silently
                    // returning `valid: false` with no diagnostic would
                    // let `check` report zero errors while `pattern_case`
                    // stays unpopulated for this pattern, so NIR lowering
                    // later has nothing to classify it by.
                    self.push_incompatible_pattern(*span, &resolved_scrutinee);
                    for a in args {
                        self.check_pattern_at_depth(a, &Ty::Error, depth + 1);
                    }
                    return (ResolvedPattern::Wildcard, false);
                };
                let Some(case_index) = info.cases.iter().position(|(n, _)| n == name) else {
                    let text = self.interner.resolve(*name);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::INCOMPATIBLE_PATTERN,
                            self.source,
                            *span,
                            format!(
                                "`{}` has no case named `{text}`",
                                self.display_for_diagnostic(&resolved_scrutinee)
                            ),
                        )
                        .with_primary_label("unknown case in this pattern"),
                    );
                    for a in args {
                        self.check_pattern_at_depth(a, &Ty::Error, depth + 1);
                    }
                    return (ResolvedPattern::Wildcard, false);
                };
                self.pattern_case.insert(*id, (item, case_index));
                let payload = info.cases[case_index].1.clone();
                let mut valid = payload.len() == args.len();
                if !valid {
                    let text = self.interner.resolve(*name);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::ARITY_MISMATCH,
                            self.source,
                            *span,
                            format!(
                                "`{text}` expects {} sub-pattern(s), found {}",
                                payload.len(),
                                args.len()
                            ),
                        )
                        .with_primary_label("wrong number of sub-patterns"),
                    );
                }
                // The resolved pattern's arity always matches the
                // case's *declared* payload arity, regardless of how
                // many sub-patterns were actually written -- never the
                // arg count from a possibly-malformed pattern (see this
                // method's doc comment). A missing position (too few
                // sub-patterns) has no HirPattern to check and is
                // padded with a wildcard; a supplied sub-pattern beyond
                // the declared arity (too many) is still checked here,
                // for its own independent diagnostics, but excluded
                // from the resolved pattern.
                let mut resolved_args = Vec::with_capacity(payload.len());
                for (i, payload_ty) in payload.iter().enumerate() {
                    let payload_ty = substitute(payload_ty, &subst);
                    match args.get(i) {
                        Some(a) => {
                            let (resolved, arg_valid) =
                                self.check_pattern_at_depth(a, &payload_ty, depth + 1);
                            valid &= arg_valid;
                            resolved_args.push(resolved);
                        }
                        None => resolved_args.push(ResolvedPattern::Wildcard),
                    }
                }
                for extra in args.iter().skip(payload.len()) {
                    self.check_pattern_at_depth(extra, &Ty::Error, depth + 1);
                }
                (
                    ResolvedPattern::Variant {
                        variant: item,
                        case: case_index,
                        args: resolved_args,
                    },
                    valid,
                )
            }
            HirPattern::Int { value, span, .. } => {
                let literal_ty = self.fresh_default(Ty::I64, VarKind::Integer);
                let valid = self.unify_report(
                    &resolved_scrutinee,
                    &literal_ty,
                    *span,
                    "pattern does not match the scrutinee's type",
                );
                (ResolvedPattern::Literal(LiteralKey::Int(*value)), valid)
            }
            HirPattern::Str { value, span, .. } => {
                let valid = self.unify_report(
                    &resolved_scrutinee,
                    &Ty::Str,
                    *span,
                    "pattern does not match the scrutinee's type",
                );
                (
                    ResolvedPattern::Literal(LiteralKey::Str(value.clone())),
                    valid,
                )
            }
            HirPattern::Char { value, span, .. } => {
                let valid = self.unify_report(
                    &resolved_scrutinee,
                    &Ty::Char,
                    *span,
                    "pattern does not match the scrutinee's type",
                );
                (ResolvedPattern::Literal(LiteralKey::Char(*value)), valid)
            }
            HirPattern::Bool { value, span, .. } => {
                let valid = self.unify_report(
                    &resolved_scrutinee,
                    &Ty::Bool,
                    *span,
                    "pattern does not match the scrutinee's type",
                );
                (ResolvedPattern::Bool(*value), valid)
            }
        }
    }

    fn push_incompatible_pattern(&mut self, span: Span, scrutinee_ty: &Ty) {
        self.diagnostics.push(
            Diagnostic::error(
                codes::INCOMPATIBLE_PATTERN,
                self.source,
                span,
                format!(
                    "a variant pattern is not compatible with the scrutinee's type `{}`",
                    self.display_for_diagnostic(scrutinee_ty)
                ),
            )
            .with_primary_label("incompatible pattern"),
        );
    }

    /// Allocates a fresh, kinded type variable for a literal, remembering
    /// the default it should resolve to if nothing else constrains it by
    /// the time checking finishes (`spec/0003`'s literal inference). The
    /// kind stops the variable from unifying with something it was never
    /// compatible with in the first place (see [`VarKind`]).
    fn fresh_default(&mut self, default: Ty, kind: VarKind) -> Ty {
        let var = self.ctx.fresh_var_with_kind(Some(kind));
        self.pending_defaults.push((var, default));
        Ty::Var(var)
    }

    fn finalize_defaults(&mut self) {
        for (var, default) in std::mem::take(&mut self.pending_defaults) {
            if let Ty::Var(root) = self.ctx.resolve(&Ty::Var(var)) {
                self.ctx.bind(root, default);
            }
        }
    }

    /// Unifies `expected` against `actual`, reporting a type-mismatch
    /// diagnostic naming both sides in that order on failure. Callers
    /// with a genuine expected/actual distinction (a declared return
    /// type vs. a returned expression's type, a parameter type vs. an
    /// argument's type) must pass them in that order — reversing it
    /// produces a correct unification but a backwards "expected X,
    /// found Y" message. Callers comparing two peer values with no
    /// canonical direction (binary operator operands, if/else branches,
    /// match arms) may pass either order.
    /// Returns whether unification succeeded -- most callers only need
    /// the diagnostic-on-mismatch side effect and ignore this, but a
    /// pattern's own literal arms need to know a failure occurred so a
    /// mismatched literal pattern can mark itself invalid the same way
    /// an arity mismatch or unknown case already does, rather than
    /// reporting T0001 while still being treated as a fully valid,
    /// analyzable pattern.
    fn unify_report(&mut self, expected: &Ty, actual: &Ty, span: Span, message: &str) -> bool {
        let (a, b) = (expected, actual);
        if let Err((ra, rb)) = unify(&mut self.ctx, a, b) {
            self.diagnostics.push(Diagnostic::error(
                codes::TYPE_MISMATCH,
                self.source,
                span,
                format!(
                    "{message}: expected `{}`, found `{}`",
                    self.display_for_diagnostic(&ra),
                    self.display_for_diagnostic(&rb)
                ),
            ));
            false
        } else {
            true
        }
    }

    /// Every typeck diagnostic that names a type goes through this one
    /// formatter, so none of them can drift into a different format than
    /// another. Two behaviors [`display_ty`] alone doesn't have:
    ///
    /// - a still-unresolved literal type variable displays as the
    ///   default it would take (`i64`/`f64`) rather than `_` --
    ///   unification failing is exactly what stops that default from
    ///   ever being applied, so the plain resolved form would otherwise
    ///   show a placeholder instead of the type the literal actually
    ///   meant;
    /// - a nominal `Ty::Named` displays through `self.registry`'s
    ///   canonical qualified name (`sales.user.User`, not just `User`),
    ///   so two same-named, differently-declared types read as
    ///   genuinely different in "expected `X`, found `Y`" rather than
    ///   the same ambiguous text twice (`rfcs/0007`). Never the raw
    ///   `ItemId` alone, and never an import alias -- the registry only
    ///   ever returns an item's own true declared identity.
    fn display_for_diagnostic(&self, ty: &Ty) -> String {
        self.display_for_diagnostic_at_depth(ty, 0)
    }

    /// `depth`-bounded the same way every other stage that walks a
    /// nested type application is (`crate::limits::MAX_GENERIC_DEPTH`):
    /// diagnostics must never overflow the stack rendering a
    /// pathologically (or maliciously) deep type, even one that itself
    /// somehow slipped past every earlier guard.
    fn display_for_diagnostic_at_depth(&self, ty: &Ty, depth: usize) -> String {
        if depth > crate::limits::MAX_GENERIC_DEPTH {
            return "...".to_string();
        }
        if let Ty::Var(v) = ty {
            match self.ctx.kind_of(*v) {
                Some(VarKind::Integer) => return display_ty(&Ty::I64, self.interner),
                Some(VarKind::Float) => return display_ty(&Ty::F64, self.interner),
                None => {}
            }
        }
        if let Ty::Named(item, _) = ty {
            return self.registry.qualified_name(*item, self.interner);
        }
        if let Ty::Param(_, name) = ty {
            return self.interner.resolve(*name).to_string();
        }
        if let Ty::Applied(item, args) = ty {
            let head = self.registry.qualified_name(*item, self.interner);
            let args_text = args
                .iter()
                .map(|a| self.display_for_diagnostic_at_depth(a, depth + 1))
                .collect::<Vec<_>>()
                .join(", ");
            return format!("{head}[{args_text}]");
        }
        display_ty(ty, self.interner)
    }

    fn expect_bool(&mut self, ty: &Ty, span: Span) {
        // Logical/conditional use (`!T`, `T && ...`, `if T { ... }`, a
        // `while` condition) is exactly as unproven for an unconstrained
        // `T` as arithmetic is (`rfcs/0008`): rejected here, once,
        // symbolically, rather than an ordinary "expected bool" mismatch
        // that would suggest `T` is simply the wrong concrete type.
        let resolved = self.ctx.resolve(ty);
        if self.report_unconstrained_type_parameter(&resolved, span) {
            return;
        }
        self.unify_report(&Ty::Bool, ty, span, "expected a boolean expression");
    }

    /// `true` for a resolved type this checker can prove *no* operation
    /// is universally valid for -- specifically, one of the enclosing
    /// generic declaration's own unconstrained type parameters
    /// (`rfcs/0008`). Distinguishing this from an ordinary "wrong
    /// concrete type" is what lets `require_numeric`/`require_integer`
    /// give `func add[T](left: T, right: T) -> T { left + right }` its
    /// own dedicated explanation instead of reporting `T` as if it were
    /// simply some non-numeric type like `bool` -- protocols/
    /// constraints (Alpha 0.1.5) are what will eventually let a type
    /// parameter prove it supports a specific operation; nothing does
    /// yet.
    fn report_unconstrained_type_parameter(&mut self, ty: &Ty, span: Span) -> bool {
        let Ty::Param(_, name) = ty else {
            return false;
        };
        let text = self.interner.resolve(*name);
        self.diagnostics.push(
            Diagnostic::error(
                codes::UNSUPPORTED_ON_TYPE_PARAMETER,
                self.source,
                span,
                format!(
                    "this operation is not available for `{text}`: an unconstrained type \
                     parameter has no operations guaranteed for every possible type"
                ),
            )
            .with_primary_label("not available for an unconstrained type parameter"),
        );
        true
    }

    fn require_numeric(&mut self, ty: &Ty, span: Span) {
        let resolved = self.ctx.resolve(ty);
        if matches!(resolved, Ty::Var(_) | Ty::Error | Ty::Never) || is_numeric(&resolved) {
            return;
        }
        if self.report_unconstrained_type_parameter(&resolved, span) {
            return;
        }
        self.diagnostics.push(Diagnostic::error(
            codes::EXPECTED_NUMERIC,
            self.source,
            span,
            format!(
                "expected a numeric type, found `{}`",
                self.display_for_diagnostic(&resolved)
            ),
        ));
    }

    fn require_integer(&mut self, ty: &Ty, span: Span) {
        let resolved = self.ctx.resolve(ty);
        let ok = match &resolved {
            // A variable with no pending float default might still
            // resolve to an integer type; one that is specifically a
            // pending *float* default (`value x = 1.0`) never will.
            Ty::Var(v) => !matches!(self.ctx.kind_of(*v), Some(VarKind::Float)),
            Ty::Error | Ty::Never => true,
            other => is_integer(other),
        };
        if ok {
            return;
        }
        if self.report_unconstrained_type_parameter(&resolved, span) {
            return;
        }
        self.diagnostics.push(Diagnostic::error(
            codes::EXPECTED_INTEGER,
            self.source,
            span,
            format!(
                "expected an integer type, found `{}`",
                self.display_for_diagnostic(&resolved)
            ),
        ));
    }

    /// Reports a construct that is parsed (and, where relevant, still
    /// walked for cascading diagnostics) but has no implemented
    /// semantics in Alpha 0.1. This is how the checker keeps a
    /// not-yet-implemented feature from silently becoming fake
    /// behavior downstream: NIR lowering and the interpreter only ever
    /// see it after this diagnostic has already been recorded.
    fn push_unsupported(&mut self, span: Span, feature: &str) {
        self.diagnostics.push(
            Diagnostic::error(
                codes::UNSUPPORTED_FEATURE,
                self.source,
                span,
                format!("{feature} is not supported in Alpha 0.1"),
            )
            .with_primary_label("not yet implemented"),
        );
    }

    /// `break`/`continue` outside of any enclosing `while`/`loop` is
    /// rejected here, at check time, rather than left for NIR lowering
    /// or the interpreter to discover -- tracking loop nesting during
    /// checking is what lets this be a normal diagnostic instead of a
    /// panic or an ignored no-op once execution reaches that point.
    fn check_loop_control(&mut self, span: Span, keyword: &str) {
        if self.loop_depth == 0 {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::LOOP_CONTROL_OUTSIDE_LOOP,
                    self.source,
                    span,
                    format!("`{keyword}` used outside of a loop"),
                )
                .with_primary_label("not inside a loop"),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::{PatternId, lower_module};
    use crate::lexer::tokenize;
    use crate::parser::Parser;
    use crate::source::SourceMap;

    fn check(text: &str) -> Vec<Diagnostic> {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, lex_diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(
            lex_diags.is_empty(),
            "unexpected lexer diagnostics: {lex_diags:?}"
        );
        let (module, parse_diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(
            parse_diags.is_empty(),
            "unexpected parser diagnostics: {parse_diags:?}"
        );
        let (hir, resolve_diags) = lower_module(&module, id, &interner);
        assert!(
            resolve_diags.is_empty(),
            "unexpected resolve diagnostics: {resolve_diags:?}"
        );
        check_module(&hir, id, &interner, EntryMain::ByName).diagnostics
    }

    fn check_full(text: &str) -> TypeckResult {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, lex_diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(
            lex_diags.is_empty(),
            "unexpected lexer diagnostics: {lex_diags:?}"
        );
        let (module, parse_diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(
            parse_diags.is_empty(),
            "unexpected parser diagnostics: {parse_diags:?}"
        );
        let (hir, resolve_diags) = lower_module(&module, id, &interner);
        assert!(
            resolve_diags.is_empty(),
            "unexpected resolve diagnostics: {resolve_diags:?}"
        );
        check_module(&hir, id, &interner, EntryMain::ByName)
    }

    #[test]
    fn well_typed_function_has_no_diagnostics() {
        let diags = check("func add(left: i64, right: i64) -> i64 { return left + right }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn integer_literal_infers_from_parameter_type() {
        let diags = check("func f(x: i32) -> i32 { return x + 1 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn float_literal_defaults_to_f64() {
        let diags = check("func f() -> f64 { return 1.5 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn integer_literal_defaults_to_i64() {
        let diags = check("func f() -> i64 { return 1 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn return_type_mismatch_is_a_diagnostic() {
        let diags = check("func f() -> i64 { return true }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn if_condition_must_be_bool() {
        let diags = check("func f() -> i64 { if 1 { return 1 } return 0 }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn while_condition_must_be_bool() {
        let diags = check("func f() { while 1 { break } }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn call_argument_count_mismatch_is_its_own_diagnostic() {
        let diags = check(
            "func add(left: i64, right: i64) -> i64 { return left + right } \
             func main() -> i64 { return add(1) }",
        );
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0002");
    }

    #[test]
    fn call_argument_type_mismatch_is_a_diagnostic() {
        let diags = check(
            "func add(left: i64, right: i64) -> i64 { return left + right } \
             func main() -> i64 { return add(true, 2) }",
        );
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn assigning_to_an_immutable_binding_is_a_diagnostic() {
        let diags = check("func f() { value x = 1; x = 2; }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0003");
    }

    #[test]
    fn assigning_to_a_mutable_binding_is_fine() {
        let diags = check("func f() { mutable x = 1; x = 2; }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn assignment_type_mismatch_is_a_diagnostic() {
        let diags = check("func f() { mutable x = 1; x = true; }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn numeric_operator_on_bool_is_a_diagnostic() {
        let diags = check("func f() -> bool { return true + false }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0004");
    }

    #[test]
    fn bitwise_operator_on_float_is_a_diagnostic() {
        let diags = check("func f() -> f64 { value x = 1.0; return x & x }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0005");
    }

    #[test]
    fn logical_and_requires_bool_operands() {
        let diags = check("func f() -> bool { return 1 && true }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn if_else_branches_must_agree_in_type() {
        let diags = check("func f() -> i64 { return if true { 1 } else { false } }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn if_without_else_used_as_tail_is_unit_typed() {
        // No diagnostic: the if's own type is unit regardless of the
        // then-branch's tail when there's no else (documented
        // simplification: this checker does not require the then-branch
        // itself to be unit).
        let diags = check("func f() { if true { 1 } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn mismatched_match_arm_types_is_a_diagnostic() {
        let diags = check("func f(x: i64) -> i64 { return match x { 1 => 10, _ => true } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn well_typed_exhaustive_match_has_no_diagnostics() {
        let diags = check("func f(x: i64) -> i64 { return match x { 1 => 10, n => n } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn arm_after_a_catch_all_binding_is_unreachable() {
        let diags = check("func f(x: i64) -> i64 { return match x { 1 => 10, n => n, _ => 0 } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0018");
    }

    #[test]
    fn unreachable_arm_does_not_also_report_a_result_type_mismatch() {
        // The second arm's body (`false`, a bool) would mismatch the
        // first arm's body (`1`, an i64) if it were joined -- but the
        // second arm is unreachable (the first arm's wildcard pattern
        // already covers every bool), so only its own unreachable-arm
        // diagnostic is expected, never a spurious arm-join mismatch on
        // top of it.
        let diags = check("func f(x: bool) -> i64 { return match x { _ => 1, true => false } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0018");
    }

    #[test]
    fn diverging_scrutinee_with_mismatched_arm_types_does_not_report_a_join_mismatch() {
        let diags = check(
            "func f() -> i64 { \
                 return match (return 1) { true => 1, false => \"x\" } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn reachable_arm_type_mismatch_is_still_reported() {
        let diags = check("func f(x: bool) -> i64 { return match x { true => 1, false => true } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn one_diverging_arm_and_one_value_arm_resolves_to_the_value_type() {
        let diags = check(
            "func f(x: bool) -> i64 { \
                 return match x { true => return 0, false => 1 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn all_reachable_arms_diverging_resolves_to_never() {
        let diags = check(
            "func f(x: bool) -> i64 { \
                 value _y = match x { true => return 0, false => return 1 }; \
                 return 0 \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn non_exhaustive_variant_match_is_a_diagnostic() {
        let diags = check(
            "variant LookupResult { Found(i64), Missing } \
             func f(r: LookupResult) -> i64 { return match r { Found(v) => v } }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0017");
        assert!(diags[0].message.contains("Missing"), "{:?}", diags[0]);
    }

    #[test]
    fn exhaustive_variant_match_with_nested_pattern_has_no_diagnostics() {
        let diags = check(
            "record User { id: i64 } \
             variant LookupResult { Found(User), Missing } \
             func f(r: LookupResult) -> i64 { \
                 return match r { \
                     Found(user) => user.id, \
                     Missing => 0, \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn literal_pattern_against_a_variant_scrutinee_is_a_diagnostic() {
        let diags = check(
            "variant Shape { Circle } \
             func f(s: Shape) -> i64 { return match s { 1 => 1, _ => 0 } }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn variant_pattern_against_a_non_variant_scrutinee_is_a_diagnostic() {
        let diags = check("func f(x: i64) -> i64 { return match x { Found(v) => v } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0021");
    }

    #[test]
    fn variant_pattern_against_a_record_scrutinee_is_a_diagnostic() {
        // A record is `Ty::Named` too, so this must not silently fall
        // through the `Ty::Named`-but-not-a-variant branch of
        // `check_pattern` with no diagnostic at all -- that would let
        // `check` report zero errors for a construct that can never
        // reach the interpreter (there's no case to classify it by).
        let diags = check(
            "record Point { x: i64 } \
             func f(p: Point) -> i64 { return match p { Found(v) => v } }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0021");
    }

    #[test]
    fn too_many_variant_sub_patterns_is_a_diagnostic_not_a_panic() {
        let diags = check(
            "variant V { A(i64) } \
             func test(v: V) -> i64 { \
                 return match v { \
                     A(x, y) => x, \
                     _ => 0 \
                 } \
             }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0002");
    }

    #[test]
    fn too_few_variant_sub_patterns_is_a_diagnostic_not_a_panic() {
        let diags = check(
            "variant V { A(i64, i64) } \
             func test(v: V) -> i64 { \
                 return match v { \
                     A(x) => x, \
                     _ => 0 \
                 } \
             }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0002");
    }

    #[test]
    fn nested_wrong_arity_pattern_is_a_diagnostic_not_a_panic() {
        let diags = check(
            "variant Inner { X(i64) } \
             variant Outer { A(Inner) } \
             func test(o: Outer) -> i64 { \
                 return match o { \
                     A(X(a, b)) => a, \
                     _ => 0 \
                 } \
             }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0002");
    }

    #[test]
    fn a_pattern_nested_past_the_depth_limit_is_a_diagnostic_not_a_stack_overflow() {
        // check_pattern's own crate::limits::MAX_PATTERN_DEPTH bound
        // exists prior to and independent of the usefulness algorithm's
        // work budget -- but the parser's own matching bound (`fix(parser):
        // bound nested pattern parsing`) now rejects any source text
        // nested this deep before typeck ever sees it, so the only way
        // left to exercise check_pattern's bound directly is a
        // hand-built HirPattern chain bypassing the parser (and
        // hir::lower) entirely, calling the same public check_module
        // entry point a real caller would.
        let depth = crate::limits::MAX_PATTERN_DEPTH + 50;
        let mut interner = Interner::new();
        let case_name = interner.intern("Wrap");
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut pattern = HirPattern::Wildcard {
            id: PatternId(0),
            span: Span::dummy(),
        };
        for i in 0..depth {
            pattern = HirPattern::Variant {
                id: PatternId(i as u32 + 1),
                name: case_name,
                args: vec![pattern],
                span: Span::dummy(),
            };
        }
        let registry = ItemRegistry::default();
        let mut checker = Checker {
            source,
            interner: &interner,
            registry: &registry,
            ctx: TypeContext::new(),
            diagnostics: Vec::new(),
            functions: HashMap::new(),
            locals: HashMap::new(),
            pending_defaults: Vec::new(),
            current_return_type: Ty::Unit,
            current_requirements: Vec::new(),
            records: HashMap::new(),
            variants: HashMap::new(),
            variant_display: HashMap::new(),
            loop_depth: 0,
            expr_types: HashMap::new(),
            pattern_case: HashMap::new(),
            call_type_args: HashMap::new(),
            call_evidence: HashMap::new(),
            protocol_call_evidence: HashMap::new(),
            generic_params: HashMap::new(),
            generic_instances: std::collections::HashSet::new(),
            protocols: HashMap::new(),
            extends: Vec::new(),
            capability_cache: HashMap::new(),
            pattern_budget: exhaustive::MAX_USEFULNESS_STEPS,
            entry_main: EntryMain::ByName,
        };
        // A non-Ty::Named scrutinee (here Ty::Error) makes every level
        // take check_pattern's own "incompatible scrutinee" branch,
        // which suppresses that diagnostic for Ty::Error specifically
        // (avoiding cascade) while still recursing into each Variant's
        // args at depth + 1 -- exactly the recursion the depth bound
        // exists to stop, with nothing else able to produce a
        // diagnostic of its own along the way.
        checker.check_pattern_at_depth(&pattern, &Ty::Error, 0);
        assert_eq!(
            checker.diagnostics.len(),
            1,
            "unexpected diagnostics: {:?}",
            checker.diagnostics
        );
        assert_eq!(checker.diagnostics[0].code, "T0019");
    }

    /// A minimal `Checker` with `pattern_budget` set to `budget` instead
    /// of the real `exhaustive::MAX_USEFULNESS_STEPS` -- the controlled
    /// test seam for exercising `MatchCoverage::Failed` deterministically
    /// against a trivial match, never a fixture that actually consumes
    /// 100,000 steps.
    fn checker_with_budget<'a>(
        interner: &'a Interner,
        registry: &'a ItemRegistry,
        source: SourceId,
        budget: usize,
    ) -> Checker<'a> {
        Checker {
            source,
            interner,
            registry,
            ctx: TypeContext::new(),
            diagnostics: Vec::new(),
            functions: HashMap::new(),
            locals: HashMap::new(),
            pending_defaults: Vec::new(),
            current_return_type: Ty::Unit,
            current_requirements: Vec::new(),
            records: HashMap::new(),
            variants: HashMap::new(),
            variant_display: HashMap::new(),
            loop_depth: 0,
            expr_types: HashMap::new(),
            pattern_case: HashMap::new(),
            call_type_args: HashMap::new(),
            call_evidence: HashMap::new(),
            protocol_call_evidence: HashMap::new(),
            generic_params: HashMap::new(),
            generic_instances: std::collections::HashSet::new(),
            protocols: HashMap::new(),
            extends: Vec::new(),
            capability_cache: HashMap::new(),
            pattern_budget: budget,
            entry_main: EntryMain::ByName,
        }
    }

    #[test]
    fn budget_failure_stops_the_match_result_join() {
        // Two wildcard arms with genuinely different, non-diverging
        // body types (i64 vs bool) -- if the join ran anyway, this
        // would report its own T0001. A budget of 1 exhausts on the
        // very first arm's own reachability check (a Wildcard against
        // an open/Bool-less scrutinee type still recurses one level
        // into the default matrix), so analysis never determines
        // reachability for either arm.
        let interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let registry = ItemRegistry::default();
        let mut checker = checker_with_budget(&interner, &registry, source, 1);
        let scrutinee = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let arms = vec![
            HirMatchArm {
                pattern: HirPattern::Wildcard {
                    id: crate::hir::PatternId(0),
                    span: Span::dummy(),
                },
                body: HirMatchArmBody::Expr(HirExpr::Int {
                    id: ExprId(1),
                    value: 1,
                    base: crate::lexer::IntBase::Decimal,
                    span: Span::dummy(),
                }),
                span: Span::dummy(),
            },
            HirMatchArm {
                pattern: HirPattern::Wildcard {
                    id: crate::hir::PatternId(1),
                    span: Span::dummy(),
                },
                body: HirMatchArmBody::Expr(HirExpr::Bool {
                    id: ExprId(2),
                    value: true,
                    span: Span::dummy(),
                }),
                span: Span::dummy(),
            },
        ];
        let result_ty = checker.check_match(&scrutinee, &arms, Span::dummy());

        assert_eq!(
            result_ty,
            Ty::Error,
            "expected a failed analysis to make the match type Ty::Error"
        );
        assert_eq!(
            checker.diagnostics.len(),
            1,
            "unexpected diagnostics: {:?}",
            checker.diagnostics
        );
        assert_eq!(checker.diagnostics[0].code, "T0019");
        assert!(!checker.diagnostics.iter().any(|d| d.code == "T0001"));
        assert!(!checker.diagnostics.iter().any(|d| d.code == "T0017"));
        assert!(!checker.diagnostics.iter().any(|d| d.code == "T0018"));
    }

    #[test]
    fn diverging_scrutinee_stays_never_even_with_a_tiny_budget() {
        // The scrutinee-diverges early return in check_match happens
        // before check_match_exhaustiveness is ever called, so an
        // exhausted budget must never change this: `return` always
        // diverges, regardless of how little budget remains for
        // analysis that never runs.
        let interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let registry = ItemRegistry::default();
        let mut checker = checker_with_budget(&interner, &registry, source, 1);
        let scrutinee = HirExpr::Return {
            id: ExprId(0),
            value: Some(Box::new(HirExpr::Int {
                id: ExprId(1),
                value: 0,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            })),
            span: Span::dummy(),
        };
        checker.current_return_type = Ty::I64;
        let arms = vec![
            HirMatchArm {
                pattern: HirPattern::Bool {
                    id: crate::hir::PatternId(0),
                    value: true,
                    span: Span::dummy(),
                },
                body: HirMatchArmBody::Expr(HirExpr::Int {
                    id: ExprId(2),
                    value: 1,
                    base: crate::lexer::IntBase::Decimal,
                    span: Span::dummy(),
                }),
                span: Span::dummy(),
            },
            HirMatchArm {
                pattern: HirPattern::Bool {
                    id: crate::hir::PatternId(1),
                    value: false,
                    span: Span::dummy(),
                },
                body: HirMatchArmBody::Expr(HirExpr::Bool {
                    id: ExprId(3),
                    value: true,
                    span: Span::dummy(),
                }),
                span: Span::dummy(),
            },
        ];
        let result_ty = checker.check_match(&scrutinee, &arms, Span::dummy());
        assert_eq!(result_ty, Ty::Never);
        assert!(!checker.diagnostics.iter().any(|d| d.code == "T0019"));
    }

    #[test]
    fn wrong_arity_pattern_with_no_catch_all_suppresses_exhaustiveness_cascade() {
        // Without a valid coverage matrix, a wrong-arity arm must not
        // also produce a non-exhaustive-match diagnostic: the coverage
        // analysis cannot be trusted once any arm's pattern is invalid,
        // so it is skipped entirely rather than risk a misleading
        // cascade on top of the arity diagnostic.
        let diags = check(
            "variant V { A(i64) } \
             func test(v: V) -> i64 { \
                 return match v { \
                     A(x, y) => x \
                 } \
             }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0002");
    }

    #[test]
    fn integer_pattern_against_a_bool_scrutinee_invalidates_the_pattern() {
        // A literal pattern's own unify_report failing must mark it
        // invalid -- not just report T0001 while still being treated as
        // a fully analyzable pattern.
        let diags = check("func f(x: bool) -> i64 { return match x { 1 => 10, _ => 0 } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn bool_pattern_against_an_integer_scrutinee_invalidates_the_pattern() {
        let diags = check("func f(x: i64) -> i64 { return match x { true => 1, _ => 0 } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn string_pattern_against_a_char_scrutinee_invalidates_the_pattern() {
        let diags = check("func f(x: char) -> i64 { return match x { \"y\" => 1, _ => 0 } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn char_pattern_against_a_string_scrutinee_invalidates_the_pattern() {
        let diags = check("func f(x: str) -> i64 { return match x { 'y' => 1, _ => 0 } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn invalid_literal_pattern_with_a_mismatched_arm_body_reports_only_its_own_diagnostic() {
        // The first arm's mismatched literal pattern (bool vs. the i64
        // scrutinee) invalidates the whole match, so the second arm's
        // bool body -- which would otherwise mismatch the third arm's
        // i64 body if joined -- must never also produce its own
        // "match arms must have the same type" T0001 on top of the
        // pattern's.
        let diags = check(
            "func f(x: i64) -> i64 { \
                 return match x { true => false, 2 => 2, _ => 0 } \
             }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn invalid_literal_pattern_with_no_catch_all_suppresses_exhaustiveness_cascade() {
        // No wildcard arm at all would ordinarily be non-exhaustive
        // (T0017) -- but the coverage matrix built from this mismatched
        // literal pattern can't be trusted, so exhaustiveness analysis
        // must be skipped entirely rather than report a misleading
        // T0017 on top of the pattern's own T0001.
        let diags = check("func f(x: bool) -> i64 { return match x { 1 => 10 } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
        assert!(!diags.iter().any(|d| d.code == "T0017"));
        assert!(!diags.iter().any(|d| d.code == "T0018"));
    }

    #[test]
    fn nested_mismatched_literal_pattern_is_a_diagnostic_not_a_panic() {
        let diags = check(
            "variant Outer { A(bool) } \
             func test(o: Outer) -> i64 { \
                 return match o { \
                     A(1) => 0, \
                     _ => 1 \
                 } \
             }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
        assert!(!diags.iter().any(|d| d.code == "T0017"));
        assert!(!diags.iter().any(|d| d.code == "T0018"));
    }

    #[test]
    fn diverging_scrutinee_makes_the_whole_match_never() {
        let diags = check(
            "func f() -> i64 { \
                 return match (return 1) { _ => true } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn defer_statement_is_reported_as_an_unsupported_feature() {
        // `defer` must never be silently dropped: it is parsed and its
        // expression is still checked, but running it has no
        // implemented semantics yet.
        let diags = check("func f() { value x = 1; defer x + 1; }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0007");
    }

    #[test]
    fn postfix_try_is_reported_as_an_unsupported_feature() {
        let diags = check("func f(x: i64) -> i64 { return x? }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0007");
    }

    #[test]
    fn range_expression_is_reported_as_an_unsupported_feature() {
        // A range must never be silently lowered to just its left
        // operand -- it has to be flagged instead.
        let diags = check("func f() { value r = 1..10; }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0007");
    }

    #[test]
    fn inclusive_range_expression_is_reported_as_an_unsupported_feature() {
        let diags = check("func f() { value r = 1..=10; }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0007");
    }

    #[test]
    fn field_access_on_a_primitive_type_is_a_diagnostic() {
        let diags = check("func f(x: i64) -> i64 { return x.y }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0013");
    }

    #[test]
    fn non_empty_uses_clause_is_reported_as_an_unsupported_feature() {
        let diags = check("func f() uses Database.Read { }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0007");
    }

    #[test]
    fn non_empty_raises_clause_is_reported_as_an_unsupported_feature() {
        let diags = check("func f() raises NotFound { }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0007");
    }

    #[test]
    fn recursive_function_type_checks() {
        let diags =
            check("func fact(n: i64) -> i64 { if n == 0 { return 1 } return n * fact(n - 1) }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn cast_expression_is_reported_as_an_unsupported_feature() {
        // `as` performs no runtime conversion in Alpha 0.1, so accepting
        // it silently would let a program type-check while lying about
        // what it does; it must be flagged instead.
        let diags = check("func f() -> f64 { value x = 1; return x as f64 }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0007");
    }

    #[test]
    fn cast_to_an_unknown_type_still_reports_the_unknown_type() {
        // The unsupported-cast diagnostic must not swallow an
        // independently wrong type name in the cast's target.
        let diags = check("func f() -> i64 { value x = 1; return x as Banana }");
        assert_eq!(diags.len(), 2);
        assert!(diags.iter().any(|d| d.code == "T0006"));
        assert!(diags.iter().any(|d| d.code == "T0007"));
    }

    #[test]
    fn explicit_binding_type_annotation_is_checked() {
        let diags = check("func f() { value x: i64 = true; }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn break_with_a_value_is_reported_until_loop_expressions_exist() {
        let diags = check("func f() { loop { break 1; } }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0007");
    }

    #[test]
    fn break_with_a_unit_value_is_still_rejected() {
        // A `unit`-typed value used to slip through silently (it
        // unifies with `unit` with no diagnostic); every value-carrying
        // `break` is unconditionally unsupported now, regardless of the
        // value's type.
        let diags = check("func f() { loop { break {}; } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0007");
    }

    #[test]
    fn break_with_a_never_value_is_still_rejected() {
        let diags = check("func f() { loop { break return; } }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0007");
    }

    #[test]
    fn mixed_integer_and_float_literal_addition_is_a_diagnostic() {
        // Regression: unifying an Integer-kinded literal variable with a
        // Float-kinded one must be rejected during `check`, never
        // silently accepted only to disagree with NIR/the interpreter
        // at runtime.
        let diags = check("func main() { value x = 1 + 2.0; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn unknown_return_type_is_a_diagnostic() {
        let diags = check("func main() -> Banana { return true }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0006");
    }

    #[test]
    fn unknown_parameter_type_is_a_diagnostic() {
        let diags = check("func f(x: Banana) -> i64 { return 0 }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0006");
    }

    #[test]
    fn declared_record_name_is_a_known_type() {
        let diags = check("record Point { x: i64, y: i64 } func f(p: Point) -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn declared_variant_name_is_a_known_type() {
        let diags = check("variant Shape { Circle } func f(s: Shape) -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn unknown_binding_annotation_type_is_a_diagnostic() {
        let diags = check("func f() { value x: Banana = 1; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0006");
    }

    #[test]
    fn return_with_trailing_semicolon_and_no_tail_type_checks() {
        // Regression: a block whose only content is a semicolon-
        // terminated `return` statement (no tail expression at all)
        // must not be reported as having type `unit`.
        let diags = check("func main() -> i64 { return 42; }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn multiple_explicit_return_paths_type_check() {
        let diags = check(
            "func classify(n: i64) -> i64 { \
                 if n < 0 { return -1; } \
                 if n == 0 { return 0; } \
                 return 1; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn if_where_both_branches_diverge_has_never_type() {
        // Used in a context (as a value bound to `x`) that would only
        // type-check if the if-expression's own type is `never`
        // (which unifies with anything) rather than `unit`.
        let diags = check(
            "func f(n: i64) -> i64 { \
                 value x: i64 = if n == 0 { return 1; } else { return 2; }; \
                 return x \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn if_join_is_the_non_diverging_branch_type_when_then_diverges() {
        // The join must not naively return "the then-branch's type":
        // here the then-branch is `never` and the else-branch is `i64`,
        // so the overall `if` must resolve to `i64`, not `never`.
        let diags = check(
            "func choose(flag: bool) -> i64 { \
                 if flag { return 1 } else { 2 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn if_join_is_the_non_diverging_branch_type_when_else_diverges() {
        // The mirror image: the join must be symmetric, so a diverging
        // else-branch must equally not overwrite a real then-branch type.
        let diags = check(
            "func choose(flag: bool) -> i64 { \
                 if flag { 2 } else { return 1 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn if_join_reports_a_mismatch_when_neither_branch_diverges() {
        let diags = check("func f() -> i64 { return if true { 1 } else { false } }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn if_condition_that_diverges_makes_the_whole_if_never() {
        // The condition itself never produces a value, so neither
        // branch is ever reached -- the whole `if` must be `never`
        // regardless of what the (still-checked) branches resolve to,
        // and the mismatched branch types below must not be reported
        // (unreachable code's *type* must not surface a diagnostic the
        // way an independent nested error still would).
        let diags = check(
            "func f() -> i64 { \
                 return if (return 1) { true } else { false } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn else_if_chain_propagates_the_join_through_every_link() {
        let diags = check(
            "func choose(n: i64) -> i64 { \
                 if n == 0 { return 1 } else if n == 1 { 2 } else { return 3 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn unary_not_on_a_diverging_operand_is_never() {
        let diags = check("func f() -> i64 { return !{ return 7 } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn comparison_with_a_diverging_right_operand_is_never() {
        let diags = check("func f() -> i64 { return 1 == { return 7 } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn comparison_with_a_diverging_left_operand_is_never() {
        let diags = check("func f() -> i64 { return { return 7 } == 1 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn arithmetic_with_a_diverging_operand_is_never() {
        let diags = check("func f() -> i64 { return 1 + { return 7 } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn assignment_with_a_diverging_right_hand_side_is_never() {
        let diags = check(
            "func f() -> i64 { \
                 mutable x = 0; \
                 return { x = { return 7 }; 0 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn call_with_a_diverging_argument_is_never() {
        let diags = check(
            "func add(a: i64, b: i64) -> i64 { return a + b } \
             func f() -> i64 { return add(1, { return 7 }) }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn logical_and_with_a_diverging_left_operand_is_never() {
        let diags = check("func f() -> bool { return { return true } && true }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn logical_and_with_a_diverging_right_operand_is_not_forced_never() {
        // The right side of `&&` is short-circuited: it may never
        // actually execute, so a `never` right operand must not force
        // the whole expression to `never` -- it stays `bool`.
        let diags = check("func f(x: bool) -> bool { return x && { return true } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn logical_or_with_a_diverging_right_operand_is_not_forced_never() {
        let diags = check("func f(x: bool) -> bool { return x || { return true } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn while_condition_that_diverges_makes_the_statement_diverge() {
        let diags = check("func main() { while { return; } {} }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn nested_if_propagates_never_through_the_outer_join() {
        let diags = check(
            "func f(a: bool, b: bool) -> i64 { \
                 if a { \
                     if b { return 1 } else { return 2 } \
                 } else { \
                     3 \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn diverging_statement_does_not_hide_later_unreachable_diagnostics() {
        // The block still diverges (type never) even though later,
        // unreachable code contains its own independent error; that
        // later error is still worth reporting.
        let diags = check("func f() -> i64 { return 1; return true; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn binding_with_diverging_initializer_diverges_the_block() {
        let diags = check("func f() -> i64 { value x = return 1; }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn assigning_to_a_literal_is_a_diagnostic() {
        let diags = check("func f() { 1 = 2; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0008");
    }

    #[test]
    fn assigning_to_a_call_result_is_a_diagnostic() {
        let diags = check("func g() -> i64 { return 1 } func f() { g() = 2; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0008");
    }

    #[test]
    fn calling_a_non_function_value_is_a_diagnostic() {
        let diags = check("func f() { value x = 1; x(); }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0009");
    }

    #[test]
    fn using_a_function_name_as_a_value_is_a_diagnostic() {
        let diags = check(
            "func add(a: i64, b: i64) -> i64 { return a + b } \
             func f() -> i64 { value g = add; return g }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0010");
    }

    #[test]
    fn break_outside_a_loop_is_a_diagnostic() {
        let diags = check("func f() { break; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0011");
    }

    #[test]
    fn continue_outside_a_loop_is_a_diagnostic() {
        let diags = check("func f() { continue; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0011");
    }

    #[test]
    fn break_inside_a_loop_statement_is_fine() {
        let diags = check("func f() { loop { break; } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn continue_inside_a_while_loop_is_fine() {
        let diags = check("func f() { while true { continue; } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn break_nested_inside_an_if_inside_a_loop_is_fine() {
        // The `if` itself doesn't change loop nesting; `break` still
        // sees the enclosing `loop`.
        let diags = check("func f() { loop { if true { break; } } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn break_after_a_loop_statement_ends_is_a_diagnostic() {
        // Loop nesting must not leak past the loop it came from.
        let diags = check("func f() { loop { break; } break; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0011");
    }

    #[test]
    fn main_with_parameters_is_a_diagnostic() {
        let diags = check("func main(x: i64) -> i64 { return x }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0012");
    }

    #[test]
    fn main_with_no_parameters_is_fine() {
        let diags = check("func main() -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn expr_types_never_leaks_an_unresolved_type_variable() {
        let result = check_full("func f() -> i64 { value x = 1; return x + 1 }");
        assert!(
            result.diagnostics.is_empty(),
            "unexpected diagnostics: {:?}",
            result.diagnostics
        );
        for (id, ty) in &result.expr_types {
            assert!(
                !matches!(ty, Ty::Var(_)),
                "expr {id:?} leaked an unresolved type variable: {ty:?}"
            );
        }
    }

    #[test]
    fn expr_types_records_a_literals_type_as_unified_with_its_context() {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", "func f(x: i32) -> i32 { return x + 1 }");
        let mut interner = Interner::new();
        let (tokens, _) = tokenize(map.get(id).content(), id, &mut interner);
        let (module, _) = Parser::new(tokens, id, &mut interner).parse_module();
        let (hir, _) = lower_module(&module, id, &interner);
        let result = check_module(&hir, id, &interner, EntryMain::ByName);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected diagnostics: {:?}",
            result.diagnostics
        );

        let HirExpr::Return { value, .. } = hir.functions[0].body.tail.as_deref().unwrap() else {
            panic!("expected return")
        };
        let HirExpr::Binary { right, .. } = value.as_deref().unwrap() else {
            panic!("expected binary")
        };
        // `1`'s own recorded type must be i32 -- what it was unified
        // with via `x` -- not the bare i64 default a literal takes with
        // no surrounding context. This is exactly what lets NIR lowering
        // read the literal's real type instead of re-deriving it.
        assert_eq!(result.expr_types.get(&right.id()), Some(&Ty::I32));
    }

    #[test]
    fn distinct_expressions_get_distinct_expr_ids() {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", "func f() -> i64 { return 1 + 2 }");
        let mut interner = Interner::new();
        let (tokens, _) = tokenize(map.get(id).content(), id, &mut interner);
        let (module, _) = Parser::new(tokens, id, &mut interner).parse_module();
        let (hir, _) = lower_module(&module, id, &interner);

        let HirExpr::Return { value, .. } = hir.functions[0].body.tail.as_deref().unwrap() else {
            panic!("expected return")
        };
        let binary = value.as_deref().unwrap();
        let HirExpr::Binary { left, right, .. } = binary else {
            panic!("expected binary")
        };
        assert_ne!(left.id(), right.id());
        assert_ne!(left.id(), binary.id());
    }

    #[test]
    fn well_typed_record_construction_has_no_diagnostics() {
        let diags = check(
            "record User { id: i64, enabled: bool } \
             func f() -> i64 { value u = User { id: 1, enabled: true }; return 0 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn record_field_type_mismatch_is_a_diagnostic() {
        let diags = check(
            "record User { id: i64 } \
             func f() { value u = User { id: true }; }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn well_typed_field_access_returns_the_declared_field_type() {
        let diags = check(
            "record User { id: i64 } \
             func f(u: User) -> i64 { return u.id }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn accessing_a_private_field_from_a_different_declaring_module_is_m0011() {
        // Hand-built: a record declared in one "module" (its own
        // source) with a private field, accessed from a function whose
        // own source differs -- the only way to exercise this without
        // a full project compilation, which is exactly the scenario
        // check_module now has to get right once modules are lowered
        // separately and merged.
        let mut map = SourceMap::new();
        let record_source = map.add_file("point.npt", "");
        let accessing_source = map.add_file("main.npt", "");
        let mut interner = Interner::new();
        let record_name = interner.intern("Point");
        let field_x = interner.intern("x");
        let field_y = interner.intern("y");
        let param_name = interner.intern("p");
        let fn_name = interner.intern("f");

        let record = crate::hir::HirRecord {
            id: ItemId(0),
            name: record_name,
            span: Span::dummy(),
            source: record_source,
            public: true,
            type_params: Vec::new(),
            fields: vec![
                crate::hir::HirField {
                    name: field_x,
                    span: Span::dummy(),
                    public: true,
                    ty: HirType::Unresolved {
                        name: interner.intern("i64"),
                        span: Span::dummy(),
                    },
                },
                crate::hir::HirField {
                    name: field_y,
                    span: Span::dummy(),
                    public: false,
                    ty: HirType::Unresolved {
                        name: interner.intern("i64"),
                        span: Span::dummy(),
                    },
                },
            ],
        };
        let param_local = LocalId(0);
        let function = HirFunction {
            id: ItemId(1),
            name: fn_name,
            name_span: Span::dummy(),
            source: accessing_source,
            public: true,
            type_params: Vec::new(),
            params: vec![crate::hir::HirParam {
                local: param_local,
                name: param_name,
                span: Span::dummy(),
                ty: HirType::Aggregate {
                    item: ItemId(0),
                    kind: crate::hir::AggregateKind::Record,
                    name: record_name,
                    args: Vec::new(),
                    span: Span::dummy(),
                },
            }],
            return_type: Some(HirType::Unresolved {
                name: interner.intern("i64"),
                span: Span::dummy(),
            }),
            uses: vec![],
            raises: vec![],
            body: crate::hir::HirBlock {
                id: crate::hir::ExprId(0),
                statements: vec![],
                tail: Some(Box::new(HirExpr::Field {
                    id: crate::hir::ExprId(1),
                    base: Box::new(HirExpr::Local {
                        id: crate::hir::ExprId(2),
                        local: param_local,
                        name: param_name,
                        span: Span::dummy(),
                    }),
                    name: field_y,
                    span: Span::dummy(),
                })),
                span: Span::dummy(),
            },
            span: Span::dummy(),
        };
        let hir = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: vec![record],
            variants: vec![],
            other_items: vec![],
        };
        let result = check_module(&hir, accessing_source, &interner, EntryMain::ByName);
        assert_eq!(
            result.diagnostics.len(),
            1,
            "unexpected diagnostics: {:?}",
            result.diagnostics
        );
        assert_eq!(result.diagnostics[0].code, "M0011");
    }

    #[test]
    fn unknown_field_access_is_a_diagnostic() {
        let diags = check(
            "record User { id: i64 } \
             func f(u: User) -> i64 { return u.age }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0014");
    }

    #[test]
    fn field_access_on_a_variant_is_a_diagnostic() {
        let diags = check(
            "variant Shape { Circle } \
             func f(s: Shape) -> i64 { return s.x }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0013");
    }

    #[test]
    fn field_mutation_is_a_diagnostic() {
        let diags = check(
            "record User { age: i64 } \
             func f(u: User) { u.age = 20; }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0015");
    }

    #[test]
    fn well_typed_variant_construction_has_no_diagnostics() {
        let diags = check(
            "variant Shape { Circle(i64), Empty } \
             func f() -> i64 { value s = Shape.Circle(1); value e = Shape.Empty; return 0 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn variant_payload_arity_mismatch_is_a_diagnostic() {
        let diags = check(
            "variant Shape { Circle(i64) } \
             func f() { value s = Shape.Circle(1, 2); }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0002");
    }

    #[test]
    fn variant_payload_type_mismatch_is_a_diagnostic() {
        let diags = check(
            "variant Shape { Circle(i64) } \
             func f() { value s = Shape.Circle(true); }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn qualified_payload_carrying_constructor_prints_the_variant_type_name() {
        // `Ty::Named`'s displayed symbol must be the variant declaration's
        // own name (`Shape`), never the case name (`Circle`), even though
        // the constructor was written qualified and carries a payload.
        let diags =
            check("variant Shape { Circle(i64) } func f() -> bool { return Shape.Circle(1) }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
        assert!(diags[0].message.contains("Shape"), "{:?}", diags[0]);
        assert!(!diags[0].message.contains("Circle"), "{:?}", diags[0]);
    }

    #[test]
    fn unqualified_constructor_prints_the_variant_type_name() {
        let diags = check("variant Shape { Circle(i64) } func f() -> bool { return Circle(1) }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
        assert!(diags[0].message.contains("Shape"), "{:?}", diags[0]);
        assert!(!diags[0].message.contains("Circle"), "{:?}", diags[0]);
    }

    #[test]
    fn unit_case_reference_prints_the_variant_type_name() {
        let diags = check("variant Shape { Empty } func f() -> bool { return Shape.Empty }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
        assert!(diags[0].message.contains("Shape"), "{:?}", diags[0]);
        assert!(!diags[0].message.contains("Empty"), "{:?}", diags[0]);
    }

    #[test]
    fn variant_argument_type_mismatch_diagnostic_mentions_the_variant_not_the_case() {
        let diags = check(
            "variant Shape { Circle(i64) } \
             variant Other { X } \
             func take(o: Other) { } \
             func f() { take(Shape.Circle(1)); }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
        assert!(diags[0].message.contains("Shape"), "{:?}", diags[0]);
        assert!(!diags[0].message.contains("Circle"), "{:?}", diags[0]);
    }

    #[test]
    fn bare_unit_case_reference_needs_no_call_syntax() {
        let diags = check(
            "variant Shape { Empty } \
             func f() { value s = Shape.Empty; }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn bare_case_reference_missing_required_payload_is_a_diagnostic() {
        let diags = check(
            "variant Shape { Circle(i64) } \
             func f() { value s = Shape.Circle; }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0002");
    }

    #[test]
    fn record_equality_is_a_diagnostic() {
        let diags = check(
            "record Point { x: i64 } \
             func f(a: Point, b: Point) -> bool { return a == b }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0016");
    }

    #[test]
    fn variant_equality_is_a_diagnostic() {
        let diags = check(
            "variant Shape { Empty } \
             func f(a: Shape, b: Shape) -> bool { return a != b }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0016");
    }

    #[test]
    fn record_values_pass_through_function_calls() {
        let diags = check(
            "record Point { x: i64 } \
             func identity(p: Point) -> Point { return p } \
             func f(p: Point) -> Point { return identity(p) }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn diverging_record_field_initializer_makes_construction_never() {
        let diags = check(
            "record Point { x: i64, y: i64 } \
             func f() -> i64 { \
                 value p = Point { x: return 1, y: 2 }; \
                 return 0 \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn single_file_mismatch_shows_the_bare_type_name_with_no_module_prefix() {
        // Single-file compilation (`check_module`'s own empty-module-path
        // registry, `rfcs/0007`) has no project-level module path at all
        // -- a nominal type mismatch must still read exactly as it did
        // before qualified diagnostics existed, never a stray `.` or an
        // empty-string prefix.
        let diags = check(
            "record User { id: i64 } \
             record Point { x: i64 } \
             func take_user(u: User) -> i64 { return u.id } \
             func f() -> i64 { value p = Point { x: 1 }; return take_user(p) }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
        assert_eq!(
            diags[0].message,
            "argument type does not match the parameter's declared type: \
             expected `User`, found `Point`"
        );
    }

    #[test]
    fn primitive_type_mismatch_diagnostics_are_unaffected_by_qualification() {
        let diags = check("func f() -> i64 { return true }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
        assert_eq!(
            diags[0].message,
            "the returned value does not match the function's declared return type: \
             expected `i64`, found `bool`"
        );
    }

    // -- Unsupported operations on an unconstrained type parameter
    // (T0027, `rfcs/0008`) --------------------------------------------

    #[test]
    fn equality_on_an_unconstrained_type_parameter_is_rejected_symbolically() {
        // The regression this fix exists for: `left == right` inside a
        // generic function's own body must fail here, at generic-body
        // checking time, never be deferred to a runtime comparison that
        // only fails once some particular call site instantiates `T`
        // with a record.
        let diags = check(
            "func same[T](left: T, right: T) -> bool { return left == right } \
             func main() -> i64 { return 1 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0027");
    }

    #[test]
    fn inequality_on_an_unconstrained_type_parameter_is_rejected_symbolically() {
        let diags = check(
            "func differs[T](left: T, right: T) -> bool { return left != right } \
             func main() -> i64 { return 1 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0027");
    }

    #[test]
    fn equality_on_an_unconstrained_type_parameter_is_rejected_even_when_instantiated_with_a_record()
     {
        // The declaration is rejected once, symbolically -- it must
        // never even reach a call site for this to be caught, but this
        // also proves that a call site instantiating `T` with a record
        // does not somehow let it through as a "record equality"
        // problem instead (that would be a *different*, misleading
        // diagnostic for the same underlying issue).
        let diags = check(
            "record Point { x: i64 } \
             func same[T](left: T, right: T) -> bool { return left == right } \
             func main() -> i64 { \
                 value p = Point { x: 1 }; \
                 value q = Point { x: 1 }; \
                 return if same(p, q) { 1 } else { 0 } \
             }",
        );
        assert!(
            diags.iter().any(|d| d.code == "T0027"),
            "expected a T0027 diagnostic, got {diags:?}"
        );
        assert!(
            diags.iter().all(|d| d.code != "T0001"),
            "the generic body's own T0027 must not cascade into an unrelated call-site \
             mismatch: {diags:?}"
        );
    }

    #[test]
    fn ordering_on_an_unconstrained_type_parameter_is_rejected_symbolically() {
        let diags = check(
            "func less[T](left: T, right: T) -> bool { return left < right } \
             func main() -> i64 { return 1 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0027");
    }

    #[test]
    fn logical_and_on_an_unconstrained_type_parameter_is_rejected_symbolically() {
        // Both operands are the same unconstrained `T`; `&&` checks each
        // side independently, so this may report once per side -- what
        // matters is that every diagnostic produced is T0027, and that
        // there is at least one.
        let diags = check(
            "func both[T](left: T, right: T) -> bool { return left && right } \
             func main() -> i64 { return 1 }",
        );
        assert!(!diags.is_empty(), "expected at least one diagnostic");
        assert!(
            diags.iter().all(|d| d.code == "T0027"),
            "unexpected diagnostics: {diags:?}"
        );
    }

    #[test]
    fn logical_not_on_an_unconstrained_type_parameter_is_rejected_symbolically() {
        let diags = check(
            "func negate[T](x: T) -> bool { return !x } \
             func main() -> i64 { return 1 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0027");
    }

    #[test]
    fn using_an_unconstrained_type_parameter_as_an_if_condition_is_rejected_symbolically() {
        let diags = check(
            "func pick[T](x: T) -> i64 { return if x { 1 } else { 0 } } \
             func main() -> i64 { return 1 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0027");
    }

    #[test]
    fn field_access_on_an_unconstrained_type_parameter_is_rejected_symbolically() {
        let diags = check(
            "func get[T](x: T) -> i64 { return x.field } \
             func main() -> i64 { return 1 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0027");
    }

    #[test]
    fn calling_an_unconstrained_type_parameter_is_rejected_symbolically() {
        let diags = check(
            "func invoke[T](x: T) -> i64 { return x() } \
             func main() -> i64 { return 1 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0027");
    }

    #[test]
    fn bitwise_and_on_an_unconstrained_type_parameter_is_rejected_symbolically() {
        let diags = check(
            "func mask[T](left: T, right: T) -> T { return left & right } \
             func main() -> i64 { return 1 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0027");
    }

    #[test]
    fn plain_movement_binding_and_return_of_an_unconstrained_type_parameter_is_valid() {
        // The operations FIX 4 must *not* reject: passing, returning,
        // and binding a value of an unconstrained `T` requires no proven
        // capability at all.
        let diags = check(
            "func identity[T](x: T) -> T { \
                 value bound = x; \
                 return bound \
             } \
             func main() -> i64 { return 1 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    // -- Exhaustiveness after generic substitution (`rfcs/0008`) --------

    #[test]
    fn generic_variant_match_is_exhaustive_using_the_instantiated_payload_type() {
        // The regression this fix exists for: `Maybe[bool]`'s `Some`
        // payload must be checked as the closed, two-value `bool` space
        // it actually is once instantiated, not the declaration's own
        // unresolved `Ty::Param`, which would never be considered fully
        // covered by any finite set of arms.
        let diags = check(
            "variant Maybe[T] { Some(T), None } \
             func inspect(v: Maybe[bool]) -> i64 { \
                 return match v { \
                     Some(true) => 1, \
                     Some(false) => 2, \
                     None => 0, \
                 } \
             } \
             func main() -> i64 { return 1 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn generic_variant_match_missing_a_bool_case_is_still_reported() {
        let diags = check(
            "variant Maybe[T] { Some(T), None } \
             func inspect(v: Maybe[bool]) -> i64 { \
                 return match v { \
                     Some(true) => 1, \
                     None => 0, \
                 } \
             } \
             func main() -> i64 { return 1 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0017");
        assert!(
            diags[0].message.contains("Some(false)"),
            "expected the concrete missing witness `Some(false)`, got: {}",
            diags[0].message
        );
    }

    #[test]
    fn generic_variant_match_with_a_redundant_arm_after_both_bool_cases_is_unreachable() {
        let diags = check(
            "variant Maybe[T] { Some(T), None } \
             func inspect(v: Maybe[bool]) -> i64 { \
                 return match v { \
                     Some(true) => 1, \
                     Some(false) => 2, \
                     Some(x) => 3, \
                     None => 0, \
                 } \
             } \
             func main() -> i64 { return 1 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0018");
    }

    #[test]
    fn nested_generic_variant_match_is_exhaustive_using_the_instantiated_payload_type() {
        let diags = check(
            "variant Maybe[T] { Some(T), None } \
             func inspect(v: Maybe[Maybe[bool]]) -> i64 { \
                 return match v { \
                     Some(Some(true)) => 1, \
                     Some(Some(false)) => 2, \
                     Some(None) => 3, \
                     None => 0, \
                 } \
             } \
             func main() -> i64 { return 1 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn nested_generic_variant_match_missing_one_inner_bool_case_is_reported() {
        let diags = check(
            "variant Maybe[T] { Some(T), None } \
             func inspect(v: Maybe[Maybe[bool]]) -> i64 { \
                 return match v { \
                     Some(Some(true)) => 1, \
                     Some(None) => 3, \
                     None => 0, \
                 } \
             } \
             func main() -> i64 { return 1 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0017");
        assert!(
            diags[0].message.contains("Some(false)"),
            "expected a concrete missing witness naming the inner `false` case, got: {}",
            diags[0].message
        );
    }

    #[test]
    fn generic_variant_exhaustiveness_still_respects_the_usefulness_budget() {
        // A hand-tightened budget (rather than a fixture that genuinely
        // consumes MAX_USEFULNESS_STEPS) proves the work budget applies
        // to a *generic* variant's substituted space the same way it
        // already does for a non-generic one -- this fix only changes
        // which space a payload position resolves to, never the
        // recursive step-counting that enforces the budget itself.
        let mut interner = Interner::new();
        let name = interner.intern("Maybe");
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let registry = ItemRegistry::default();
        let mut checker = checker_with_budget(&interner, &registry, source, 1);
        let maybe = ItemId(0);
        let t = TypeParamId(0);
        checker.variants.insert(
            maybe,
            VariantInfo {
                name,
                cases: vec![(name, vec![Ty::Param(t, name)]), (name, vec![])],
                type_params: vec![t],
            },
        );
        let scrutinee = Ty::Applied(maybe, vec![Ty::Bool]);
        let resolved_patterns = vec![
            ResolvedPattern::Variant {
                variant: maybe,
                case: 0,
                args: vec![ResolvedPattern::Bool(true)],
            },
            ResolvedPattern::Variant {
                variant: maybe,
                case: 0,
                args: vec![ResolvedPattern::Bool(false)],
            },
            ResolvedPattern::Variant {
                variant: maybe,
                case: 1,
                args: vec![],
            },
        ];
        let trivial_arm = || HirMatchArm {
            pattern: HirPattern::Wildcard {
                id: crate::hir::PatternId(0),
                span: Span::dummy(),
            },
            body: HirMatchArmBody::Expr(HirExpr::Int {
                id: ExprId(0),
                value: 0,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            }),
            span: Span::dummy(),
        };
        let arms = vec![trivial_arm(), trivial_arm(), trivial_arm()];
        let coverage = checker.check_match_exhaustiveness(
            &scrutinee,
            &resolved_patterns,
            &arms,
            Span::dummy(),
        );
        assert!(
            matches!(coverage, MatchCoverage::Failed),
            "expected the tiny budget to fail this generic match's analysis"
        );
        assert!(
            checker
                .diagnostics
                .iter()
                .any(|d| d.code == codes::PATTERN_BUDGET_EXCEEDED),
            "expected a budget-exceeded diagnostic, got {:?}",
            checker.diagnostics
        );
    }
}
