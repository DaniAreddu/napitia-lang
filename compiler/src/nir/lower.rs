//! HIR-to-NIR lowering.
//!
//! Every local (parameter, `value`/`mutable` statement) gets a storage
//! slot and is accessed uniformly through `alloc`/`store`/`load`; NIR
//! does not construct phi nodes in this milestone (`spec/0006`). A
//! branching expression used as a value (`if`/`&&`/`||`) instead uses an
//! implicit temporary slot: each arm stores its result into the slot
//! before jumping to a shared merge block, which then loads it — the
//! same effect a phi node would have, without needing one.
//!
//! Lowering assumes its input already passed type-checking, so in the
//! ordinary pipeline (`driver::ir`) it never runs on a program the
//! checker rejected. Even so, lowering is atomic: either every function
//! lowers and the caller gets a complete `Module`, or lowering fails
//! with diagnostics and the caller gets no module at all. There is no
//! partial result -- a `Call` in a successfully-lowered function can
//! never reference a function that lowering silently left out, because
//! there is no way to leave one out and still get a `Module` back.

use std::collections::{BTreeMap, HashMap, HashSet};

use super::{
    BasicBlock, CaseLayout, Const, ExtendLayout, Function, InvokeErrTarget, Module, Param,
    ProtocolLayout, ProtocolMethodLayout, RecordLayout, Terminator, ValueId, ValueKind,
    VariantLayout,
};
use crate::diagnostics::Diagnostic;
use crate::hir::{
    ExprId, HirBlock, HirElse, HirExpr, HirFailurePattern, HirFieldInit, HirFunction, HirHandleArm,
    HirHandleArmKind, HirMatchArm, HirMatchArmBody, HirModule, HirPattern, HirStmt, ItemId,
    LocalId, PatternId, TypeParamId,
};
use crate::limits::MAX_PATTERN_DEPTH;
use crate::place::{FieldId, Place, Projection};
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
use crate::syntax::ast::{AssignOp, BinaryOp, UnaryOp};
use crate::types::{CapabilityRequirement, Evidence, Ty, is_numeric, primitive_from_name};

use super::block::BlockId;

mod codes {
    /// A construct reached NIR lowering without the checker having
    /// already rejected it. In the ordinary pipeline this should be
    /// unreachable (`typeck` gates `match`/field access with its own
    /// T0007 first) -- this is lowering's own defense-in-depth, for
    /// direct callers that bypass that gate.
    pub const UNSUPPORTED_IN_NIR: &str = "I0001";
    /// Lowering itself failed to uphold one of its own structural
    /// invariants (e.g. a block was left without a terminator). This
    /// should never happen for any HIR built by `hir::lower_module` --
    /// it is a bug in `nir::lower` itself, reported as a diagnostic
    /// instead of a panic so that even a lowering bug degrades to a
    /// normal compiler error rather than crashing the process.
    pub const INTERNAL_INVARIANT_VIOLATED: &str = "I0002";
}

// Boxed so a single-`Diagnostic` `Err` doesn't force every `LowerResult`
// (including `LowerResult<()>`) to be as large as `Diagnostic` itself.
type LowerResult<T> = Result<T, Box<Diagnostic>>;

/// Lowers every function in `hir` to NIR. Either every function lowers
/// successfully and the whole `Module` is returned, or one or more
/// failed and the *only* thing returned is their diagnostics -- there is
/// no way to get back a `Module` with some functions missing.
#[allow(clippy::too_many_arguments)]
pub fn lower_module(
    hir: &HirModule,
    local_types: &HashMap<LocalId, Ty>,
    expr_types: &HashMap<ExprId, Ty>,
    pattern_case: &HashMap<PatternId, (ItemId, usize)>,
    call_type_args: &HashMap<ExprId, Vec<Ty>>,
    call_evidence: &HashMap<ExprId, Vec<Evidence>>,
    protocol_call_evidence: &HashMap<ExprId, Evidence>,
    cleanup_edges: &BTreeMap<ExprId, Vec<crate::resourceck::CleanupAction>>,
    consume_sites: &BTreeMap<ExprId, crate::resourceck::ConsumeInfo>,
    defer_plans: &BTreeMap<ExprId, crate::resourceck::CheckedDeferPlan>,
    interner: &Interner,
    source: SourceId,
) -> Result<Module, Vec<Diagnostic>> {
    lower_module_impl(
        hir,
        local_types,
        expr_types,
        pattern_case,
        call_type_args,
        call_evidence,
        protocol_call_evidence,
        cleanup_edges,
        consume_sites,
        defer_plans,
        interner,
        source,
        ModulePathMode::SingleFile,
    )
}

/// Like [`lower_module`], but for a caller that can supply each
/// declaring module's own dotted path -- read back by
/// [`canonical_raises`] so two variants sharing a bare name from
/// *different* modules still canonicalize to a stable, module-
/// qualified order rather than an ambiguous tie (`rfcs/0007`,
/// `rfcs/0010`). Always runs in [`ModulePathMode::Project`], even if
/// `module_path_of` happens to be empty -- unlike `lower_module`'s own
/// `SingleFile` mode, an empty table here means every lookup inside it
/// is a genuine metadata gap, not "no project at all".
#[allow(clippy::too_many_arguments)]
pub fn lower_module_with_paths(
    hir: &HirModule,
    local_types: &HashMap<LocalId, Ty>,
    expr_types: &HashMap<ExprId, Ty>,
    pattern_case: &HashMap<PatternId, (ItemId, usize)>,
    call_type_args: &HashMap<ExprId, Vec<Ty>>,
    call_evidence: &HashMap<ExprId, Vec<Evidence>>,
    protocol_call_evidence: &HashMap<ExprId, Evidence>,
    cleanup_edges: &BTreeMap<ExprId, Vec<crate::resourceck::CleanupAction>>,
    consume_sites: &BTreeMap<ExprId, crate::resourceck::ConsumeInfo>,
    defer_plans: &BTreeMap<ExprId, crate::resourceck::CheckedDeferPlan>,
    interner: &Interner,
    source: SourceId,
    module_path_of: &HashMap<SourceId, String>,
) -> Result<Module, Vec<Diagnostic>> {
    lower_module_impl(
        hir,
        local_types,
        expr_types,
        pattern_case,
        call_type_args,
        call_evidence,
        protocol_call_evidence,
        cleanup_edges,
        consume_sites,
        defer_plans,
        interner,
        source,
        ModulePathMode::Project(module_path_of),
    )
}

#[allow(clippy::too_many_arguments)]
fn lower_module_impl(
    hir: &HirModule,
    local_types: &HashMap<LocalId, Ty>,
    expr_types: &HashMap<ExprId, Ty>,
    pattern_case: &HashMap<PatternId, (ItemId, usize)>,
    call_type_args: &HashMap<ExprId, Vec<Ty>>,
    call_evidence: &HashMap<ExprId, Vec<Evidence>>,
    protocol_call_evidence: &HashMap<ExprId, Evidence>,
    cleanup_edges: &BTreeMap<ExprId, Vec<crate::resourceck::CleanupAction>>,
    consume_sites: &BTreeMap<ExprId, crate::resourceck::ConsumeInfo>,
    defer_plans: &BTreeMap<ExprId, crate::resourceck::CheckedDeferPlan>,
    interner: &Interner,
    source: SourceId,
    module_path_mode: ModulePathMode<'_>,
) -> Result<Module, Vec<Diagnostic>> {
    // Every module-level item's ItemId must be globally unique across
    // records, variants, and functions alike -- not just unique within
    // its own kind. hir::lower's own name resolution already keeps this
    // true for any HIR it produces, but this is a public entry point a
    // caller can invoke directly with a hand-built HirModule bypassing
    // that guarantee. Without this check, a duplicate id would make
    // record_layouts/variant_layouts silently overwrite the first
    // entry on insert, then panic on the second of two removals below
    // ("just inserted" no longer holds); a cross-kind collision would
    // let records/variants/function_sigs disagree about what the same
    // id names. Checked here, before any layout is built or any
    // function is lowered, so a malformed module fails atomically
    // rather than reaching either failure mode.
    let identity_diagnostics = validate_item_identities(hir, interner, source);
    if !identity_diagnostics.is_empty() {
        return Err(identity_diagnostics);
    }

    let mut record_layouts: HashMap<ItemId, RecordLayout> = HashMap::new();
    let mut record_order: Vec<ItemId> = Vec::new();
    for r in &hir.records {
        let fields = r
            .fields
            .iter()
            .map(|f| (f.name, resolve_named_type(interner, &f.ty)))
            .collect();
        record_order.push(r.id);
        record_layouts.insert(
            r.id,
            RecordLayout {
                name: r.name,
                type_params: r.type_params.iter().map(|p| (p.id, p.name)).collect(),
                fields,
                affine: r.affine,
            },
        );
    }
    let mut variant_layouts: HashMap<ItemId, VariantLayout> = HashMap::new();
    let mut variant_source: HashMap<ItemId, SourceId> = HashMap::new();
    let mut variant_order: Vec<ItemId> = Vec::new();
    for v in &hir.variants {
        variant_source.insert(v.id, v.source);
        let cases = v
            .cases
            .iter()
            .map(|c| CaseLayout {
                name: c.name,
                payload: c
                    .payload
                    .iter()
                    .map(|t| resolve_named_type(interner, t))
                    .collect(),
            })
            .collect();
        variant_order.push(v.id);
        variant_layouts.insert(
            v.id,
            VariantLayout {
                name: v.name,
                type_params: v.type_params.iter().map(|p| (p.id, p.name)).collect(),
                cases,
            },
        );
    }

    let mut function_sigs = HashMap::new();
    let mut function_requirements: HashMap<ItemId, Vec<CapabilityRequirement>> = HashMap::new();
    let mut function_raises: HashMap<ItemId, Vec<ItemId>> = HashMap::new();
    for f in &hir.functions {
        let params = f
            .params
            .iter()
            .map(|p| resolve_named_type(interner, &p.ty))
            .collect();
        let ret = f
            .return_type
            .as_ref()
            .map(|t| resolve_named_type(interner, t))
            .unwrap_or(Ty::Unit);
        let type_params = f.type_params.iter().map(|p| p.id).collect();
        function_sigs.insert(f.id, (type_params, params, ret));
        function_requirements.insert(
            f.id,
            f.requirements
                .iter()
                .map(|r| resolve_requirement(interner, r))
                .collect(),
        );
        let raises = match canonical_raises(
            f.raises.iter().map(|r| r.variant).collect(),
            &variant_layouts,
            &variant_source,
            module_path_mode,
            interner,
            source,
        ) {
            Ok(raises) => raises,
            Err(diagnostic) => return Err(vec![*diagnostic]),
        };
        function_raises.insert(f.id, raises);
    }

    // Every declared protocol's layout, in declaration order -- built
    // once, up front, since an extend's own method table (below) needs
    // to look a protocol's method names up by index.
    let mut protocols: Vec<(ItemId, ProtocolLayout)> = Vec::with_capacity(hir.protocols.len());
    for p in &hir.protocols {
        let methods = p
            .methods
            .iter()
            .map(|m| ProtocolMethodLayout {
                name: m.name,
                params: m
                    .params
                    .iter()
                    .map(|t| resolve_named_type(interner, t))
                    .collect(),
                return_type: m
                    .return_type
                    .as_ref()
                    .map(|t| resolve_named_type(interner, t))
                    .unwrap_or(Ty::Unit),
            })
            .collect();
        protocols.push((
            p.id,
            ProtocolLayout {
                name: p.name,
                type_params: p.type_params.iter().map(|tp| (tp.id, tp.name)).collect(),
                methods,
            },
        ));
    }

    // Every accepted extend's layout, in declaration order. `nir::lower`
    // trusts that every extend it sees here already passed `typeck`'s
    // authority/overlap/completeness validation (this module's own
    // "input already passed type-checking" contract, see its own module
    // doc) -- an unauthorized or incomplete extend never reaches here at
    // all in the ordinary pipeline. Each extend method is registered
    // exactly like an ordinary function (sharing the extend's own
    // `type_params`/`requirements`) and lowered the same way, below.
    let mut extends: Vec<(ItemId, ExtendLayout)> = Vec::with_capacity(hir.extends.len());
    let mut function_named_type_params: HashMap<ItemId, Vec<(crate::hir::TypeParamId, Symbol)>> =
        HashMap::new();
    for e in &hir.extends {
        let extend_type_params: Vec<crate::hir::TypeParamId> =
            e.type_params.iter().map(|p| p.id).collect();
        let extend_named_type_params: Vec<(crate::hir::TypeParamId, Symbol)> =
            e.type_params.iter().map(|p| (p.id, p.name)).collect();
        for m in &e.methods {
            function_named_type_params.insert(m.id, extend_named_type_params.clone());
        }
        let protocol_arguments: Vec<Ty> = e
            .protocol_arguments
            .iter()
            .map(|t| resolve_named_type(interner, t))
            .collect();
        let requirements: Vec<CapabilityRequirement> = e
            .requirements
            .iter()
            .map(|r| resolve_requirement(interner, r))
            .collect();
        let proto_method_names: Vec<Symbol> = protocols
            .iter()
            .find(|(id, _)| *id == e.protocol)
            .map(|(_, layout)| layout.methods.iter().map(|m| m.name).collect())
            .unwrap_or_default();
        let mut methods_by_index: Vec<Option<ItemId>> = vec![None; proto_method_names.len()];
        for m in &e.methods {
            function_sigs.insert(
                m.id,
                (
                    extend_type_params.clone(),
                    m.params
                        .iter()
                        .map(|p| resolve_named_type(interner, &p.ty))
                        .collect(),
                    m.return_type
                        .as_ref()
                        .map(|t| resolve_named_type(interner, t))
                        .unwrap_or(Ty::Unit),
                ),
            );
            function_requirements.insert(m.id, requirements.clone());
            let method_raises = match canonical_raises(
                m.raises.iter().map(|r| r.variant).collect(),
                &variant_layouts,
                &variant_source,
                module_path_mode,
                interner,
                source,
            ) {
                Ok(raises) => raises,
                Err(diagnostic) => return Err(vec![*diagnostic]),
            };
            function_raises.insert(m.id, method_raises);
            if let Some(index) = proto_method_names.iter().position(|n| *n == m.name) {
                methods_by_index[index] = Some(m.id);
            }
        }
        let mut methods = Vec::with_capacity(methods_by_index.len());
        for (index, method_id) in methods_by_index.into_iter().enumerate() {
            match method_id {
                Some(id) => methods.push(id),
                None => {
                    return Err(vec![Diagnostic::error(
                        codes::INTERNAL_INVARIANT_VIOLATED,
                        source,
                        e.span,
                        format!(
                            "extend for protocol method index {index} has no implementing function; typeck should have already rejected this incomplete extend"
                        ),
                    )]);
                }
            }
        }
        extends.push((
            e.id,
            ExtendLayout {
                protocol: e.protocol,
                type_params: extend_named_type_params,
                protocol_arguments,
                requirements,
                methods,
            },
        ));
    }

    let mut lowering = Lowering {
        local_types,
        expr_types,
        pattern_case,
        call_type_args,
        call_evidence,
        protocol_call_evidence,
        interner,
        source,
        module_path_mode,
        records: record_layouts,
        variants: variant_layouts,
        variant_source,
        function_sigs,
        function_requirements,
        function_raises,
        function_named_type_params,
        cleanup_edges,
        consume_sites,
        defer_plans,
    };
    let mut functions = Vec::new();
    let mut diagnostics = Vec::new();
    for f in &hir.functions {
        match lowering.lower_function(f) {
            Ok(nir_fn) => functions.push(nir_fn),
            Err(diag) => diagnostics.push(*diag),
        }
    }
    for e in &hir.extends {
        for m in &e.methods {
            match lowering.lower_function(m) {
                Ok(nir_fn) => functions.push(nir_fn),
                Err(diag) => diagnostics.push(*diag),
            }
        }
    }

    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }

    // `record_order`/`variant_order` were built by pushing each item's
    // id exactly once per item in `hir.records`/`hir.variants`, and the
    // identity validation above already rejected any duplicate id
    // within either kind -- so every id removed here is guaranteed to
    // still be present, exactly once. Returned as a diagnostic instead
    // of an `.expect()` panic anyway: this function's own atomicity
    // guarantee should never depend on a caller trusting that an
    // earlier check in this same function was never changed to miss a
    // case, the same defense-in-depth posture the rest of this module
    // already takes toward every other stage's guarantees.
    let mut records = Vec::with_capacity(record_order.len());
    for id in record_order {
        let Some(layout) = lowering.records.remove(&id) else {
            return Err(vec![*lowering.internal_error(&format!(
                "record layout for {id:?} was not built during lowering"
            ))]);
        };
        records.push((id, layout));
    }
    let mut variants = Vec::with_capacity(variant_order.len());
    for id in variant_order {
        let Some(layout) = lowering.variants.remove(&id) else {
            return Err(vec![*lowering.internal_error(&format!(
                "variant layout for {id:?} was not built during lowering"
            ))]);
        };
        variants.push((id, layout));
    }

    Ok(Module {
        functions,
        records,
        variants,
        protocols,
        extends,
    })
}

/// Which kind of module-level item an `ItemId` names, for a collision
/// diagnostic to describe accurately.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ItemKind {
    Record,
    Variant,
    Function,
    Protocol,
    Extend,
}

impl ItemKind {
    fn describe(self) -> &'static str {
        match self {
            ItemKind::Protocol => "protocol",
            ItemKind::Extend => "extend",
            ItemKind::Record => "record",
            ItemKind::Variant => "variant",
            ItemKind::Function => "function",
        }
    }
}

/// Checks that every record/variant/function's `ItemId` is unique
/// across the whole module -- not merely unique within its own kind.
/// Visits records, then variants, then functions, each in their own
/// declaration order (never a `HashMap`'s iteration order), so the
/// diagnostics this produces are identical across repeated runs.
fn validate_item_identities(
    hir: &HirModule,
    interner: &Interner,
    source: SourceId,
) -> Vec<Diagnostic> {
    let mut seen: HashMap<ItemId, ItemKind> = HashMap::new();
    let mut diagnostics = Vec::new();
    let mut check = |id: ItemId, kind: ItemKind, name: Symbol, span: Span| {
        let text = interner.resolve(name);
        match seen.get(&id) {
            Some(&existing) if existing == kind => {
                diagnostics.push(Diagnostic::error(
                    codes::INTERNAL_INVARIANT_VIOLATED,
                    source,
                    span,
                    format!(
                        "{} `{text}` reuses an id already used by another {} in this module",
                        kind.describe(),
                        kind.describe()
                    ),
                ));
            }
            Some(&existing) => {
                diagnostics.push(Diagnostic::error(
                    codes::INTERNAL_INVARIANT_VIOLATED,
                    source,
                    span,
                    format!(
                        "{} `{text}` reuses an id already used by a {} in this module",
                        kind.describe(),
                        existing.describe()
                    ),
                ));
            }
            None => {
                seen.insert(id, kind);
            }
        }
    };
    for r in &hir.records {
        check(r.id, ItemKind::Record, r.name, r.span);
    }
    for v in &hir.variants {
        check(v.id, ItemKind::Variant, v.name, v.span);
    }
    for f in &hir.functions {
        check(f.id, ItemKind::Function, f.name, f.name_span);
    }
    for p in &hir.protocols {
        check(p.id, ItemKind::Protocol, p.name, p.name_span);
    }
    for e in &hir.extends {
        // An extend has no name of its own; its own protocol's name is
        // used only for this diagnostic's own text, never as this
        // extend's identity. An extend whose protocol reference never
        // resolved (`hir::lower` already reported that separately) has
        // no name to borrow here, so its own id-collision check is
        // skipped rather than fabricating one.
        if let Some(protocol_name) = hir
            .protocols
            .iter()
            .find(|p| p.id == e.protocol)
            .map(|p| p.name)
        {
            check(e.id, ItemKind::Extend, protocol_name, e.span);
        }
        for m in &e.methods {
            check(m.id, ItemKind::Function, m.name, m.name_span);
        }
    }
    diagnostics
}

/// Converts a type reference already resolved by `hir::lower` against
/// its *declaring module's own* namespace (see [`crate::hir::HirType`])
/// into `Ty` -- an aggregate reference is already an exact `ItemId` by
/// this point, no lookup needed. Unlike typeck, an `Unresolved` name
/// that also isn't a primitive is never reachable in the ordinary
/// pipeline (typeck already rejected it with its own `T0006` diagnostic
/// before lowering ever ran), so falling back to `Ty::Error` here is
/// only ever exercised by a direct caller that bypasses that gate -- the
/// same defense-in-depth posture as the rest of this module.
fn resolve_named_type(interner: &Interner, ty: &crate::hir::HirType) -> Ty {
    resolve_named_type_at_depth(interner, ty, 0)
}

/// `depth` bounds recursion into nested `Ty::Applied` arguments the same
/// way every other stage that walks a type application does
/// (`crate::limits::MAX_GENERIC_DEPTH`) -- `nir::lower_module` is a
/// public entry point a direct caller can invoke with hand-built HIR
/// that bypasses `hir::lower`'s own depth guard (R0019) entirely, so
/// this cannot simply trust that earlier stage to have already bounded
/// the input.
fn resolve_named_type_at_depth(interner: &Interner, ty: &crate::hir::HirType, depth: usize) -> Ty {
    if depth > crate::limits::MAX_GENERIC_DEPTH {
        return Ty::Error;
    }
    match ty {
        crate::hir::HirType::Aggregate {
            item, name, args, ..
        } => {
            if args.is_empty() {
                Ty::Named(*item, *name)
            } else {
                // A generic declaration's own layout keeps its field/
                // payload/parameter types *symbolic* (one canonical
                // schema, never duplicated per instantiation, `rfcs/0008`)
                // -- but a reference *to* that declaration (a parameter
                // typed `Box[i64]`, say) is always a concrete application,
                // resolved recursively the same way `hir::lower`/`typeck`
                // already do.
                Ty::Applied(
                    *item,
                    args.iter()
                        .map(|a| resolve_named_type_at_depth(interner, a, depth + 1))
                        .collect(),
                )
            }
        }
        crate::hir::HirType::Param { id, name, .. } => Ty::Param(*id, *name),
        crate::hir::HirType::Unresolved { name, .. } => {
            let text = interner.resolve(*name);
            primitive_from_name(text).unwrap_or(Ty::Error)
        }
    }
}

/// Converts one HIR-level capability requirement (`rfcs/0009`) into its
/// canonical form, the same "read back what typeck already resolved,
/// never re-validate" discipline `resolve_named_type` follows -- typeck
/// already rejected an unknown protocol or wrong arity; this module
/// never runs at all for a program that didn't already pass that check
/// (`nir::lower`'s own module doc).
fn resolve_requirement(
    interner: &Interner,
    requirement: &crate::hir::HirCapabilityRequirement,
) -> crate::types::CapabilityRequirement {
    crate::types::CapabilityRequirement::new(
        requirement.protocol,
        requirement
            .arguments
            .iter()
            .map(|a| resolve_named_type(interner, a))
            .collect(),
    )
}

/// Canonicalizes a function's own raised-effect set (`rfcs/0010`) by
/// each variant's own *stable qualified identity* -- its declaring
/// module's own dotted path (`""` for single-file compilation, which
/// has no project-level module path at all, `rfcs/0007`) paired with
/// its own declared name -- never by raw `ItemId`, which is only ever
/// assigned in whatever order declarations/imports happened to be
/// discovered in, and can differ across two otherwise-identical
/// compilations that merely reorder those without changing what the
/// program means. Two variants sharing a bare name from *different*
/// modules are still correctly distinguished (their own module paths
/// differ); the only way an actual tie could survive is two items
/// genuinely sharing both a module and a name, which duplicate-
/// declaration checking already rejects independently -- `sort_by_key`
/// is stable, so even that unreachable case would just preserve the
/// (already-deterministic, source-declaration-order) input order rather
/// than fall back to `ItemId`. `Function.raises`'s own stored order is
/// what `lower_invoke` iterates to build each `Invoke`'s own
/// `err_targets`, so this is what actually keeps two semantically
/// identical programs' NIR (block/value numbering, not just the printed
/// signature) byte-identical under such reordering -- HIR's own
/// `raises` stays in source declaration order throughout (needed for
/// its own diagnostics' span-accurate reporting); only this NIR-facing
/// copy is canonicalized.
///
/// Every entry here was already resolved to a real declared variant by
/// `hir::lower`'s own `resolve_raises`, so a missing `variant_layouts`
/// entry is unreachable for any HIR it produced -- but this is a public
/// entry point (`lower_module`) a direct caller can invoke with
/// hand-built HIR bypassing that guarantee, so it fails atomically with
/// a structured diagnostic rather than silently sorting an unresolvable
/// entry as if it belonged first (or last).
/// Which module-path identity a lowering call is running under --
/// deciding *by the caller's own explicit choice*, never inferred from
/// whether a supplied table happens to be empty. `lower_module`'s own
/// wrapper always passes `SingleFile`; `lower_module_with_paths` always
/// passes `Project`, even when its own `module_path_of` table happens
/// to be empty (an empty table in `Project` mode means every lookup
/// inside it is a genuine metadata gap, not "no project" -- exactly the
/// distinction an `is_empty()` sentinel could never make).
#[derive(Clone, Copy)]
enum ModulePathMode<'a> {
    /// Single-file compilation has no project-level module path at all
    /// (`rfcs/0007`); every raised variant's own canonical module path
    /// is legitimately empty.
    SingleFile,
    /// Project compilation: every raised variant's own declaring
    /// `SourceId` must resolve to an entry in this table, built once,
    /// up front, with one entry per module actually in the project
    /// (`project::compile`). A miss is a genuine metadata gap, never a
    /// legitimate empty path.
    Project(&'a HashMap<SourceId, String>),
}

fn canonical_raises(
    mut raises: Vec<ItemId>,
    variant_layouts: &HashMap<ItemId, VariantLayout>,
    variant_source: &HashMap<ItemId, SourceId>,
    module_path_mode: ModulePathMode<'_>,
    interner: &Interner,
    source: SourceId,
) -> LowerResult<Vec<ItemId>> {
    let mut key_of: HashMap<ItemId, (String, String)> = HashMap::with_capacity(raises.len());
    for item in &raises {
        let Some(layout) = variant_layouts.get(item) else {
            return Err(Box::new(Diagnostic::error(
                codes::INTERNAL_INVARIANT_VIOLATED,
                source,
                Span::dummy(),
                format!(
                    "a function's own `raises` names id {item:?}, which does not resolve to any declared variant"
                ),
            )));
        };
        let module_path = match module_path_mode {
            ModulePathMode::SingleFile => String::new(),
            ModulePathMode::Project(module_path_of) => {
                let Some(&decl_source) = variant_source.get(item) else {
                    return Err(Box::new(Diagnostic::error(
                        codes::INTERNAL_INVARIANT_VIOLATED,
                        source,
                        Span::dummy(),
                        format!(
                            "a function's own `raises` names id {item:?}, whose declaring module could not be resolved"
                        ),
                    )));
                };
                let Some(path) = module_path_of.get(&decl_source) else {
                    return Err(Box::new(Diagnostic::error(
                        codes::INTERNAL_INVARIANT_VIOLATED,
                        source,
                        Span::dummy(),
                        format!(
                            "a function's own `raises` names id {item:?}, declared in a module this project's own module-path table has no entry for"
                        ),
                    )));
                };
                path.clone()
            }
        };
        let name = interner.resolve(layout.name).to_string();
        key_of.insert(*item, (module_path, name));
    }
    raises.sort_by(|a, b| key_of[a].cmp(&key_of[b]));
    Ok(raises)
}

struct Lowering<'a> {
    local_types: &'a HashMap<LocalId, Ty>,
    expr_types: &'a HashMap<ExprId, Ty>,
    pattern_case: &'a HashMap<PatternId, (ItemId, usize)>,
    /// Every generic call/construction's own concrete type arguments, as
    /// `typeck` resolved them, keyed by that expression's `ExprId`
    /// (`rfcs/0008`) -- read back here rather than re-inferred, the same
    /// "typeck already decided, lowering only reads it back" discipline
    /// `expr_types`/`local_types` already follow.
    call_type_args: &'a HashMap<ExprId, Vec<Ty>>,
    /// Every call's own resolved capability evidence (`rfcs/0009`), one
    /// entry per requirement the callee declares, in that same order --
    /// read back here, never re-resolved (mirrors `call_type_args`).
    call_evidence: &'a HashMap<ExprId, Vec<Evidence>>,
    /// Every explicit protocol-call expression's own resolved evidence,
    /// keyed by that call's own `ExprId` (`rfcs/0009`).
    protocol_call_evidence: &'a HashMap<ExprId, Evidence>,
    interner: &'a Interner,
    source: SourceId,
    /// Whether this lowering is single-file or project-mode, and (in
    /// project mode) every declaring module's own dotted path by
    /// `SourceId` -- read back by `canonical_raises` so two variants
    /// sharing a bare name from different modules still canonicalize to
    /// a stable order (`rfcs/0007`, `rfcs/0010`).
    module_path_mode: ModulePathMode<'a>,
    records: HashMap<ItemId, RecordLayout>,
    variants: HashMap<ItemId, VariantLayout>,
    /// Every declared variant's own declaring `SourceId`, by `ItemId` --
    /// read back by `canonical_raises` (together with `module_path_mode`)
    /// to resolve each raised variant's own stable qualified identity.
    variant_source: HashMap<ItemId, SourceId>,
    /// `(this function's own generic parameters, its param types, its
    /// return type)`. The parameter/return types may reference the
    /// first element via `Ty::Param`; a call site substitutes its own
    /// `call_type_args` for them (`rfcs/0008`).
    function_sigs: HashMap<ItemId, (Vec<crate::hir::TypeParamId>, Vec<Ty>, Ty)>,
    /// Every function/extend method's own capability requirements
    /// (`rfcs/0009`), in declared order -- a `Call` targeting one of
    /// these carries exactly this many evidence entries.
    function_requirements: HashMap<ItemId, Vec<CapabilityRequirement>>,
    /// Every function/extend method's own declared raised-error set
    /// (`rfcs/0010`), canonical and in a fixed order -- read back by
    /// `lower_invoke` to decide postfix `?`/`handle`'s own `Invoke`
    /// failure edges, one per entry here, without re-deriving it from
    /// whichever `Function` this callee eventually lowers to (which may
    /// not even exist yet, since lowering order is not the same as
    /// declaration order for extend methods).
    function_raises: HashMap<ItemId, Vec<ItemId>>,
    /// An extend method's own *displayed* generic parameters -- always
    /// its owning extend's own `type_params` (never empty the way its
    /// own `HirFunction::type_params` is), keyed by the method's own
    /// `ItemId`. Absent (falls back to `f.type_params` directly) for an
    /// ordinary function, which owns its parameters itself.
    function_named_type_params: HashMap<ItemId, Vec<(crate::hir::TypeParamId, Symbol)>>,
    /// `resourceck`'s own authoritative, checked cleanup plan
    /// (`rfcs/0011`), keyed by the exiting HIR node's own stable id --
    /// the single source of truth for which locals still need
    /// destroying and which `defer`s still need running at any given
    /// reachable exit. Lowering never independently decides this itself
    /// (no `moved_out`/per-branch join bookkeeping of its own): it
    /// looks the already-checked answer up here and simply materializes
    /// it as real instructions, in the order given.
    cleanup_edges: &'a BTreeMap<ExprId, Vec<crate::resourceck::CleanupAction>>,
    /// `resourceck`'s own authoritative observe-vs-transfer decision
    /// for every resource-typed expression it checked (`rfcs/0011`),
    /// keyed by that exact expression's own `ExprId` -- a binding's own
    /// initializer, an assignment's own value, or a call/`Invoke`
    /// argument. Lowering reads this back directly (`lookup_consume`)
    /// rather than re-deriving the same verdict from the expression's
    /// own HIR shape or a callee's declared `take` flags a second time.
    consume_sites: &'a BTreeMap<ExprId, crate::resourceck::ConsumeInfo>,
    /// `resourceck`'s own checked plan for every `defer` statement
    /// (`rfcs/0011`), keyed by that exact call expression's own
    /// `ExprId` -- see `resourceck::CheckedDeferPlan`.
    defer_plans: &'a BTreeMap<ExprId, crate::resourceck::CheckedDeferPlan>,
}

#[derive(Copy, Clone)]
struct LoopCtx {
    break_target: BlockId,
    continue_target: BlockId,
}

struct PendingBlock {
    id: BlockId,
    instructions: Vec<crate::nir::Instruction>,
    terminator: Option<Terminator>,
}

/// How a resolved local is represented in NIR. A local that is never
/// reassigned (every parameter; a `value` binding) is just the `ValueId`
/// that first produced it — referencing it needs no `load` at all. Only
/// a `mutable` binding gets a real storage slot (an `alloc`), since only
/// it can ever need a `store` after its initializer.
#[derive(Copy, Clone, Debug)]
enum LocalBinding {
    Direct(ValueId),
    Slot(ValueId),
}

/// A deferred call's own callee/arguments, already lowered (evaluated
/// once, at the `defer` statement itself, per `rfcs/0011`) and replayed
/// as an ordinary `Call` at every cleanup point this function currently
/// supports (normal fallthrough, and an explicit `return` in the same
/// function-level scope -- see `ResourceScope`'s own doc comment for
/// this milestone's honest scope limits).
#[derive(Clone)]
struct PendingDefer {
    callee: ItemId,
    type_args: Vec<Ty>,
    args: Vec<ValueId>,
    evidence: Vec<Evidence>,
    /// The deferred callee's own declared return type (Blocker 6) --
    /// never `Ty::Unit` fabricated regardless of what the callee
    /// actually returns: the replayed `Call` at cleanup time must
    /// carry the same real result type an ordinary call to the same
    /// function would, even though that result is always discarded
    /// (a resource-returning callee is rejected outright at `defer`
    /// registration, so this is never itself an affine type here).
    ret_ty: Ty,
}

/// The result of lowering one expression: either a real value the
/// current (still-open) block can keep building on, or proof that
/// control already left this block. `return`/`break`/`continue` lower
/// straight to a real NIR terminator rather than a synthetic "unit"
/// instruction, so once one of them fires there is no value left to
/// store, pass as an operand, or branch on -- every caller that
/// receives `Diverged` must stop emitting into the current block and
/// propagate `Diverged` upward immediately, instead of inventing a
/// placeholder value to keep going. This is what makes "no instruction
/// is ever appended after a block's terminator" a property the type
/// system enforces, rather than something callers have to remember to
/// check with `current_terminated()`.
#[derive(Copy, Clone, Debug, PartialEq)]
enum LoweredExpr {
    Value(ValueId),
    Diverged,
}

/// Where a `match` decision tree's own winning arm hands its value off,
/// once decided (`rfcs/0011`, Blocker 2): merged into a shared slot for
/// the construct's own ordinary value (`Merge`, exactly like before),
/// or forwarded straight to an enclosing `return`'s own per-branch
/// sink (`Return`), exactly like `Lowering::lower_into_return_sink`
/// already does for a nested `if`. Wrapped in `Option` by every caller
/// (never a bare `ArmSink`) the same way `merge: Option<(ValueId,
/// BlockId)>` already was: `None` means every arm diverges on its own
/// (`Ty::Never`), so there is no value for any arm to hand off to
/// anything at all.
enum ArmSink<'a, 'f> {
    Merge(ValueId, BlockId),
    Return(
        Ty,
        &'f mut dyn FnMut(&mut Lowering<'a>, &mut FnBuilder, ValueId) -> LowerResult<LoweredExpr>,
    ),
}

impl<'a> ArmSink<'a, '_> {
    /// Produces a fresh, independently-usable `ArmSink` referring to
    /// the same underlying slot/sink -- required at every recursive
    /// decision-tree call site that itself sits inside a loop over
    /// several sibling cases (`lower_bool_switch`'s two arms,
    /// `lower_variant_switch`'s cases, `lower_literal_chain`'s then/
    /// else split): `Merge` is trivially `Copy`, but `Return`'s own
    /// `&mut dyn FnMut` is not, so it must be explicitly reborrowed
    /// (exactly like `Lowering::lower_into_return_sink`'s own `&mut
    /// *finish` reborrows already do) rather than moved once and
    /// exhausted after the first sibling.
    fn reborrow(&mut self) -> ArmSink<'a, '_> {
        match self {
            ArmSink::Merge(slot, after) => ArmSink::Merge(*slot, *after),
            ArmSink::Return(hint, finish) => ArmSink::Return(hint.clone(), &mut **finish),
        }
    }
}

/// Per-function mutable lowering state: value numbering, the
/// in-progress block list, and the active loop's break/continue targets.
struct FnBuilder {
    next_value: u32,
    local_bindings: HashMap<LocalId, LocalBinding>,
    blocks: Vec<PendingBlock>,
    current: BlockId,
    loop_stack: Vec<LoopCtx>,
    /// The enclosing function's declared return type, used to hint a
    /// bare literal in `return <literal>` to the right type instead of
    /// the usual i64/f64 default.
    return_ty: Ty,
    /// Every `defer` statement's own already-lowered callee/arguments,
    /// keyed by that exact statement's own callee-expression id
    /// (`rfcs/0011`) -- populated once, when lowering first reaches
    /// that `defer` statement itself, and read back (never re-lowered)
    /// every time a checked cleanup action from `resourceck`'s own
    /// `ResourceCheckResult::cleanup_edges` replays it. Argument
    /// evaluation happens exactly once, here, at registration time,
    /// matching `defer`'s own "never delays argument evaluation, only
    /// the call's own side effect" rule.
    defer_calls: HashMap<ExprId, PendingDefer>,
}

impl FnBuilder {
    fn new(return_ty: Ty) -> Self {
        let entry = BlockId(0);
        FnBuilder {
            next_value: 0,
            local_bindings: HashMap::new(),
            blocks: vec![PendingBlock {
                id: entry,
                instructions: Vec::new(),
                terminator: None,
            }],
            current: entry,
            loop_stack: Vec::new(),
            return_ty,
            defer_calls: HashMap::new(),
        }
    }

    fn fresh_value(&mut self) -> ValueId {
        let id = ValueId(self.next_value);
        self.next_value += 1;
        id
    }

    fn alloc_slot(&mut self, ty: Ty) -> ValueId {
        self.push_value(ty, ValueKind::Alloc)
    }

    fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(PendingBlock {
            id,
            instructions: Vec::new(),
            terminator: None,
        });
        id
    }

    fn switch_to(&mut self, id: BlockId) {
        self.current = id;
    }

    fn current_block_mut(&mut self) -> &mut PendingBlock {
        let idx = self.current.0 as usize;
        &mut self.blocks[idx]
    }

    fn current_terminated(&self) -> bool {
        self.blocks[self.current.0 as usize].terminator.is_some()
    }

    fn push_value(&mut self, ty: Ty, kind: ValueKind) -> ValueId {
        debug_assert!(
            !self.current_terminated(),
            "internal invariant: appended a value to block {:?} after it was already terminated",
            self.current
        );
        let result = self.fresh_value();
        self.current_block_mut()
            .instructions
            .push(crate::nir::Instruction::Value { result, ty, kind });
        result
    }

    fn push_store(&mut self, slot: ValueId, value: ValueId, mode: crate::nir::OwnershipMode) {
        debug_assert!(
            !self.current_terminated(),
            "internal invariant: appended a store to block {:?} after it was already terminated",
            self.current
        );
        self.current_block_mut()
            .instructions
            .push(crate::nir::Instruction::Store { slot, value, mode });
    }

    /// Appends any non-value-producing instruction (currently only
    /// `Instruction::Drop`, `rfcs/0011`) to the current block.
    fn push_instruction(&mut self, instruction: crate::nir::Instruction) {
        debug_assert!(
            !self.current_terminated(),
            "internal invariant: appended an instruction to block {:?} after it was already terminated",
            self.current
        );
        self.current_block_mut().instructions.push(instruction);
    }

    /// Sets the current block's terminator. This is the one place a
    /// block transitions from "still being built" to "closed" --
    /// `push_value`/`push_store` refuse (in debug builds) to append
    /// anything to a block afterward, so every lowering path must emit
    /// all of a block's instructions before calling this, never after.
    fn terminate(&mut self, term: Terminator) {
        debug_assert!(
            !self.current_terminated(),
            "internal invariant: block {:?} was terminated twice",
            self.current
        );
        self.current_block_mut().terminator = Some(term);
    }

    /// Converts every block built so far into its finished form, or
    /// reports the id of the first block still missing a terminator.
    /// Every code path that creates a block is responsible for either
    /// terminating it or (for `while`'s lazily-created loop-body/exit
    /// blocks) never creating it in the first place -- if that
    /// invariant is ever violated despite that, this is where it is
    /// caught, as a `Result` a caller with real source context can turn
    /// into a diagnostic, not a panic on arbitrary user input.
    fn finish_blocks(self) -> Result<Vec<BasicBlock>, BlockId> {
        self.blocks
            .into_iter()
            .map(|b| match b.terminator {
                Some(terminator) => Ok(BasicBlock {
                    id: b.id,
                    instructions: b.instructions,
                    terminator,
                }),
                None => Err(b.id),
            })
            .collect()
    }
}

impl<'a> Lowering<'a> {
    fn lower_function(&mut self, f: &HirFunction) -> LowerResult<Function> {
        let return_type = f
            .return_type
            .as_ref()
            .map(|t| self.resolve_named_type(t))
            .unwrap_or(Ty::Unit);
        let mut fb = FnBuilder::new(return_type.clone());
        let mut params = Vec::new();
        for p in &f.params {
            let Some(ty) = self.local_types.get(&p.local).cloned() else {
                return Err(self.internal_error(&format!(
                    "parameter {:?} has no type recorded by typeck",
                    p.local
                )));
            };
            let value = fb.fresh_value();
            fb.local_bindings
                .insert(p.local, LocalBinding::Direct(value));
            params.push(Param {
                value,
                ty,
                take: p.take,
            });
        }

        // The function's own implicit tail return is lowered through
        // the same per-branch sink [`Self::lower_into_return_sink`]
        // explicit `return` uses (Blocker 2) -- a resource-typed
        // compound tail (`if cond { left } else { right }`, with no
        // explicit `return` at all) needs exactly the same per-branch
        // cleanup+terminate, not a single post-merge guess.
        let return_type_for_tail = return_type.clone();
        let mut finish_tail = |this: &mut Self, fb: &mut FnBuilder, v: ValueId| {
            if matches!(return_type_for_tail, Ty::Unit) {
                fb.terminate(Terminator::Return(None));
            } else {
                let v = this.move_if_transferred(fb, v, &return_type_for_tail, true);
                fb.terminate(Terminator::Return(Some(v)));
            }
            Ok(LoweredExpr::Diverged)
        };
        if self.is_affine(&return_type) {
            self.lower_into_return_sink_block(&mut fb, &f.body, &return_type, &mut finish_tail)?;
        } else {
            let body_result = self.lower_block_value(&mut fb, &f.body)?;
            if !fb.current_terminated() {
                // `Diverged` always means the block that produced it is
                // already terminated (see `LoweredExpr`), so reaching
                // here means the body itself did produce a real value.
                let LoweredExpr::Value(body_value) = body_result else {
                    unreachable!(
                        "internal invariant: a Diverged result always already terminated its block"
                    );
                };
                self.emit_checked_cleanup(&mut fb, f.body.id)?;
                finish_tail(self, &mut fb, body_value)?;
            }
        }

        let blocks = fb.finish_blocks().map_err(|block_id| {
            Box::new(Diagnostic::error(
                codes::INTERNAL_INVARIANT_VIOLATED,
                self.source,
                f.name_span,
                format!(
                    "internal error lowering `{}`: block bb{} was never given a terminator",
                    self.interner.resolve(f.name),
                    block_id.0
                ),
            ))
        })?;

        // An extend method's own `f.type_params` is always empty (see
        // `HirFunction::type_params`'s own doc comment): its real
        // generic parameters are its *owning extend's* own, looked up
        // here by name rather than assumed empty, so a conditional
        // extend's NIR function still carries its own `[T]` correctly.
        let type_params = self
            .function_named_type_params
            .get(&f.id)
            .cloned()
            .unwrap_or_else(|| f.type_params.iter().map(|p| (p.id, p.name)).collect());
        let requirements = self
            .function_requirements
            .get(&f.id)
            .cloned()
            .unwrap_or_default();
        let raises = canonical_raises(
            f.raises.iter().map(|r| r.variant).collect(),
            &self.variants,
            &self.variant_source,
            self.module_path_mode,
            self.interner,
            self.source,
        )?;
        Ok(Function {
            id: f.id,
            name: f.name,
            type_params,
            requirements,
            params,
            return_type,
            raises,
            blocks,
        })
    }

    fn resolve_named_type(&self, ty: &crate::hir::HirType) -> Ty {
        resolve_named_type(self.interner, ty)
    }

    // ---- reading typeck's already-resolved types ----
    //
    // Lowering never re-derives or approximates a type: typeck recorded
    // the final, resolved type of every expression and block it visited
    // (`expr_types`), so picking the right instruction (e.g. `add.i64`
    // vs `add.f64`) is always a lookup by the node's own `ExprId`, never
    // a re-inference.

    fn expr_ty(&self, expr: &HirExpr) -> LowerResult<Ty> {
        self.expr_types.get(&expr.id()).cloned().ok_or_else(|| {
            self.internal_error(&format!(
                "expression {:?} has no type recorded by typeck",
                expr.id()
            ))
        })
    }

    /// Builds the diagnostic for a construct that reached lowering
    /// without the checker having already rejected it -- see
    /// `codes::UNSUPPORTED_IN_NIR`.
    fn unsupported(&self, span: Span, feature: &str) -> Box<Diagnostic> {
        Box::new(Diagnostic::error(
            codes::UNSUPPORTED_IN_NIR,
            self.source,
            span,
            format!("{feature} cannot be lowered to NIR"),
        ))
    }

    // ---- statement/block lowering ----

    fn lower_block_void(&mut self, fb: &mut FnBuilder, block: &HirBlock) -> LowerResult<()> {
        for stmt in &block.statements {
            self.lower_stmt(fb, stmt)?;
            if fb.current_terminated() {
                return Ok(());
            }
        }
        if let Some(tail) = &block.tail {
            self.lower_expr(fb, tail)?;
        }
        Ok(())
    }

    fn lower_block_value(
        &mut self,
        fb: &mut FnBuilder,
        block: &HirBlock,
    ) -> LowerResult<LoweredExpr> {
        for stmt in &block.statements {
            self.lower_stmt(fb, stmt)?;
            if fb.current_terminated() {
                // A statement already diverged the block; there is
                // nothing left to lower and nowhere left to put another
                // instruction.
                return Ok(LoweredExpr::Diverged);
            }
        }
        match &block.tail {
            Some(tail) => self.lower_expr(fb, tail),
            None => Ok(LoweredExpr::Value(
                fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)),
            )),
        }
    }

    fn lower_stmt(&mut self, fb: &mut FnBuilder, stmt: &HirStmt) -> LowerResult<()> {
        match stmt {
            HirStmt::Binding(b) => {
                let Some(ty) = self.local_types.get(&b.local).cloned() else {
                    return Err(self.internal_error(&format!(
                        "binding {:?} has no type recorded by typeck",
                        b.local
                    )));
                };
                let value = match self.lower_expr_hinted(fb, &b.value, &ty)? {
                    LoweredExpr::Value(v) => v,
                    // The initializer itself diverged (e.g. `value x =
                    // return 1;`): the binding is never actually
                    // created, and the block is already terminated, so
                    // there is nothing left to allocate or store into.
                    LoweredExpr::Diverged => return Ok(()),
                };
                let binding = if b.mutable {
                    let slot = fb.alloc_slot(ty.clone());
                    // A `value`/`mutable` binding's own initializer is
                    // always checked with `ConsumeKind::Other`
                    // (`resourceck::flow::check_binding`) -- never a
                    // mere observation -- so a resource-typed one always
                    // transfers ownership into this fresh slot. Read
                    // back from `resourceck`'s own checked decision
                    // directly, rather than re-derived from `ty` alone.
                    let transfers =
                        self.lookup_consume_mode(b.value.id(), &ty, "a binding initializer")?;
                    let mode = if transfers {
                        crate::nir::OwnershipMode::Transfer
                    } else {
                        crate::nir::OwnershipMode::Observe
                    };
                    fb.push_store(slot, value, mode);
                    LocalBinding::Slot(slot)
                } else if matches!(b.value, HirExpr::Local { .. })
                    && self.lookup_consume_mode(b.value.id(), &ty, "a binding initializer")?
                {
                    // Rebinding a resource directly from another
                    // already-owned local (`value b = a;`) transfers
                    // ownership explicitly, even with no slot involved:
                    // `a`'s own prior identity must not remain
                    // independently usable after this point.
                    let moved = fb.push_value(ty.clone(), ValueKind::Move { source: value });
                    LocalBinding::Direct(moved)
                } else {
                    LocalBinding::Direct(value)
                };
                fb.local_bindings.insert(b.local, binding);
                Ok(())
            }
            HirStmt::Expr(e) => {
                self.lower_expr(fb, e)?;
                Ok(())
            }
            HirStmt::Defer { expr, span } => {
                let Some(pending) = self.lower_defer_call(fb, expr, *span)? else {
                    return Ok(());
                };
                fb.defer_calls.insert(expr.id(), pending);
                Ok(())
            }
            HirStmt::Drop { expr, .. } => {
                // A bare local reference naming an owned, possibly
                // *partially*-moved aggregate (`rfcs/0012`) has its own
                // checked structural cleanup plan recorded directly
                // under this exact operand's own `ExprId` (`resourceck::
                // flow::FlowChecker::check_drop` -- reusing
                // `cleanup_edges`'s own existing shape, since an
                // explicit `drop` is its own one-off exit): replaying it
                // destroys exactly the still-live descendants
                // `structural_drop_targets` already proved remain, in
                // their own correct reverse-declaration order, followed
                // by the aggregate's own outer identity last if it is
                // itself a declared `resource` -- never a single naive
                // whole-value `Drop`, which would silently leak every
                // field already-moved-out has NOT already accounted
                // for. Any other resource-typed expression (e.g.
                // dropping a freshly-constructed value with no binding
                // at all, which `check_drop` never records a plan for)
                // falls back to the original direct lowering: evaluated
                // and destroyed the same way, just with no local to
                // update bookkeeping for.
                if self.cleanup_edges.contains_key(&expr.id()) {
                    return self.emit_checked_cleanup(fb, expr.id());
                }
                let value = match self.lower_expr(fb, expr)? {
                    LoweredExpr::Value(v) => v,
                    LoweredExpr::Diverged => return Ok(()),
                };
                fb.push_instruction(crate::nir::Instruction::Drop { value });
                Ok(())
            }
            HirStmt::While {
                condition, body, ..
            } => self.lower_while(fb, condition, body),
            HirStmt::Loop { body, .. } => self.lower_loop(fb, body),
        }
    }

    /// `true` iff `ty` is transitively affine (`rfcs/0012`): a declared
    /// `resource` itself, or a record/variant/resource reachably
    /// containing one -- independently recomputed from this stage's own
    /// `records`/`variants` layouts, mirroring `resourceck`'s identical
    /// query (`resourceck::is_affine_item`/`is_affine_ty`) rather than
    /// trusting its verdict passed through unchecked, exactly like every
    /// other fact `nir::lower` re-derives from checked metadata instead
    /// of assuming. Guarded against a genuinely cyclic declaration
    /// (already independently rejected elsewhere as an infinite-size
    /// layout) the same way both of those do: a cycle back-edge
    /// contributes `false` to *that one* occurrence's own disjunction,
    /// never cached (this stage does not memoize at all, unlike
    /// `resourceck`'s own per-module query, since it is not called
    /// densely enough per module to need to).
    fn is_affine(&self, ty: &Ty) -> bool {
        self.is_affine_visiting(ty, &mut HashSet::new())
    }

    fn is_affine_visiting(&self, ty: &Ty, visiting: &mut HashSet<ItemId>) -> bool {
        let field_types = |item: &ItemId| -> Vec<Ty> {
            if let Some(record) = self.records.get(item) {
                record.fields.iter().map(|(_, t)| t.clone()).collect()
            } else if let Some(variant) = self.variants.get(item) {
                variant
                    .cases
                    .iter()
                    .flat_map(|c| c.payload.clone())
                    .collect()
            } else {
                Vec::new()
            }
        };
        match ty {
            Ty::Named(item, _) => {
                if self.records.get(item).is_some_and(|r| r.affine) {
                    return true;
                }
                if !visiting.insert(*item) {
                    return false;
                }
                let result = field_types(item)
                    .iter()
                    .any(|fty| self.is_affine_visiting(fty, visiting));
                visiting.remove(item);
                result
            }
            Ty::Applied(item, args) => {
                if self.records.get(item).is_some_and(|r| r.affine) {
                    return true;
                }
                if !visiting.insert(*item) {
                    return false;
                }
                let type_params: Option<Vec<TypeParamId>> = self
                    .records
                    .get(item)
                    .map(|r| r.type_params.iter().map(|(id, _)| *id).collect())
                    .or_else(|| {
                        self.variants
                            .get(item)
                            .map(|v| v.type_params.iter().map(|(id, _)| *id).collect())
                    });
                // Missing or arity-disagreeing generic metadata is
                // never an *empty* substitution: an unsubstituted
                // `Ty::Param` answers `false` here, which would let a
                // genuinely affine instantiation be lowered as a
                // freely-copyable value. Fail closed instead -- treat
                // it as affine, so the ownership machinery demands an
                // explicit owner and the mismatch surfaces as a
                // structured diagnostic rather than a silent leak.
                let Some(type_params) = type_params.filter(|p| p.len() == args.len()) else {
                    visiting.remove(item);
                    return true;
                };
                let subst: HashMap<TypeParamId, Ty> =
                    type_params.into_iter().zip(args.iter().cloned()).collect();
                let result = field_types(item).iter().any(|fty| {
                    self.is_affine_visiting(&crate::types::substitute(fty, &subst), visiting)
                });
                visiting.remove(item);
                result
            }
            _ => false,
        }
    }

    /// Mirrors `resourceck::flow::FlowChecker::resolve_place`: `expr`
    /// resolves to a stable structural place iff it is a bare local, or
    /// a `Field` access chain rooted in one through nothing but further
    /// `Field` accesses -- exactly the condition `resourceck` already
    /// used to decide whether to track this exact access as a place at
    /// all. Field indices are independently re-derived here by name,
    /// exactly like `lower_field`'s own non-affine path already does,
    /// rather than trusting a second parallel resolution passed through
    /// unchecked.
    fn resolve_place_expr(&mut self, expr: &HirExpr) -> LowerResult<Option<Place<LocalId>>> {
        match expr {
            HirExpr::Local { local, .. } => Ok(Some(Place::root(*local))),
            HirExpr::Field { base, name, .. } => {
                let Some(base_place) = self.resolve_place_expr(base)? else {
                    return Ok(None);
                };
                let base_ty = self.expr_ty(base)?;
                let record = match base_ty {
                    Ty::Named(record, _) | Ty::Applied(record, _) => record,
                    _ => {
                        return Err(
                            self.unsupported(base.span(), "field access on a non-record type")
                        );
                    }
                };
                let field_index = self
                    .records
                    .get(&record)
                    .and_then(|r| r.fields.iter().position(|(n, _)| *n == *name))
                    .ok_or_else(|| {
                        self.unsupported(expr.span(), "field access on an unknown field")
                    })?;
                Ok(Some(base_place.field(record, FieldId(field_index as u32))))
            }
            _ => Ok(None),
        }
    }

    /// Resolves a HIR-rooted structural place (`resourceck::flow`'s own
    /// [`Place<LocalId>`]) to its NIR counterpart -- rooted at that
    /// local's own *current* SSA value -- and the place's own resolved
    /// type, by loading the root and walking each projection step
    /// against `self.records` (the same stable field identity
    /// `resourceck` already validated, independently revalidated here
    /// rather than trusted blindly). `Projection` itself carries no root
    /// type parameter at all (only [`Place`] does), so the projection
    /// list is reused unchanged -- never rebuilt field by field.
    fn resolve_nir_place(
        &mut self,
        fb: &mut FnBuilder,
        place: &Place<LocalId>,
    ) -> LowerResult<(Place<ValueId>, Ty)> {
        let Some(binding) = fb.local_bindings.get(&place.root).copied() else {
            return Err(self.internal_error(&format!(
                "a checked place names local {:?}, which this frame never bound",
                place.root
            )));
        };
        let root_value = self.load_current(fb, place.root, binding)?;
        let Some(mut ty) = self.local_types.get(&place.root).cloned() else {
            return Err(self.internal_error(&format!(
                "local {:?} has no type recorded by typeck",
                place.root
            )));
        };
        for projection in &place.projections {
            let Projection::Field { owner, field } = projection else {
                return Err(self.internal_error(
                    "a checked place projects through a variant field, which this milestone's \
                     structural places never produce",
                ));
            };
            // A generic aggregate's own declared field type is still
            // symbolic (`Ty::Param`) -- substituted here with whatever
            // arguments *this* place's own current type carries, so the
            // NIR instruction this place feeds is typed `File`, not a
            // bare `T` that escapes its own declaration (`rfcs/0008`).
            let args: Vec<Ty> = match &ty {
                Ty::Named(item, _) if item == owner => Vec::new(),
                Ty::Applied(item, args) if item == owner => args.clone(),
                other => {
                    return Err(self.internal_error(&format!(
                        "a checked place projects a field of {owner:?} through a value of a \
                         different type ({other:?})"
                    )));
                }
            };
            let Some(record) = self.records.get(owner) else {
                return Err(self.internal_error(&format!(
                    "a checked place projects through unknown record {owner:?}"
                )));
            };
            let Some((_, field_ty)) = record.fields.get(field.0 as usize) else {
                return Err(self.internal_error(&format!(
                    "a checked place projects field {field:?}, out of range for record {owner:?}"
                )));
            };
            if record.type_params.len() != args.len() {
                return Err(self.internal_error(&format!(
                    "a checked place projects through {owner:?}, which declares {} type \
                     parameter(s) but is applied to {} type argument(s)",
                    record.type_params.len(),
                    args.len()
                )));
            }
            let subst: HashMap<crate::hir::TypeParamId, Ty> = record
                .type_params
                .iter()
                .map(|(id, _)| *id)
                .zip(args)
                .collect();
            ty = crate::types::substitute(field_ty, &subst);
        }
        Ok((
            Place {
                root: root_value,
                projections: place.projections.clone(),
            },
            ty,
        ))
    }

    /// `resourceck`'s own checked observe-vs-transfer decision for a
    /// field-read expression's own id (`rfcs/0012`) -- unlike
    /// [`Self::lookup_consume_mode`] (for a position that is *always* a
    /// consuming one), a field read's own position is only sometimes
    /// consuming: `resourceck` records nothing at all for a pure
    /// observation (there is no ownership decision to make), so a
    /// missing entry here means `Observe`, not a structural mismatch.
    fn field_read_mode(&self, id: ExprId) -> crate::nir::OwnershipMode {
        match self.consume_sites.get(&id) {
            Some(crate::resourceck::ConsumeInfo::Transfer) => crate::nir::OwnershipMode::Transfer,
            _ => crate::nir::OwnershipMode::Observe,
        }
    }

    /// The current NIR value behind `local`'s own binding: its value
    /// directly, or (for a `mutable` binding) a fresh `Load` of its
    /// slot, typed from `self.local_types` exactly like an ordinary
    /// `HirExpr::Local` read already is.
    fn load_current(
        &self,
        fb: &mut FnBuilder,
        local: LocalId,
        binding: LocalBinding,
    ) -> LowerResult<ValueId> {
        match binding {
            LocalBinding::Direct(value) => Ok(value),
            LocalBinding::Slot(slot) => {
                let Some(ty) = self.local_types.get(&local).cloned() else {
                    return Err(self.internal_error(&format!(
                        "local {local:?} has a bound slot but no recorded type"
                    )));
                };
                Ok(fb.push_value(ty, ValueKind::Load(slot)))
            }
        }
    }

    /// Lowers a `defer`'s own call expression's callee/arguments *now*
    /// (`rfcs/0011`: a `defer` never delays argument evaluation, only
    /// the call's own side effect), without emitting the call itself --
    /// returns the pieces needed to replay it later, at each cleanup
    /// point. `None` (with an internal-error diagnostic) for anything
    /// this milestone's own scoped-down `defer` support does not cover:
    /// a callee that isn't a plain, non-generic, capability-free
    /// function reference.
    fn lower_defer_call(
        &mut self,
        fb: &mut FnBuilder,
        expr: &HirExpr,
        span: Span,
    ) -> LowerResult<Option<PendingDefer>> {
        let HirExpr::Call { callee, args, .. } = expr else {
            return Err(self.unsupported(span, "a `defer` whose expression is not a direct call"));
        };
        let HirExpr::Function { item, .. } = callee.as_ref() else {
            return Err(self.unsupported(
                span,
                "a `defer` whose callee is not a plain function reference",
            ));
        };
        let (type_params, param_tys, ret_ty) = self.lookup_function_sig(*item, "a `defer` call")?;
        if !type_params.is_empty() {
            return Err(self.unsupported(span, "a `defer` calling a generic function"));
        }
        // Cleanup-time failure semantics (what happens to a `raise`
        // reaching the *enclosing* function's own cleanup point, which
        // may already be mid-way through unwinding for a different
        // reason) are not implemented this milestone (Blocker 6) --
        // rejected outright here rather than silently dropping the
        // raised effect or miscompiling it.
        let raises = self.lookup_function_raises(*item, "a `defer` call")?;
        if !raises.is_empty() {
            return Err(self.unsupported(span, "a `defer` calling a fallible function"));
        }
        // A deferred call whose own result is itself a resource would
        // need a new owner lined up for it at cleanup time, which this
        // milestone has no mechanism for at all (Blocker 6) -- rejected
        // outright rather than silently leaking (or double-owning) it.
        if self.is_affine(&ret_ty) {
            return Err(self.unsupported(span, "a `defer` calling a function returning a resource"));
        }
        // `resourceck::flow::check_defer` already recorded exactly this
        // shape's own checked plan (`rfcs/0011`) -- the same per-
        // argument observe/transfer verdict `check_expr_ctx`'s own
        // `HirExpr::Call` handling decided, running this call through
        // the same move-checking any other call gets. A structural
        // mismatch here (this exact shape reached lowering, but
        // resourceck recorded no plan for it) is a bug in one stage or
        // the other, never silently treated as "observe everything".
        let plan = self.defer_plans.get(&expr.id()).cloned().ok_or_else(|| {
            self.internal_error(&format!(
                "a `defer` calling {item:?} has no checked argument plan recorded by resourceck"
            ))
        })?;
        // The plan's own shape must independently agree with what this
        // stage resolves on its own, in every dimension -- a plan that
        // merely exists is not enough (`rfcs/0011`): the wrong callee,
        // the wrong argument/return type count, or a return type
        // disagreement all mean the two stages disagree about this
        // exact `defer`, which is never silently trusted just because a
        // plan happens to be present.
        if plan.callee != *item {
            return Err(self.internal_error(&format!(
                "a `defer` calling {item:?} has a checked plan naming a different callee ({:?})",
                plan.callee
            )));
        }
        if plan.arg_modes.len() != args.len() {
            return Err(self.internal_error(&format!(
                "a `defer` calling {item:?} has {} checked argument mode(s) but {} argument(s)",
                plan.arg_modes.len(),
                args.len()
            )));
        }
        if plan.arg_types.len() != args.len() {
            return Err(self.internal_error(&format!(
                "a `defer` calling {item:?} has {} checked argument type(s) but {} argument(s)",
                plan.arg_types.len(),
                args.len()
            )));
        }
        if plan.arg_places.len() != args.len() {
            return Err(self.internal_error(&format!(
                "a `defer` calling {item:?} has {} checked argument place(s) but {} argument(s)",
                plan.arg_places.len(),
                args.len()
            )));
        }
        if param_tys.len() != args.len() {
            return Err(self.internal_error(&format!(
                "a `defer` calling {item:?} declares {} parameter(s) but is called with {} argument(s)",
                param_tys.len(),
                args.len()
            )));
        }
        if plan.return_type != ret_ty {
            return Err(self.internal_error(&format!(
                "a `defer` calling {item:?} has a checked return type that disagrees with its own resolved signature"
            )));
        }
        let mut arg_values = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            let hint = &param_tys[i];
            if plan.arg_types[i] != *hint {
                return Err(self.internal_error(&format!(
                    "a `defer` calling {item:?} has a checked argument type for argument {i} that disagrees with its own resolved parameter type"
                )));
            }
            // The exact place `resourceck` recorded for this argument
            // (`rfcs/0012`) must be the same place this stage resolves
            // on its own -- a plan naming `session` where this resolves
            // `session.input` (or vice versa) means the two stages
            // disagree about *what* this `defer` captures, which is
            // never silently trusted just because a plan is present.
            let resolved_place = if self.is_affine(hint) {
                self.resolve_place_expr(arg)?
            } else {
                None
            };
            if plan.arg_places[i] != resolved_place {
                return Err(self.internal_error(&format!(
                    "a `defer` calling {item:?} has a checked place for argument {i} that disagrees with the place this stage resolves for it"
                )));
            }
            let v = match self.lower_expr_hinted(fb, arg, hint)? {
                LoweredExpr::Value(v) => v,
                LoweredExpr::Diverged => {
                    return Err(self.unsupported(span, "a `defer` whose own argument diverges"));
                }
            };
            // A `take` parameter transfers ownership of this argument
            // into a dedicated, hidden capture *right here, at
            // registration time* (`rfcs/0011`, Blocker 6) -- not later,
            // when the deferred call this capture feeds actually
            // replays. `resourceck` already decided this argument
            // transfers (`checker::flow::check_defer` running the call
            // through the same move-checking `check_expr` any other
            // call gets); this `DeferCapture` only ever materializes
            // that decision, immediately, so the replayed `Call` later
            // consumes the already-captured owner, never the caller's
            // own (by then long-invalid) original argument value.
            // Cross-checked against `consume_sites` -- the exact same
            // verdict `check_expr_ctx`'s own `HirExpr::Call` handling
            // recorded for this same argument -- rather than trusted
            // from the defer plan alone.
            let plan_transfers =
                matches!(plan.arg_modes[i], crate::resourceck::ConsumeInfo::Transfer);
            let site_transfers = self.lookup_consume_mode(arg.id(), hint, "a defer argument")?;
            if plan_transfers != site_transfers {
                return Err(self.internal_error(&format!(
                    "a `defer` calling {item:?} has argument {i}'s own checked plan mode disagreeing with its own recorded consume site"
                )));
            }
            let captured = if plan_transfers && self.is_affine(hint) {
                fb.push_value(hint.clone(), ValueKind::DeferCapture { source: v })
            } else {
                v
            };
            arg_values.push(captured);
        }
        let requirements = self.lookup_function_requirements(*item, "a `defer` call")?;
        if !requirements.is_empty() {
            return Err(self.unsupported(span, "a `defer` calling a capability-requiring function"));
        }
        Ok(Some(PendingDefer {
            callee: *item,
            type_args: Vec::new(),
            args: arg_values,
            evidence: Vec::new(),
            ret_ty,
        }))
    }

    /// Replays `resourceck`'s own checked cleanup list for `exit_id`
    /// (`ResourceCheckResult::cleanup_edges`, already in replay order --
    /// last declared/registered first), materializing each entry as a
    /// real `Drop` instruction or a replayed deferred `Call` (`rfcs/0011`).
    /// Lowering does not decide *whether* a local still needs dropping
    /// here (`resourceck` already excluded anything `Moved`/`Dropped`
    /// from this exact list) -- only *how* to materialize each entry
    /// this stage already proved is owed. Every call site only ever
    /// reaches this for an exit lowering itself has already independently
    /// determined is reachable (an unreachable one is never lowered at
    /// all -- see e.g. `LoweredExpr::Diverged` short-circuiting before
    /// any of these call sites), so a missing `exit_id` here is never a
    /// legitimate "unreachable" case: it means resourceck recorded no
    /// plan for an exit lowering still reached, a structural mismatch
    /// between the two stages -- reported as an internal error, never
    /// silently treated as "nothing to clean up".
    fn emit_checked_cleanup(&mut self, fb: &mut FnBuilder, exit_id: ExprId) -> LowerResult<()> {
        let Some(actions) = self.cleanup_edges.get(&exit_id).cloned() else {
            return Err(self.internal_error(&format!(
                "exit {exit_id:?} is reachable but resourceck recorded no checked cleanup plan for it"
            )));
        };
        // `resourceck`'s own `cleanup_edges` is already in replay order
        // (last declared/registered first, `rfcs/0011`) -- so every
        // `Defer` this exact list replays must name a strictly
        // *decreasing* `registration_order`, matching that same LIFO
        // discipline from its own `CheckedDeferPlan`. Never trusted
        // silently: a plan replayed out of its own declared order would
        // run deferred calls in the wrong sequence without ever
        // producing a diagnostic otherwise.
        let mut last_defer_registration: Option<u32> = None;
        for action in actions {
            match action {
                crate::resourceck::CleanupAction::Drop(place) => {
                    // `resourceck` only ever schedules a `Drop` for a
                    // place it already proved `Available`/
                    // `DropScheduled` at this exact exit -- which itself
                    // already means this exact place's own root was
                    // bound on whichever path reached here. A missing
                    // binding means this checked plan and what lowering
                    // actually built have disagreed, not that there is
                    // nothing to clean up here. A bare root (`rfcs/
                    // 0011`) destroys exactly the local's own current
                    // value, unchanged from before Alpha 0.1.8; a
                    // projected place (`rfcs/0012`) moves the exact
                    // structural field out first (`PlaceRead`, `mode:
                    // Transfer`) and destroys *that* -- "get the value,
                    // then drop it" is `drop.place`'s own realization,
                    // see `Instruction::PlaceRead`'s own doc comment.
                    let value = if place.projections.is_empty() {
                        let Some(binding) = fb.local_bindings.get(&place.root).copied() else {
                            return Err(self.internal_error(&format!(
                                "a checked cleanup action drops local {:?}, which this frame never bound",
                                place.root
                            )));
                        };
                        self.load_current(fb, place.root, binding)?
                    } else {
                        let (nir_place, ty) = self.resolve_nir_place(fb, &place)?;
                        fb.push_value(
                            ty,
                            ValueKind::PlaceRead {
                                place: nir_place,
                                mode: crate::nir::OwnershipMode::Transfer,
                            },
                        )
                    };
                    fb.push_instruction(crate::nir::Instruction::Drop { value });
                }
                crate::resourceck::CleanupAction::Defer(defer_id) => {
                    let Some(pending) = fb.defer_calls.get(&defer_id).cloned() else {
                        return Err(self.internal_error(
                            "a checked cleanup action replays a `defer` this frame never lowered",
                        ));
                    };
                    let Some(plan) = self.defer_plans.get(&defer_id) else {
                        return Err(self.internal_error(&format!(
                            "a checked cleanup action replays defer {defer_id:?}, which has no checked plan recorded"
                        )));
                    };
                    if let Some(last) = last_defer_registration
                        && plan.registration_order >= last
                    {
                        return Err(self.internal_error(&format!(
                            "a checked cleanup list replays defer {defer_id:?} out of its own declared LIFO registration order"
                        )));
                    }
                    last_defer_registration = Some(plan.registration_order);
                    fb.push_value(
                        pending.ret_ty,
                        ValueKind::Call(
                            pending.callee,
                            pending.type_args,
                            pending.args,
                            pending.evidence,
                        ),
                    );
                }
            }
        }
        Ok(())
    }

    /// Lowers a *nested* block (an `if`/`match`/`handle` arm body, a
    /// `while`/`loop` body, or a bare `{ ... }` block expression) as its
    /// own resource-cleanup scope, distinct from the enclosing
    /// function's own top-level one (`rfcs/0011`). Any resource local
    /// this block itself declares and never moves is destroyed exactly
    /// once, right here, at this block's own normal fallthrough exit --
    /// never left in the function-wide cleanup list for an *enclosing*
    /// scope's own later cleanup to also (incorrectly) replay, which
    /// would either double-drop it or, since a value only ever a nested
    /// block's own nested basic blocks defined does not dominate
    /// anywhere outside that block, fail NIR verification outright. A
    /// block that itself diverges (`return`/`raise`/`break`/`continue`)
    /// needs no separate handling here: whichever function-level
    /// cleanup point it already terminated through has already replayed
    /// every entry up to and including this scope's own (`emit_cleanup`
    /// always covers the *whole*, still-flat list) -- this only ever
    /// needs to act, and truncate, on top of that.
    fn lower_scoped_block(
        &mut self,
        fb: &mut FnBuilder,
        block: &HirBlock,
    ) -> LowerResult<LoweredExpr> {
        let result = self.lower_block_value(fb, block)?;
        if !fb.current_terminated() {
            self.emit_checked_cleanup(fb, block.id)?;
        }
        Ok(result)
    }

    /// Like [`Self::lower_scoped_block`], for a `while`/`loop` body
    /// (`lower_block_void`'s own void-result shape) -- a resource this
    /// loop body itself declares fresh each iteration is destroyed at
    /// the body's own normal fallthrough (the back edge to the loop
    /// header), never left for the function-wide list to replay after
    /// the loop, where its own value would not dominate at all.
    fn lower_scoped_block_void(&mut self, fb: &mut FnBuilder, block: &HirBlock) -> LowerResult<()> {
        self.lower_block_void(fb, block)?;
        if !fb.current_terminated() {
            self.emit_checked_cleanup(fb, block.id)?;
        }
        Ok(())
    }

    /// Lowers one branch/arm's own body (`f`) (`rfcs/0011`). Historically
    /// this isolated a per-branch `moved_out` snapshot so a sibling
    /// branch's own moves couldn't leak into this one -- lowering no
    /// longer maintains any such cross-branch mutable ownership state at
    /// all: `resourceck::flow`'s own per-branch state clone already
    /// isolates each branch when it builds `ResourceCheckResult::
    /// cleanup_edges`, so every exit `f` reaches looks its own already-
    /// correctly-isolated cleanup list up directly, with nothing left
    /// here to isolate a second time. Kept as a named seam (rather than
    /// inlining every one of its call sites) purely so each branch/arm
    /// of a branching construct's own lowering reads the same way it
    /// always has.
    fn lower_branch_moves<T>(
        &mut self,
        fb: &mut FnBuilder,
        f: impl FnOnce(&mut Self, &mut FnBuilder) -> LowerResult<T>,
    ) -> LowerResult<T> {
        f(self, fb)
    }

    /// `return <expr>;`/`return;` (`rfcs/0011`, Blocker 2). A
    /// resource-typed `expr` that is itself a nested `if`/block is
    /// lowered through [`Self::lower_into_return_sink`] rather than
    /// the ordinary value-producing path (`if`/`match`/`handle`'s own
    /// shared-slot-then-merge machinery): a different underlying
    /// resource local may be the one actually transferred on each
    /// reachable branch (e.g. `return if cond { left } else { right
    /// }`, where `left` is moved and `right` must still be dropped on
    /// the `then` path, and vice versa on `else`), and NIR has no phi
    /// node to reconcile two branches' disagreeing ownership facts at
    /// one shared point -- so this `return`'s own cleanup+terminate
    /// must run separately inside each branch, using that branch's own
    /// correctly-isolated `moved_out` (see [`Self::lower_branch_moves`]).
    /// `resourceck` already rejects every other compound-origin shape
    /// (`match`/`handle`, or a non-`return` consuming position) this
    /// milestone cannot yet lower soundly, so `expr` reaching here is
    /// never one of those.
    fn lower_return(
        &mut self,
        fb: &mut FnBuilder,
        id: ExprId,
        value: Option<&HirExpr>,
    ) -> LowerResult<LoweredExpr> {
        let Some(value) = value else {
            self.emit_checked_cleanup(fb, id)?;
            fb.terminate(Terminator::Return(None));
            return Ok(LoweredExpr::Diverged);
        };
        let ret_ty = fb.return_ty.clone();
        let ret_ty_for_finish = ret_ty.clone();
        let mut finish = |this: &mut Self, fb: &mut FnBuilder, v: ValueId| {
            // Transfers ownership out to the caller explicitly
            // (`rfcs/0011`) -- a no-op for a non-affine `ret_ty`. Applied
            // uniformly here, in `finish` itself, so every leaf that
            // reaches it (a direct return value, or one compound branch
            // of a nested `if`/`match`/`handle`/block) gets the exact
            // same treatment without each call site needing to remember
            // to.
            let v = this.move_if_transferred(fb, v, &ret_ty_for_finish, true);
            fb.terminate(Terminator::Return(Some(v)));
            Ok(LoweredExpr::Diverged)
        };
        // The per-branch sink is only actually needed (and only ever
        // changes the NIR shape produced) for a resource-typed return
        // value -- a plain value type has no ownership ambiguity a
        // single post-merge terminator could get wrong, so it keeps
        // the ordinary, simpler shared-slot-then-merge lowering
        // (`rfcs/0011`, Blocker 2 is scoped to affine types only). Each
        // compound leaf calls `emit_checked_cleanup` itself, keyed by
        // its own id (see `lower_into_return_sink`'s own catch-all); a
        // direct, non-compound return value has no leaf of its own, so
        // it is keyed by this `return`'s own id instead, right here.
        if self.is_affine(&ret_ty) {
            self.lower_into_return_sink(fb, value, &ret_ty, &mut finish)
        } else {
            let v = match self.lower_expr_hinted(fb, value, &ret_ty)? {
                LoweredExpr::Value(v) => v,
                LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
            };
            self.emit_checked_cleanup(fb, id)?;
            finish(self, fb, v)
        }
    }

    /// Lowers `expr` in a position whose own final value must be
    /// handed to `finish` (a `return`'s own cleanup+terminate, or the
    /// function's own implicit-tail-return finish) separately on each
    /// reachable leaf of a nested `if`/block wrapping `expr`, instead
    /// of merging every branch's value into one shared slot first and
    /// calling `finish` once, afterward. See [`Self::lower_return`]'s
    /// own doc comment for why this is required at all.
    fn lower_into_return_sink(
        &mut self,
        fb: &mut FnBuilder,
        expr: &HirExpr,
        hint: &Ty,
        finish: &mut dyn FnMut(&mut Self, &mut FnBuilder, ValueId) -> LowerResult<LoweredExpr>,
    ) -> LowerResult<LoweredExpr> {
        match expr {
            HirExpr::Block(block) => self.lower_into_return_sink_block(fb, block, hint, finish),
            HirExpr::Match {
                scrutinee, arms, ..
            } => self.lower_match_into_return_sink(fb, scrutinee, arms, hint, finish),
            HirExpr::Handle { operand, arms, .. } => {
                self.lower_handle_into_return_sink(fb, operand, arms, hint, finish)
            }
            HirExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let cond_value = match self.lower_expr(fb, condition)? {
                    LoweredExpr::Value(v) => v,
                    LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
                };
                let then_block = fb.new_block();
                let else_block = fb.new_block();
                fb.terminate(Terminator::CondBranch {
                    condition: cond_value,
                    then_block,
                    else_block,
                });

                fb.switch_to(then_block);
                self.lower_branch_moves(fb, |this, fb| {
                    this.lower_into_return_sink_block(fb, then_branch, hint, &mut *finish)
                })?;

                fb.switch_to(else_block);
                self.lower_branch_moves(fb, |this, fb| match else_branch {
                    Some(HirElse::Block(b)) => {
                        this.lower_into_return_sink_block(fb, b, hint, &mut *finish)
                    }
                    Some(HirElse::If(inner)) => {
                        this.lower_into_return_sink(fb, inner, hint, &mut *finish)
                    }
                    None => {
                        let v = fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit));
                        finish(this, fb, v)
                    }
                })?;

                Ok(LoweredExpr::Diverged)
            }
            _ => {
                let value = match self.lower_expr_hinted(fb, expr, hint)? {
                    LoweredExpr::Value(v) => v,
                    LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
                };
                // This exact leaf is one branch's own return value
                // (`rfcs/0011`, Blocker 2): `resourceck::flow`'s own
                // `check_block_ctx_inner` records this leaf's own
                // checked cleanup under this same id, using that
                // branch's own state before any join with a sibling
                // branch runs.
                self.emit_checked_cleanup(fb, expr.id())?;
                finish(self, fb, value)
            }
        }
    }

    /// Like [`Self::lower_into_return_sink`], for one nested block's
    /// own statements + tail directly (an `if`-branch's own body, or a
    /// bare `{ ... }` wrapping the sink's own expression) -- scoped
    /// exactly like [`Self::lower_scoped_block`], so a resource this
    /// block itself declares and never moves does not leak into a
    /// sibling branch's own cleanup list.
    fn lower_into_return_sink_block(
        &mut self,
        fb: &mut FnBuilder,
        block: &HirBlock,
        hint: &Ty,
        finish: &mut dyn FnMut(&mut Self, &mut FnBuilder, ValueId) -> LowerResult<LoweredExpr>,
    ) -> LowerResult<LoweredExpr> {
        for stmt in &block.statements {
            self.lower_stmt(fb, stmt)?;
            if fb.current_terminated() {
                return Ok(LoweredExpr::Diverged);
            }
        }
        match &block.tail {
            Some(tail) => self.lower_into_return_sink(fb, tail, hint, finish),
            None => {
                let v = fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit));
                finish(self, fb, v)
            }
        }
    }

    fn lower_while(
        &mut self,
        fb: &mut FnBuilder,
        condition: &HirExpr,
        body: &HirBlock,
    ) -> LowerResult<()> {
        let header = fb.new_block();
        fb.terminate(Terminator::Branch(header));

        // `loop_body`/`after` are deliberately not created until the
        // condition is known to produce a real value: creating them
        // upfront and then hitting the early `Diverged` return below
        // would leave them permanently unterminated (nothing branches
        // to them, and nothing ever will), which is exactly the
        // "internal invariant: every NIR block must have a terminator"
        // panic this is guarding against. Lowering them lazily means
        // there is simply nothing left dangling on this path.
        fb.switch_to(header);
        let cond_value = match self.lower_expr(fb, condition)? {
            LoweredExpr::Value(v) => v,
            // The condition itself diverged and already gave `header`
            // a real terminator (whatever `return`/`break`/`continue`
            // it lowered to); the loop body and exit block are never
            // reachable, so they are never created at all.
            LoweredExpr::Diverged => return Ok(()),
        };
        let loop_body = fb.new_block();
        let after = fb.new_block();
        fb.terminate(Terminator::CondBranch {
            condition: cond_value,
            then_block: loop_body,
            else_block: after,
        });

        fb.switch_to(loop_body);
        fb.loop_stack.push(LoopCtx {
            break_target: after,
            continue_target: header,
        });
        self.lower_scoped_block_void(fb, body)?;
        fb.loop_stack.pop();
        if !fb.current_terminated() {
            fb.terminate(Terminator::Branch(header));
        }

        // `after` is reached either through the condition-false edge or
        // through some reachable `break`; `resourceck::flow`'s own
        // `finish_loop` already joined every one of those into a single
        // agreed-upon state before recording whatever comes lexically
        // after this loop's own checked cleanup -- nothing further to
        // reconcile here.
        fb.switch_to(after);
        Ok(())
    }

    fn lower_loop(&mut self, fb: &mut FnBuilder, body: &HirBlock) -> LowerResult<()> {
        let header = fb.new_block();
        let after = fb.new_block();
        fb.terminate(Terminator::Branch(header));

        fb.switch_to(header);
        fb.loop_stack.push(LoopCtx {
            break_target: after,
            continue_target: header,
        });
        self.lower_scoped_block_void(fb, body)?;
        fb.loop_stack.pop();
        if !fb.current_terminated() {
            fb.terminate(Terminator::Branch(header));
        }

        // A bare `loop` has no condition-false edge at all -- only a
        // reachable `break` can ever reach `after`. If none exist,
        // `after` is itself unreachable, and nothing lexically after
        // this loop is either (`resourceck`'s own `stmt_diverges`
        // already treats such a loop as divergent).
        fb.switch_to(after);
        Ok(())
    }

    // ---- expression lowering ----

    fn lower_expr(&mut self, fb: &mut FnBuilder, expr: &HirExpr) -> LowerResult<LoweredExpr> {
        match expr {
            HirExpr::Int { value, .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::I64, ValueKind::Const(Const::Int(*value))),
            )),
            HirExpr::Float { value, .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::F64, ValueKind::Const(Const::Float(*value))),
            )),
            HirExpr::Str { value, .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::Str, ValueKind::Const(Const::Str(value.clone()))),
            )),
            HirExpr::Char { value, .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::Char, ValueKind::Const(Const::Char(*value))),
            )),
            HirExpr::Bool { value, .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::Bool, ValueKind::Const(Const::Bool(*value))),
            )),
            HirExpr::Local { local, .. } => {
                // A hand-built HIR module can name a `LocalId` this
                // function never actually bound (no matching parameter
                // or `let`-style statement) -- `hir::lower`'s own name
                // resolution already rules this out for the ordinary
                // pipeline, but this module never trusts that a direct
                // caller bypassing it did too.
                let Some(&binding) = fb.local_bindings.get(local) else {
                    return Err(self.internal_error(&format!(
                        "local {local:?} is read before it was ever bound"
                    )));
                };
                match binding {
                    LocalBinding::Direct(value) => Ok(LoweredExpr::Value(value)),
                    LocalBinding::Slot(slot) => {
                        let Some(ty) = self.local_types.get(local).cloned() else {
                            return Err(self.internal_error(&format!(
                                "local {local:?} has a bound slot but no recorded type"
                            )));
                        };
                        Ok(LoweredExpr::Value(fb.push_value(ty, ValueKind::Load(slot))))
                    }
                }
            }
            // typeck rejects a function name used outside of a call
            // position outright (T0010) before lowering ever runs in
            // the normal pipeline. A direct caller bypassing that gate
            // must not get a fabricated `Ty::Error` placeholder value
            // in its place -- functions are not first-class values in
            // this milestone at all.
            HirExpr::Function { name, span, .. } => {
                let text = self.interner.resolve(*name);
                Err(self.unsupported(*span, &format!("using `{text}` as a first-class value")))
            }
            // A bare (uncalled) case reference: `typeck` already
            // confirmed this case carries no payload (else it recorded
            // `Ty::Error` and this is unreachable for a well-typed
            // program) -- routed through the same lower_variant_construct
            // a `Variant.Case(...)` call goes through, with an empty
            // argument list, so an unknown variant, an invalid case
            // index, and (via the existing arity check) a bare
            // reference to a case that actually carries a payload are
            // all rejected the same one way, not by a second,
            // independently-drifting implementation here.
            HirExpr::CaseRef { variant, case, .. } => {
                self.lower_variant_construct(fb, *variant, *case, &[], expr)
            }
            // There are no first-class/dynamic protocol methods in
            // Alpha 0.1.5 (`rfcs/0009`); typeck already rejects a bare
            // (uncalled) reference outright before lowering ever runs
            // in the normal pipeline.
            HirExpr::ProtocolMethodRef { name, span, .. } => {
                let text = self.interner.resolve(*name);
                Err(self.unsupported(
                    *span,
                    &format!("using protocol method `{text}` as a first-class value"),
                ))
            }
            HirExpr::Unary { op, operand, .. } => self.lower_unary(fb, *op, operand),
            HirExpr::Binary {
                op,
                left,
                right,
                span,
                ..
            } => self.lower_binary(fb, *op, left, right, *span),
            HirExpr::Assign {
                target, op, value, ..
            } => self.lower_assign(fb, target, *op, value),
            HirExpr::Call { callee, args, .. } => self.lower_call(fb, callee, args, expr),
            HirExpr::Field { base, name, .. } => self.lower_field(fb, base, *name, expr),
            // typeck rejects both of these outright (T0007) before
            // lowering ever runs in the normal pipeline. A direct
            // caller bypassing that gate must not get identity lowering
            // in their place: `as` performs no runtime conversion at
            // all in this milestone, and `?` has no propagation
            // semantics -- silently forwarding the unconverted /
            // unpropagated inner value would let either "succeed" while
            // lying about what it does.
            HirExpr::Cast { span, .. } => Err(self.unsupported(*span, "casts (`as`)")),
            HirExpr::Try {
                expr: inner, id, ..
            } => self.lower_try(fb, *id, inner),
            HirExpr::Raise { operand, id, .. } => self.lower_raise(fb, *id, operand),
            HirExpr::Handle { operand, arms, .. } => {
                let result_ty = self.expr_ty(expr)?;
                self.lower_handle(fb, operand, arms, result_ty)
            }
            HirExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let result_ty = self.expr_ty(expr)?;
                self.lower_if(fb, condition, then_branch, else_branch, result_ty)
            }
            HirExpr::Match {
                scrutinee, arms, ..
            } => {
                let result_ty = self.expr_ty(expr)?;
                self.lower_match(fb, scrutinee, arms, result_ty)
            }
            HirExpr::Block(b) => self.lower_scoped_block(fb, b),
            HirExpr::RecordLiteral { record, fields, .. } => {
                self.lower_record_literal(fb, *record, fields, expr)
            }
            HirExpr::Return { value, id, .. } => self.lower_return(fb, *id, value.as_deref()),
            HirExpr::Break {
                value, id, span, ..
            } => {
                // typeck rejects any value-carrying `break` outright
                // (T0007) regardless of the value's type, before
                // lowering ever runs in the normal pipeline. A direct
                // caller bypassing that gate must not have the value
                // silently evaluated and discarded as though it were an
                // ordinary valueless `break` -- loop-as-expression has
                // no lowering at all yet.
                if value.is_some() {
                    return Err(
                        self.unsupported(*span, "`break` with a value (loop-as-expression)")
                    );
                }
                let ctx = *fb
                    .loop_stack
                    .last()
                    .ok_or_else(|| self.unsupported(*span, "`break` outside a loop"))?;
                // Destroys exactly this iteration's own live resources
                // (`rfcs/0011`, Blocker 5) before jumping past the loop
                // entirely -- `resourceck::flow` already recorded this
                // exact `break`'s own checked cleanup list, covering
                // only what this loop's own current iteration owns
                // (nested scopes included), never an enclosing scope's
                // (an outer loop, or the function itself).
                self.emit_checked_cleanup(fb, *id)?;
                fb.terminate(Terminator::Branch(ctx.break_target));
                Ok(LoweredExpr::Diverged)
            }
            HirExpr::Continue { id, span, .. } => {
                let ctx = *fb
                    .loop_stack
                    .last()
                    .ok_or_else(|| self.unsupported(*span, "`continue` outside a loop"))?;
                // Same cleanup as `break` above, before looping back to
                // the condition instead of past it -- this iteration's
                // own resources must still be destroyed exactly once
                // before the next iteration freshly redeclares them.
                self.emit_checked_cleanup(fb, *id)?;
                fb.terminate(Terminator::Branch(ctx.continue_target));
                Ok(LoweredExpr::Diverged)
            }
            HirExpr::Error { .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::Error, ValueKind::Const(Const::Unit)),
            )),
        }
    }

    /// Lowers `expr`, using `hint` as the type for a bare integer/float
    /// literal (a literal has no type of its own; it takes whatever
    /// the surrounding context already unified it with).
    fn lower_expr_hinted(
        &mut self,
        fb: &mut FnBuilder,
        expr: &HirExpr,
        hint: &Ty,
    ) -> LowerResult<LoweredExpr> {
        match expr {
            HirExpr::Int { value, .. } if is_numeric(hint) => Ok(LoweredExpr::Value(
                fb.push_value(hint.clone(), ValueKind::Const(Const::Int(*value))),
            )),
            HirExpr::Float { value, .. } if is_numeric(hint) => Ok(LoweredExpr::Value(
                fb.push_value(hint.clone(), ValueKind::Const(Const::Float(*value))),
            )),
            _ => self.lower_expr(fb, expr),
        }
    }

    fn lower_unary(
        &mut self,
        fb: &mut FnBuilder,
        op: UnaryOp,
        operand: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        let ty = self.expr_ty(operand)?;
        let v = match self.lower_expr_hinted(fb, operand, &ty)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        Ok(LoweredExpr::Value(match op {
            UnaryOp::Neg => fb.push_value(ty, ValueKind::Neg(v)),
            UnaryOp::Not | UnaryOp::BitNot => fb.push_value(ty, ValueKind::Not(v)),
        }))
    }

    fn lower_binary(
        &mut self,
        fb: &mut FnBuilder,
        op: BinaryOp,
        left: &HirExpr,
        right: &HirExpr,
        span: Span,
    ) -> LowerResult<LoweredExpr> {
        match op {
            BinaryOp::And => return self.lower_short_circuit(fb, left, right, false),
            BinaryOp::Or => return self.lower_short_circuit(fb, left, right, true),
            // typeck rejects every range expression outright (T0007)
            // before lowering ever runs in the normal pipeline. A
            // direct caller bypassing that gate must not get "lowered
            // to its left endpoint" in its place -- there is no range
            // value or iteration support at all in this milestone, so
            // silently keeping just one side would misrepresent what
            // the expression means, not merely leave it unsupported.
            BinaryOp::Range | BinaryOp::RangeInclusive => {
                return Err(self.unsupported(span, "range expressions (`..`/`..=`)"));
            }
            _ => {}
        }

        // typeck already unified left and right to the same type (or
        // recorded a diagnostic if it couldn't), so either side's
        // resolved expr_type is the operand type -- no need to guess
        // which side "actually" carries it based on which is a literal.
        let operand_ty = self.expr_ty(left)?;

        let lv = match self.lower_expr_hinted(fb, left, &operand_ty)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        let rv = match self.lower_expr_hinted(fb, right, &operand_ty)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };

        let kind = match op {
            BinaryOp::Add => ValueKind::Add(lv, rv),
            BinaryOp::Sub => ValueKind::Sub(lv, rv),
            BinaryOp::Mul => ValueKind::Mul(lv, rv),
            BinaryOp::Div => ValueKind::Div(lv, rv),
            BinaryOp::Rem => ValueKind::Rem(lv, rv),
            BinaryOp::BitAnd => ValueKind::And(lv, rv),
            BinaryOp::BitOr => ValueKind::Or(lv, rv),
            BinaryOp::BitXor => ValueKind::Xor(lv, rv),
            BinaryOp::Shl => ValueKind::Shl(lv, rv),
            BinaryOp::Shr => ValueKind::Shr(lv, rv),
            BinaryOp::Eq => ValueKind::Eq(lv, rv),
            BinaryOp::Ne => ValueKind::Ne(lv, rv),
            BinaryOp::Lt => ValueKind::Lt(lv, rv),
            BinaryOp::Le => ValueKind::Le(lv, rv),
            BinaryOp::Gt => ValueKind::Gt(lv, rv),
            BinaryOp::Ge => ValueKind::Ge(lv, rv),
            BinaryOp::And | BinaryOp::Or | BinaryOp::Range | BinaryOp::RangeInclusive => {
                unreachable!("handled above")
            }
        };
        let result_ty = match op {
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge => Ty::Bool,
            _ => operand_ty,
        };
        Ok(LoweredExpr::Value(fb.push_value(result_ty, kind)))
    }

    /// Lowers `&&`/`||` with short-circuit evaluation: the right operand
    /// is only evaluated when the left doesn't already decide the
    /// result. `short_on_true` is `true` for `||` (stop as soon as the
    /// left side is true) and `false` for `&&` (stop as soon as it's
    /// false).
    fn lower_short_circuit(
        &mut self,
        fb: &mut FnBuilder,
        left: &HirExpr,
        right: &HirExpr,
        short_on_true: bool,
    ) -> LowerResult<LoweredExpr> {
        let left_value = match self.lower_expr(fb, left)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        let right_block = fb.new_block();
        let after_block = fb.new_block();
        let result_slot = fb.alloc_slot(Ty::Bool);

        fb.push_store(result_slot, left_value, crate::nir::OwnershipMode::Observe);
        let (then_block, else_block) = if short_on_true {
            (after_block, right_block)
        } else {
            (right_block, after_block)
        };
        fb.terminate(Terminator::CondBranch {
            condition: left_value,
            then_block,
            else_block,
        });

        fb.switch_to(right_block);
        // A Diverged right side already terminated `right_block` itself
        // (via whatever return/break/continue it lowered to); there is
        // no value to store and no `after_block` branch to add on top
        // of that.
        if let LoweredExpr::Value(right_value) = self.lower_expr(fb, right)? {
            fb.push_store(result_slot, right_value, crate::nir::OwnershipMode::Observe);
            fb.terminate(Terminator::Branch(after_block));
        }

        fb.switch_to(after_block);
        Ok(LoweredExpr::Value(
            fb.push_value(Ty::Bool, ValueKind::Load(result_slot)),
        ))
    }

    fn lower_assign(
        &mut self,
        fb: &mut FnBuilder,
        target: &HirExpr,
        op: AssignOp,
        value: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        // Reinitializing an affine field place (`session.input =
        // open_file();`, `rfcs/0012`) -- `typeck` only ever accepts this
        // target shape for a plain `=` into an affine field
        // (`Checker::check_assign`), and `resourceck` already proved the
        // target place is provably empty on every reachable path before
        // this instruction is ever reached; lowering itself resolves the
        // place fresh here (never trusting a HIR-level annotation) and
        // emits an explicit `StorePlace`.
        if let HirExpr::Field { .. } = target {
            let target_ty = self.expr_ty(target)?;
            if self.is_affine(&target_ty) {
                let Some(place) = self.resolve_place_expr(target)? else {
                    return Err(self.internal_error(
                        "an affine field assignment target has no resolvable structural place",
                    ));
                };
                let (nir_place, ty) = self.resolve_nir_place(fb, &place)?;
                let value_value = match self.lower_expr_hinted(fb, value, &ty)? {
                    LoweredExpr::Value(v) => v,
                    LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
                };
                fb.push_instruction(crate::nir::Instruction::StorePlace {
                    place: nir_place,
                    value: value_value,
                });
                return Ok(LoweredExpr::Value(
                    fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)),
                ));
            }
        }
        let HirExpr::Local { local, .. } = target else {
            if matches!(self.lower_expr(fb, target)?, LoweredExpr::Diverged) {
                return Ok(LoweredExpr::Diverged);
            }
            if matches!(self.lower_expr(fb, value)?, LoweredExpr::Diverged) {
                return Ok(LoweredExpr::Diverged);
            }
            return Ok(LoweredExpr::Value(
                fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)),
            ));
        };
        // typeck rejects assigning to a binding that isn't `mutable`
        // before NIR lowering ever runs, so a well-typed program's
        // assignment target always has a real slot here -- but a direct
        // caller hand-building HIR past that gate could still name an
        // unbound, or immutable (`LocalBinding::Direct`), local as an
        // assignment's own target.
        let slot = match fb.local_bindings.get(local) {
            Some(LocalBinding::Slot(slot)) => *slot,
            other => {
                return Err(self.internal_error(&format!(
                    "assignment target {local:?} must be a mutable local's slot, found {other:?}"
                )));
            }
        };
        let Some(target_ty) = self.local_types.get(local).cloned() else {
            return Err(self.internal_error(&format!(
                "assignment target {local:?} has no type recorded by typeck"
            )));
        };
        let value_value = match self.lower_expr_hinted(fb, value, &target_ty)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        // Resource reassignment (`rfcs/0011`, Blocker 5): `resourceck`
        // already proved the target's own previous value was moved or
        // dropped before this reassignment was ever accepted, and that
        // a plain-local RHS (`target = source;`) is itself consumed by
        // it exactly like any other move. `resourceck::flow`'s own
        // checked cleanup plan already reflects both halves of that on
        // its own -- `local`'s own `Drop` entry is only ever included
        // in a cleanup snapshot taken while `resourceck` still
        // considers it `Available`/`DropScheduled`, and `source`'s own
        // is excluded from any snapshot taken after this reassignment,
        // since `resourceck` already transitioned it to `Moved` -- so
        // lowering has nothing further of its own to update here.
        let final_value = match op {
            AssignOp::Assign => value_value,
            _ => {
                let current = fb.push_value(target_ty.clone(), ValueKind::Load(slot));
                let kind = match op {
                    AssignOp::Add => ValueKind::Add(current, value_value),
                    AssignOp::Sub => ValueKind::Sub(current, value_value),
                    AssignOp::Mul => ValueKind::Mul(current, value_value),
                    AssignOp::Div => ValueKind::Div(current, value_value),
                    AssignOp::Rem => ValueKind::Rem(current, value_value),
                    AssignOp::BitAnd => ValueKind::And(current, value_value),
                    AssignOp::BitOr => ValueKind::Or(current, value_value),
                    AssignOp::BitXor => ValueKind::Xor(current, value_value),
                    AssignOp::Shl => ValueKind::Shl(current, value_value),
                    AssignOp::Shr => ValueKind::Shr(current, value_value),
                    AssignOp::Assign => unreachable!("handled above"),
                };
                fb.push_value(target_ty.clone(), kind)
            }
        };
        // A plain reassignment (`target = source;`) is itself a move,
        // exactly like a `value`/`mutable` binding's own initializer
        // (`ConsumeKind::Other`); a compound assignment (`target +=
        // ...`) is always numeric/bitwise, never affine, and never
        // itself checked by `resourceck` as a consume site at all.
        let transfers = op == AssignOp::Assign
            && self.lookup_consume_mode(value.id(), &target_ty, "an assignment value")?;
        let mode = if transfers {
            crate::nir::OwnershipMode::Transfer
        } else {
            crate::nir::OwnershipMode::Observe
        };
        fb.push_store(slot, final_value, mode);
        Ok(LoweredExpr::Value(
            fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)),
        ))
    }

    fn lower_call(
        &mut self,
        fb: &mut FnBuilder,
        callee: &HirExpr,
        args: &[HirExpr],
        call_expr: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        if let HirExpr::CaseRef { variant, case, .. } = callee {
            return self.lower_variant_construct(fb, *variant, *case, args, call_expr);
        }
        if let HirExpr::ProtocolMethodRef {
            protocol,
            arguments,
            method,
            ..
        } = callee
        {
            return self.lower_protocol_call(fb, *protocol, arguments, *method, args, call_expr);
        }

        let HirExpr::Function { item, .. } = callee else {
            // typeck already rejects a call whose callee doesn't
            // resolve to an actual function (Napitia has no first-class
            // function values); reaching here means a caller lowered
            // hand-built HIR bypassing that check. The callee and
            // arguments are still checked for their own divergence (a
            // diverging callee/argument really would make the whole
            // call unreachable), but the call itself must never
            // fabricate a successful `Ty::Error`/`Const::Unit` result --
            // that would silently invent a value nothing in the source
            // actually produced.
            if matches!(self.lower_expr(fb, callee)?, LoweredExpr::Diverged) {
                return Ok(LoweredExpr::Diverged);
            }
            for arg in args {
                if matches!(self.lower_expr(fb, arg)?, LoweredExpr::Diverged) {
                    return Ok(LoweredExpr::Diverged);
                }
            }
            return Err(self.internal_error("call target does not resolve to a function"));
        };
        let (type_params, param_tys, _ret_ty) = self.lookup_function_sig(*item, "a call")?;
        // Resolved once by `typeck` (inferred or explicit) and read back
        // here, never re-inferred -- the same "typeck already decided"
        // discipline every other type in this module already follows
        // (`rfcs/0008`). Empty for a non-generic call.
        let type_args = self.resolve_call_type_args(call_expr.id(), &type_params, "a call")?;
        let subst: HashMap<crate::hir::TypeParamId, Ty> = type_params
            .into_iter()
            .zip(type_args.iter().cloned())
            .collect();
        if param_tys.len() != args.len() {
            return Err(self.internal_error(&format!(
                "a call to {item:?} has {} argument(s) but its own resolved signature declares {}",
                args.len(),
                param_tys.len()
            )));
        }
        let mut arg_values = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            let hint = crate::types::substitute(&param_tys[i], &subst);
            let v = match self.lower_expr_hinted(fb, arg, &hint)? {
                LoweredExpr::Value(v) => v,
                LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
            };
            // `resourceck` already decided whether this exact argument
            // transfers ownership into the call (`rfcs/0011`): its own
            // checked cleanup plan already excludes a transferred
            // argument's own source local from its former scope's
            // cleanup wherever it would otherwise be dropped again --
            // this explicit `Move` only ever materializes that already-
            // checked decision, read back directly, never re-derived
            // from the callee's own `take` flags a second time.
            let transfers = self.lookup_consume_mode(arg.id(), &hint, "a call argument")?;
            arg_values.push(self.move_if_transferred(fb, v, &hint, transfers));
        }
        let requirements = self.lookup_function_requirements(*item, "a call")?;
        let evidence = self.resolve_call_evidence(call_expr.id(), &requirements, "a call")?;
        let call_ty = self.expr_ty(call_expr)?;
        Ok(LoweredExpr::Value(fb.push_value(
            call_ty,
            ValueKind::Call(*item, type_args, arg_values, evidence),
        )))
    }

    /// Shared setup for postfix `?`/`handle` (`rfcs/0010`): both require
    /// their own operand to structurally be a direct call to a fallible
    /// function (`typeck`'s own `check_try`/`check_handle` already
    /// enforce this before a well-typed program ever reaches lowering).
    /// Lowers the callee's own arguments exactly like an ordinary call,
    /// then terminates the current block with `Terminator::Invoke`.
    ///
    /// Returns `None` (never emitting an `Invoke` at all) when the
    /// operand itself was not actually a fallible call -- either because
    /// evaluating it (for its own independent side effects/divergence,
    /// still required even though the result is never used as a value)
    /// diverged, or because a direct caller bypassed `typeck` with
    /// malformed HIR; the caller must propagate `LoweredExpr::Diverged`
    /// in the former case exactly as if this were any other diverging
    /// subexpression.
    ///
    /// On success, returns the callee's own return type, the slot/block
    /// its success edge stores into and continues at, one
    /// `(variant, slot, block)` triple per effect the callee declares in
    /// `raises` (in that same canonical order), and -- only when
    /// `merge_result_ty` was given -- an extra slot/block allocated on
    /// this same still-open block for the caller's own use (`handle`'s
    /// own result slot/merge block, which must dominate every arm the
    /// same way `lower_match`'s own result slot does; allocating it here,
    /// before the `Invoke` that is about to terminate this block, is the
    /// only way to still append to it -- the caller is responsible for
    /// actually lowering each failure block's own body before the
    /// enclosing function is finished.
    #[allow(clippy::type_complexity)]
    fn lower_invoke(
        &mut self,
        fb: &mut FnBuilder,
        operand: &HirExpr,
        context: &str,
        merge_result_ty: Option<&Ty>,
    ) -> LowerResult<
        Option<(
            Ty,
            ValueId,
            BlockId,
            Vec<(ItemId, ValueId, BlockId)>,
            Option<(ValueId, BlockId)>,
        )>,
    > {
        let HirExpr::Call { callee, args, .. } = operand else {
            if matches!(self.lower_expr(fb, operand)?, LoweredExpr::Diverged) {
                return Ok(None);
            }
            return Err(self.internal_error(&format!(
                "{context}'s operand is not a direct call to a fallible function"
            )));
        };
        let HirExpr::Function { item, .. } = &**callee else {
            if matches!(self.lower_expr(fb, callee)?, LoweredExpr::Diverged) {
                return Ok(None);
            }
            for arg in args {
                if matches!(self.lower_expr(fb, arg)?, LoweredExpr::Diverged) {
                    return Ok(None);
                }
            }
            return Err(self.internal_error(&format!(
                "{context}'s operand does not call a named function"
            )));
        };
        let (type_params, param_tys, ret_ty) = self.lookup_function_sig(*item, context)?;
        let type_args = self.resolve_call_type_args(operand.id(), &type_params, context)?;
        let subst: HashMap<crate::hir::TypeParamId, Ty> = type_params
            .into_iter()
            .zip(type_args.iter().cloned())
            .collect();
        // Unlike an ordinary `Call` (which reads its own already-
        // substituted result type back from `expr_types`, since typeck
        // recorded the whole call expression's type there), `Invoke`
        // builds its own `ok_slot` type directly from the callee's own
        // declared (still-symbolic, for a generic callee) signature --
        // so it must substitute this itself, or a generic fallible
        // callee's success slot would keep a dangling `Ty::Param` no
        // concrete value ever actually has, corrupting every downstream
        // instruction that reads it (`rfcs/0008`).
        let ret_ty = crate::types::substitute(&ret_ty, &subst);
        if param_tys.len() != args.len() {
            return Err(self.internal_error(&format!(
                "{context} calls {item:?} with {} argument(s) but its own resolved signature declares {}",
                args.len(),
                param_tys.len()
            )));
        }
        let mut arg_values = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            let hint = crate::types::substitute(&param_tys[i], &subst);
            let v = match self.lower_expr_hinted(fb, arg, &hint)? {
                LoweredExpr::Value(v) => v,
                LoweredExpr::Diverged => return Ok(None),
            };
            // Exactly `lower_call`'s own rule (`rfcs/0011`, Blocker 1):
            // an argument transfers ownership into the call whether
            // that call is an ordinary `Call` or a fallible `Invoke` --
            // `resourceck` already decided this, and its own checked
            // cleanup plan already reflects it on every edge (the
            // success edge, and every failure edge alike); this
            // explicit `Move` only ever materializes it, read back
            // directly rather than re-derived from the callee's own
            // `take` flags a second time.
            let transfers = self.lookup_consume_mode(arg.id(), &hint, "an invoke argument")?;
            arg_values.push(self.move_if_transferred(fb, v, &hint, transfers));
        }
        let requirements = self.lookup_function_requirements(*item, context)?;
        let evidence = self.resolve_call_evidence(operand.id(), &requirements, context)?;
        let raises = self.lookup_function_raises(*item, context)?;

        // Allocated here, before the `Invoke` below terminates this
        // block -- not by the caller afterward, when it would already be
        // too late to append anything to it.
        let merge = merge_result_ty.map(|ty| (fb.alloc_slot(ty.clone()), fb.new_block()));

        let ok_slot = fb.alloc_slot(ret_ty.clone());
        let ok_target = fb.new_block();
        let mut err_targets = Vec::with_capacity(raises.len());
        let mut err_blocks = Vec::with_capacity(raises.len());
        for variant in &raises {
            let Some(layout) = self.variants.get(variant) else {
                return Err(self.internal_error(&format!(
                    "{context}'s callee declares raising unknown variant id {variant:?}"
                )));
            };
            let err_slot = fb.alloc_slot(Ty::Named(*variant, layout.name));
            let dispatch_block = fb.new_block();
            err_targets.push(InvokeErrTarget {
                variant: *variant,
                slot: err_slot,
                target: dispatch_block,
            });
            err_blocks.push((*variant, err_slot, dispatch_block));
        }

        fb.terminate(Terminator::Invoke {
            callee: *item,
            type_args,
            args: arg_values,
            evidence,
            ok_slot,
            ok_target,
            err_targets,
        });
        Ok(Some((ret_ty, ok_slot, ok_target, err_blocks, merge)))
    }

    /// Postfix `?` (`rfcs/0010`). On the callee's success edge, simply
    /// loads and forwards the success value; on each failure edge,
    /// forwards the exact same raised value onward unchanged via this
    /// function's own `Terminator::Raise` -- `typeck`'s own
    /// `PROPAGATION_NOT_DECLARED` check already proved every one of
    /// those effects is also a member of this function's own `raises`.
    fn lower_try(
        &mut self,
        fb: &mut FnBuilder,
        id: ExprId,
        operand: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        let Some((ret_ty, ok_slot, ok_target, err_blocks, _)) =
            self.lower_invoke(fb, operand, "postfix `?`", None)?
        else {
            return Ok(LoweredExpr::Diverged);
        };
        for (variant, err_slot, dispatch_block) in err_blocks {
            let Some(layout) = self.variants.get(&variant) else {
                return Err(self.internal_error("postfix `?` propagates an unknown variant"));
            };
            let name = layout.name;
            fb.switch_to(dispatch_block);
            let loaded = fb.push_value(Ty::Named(variant, name), ValueKind::Load(err_slot));
            // Propagating out via `?` leaves this function's own scope
            // exactly like an explicit `raise`/`return` does
            // (`rfcs/0011`): every failure dispatch block replays this
            // exact `?`'s own checked cleanup (looked up once by its
            // own id, since the state at the point of the `?` does not
            // depend on which raised variant actually propagated).
            self.emit_checked_cleanup(fb, id)?;
            fb.terminate(Terminator::Raise { value: loaded });
        }
        fb.switch_to(ok_target);
        Ok(LoweredExpr::Value(
            fb.push_value(ret_ty, ValueKind::Load(ok_slot)),
        ))
    }

    /// `raise <operand>` (`rfcs/0010`). Always diverges, exactly like
    /// `return`/`break`: `operand` is evaluated exactly once, then the
    /// current block ends with `Terminator::Raise` instead of falling
    /// through to anything else.
    fn lower_raise(
        &mut self,
        fb: &mut FnBuilder,
        id: ExprId,
        operand: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        let value = match self.lower_expr(fb, operand)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        // `raise` leaves this function's own scope exactly like `return`
        // does (`rfcs/0011`): every still-owned resource this function's
        // own top-level scope owns, and every registered `defer`, must
        // still run before control actually transfers to the caller's
        // own failure edge.
        self.emit_checked_cleanup(fb, id)?;
        // A no-op today (a raised value is always a declared error
        // variant, and `RESOURCE_FIELD_IN_ORDINARY_AGGREGATE`/T0064
        // already forbids an affine field in any aggregate, so `operand`
        // itself is never actually resource-typed) -- kept for the same
        // reason `lower_raise` still calls `emit_checked_cleanup` at
        // all: an explicit transfer out through `raise`, wherever the
        // accepted language ever does permit one, must never depend on
        // this call site remembering to add it later.
        let ty = self.expr_ty(operand)?;
        let value = self.move_if_transferred(fb, value, &ty, true);
        fb.terminate(Terminator::Raise { value });
        Ok(LoweredExpr::Diverged)
    }

    /// `handle <operand> { ... }` (`rfcs/0010`). The callee's success
    /// edge binds `success`'s pattern and lowers its body; each failure
    /// edge is switched on its own variant's case, dispatching to
    /// whichever `failure` arm's body `typeck`'s own exhaustiveness check
    /// already proved covers it (a `Case` arm covers exactly the one
    /// case it names; a single trailing wildcard covers everything no
    /// `Case` arm already claimed, across every raised type at once) --
    /// every arm body is lowered exactly once, in a block shared by
    /// every case it covers, mirroring how an ordinary `match`'s own
    /// wildcard/binding arm reuses one target across several
    /// `Terminator::Switch` cases.
    fn lower_handle(
        &mut self,
        fb: &mut FnBuilder,
        operand: &HirExpr,
        arms: &[HirHandleArm],
        result_ty: Ty,
    ) -> LowerResult<LoweredExpr> {
        // No result slot/merge block at all when every reachable arm
        // diverges (`typeck` already proved this) -- mirrors
        // `lower_match`'s own `Ty::Never` short-circuit. Requested from
        // `lower_invoke` itself (rather than allocated here afterward),
        // since by the time it returns, the block it would need to
        // allocate into is already terminated by the `Invoke`.
        let merge_result_ty = (result_ty != Ty::Never).then_some(&result_ty);
        let Some((ok_ty, ok_slot, ok_target, err_blocks, merge)) =
            self.lower_invoke(fb, operand, "`handle`", merge_result_ty)?
        else {
            return Ok(LoweredExpr::Diverged);
        };
        let sink = merge.map(|(slot, after)| ArmSink::Merge(slot, after));
        self.lower_handle_dispatch(
            fb, arms, ok_ty, ok_slot, ok_target, err_blocks, sink, result_ty,
        )
    }

    /// Lowers `expr` (a `handle`) in a position whose own final value
    /// must be handed to `finish` separately on each reachable arm,
    /// instead of merging every arm's value into one shared slot first
    /// -- exactly [`Self::lower_match_into_return_sink`]'s own treatment
    /// of a `match`, applied to `handle`'s own success/failure dispatch
    /// (`rfcs/0011`, Blocker 2).
    fn lower_handle_into_return_sink(
        &mut self,
        fb: &mut FnBuilder,
        operand: &HirExpr,
        arms: &[HirHandleArm],
        hint: &Ty,
        finish: &mut dyn FnMut(&mut Self, &mut FnBuilder, ValueId) -> LowerResult<LoweredExpr>,
    ) -> LowerResult<LoweredExpr> {
        // No merge slot at all -- exactly like postfix `?`'s own
        // `lower_try` (`merge_result_ty: None`): each arm hands its own
        // value straight to `finish`, which terminates its own block
        // itself, so there is no shared value for anything to merge.
        let Some((ok_ty, ok_slot, ok_target, err_blocks, _)) =
            self.lower_invoke(fb, operand, "`handle`", None)?
        else {
            return Ok(LoweredExpr::Diverged);
        };
        self.lower_handle_dispatch(
            fb,
            arms,
            ok_ty,
            ok_slot,
            ok_target,
            err_blocks,
            Some(ArmSink::Return(hint.clone(), finish)),
            Ty::Never,
        )
    }

    /// The shared success/failure dispatch both [`Self::lower_handle`]
    /// and [`Self::lower_handle_into_return_sink`] delegate to, once
    /// each has resolved its own `sink` (a shared merge slot, or an
    /// enclosing `return`'s own per-arm sink) through
    /// [`Self::lower_invoke`] in whichever way its own caller needs.
    /// `result_ty` is only ever consulted in the `ArmSink::Merge` case
    /// (the merge slot's own final `Load`'s type) -- callers with no
    /// merge slot at all pass `Ty::Never`, which is never read.
    #[allow(clippy::too_many_arguments)]
    fn lower_handle_dispatch(
        &mut self,
        fb: &mut FnBuilder,
        arms: &[HirHandleArm],
        ok_ty: Ty,
        ok_slot: ValueId,
        ok_target: BlockId,
        err_blocks: Vec<(ItemId, ValueId, BlockId)>,
        mut sink: Option<ArmSink<'a, '_>>,
        result_ty: Ty,
    ) -> LowerResult<LoweredExpr> {
        // For every (variant, case-index) pair any raised effect
        // declares, which arm (by index into `arms`) actually covers it:
        // the first `Case` arm naming it, or else the single trailing
        // wildcard. Only ever consulted for pairs `typeck` already
        // proved are covered by exactly one of these.
        let mut case_arm: HashMap<(ItemId, usize), usize> = HashMap::new();
        let mut wildcard_arm: Option<usize> = None;
        for (i, arm) in arms.iter().enumerate() {
            match &arm.kind {
                HirHandleArmKind::Failure(HirFailurePattern::Case {
                    variant: Some(v),
                    case: Some(c),
                    ..
                }) => {
                    case_arm.entry((*v, *c)).or_insert(i);
                }
                HirHandleArmKind::Failure(HirFailurePattern::Wildcard { .. })
                    if wildcard_arm.is_none() =>
                {
                    wildcard_arm = Some(i);
                }
                _ => {}
            }
        }

        // Each failure arm's own block, built (and immediately lowered)
        // the first time any case reaches it -- a later case reaching
        // the very same arm just reuses the block already recorded here.
        let mut arm_blocks: HashMap<usize, BlockId> = HashMap::new();

        for (variant, err_slot, dispatch_block) in err_blocks {
            let Some(layout) = self.variants.get(&variant) else {
                return Err(self.internal_error("`handle` dispatches an unknown raised variant"));
            };
            let variant_name = layout.name;
            // Cloned out from under `layout` up front, so the borrow
            // doesn't linger into the loop below (which needs `&mut
            // self` to bind patterns and lower each arm's body).
            let case_payload_tys: Vec<Vec<Ty>> =
                layout.cases.iter().map(|c| c.payload.clone()).collect();
            let num_cases = case_payload_tys.len();
            fb.switch_to(dispatch_block);
            let loaded = fb.push_value(Ty::Named(variant, variant_name), ValueKind::Load(err_slot));

            let mut case_targets = Vec::with_capacity(num_cases);
            for (case_index, payload_tys) in case_payload_tys.iter().enumerate() {
                let Some(&arm_index) = case_arm
                    .get(&(variant, case_index))
                    .or(wildcard_arm.as_ref())
                else {
                    return Err(self.internal_error(&format!(
                        "`handle` has no covering arm for case {case_index} of a raised variant; typeck should have already rejected this as non-exhaustive"
                    )));
                };
                if let Some(&block) = arm_blocks.get(&arm_index) {
                    case_targets.push(block);
                    continue;
                }
                let block = fb.new_block();
                arm_blocks.insert(arm_index, block);
                case_targets.push(block);

                fb.switch_to(block);
                let HirHandleArmKind::Failure(pattern) = &arms[arm_index].kind else {
                    return Err(self.internal_error(
                        "`handle`'s failure dispatch resolved to a non-failure arm",
                    ));
                };
                if let HirFailurePattern::Case { args: payload, .. } = pattern {
                    if payload.len() != payload_tys.len() {
                        return Err(self.internal_error(&format!(
                            "failure pattern for case {case_index} of a raised variant has {} sub-pattern(s), expected {}",
                            payload.len(),
                            payload_tys.len()
                        )));
                    }
                    for (i, (pat, ty)) in payload.iter().zip(payload_tys.iter()).enumerate() {
                        let v = fb.push_value(
                            ty.clone(),
                            ValueKind::VariantPayload {
                                base: loaded,
                                variant,
                                case: case_index,
                                index: i,
                            },
                        );
                        self.bind_arm_pattern(fb, pat, v, ty)?;
                    }
                }
                let body = &arms[arm_index].body;
                let body_id = match body {
                    HirMatchArmBody::Expr(e) => e.id(),
                    HirMatchArmBody::Block(b) => b.id,
                };
                let arm_sink = sink.as_mut().map(|s| s.reborrow());
                self.lower_branch_moves(fb, |this, fb| {
                    this.lower_handle_arm_body(fb, body, arm_sink, body_id)
                })?;
                fb.switch_to(dispatch_block);
            }
            fb.terminate(Terminator::Switch {
                scrutinee: loaded,
                variant,
                cases: case_targets,
            });
        }

        fb.switch_to(ok_target);
        let ok_value = fb.push_value(ok_ty.clone(), ValueKind::Load(ok_slot));
        let Some(success_arm) = arms
            .iter()
            .find(|a| matches!(a.kind, HirHandleArmKind::Success(_)))
        else {
            return Err(self.internal_error(
                "`handle` has no success arm; typeck should have already rejected this",
            ));
        };
        let HirHandleArmKind::Success(pattern) = &success_arm.kind else {
            unreachable!("just matched Success above");
        };
        // Blocker 4: `success file => ...` owns the callee's returned
        // resource -- `resourceck` already scheduled it for cleanup, so
        // leaving the arm without moving/returning/dropping `file`
        // still destroys it exactly once instead of leaking it.
        self.bind_arm_pattern(fb, pattern, ok_value, &ok_ty)?;
        let success_body_id = match &success_arm.body {
            HirMatchArmBody::Expr(e) => e.id(),
            HirMatchArmBody::Block(b) => b.id,
        };
        let success_sink = sink.as_mut().map(|s| s.reborrow());
        self.lower_branch_moves(fb, |this, fb| {
            this.lower_handle_arm_body(fb, &success_arm.body, success_sink, success_body_id)
        })?;

        match sink {
            Some(ArmSink::Merge(slot, after)) => {
                fb.switch_to(after);
                Ok(LoweredExpr::Value(
                    fb.push_value(result_ty, ValueKind::Load(slot)),
                ))
            }
            Some(ArmSink::Return(..)) | None => Ok(LoweredExpr::Diverged),
        }
    }

    /// Binds a `success`/failure-payload pattern -- always a bare `Bind`
    /// or `Wildcard` once resolved (`typeck` rejects anything else) -- to
    /// an already-computed value. A resource-typed binding (only ever
    /// possible for a `success` pattern -- a failure payload's own type
    /// is a raised variant's case payload, which
    /// `RESOURCE_FIELD_IN_ORDINARY_AGGREGATE` already forbids from ever
    /// being affine) owns that value exactly like an ordinary `value`
    /// binding does (`rfcs/0011`, Blocker 4): scheduled for cleanup the
    /// same way, so leaving the arm without moving, returning, or
    /// explicitly dropping it still destroys it exactly once, rather
    /// than silently leaking it.
    fn bind_arm_pattern(
        &mut self,
        fb: &mut FnBuilder,
        pattern: &HirPattern,
        value: ValueId,
        value_ty: &Ty,
    ) -> LowerResult<()> {
        match pattern {
            HirPattern::Bind { local, .. } => {
                fb.local_bindings
                    .insert(*local, LocalBinding::Direct(value));
                Ok(())
            }
            // A `_` pattern names nothing a later expression could ever
            // refer to, so a resource-typed value bound this way (only
            // ever a `success` pattern -- see `bind_arm_pattern`'s own
            // doc comment) can never be moved, returned, or explicitly
            // dropped through it either. There is no local to schedule
            // ordinary cleanup for, so it is destroyed immediately,
            // right here, rather than silently discarded and leaked.
            HirPattern::Wildcard { .. } => {
                if self.is_affine(value_ty) {
                    fb.push_instruction(crate::nir::Instruction::Drop { value });
                }
                Ok(())
            }
            other => Err(self.internal_error(&format!(
                "a `handle` arm's pattern other than a bare bind or wildcard reached lowering: {other:?}"
            ))),
        }
    }

    /// Lowers one `handle`/`match` arm's body, storing its value into
    /// `merge`'s slot and branching to its block. Does nothing further
    /// when the body diverged on its own (it already replayed its own
    /// checked cleanup through whichever exit -- `return`/`raise`/
    /// `break`/`continue` -- it actually terminated through).
    /// `resourceck::flow` records this arm's own combined
    /// pattern-binding-plus-body cleanup under this exact body's own id
    /// (`body_id` -- `block.id` for a block body, the tail expression's
    /// own id for a bare one -- see `resourceck::flow::
    /// check_match_arms`/`check_handle_arms`), so a normal completion
    /// looks it up by that same id, once, right here.
    fn lower_arm_body(
        &mut self,
        fb: &mut FnBuilder,
        body: &HirMatchArmBody,
        merge: Option<(ValueId, BlockId)>,
        body_id: ExprId,
    ) -> LowerResult<()> {
        // `lower_block_value`, not `lower_scoped_block`: this arm's own
        // wider cleanup lookup below (keyed by `body_id`) already covers
        // a block body's own internal locals combined with this arm's
        // own pattern binding, exactly mirroring `resourceck::flow`'s
        // own `check_block_ctx_body` bypass -- calling the ordinary,
        // self-cleaning `lower_scoped_block` here as well would look
        // the identical `block.id` entry up (and replay it) a second
        // time.
        let result = match body {
            HirMatchArmBody::Expr(e) => self.lower_expr(fb, e)?,
            HirMatchArmBody::Block(b) => self.lower_block_value(fb, b)?,
        };
        if let LoweredExpr::Value(v) = result
            && let Some((slot, after)) = merge
        {
            self.emit_checked_cleanup(fb, body_id)?;
            // A resource-typed match/handle arm only ever reaches this
            // ordinary merge-into-slot path in an observing (`Read`)
            // context -- any consuming (`return`) context is instead
            // routed through `lower_arm_body_into_return_sink`, which
            // never allocates a merge slot at all (`rfcs/0011`).
            fb.push_store(slot, v, crate::nir::OwnershipMode::Observe);
            fb.terminate(Terminator::Branch(after));
        }
        Ok(())
    }

    /// Like [`Self::lower_arm_body`], but for a winning arm reached
    /// through [`Self::lower_match_into_return_sink`] instead of an
    /// ordinary merge-into-slot `match` (`rfcs/0011`, Blocker 2):
    /// `finish` is called directly on this arm's own value, exactly
    /// like a nested `if`-branch's own leaf already is by
    /// [`Self::lower_into_return_sink`], which this delegates straight
    /// to -- correctly recursing into a further nested `if`/`match`/
    /// block this exact arm's own body might itself be, rather than
    /// treating it as a single opaque leaf the way [`Self::
    /// lower_arm_body`]'s flat `lower_expr`/`lower_block_value` call
    /// would.
    fn lower_arm_body_into_return_sink(
        &mut self,
        fb: &mut FnBuilder,
        body: &HirMatchArmBody,
        hint: &Ty,
        finish: &mut dyn FnMut(&mut Self, &mut FnBuilder, ValueId) -> LowerResult<LoweredExpr>,
    ) -> LowerResult<LoweredExpr> {
        match body {
            HirMatchArmBody::Expr(e) => self.lower_into_return_sink(fb, e, hint, finish),
            HirMatchArmBody::Block(b) => self.lower_into_return_sink_block(fb, b, hint, finish),
        }
    }

    /// One `handle` arm's own share of [`Self::lower_handle_dispatch`]:
    /// dispatches to the ordinary merge-into-slot
    /// [`Self::lower_arm_body`] or the per-arm [`Self::
    /// lower_arm_body_into_return_sink`], whichever `sink` calls for.
    fn lower_handle_arm_body(
        &mut self,
        fb: &mut FnBuilder,
        body: &HirMatchArmBody,
        sink: Option<ArmSink<'a, '_>>,
        body_id: ExprId,
    ) -> LowerResult<()> {
        match sink {
            Some(ArmSink::Merge(slot, after)) => {
                self.lower_arm_body(fb, body, Some((slot, after)), body_id)
            }
            Some(ArmSink::Return(hint, finish)) => {
                self.lower_arm_body_into_return_sink(fb, body, &hint, finish)?;
                Ok(())
            }
            None => self.lower_arm_body(fb, body, None, body_id),
        }
    }

    /// Lowers an explicit protocol-call expression,
    /// `Protocol[Args].method(..)` (`rfcs/0009`) -- `typeck` already
    /// resolved exactly which extension (or forwarded requirement)
    /// answers this specific call (`protocol_call_evidence`); lowering
    /// only ever reads that back, never re-resolves it.
    fn lower_protocol_call(
        &mut self,
        fb: &mut FnBuilder,
        protocol: ItemId,
        arguments: &[crate::hir::HirType],
        method: usize,
        args: &[HirExpr],
        call_expr: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        let resolved_arguments: Vec<Ty> = arguments
            .iter()
            .map(|a| self.resolve_named_type(a))
            .collect();
        let mut arg_values = Vec::with_capacity(args.len());
        for arg in args {
            match self.lower_expr(fb, arg)? {
                LoweredExpr::Value(v) => arg_values.push(v),
                LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
            }
        }
        let Some(evidence) = self.protocol_call_evidence.get(&call_expr.id()).cloned() else {
            return Err(self.internal_error(
                "protocol call has no recorded call-site evidence from typeck's capability solver",
            ));
        };
        let call_ty = self.expr_ty(call_expr)?;
        Ok(LoweredExpr::Value(fb.push_value(
            call_ty,
            ValueKind::ProtocolCall {
                protocol,
                arguments: resolved_arguments,
                method,
                evidence,
                args: arg_values,
            },
        )))
    }

    fn lower_variant_construct(
        &mut self,
        fb: &mut FnBuilder,
        variant: ItemId,
        case: usize,
        args: &[HirExpr],
        call_expr: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        // A well-typed program always has a real entry here (typeck
        // already validated the variant and case); a caller that lowers
        // hand-built HIR bypassing typeck must get a structured
        // diagnostic instead of an out-of-bounds panic or a fabricated
        // payload-type hint for an unknown case.
        let (type_params, payload_tys) = match self.variants.get(&variant).and_then(|v| {
            let ids: Vec<crate::hir::TypeParamId> =
                v.type_params.iter().map(|(id, _)| *id).collect();
            v.cases.get(case).map(|c| (ids, c.payload.clone()))
        }) {
            Some(found) => found,
            None => {
                return Err(self.internal_error(&format!(
                    "variant construction references unknown variant/case ({variant:?}, {case})"
                )));
            }
        };
        // Resolved once by `typeck` and read back here, never re-inferred
        // (`rfcs/0008`) -- empty for a non-generic variant. This also
        // covers a *bare* unit-case reference (`Maybe[i64].None`, no call
        // syntax at all), which lowers through this same function.
        let type_args =
            self.resolve_call_type_args(call_expr.id(), &type_params, "a variant construction")?;
        let subst: HashMap<crate::hir::TypeParamId, Ty> = type_params
            .into_iter()
            .zip(type_args.iter().cloned())
            .collect();
        // The complete shape is validated before a single argument is
        // evaluated: too few arguments would otherwise leave `payload`
        // shorter than the case's declared arity, and too many would
        // leave it longer, either way fabricating a `variant.create`
        // whose payload count doesn't match its own declared case.
        if args.len() != payload_tys.len() {
            return Err(self.internal_error(&format!(
                "variant construction for case {case} of {variant:?} has {} argument(s), expected {}",
                args.len(),
                payload_tys.len()
            )));
        }
        let mut payload = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            // The arity check just above already guarantees `i` is in
            // range; still checked explicitly (never `Ty::Error`) rather
            // than trusted blindly.
            let Some(param_ty) = payload_tys.get(i) else {
                return Err(self.internal_error(&format!(
                    "variant construction for case {case} of {variant:?} has no declared payload type for argument {i}"
                )));
            };
            let hint = crate::types::substitute(param_ty, &subst);
            match self.lower_expr_hinted(fb, arg, &hint)? {
                LoweredExpr::Value(v) => payload.push(v),
                LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
            }
        }
        let call_ty = self.expr_ty(call_expr)?;
        Ok(LoweredExpr::Value(fb.push_value(
            call_ty,
            ValueKind::VariantCreate {
                variant,
                case,
                type_args,
                payload,
            },
        )))
    }

    /// `TypeName { field: expr, ... }`. Each field is evaluated exactly
    /// once, in **source order** (`fields` is already in that order --
    /// see `HirExpr::RecordLiteral`'s doc comment), then reordered into
    /// **declaration order** for `record.create` -- runtime layout
    /// always follows declaration order, independent of how the
    /// construction site wrote them.
    fn lower_record_literal(
        &mut self,
        fb: &mut FnBuilder,
        record: ItemId,
        fields: &[HirFieldInit],
        literal_expr: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        // typeck/hir::lower already reject a source-level unknown
        // record, out-of-range/duplicate field index, or missing field;
        // reaching any of these means a caller lowered a
        // HirExpr::RecordLiteral built by hand (or otherwise bypassing
        // those checks). The complete shape is validated up front,
        // before a single field is evaluated, so lowering never
        // silently drops an out-of-range field into nowhere or lets a
        // duplicate index overwrite an earlier field's already-lowered
        // value in its temporary slot -- either would fabricate a
        // `record.create` that doesn't reflect what was actually
        // written.
        let Some(layout) = self.records.get(&record) else {
            return Err(self.internal_error(&format!(
                "record construction references unknown record {record:?}"
            )));
        };
        let field_count = layout.fields.len();
        let mut seen = vec![false; field_count];
        for f in fields {
            let Some(slot_seen) = seen.get_mut(f.field_index) else {
                return Err(self.internal_error(&format!(
                    "record construction's field index {} is out of range for {record:?}'s {field_count} declared field(s)",
                    f.field_index
                )));
            };
            if *slot_seen {
                return Err(self.internal_error(&format!(
                    "record construction reuses field index {} more than once",
                    f.field_index
                )));
            }
            *slot_seen = true;
        }
        if let Some(missing) = seen.iter().position(|&s| !s) {
            return Err(
                self.internal_error(&format!("record construction is missing field {missing}"))
            );
        }

        // Resolved once by `typeck` and read back here, never re-inferred
        // (`rfcs/0008`) -- empty for a non-generic record. Generic record
        // construction always supplies this explicitly (`Box[i64] { .. }`),
        // so it is never itself inferred the way a call's can be.
        let type_params: Vec<crate::hir::TypeParamId> = self.records[&record]
            .type_params
            .iter()
            .map(|(id, _)| *id)
            .collect();
        let type_args =
            self.resolve_call_type_args(literal_expr.id(), &type_params, "a record construction")?;
        let subst: HashMap<crate::hir::TypeParamId, Ty> = type_params
            .into_iter()
            .zip(type_args.iter().cloned())
            .collect();

        let mut by_index: Vec<Option<ValueId>> = vec![None; field_count];
        for f in fields {
            let declared = self.records[&record].fields[f.field_index].1.clone();
            let hint = crate::types::substitute(&declared, &subst);
            match self.lower_expr_hinted(fb, &f.value, &hint)? {
                LoweredExpr::Value(v) => {
                    by_index[f.field_index] = Some(v);
                    // A resource-typed field is rejected outright at its
                    // own containing aggregate's declaration
                    // (`RESOURCE_FIELD_IN_ORDINARY_AGGREGATE`, T0064),
                    // so no well-typed program ever reaches this point
                    // with an affine `f.value` at all.
                }
                // A diverging initializer means the whole construction
                // never completes; no field written after it in source
                // order is lowered as reachable work.
                LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
            }
        }
        let ordered: Vec<ValueId> = by_index
            .into_iter()
            .map(|v| v.expect("every index was already proven present above"))
            .collect();
        let literal_ty = self.expr_ty(literal_expr)?;
        Ok(LoweredExpr::Value(fb.push_value(
            literal_ty,
            ValueKind::RecordCreate(record, type_args, ordered),
        )))
    }

    fn lower_field(
        &mut self,
        fb: &mut FnBuilder,
        base: &HirExpr,
        name: Symbol,
        field_expr: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        // An affine field access (`rfcs/0012`, lifting Alpha 0.1.7's
        // blanket rejection of a resource-typed field in any aggregate)
        // is lowered as a structural place read, never an eager
        // whole-base evaluation plus `RecordField`: `base` is walked
        // through `resolve_place_expr` itself (never `lower_expr(base)`
        // first), so an intermediate `Field` in the chain is never
        // treated as a whole-value read of its own base -- reading
        // through an already-partially-moved intermediate aggregate
        // (`session.output` after `session.input` was moved) must stay
        // valid. `resourceck` already proved `base` resolves to a
        // stable place whenever this field's own type is affine and the
        // program is valid at all (a temporary would already have been
        // rejected there as a leak) -- an unresolvable place here is
        // therefore always a structural mismatch, not a case to fall
        // back silently from.
        let field_ty = self.expr_ty(field_expr)?;
        if self.is_affine(&field_ty) {
            let Some(place) = self.resolve_place_expr(field_expr)? else {
                return Err(self.internal_error(
                    "an affine field access has no resolvable structural place, but resourceck \
                     already accepted this program",
                ));
            };
            let (nir_place, ty) = self.resolve_nir_place(fb, &place)?;
            let mode = self.field_read_mode(field_expr.id());
            return Ok(LoweredExpr::Value(fb.push_value(
                ty,
                ValueKind::PlaceRead {
                    place: nir_place,
                    mode,
                },
            )));
        }
        let base_value = match self.lower_expr(fb, base)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        let base_ty = self.expr_ty(base)?;
        // A generic record's own body (e.g. `unwrap[T](box: Box[T]) ->
        // T { box.value }`) accesses a field whose base is symbolically
        // typed `Box[T]` (`Ty::Applied`), never `Ty::Named` -- checked
        // once, symbolically, the same way every other operation on an
        // unconstrained type parameter is (`rfcs/0008`). Field lookup
        // itself only ever needs the declaration's own (unsubstituted)
        // field list, never the concrete/symbolic arguments, so both
        // forms resolve identically here.
        let record = match base_ty {
            Ty::Named(record, _) => record,
            Ty::Applied(record, _) => record,
            _ => {
                return Err(
                    self.unsupported(field_expr.span(), "field access on a non-record type")
                );
            }
        };
        let field_index = self
            .records
            .get(&record)
            .and_then(|r| r.fields.iter().position(|(n, _)| *n == name))
            .ok_or_else(|| {
                self.unsupported(field_expr.span(), "field access on an unknown field")
            })?;
        Ok(LoweredExpr::Value(fb.push_value(
            field_ty,
            ValueKind::RecordField {
                base: base_value,
                record,
                field: field_index,
            },
        )))
    }

    fn lower_if(
        &mut self,
        fb: &mut FnBuilder,
        condition: &HirExpr,
        then_branch: &HirBlock,
        else_branch: &Option<HirElse>,
        result_ty: Ty,
    ) -> LowerResult<LoweredExpr> {
        let cond_value = match self.lower_expr(fb, condition)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };

        let then_block = fb.new_block();
        let else_block = fb.new_block();

        // `result_ty` is typeck's already-resolved never-join of both
        // branches (spec/0003): the condition itself already produced a
        // real value above, so the only way this whole `if` can be
        // `never` is if both branches diverge. When that's the case
        // there is nothing to merge -- no result slot and no
        // `after_block` are ever created, since each branch's own
        // terminator (whatever `return`/nested-diverging-`if` it
        // lowers to) already leaves a complete, valid CFG on its own.
        if result_ty == Ty::Never {
            fb.terminate(Terminator::CondBranch {
                condition: cond_value,
                then_block,
                else_block,
            });

            fb.switch_to(then_block);
            let then_result =
                self.lower_branch_moves(fb, |this, fb| this.lower_scoped_block(fb, then_branch))?;

            fb.switch_to(else_block);
            let else_result = self.lower_branch_moves(fb, |this, fb| match else_branch {
                Some(HirElse::Block(b)) => this.lower_scoped_block(fb, b),
                Some(HirElse::If(inner)) => this.lower_expr(fb, inner),
                // An else-less `if` always types as `unit` in the
                // ordinary pipeline (see below), never `never` -- but
                // `expr_types` is caller-supplied data a direct caller
                // hand-building HIR controls directly, and could name
                // an else-less `if` as `Ty::Never` with no HIR-level
                // else branch to actually justify it.
                None => Err(this.internal_error(
                    "an else-less `if` was typed as `never`, which requires a diverging else \
                     branch that does not exist",
                )),
            })?;
            debug_assert!(
                matches!(then_result, LoweredExpr::Diverged)
                    && matches!(else_result, LoweredExpr::Diverged),
                "internal invariant: typeck reported this `if` as `never`, so both branches \
                 must diverge"
            );
            return Ok(LoweredExpr::Diverged);
        }

        // At least one branch is required to produce a real value of
        // `result_ty` here (typeck already ruled out "both diverge"
        // above). The slot and merge block belong to whichever block
        // is current before the branch -- allocating the slot here
        // both keeps it dominating both `then_block` and `else_block`
        // (required by the verifier) and keeps every instruction
        // belonging to this block emitted before it acquires its
        // terminator (spec/0006): nothing may be appended afterward.
        let result_slot = fb.alloc_slot(result_ty.clone());
        let after_block = fb.new_block();
        fb.terminate(Terminator::CondBranch {
            condition: cond_value,
            then_block,
            else_block,
        });

        fb.switch_to(then_block);
        if let LoweredExpr::Value(then_value) =
            self.lower_branch_moves(fb, |this, fb| this.lower_scoped_block(fb, then_branch))?
        {
            if else_branch.is_none() {
                // No `else`: typeck gives the whole expression type
                // `unit` regardless of what the then-branch's own tail
                // expression resolves to (spec/0002 -- an `if` without
                // `else` is never used for its value), so the
                // then-branch's real value (whatever type it has) is
                // evaluated for its side effects and then discarded.
                // Storing it into `result_slot` here -- which is always
                // declared `unit` on this path -- would store a value
                // of the wrong type into it.
                let _ = then_value;
                let unit_value = fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit));
                fb.push_store(result_slot, unit_value, crate::nir::OwnershipMode::Observe);
            } else {
                // A resource-typed `if` only ever reaches this ordinary
                // merge-into-slot path in an observing (`Read`) context
                // -- any consuming (`return`) context is instead routed
                // through `lower_into_return_sink`, which never
                // allocates a merge slot at all (`rfcs/0011`).
                fb.push_store(result_slot, then_value, crate::nir::OwnershipMode::Observe);
            }
            fb.terminate(Terminator::Branch(after_block));
        }

        fb.switch_to(else_block);
        match else_branch {
            Some(HirElse::Block(b)) => {
                if let LoweredExpr::Value(else_value) =
                    self.lower_branch_moves(fb, |this, fb| this.lower_scoped_block(fb, b))?
                {
                    fb.push_store(result_slot, else_value, crate::nir::OwnershipMode::Observe);
                    fb.terminate(Terminator::Branch(after_block));
                }
            }
            Some(HirElse::If(inner)) => {
                if let LoweredExpr::Value(else_value) =
                    self.lower_branch_moves(fb, |this, fb| this.lower_expr(fb, inner))?
                {
                    fb.push_store(result_slot, else_value, crate::nir::OwnershipMode::Observe);
                    fb.terminate(Terminator::Branch(after_block));
                }
            }
            None => {
                self.lower_branch_moves(fb, |_, fb| {
                    let unit_value = fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit));
                    fb.push_store(result_slot, unit_value, crate::nir::OwnershipMode::Observe);
                    fb.terminate(Terminator::Branch(after_block));
                    Ok(())
                })?;
            }
        }

        fb.switch_to(after_block);
        Ok(LoweredExpr::Value(
            fb.push_value(result_ty, ValueKind::Load(result_slot)),
        ))
    }

    // ---- match lowering: a decision tree over a pattern matrix ----
    //
    // Mirrors the same recursive specialize/default structure
    // `typeck::exhaustive` uses for its analysis (see RFC 0005's "Match
    // lowering"), but building real NIR blocks instead of checking
    // coverage. A "row" carries one pattern slot per currently pending
    // occurrence (the original scrutinee, plus one fresh occurrence per
    // payload position introduced by descending into a `Variant`
    // pattern) -- `PatternSlot::Wildcard` pads a row that doesn't
    // itself constrain a newly-introduced occurrence (a wildcard/
    // binding/unit-case row matches every payload position trivially),
    // keeping every row in one matrix the same length.

    fn lower_match(
        &mut self,
        fb: &mut FnBuilder,
        scrutinee: &HirExpr,
        arms: &[HirMatchArm],
        result_ty: Ty,
    ) -> LowerResult<LoweredExpr> {
        let scrutinee_value = match self.lower_expr(fb, scrutinee)? {
            LoweredExpr::Value(v) => v,
            // A diverging scrutinee is evaluated exactly once, before
            // any pattern could ever be tested -- the whole match is
            // `never`, and no arm is lowered as reachable work.
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        let scrutinee_ty = self.expr_ty(scrutinee)?;

        let rows: Vec<MatrixRow> = arms
            .iter()
            .enumerate()
            .map(|(i, arm)| MatrixRow {
                arm_index: i,
                patterns: vec![PatternSlot::Real(&arm.pattern)],
                bindings: Vec::new(),
                discarded: Vec::new(),
            })
            .collect();
        let occurrences = vec![Occurrence {
            value: scrutinee_value,
            ty: scrutinee_ty,
        }];

        if result_ty == Ty::Never {
            // Every arm diverges (typeck already proved this); no
            // result slot or merge block is ever created -- each arm's
            // own terminator is already a complete CFG on its own.
            self.lower_decision(fb, rows, occurrences, arms, None, 0)?;
            return Ok(LoweredExpr::Diverged);
        }

        // The slot and merge block belong to the block current before
        // any branching starts, so they dominate every arm -- the same
        // discipline `lower_if` already uses for its own result slot.
        let result_slot = fb.alloc_slot(result_ty.clone());
        let after_block = fb.new_block();
        self.lower_decision(
            fb,
            rows,
            occurrences,
            arms,
            Some(ArmSink::Merge(result_slot, after_block)),
            0,
        )?;

        fb.switch_to(after_block);
        Ok(LoweredExpr::Value(
            fb.push_value(result_ty, ValueKind::Load(result_slot)),
        ))
    }

    /// Lowers `expr` (a `match`) in a position whose own final value
    /// must be handed to `finish` separately on each reachable winning
    /// arm, instead of merging every arm's value into one shared slot
    /// first -- exactly `Lowering::lower_into_return_sink`'s own
    /// treatment of a nested `if`, generalized to a `match`'s own
    /// decision tree (`rfcs/0011`, Blocker 2).
    fn lower_match_into_return_sink(
        &mut self,
        fb: &mut FnBuilder,
        scrutinee: &HirExpr,
        arms: &[HirMatchArm],
        hint: &Ty,
        finish: &mut dyn FnMut(&mut Self, &mut FnBuilder, ValueId) -> LowerResult<LoweredExpr>,
    ) -> LowerResult<LoweredExpr> {
        let scrutinee_value = match self.lower_expr(fb, scrutinee)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        let scrutinee_ty = self.expr_ty(scrutinee)?;

        let rows: Vec<MatrixRow> = arms
            .iter()
            .enumerate()
            .map(|(i, arm)| MatrixRow {
                arm_index: i,
                patterns: vec![PatternSlot::Real(&arm.pattern)],
                bindings: Vec::new(),
                discarded: Vec::new(),
            })
            .collect();
        let occurrences = vec![Occurrence {
            value: scrutinee_value,
            ty: scrutinee_ty,
        }];
        self.lower_decision(
            fb,
            rows,
            occurrences,
            arms,
            Some(ArmSink::Return(hint.clone(), finish)),
            0,
        )?;
        Ok(LoweredExpr::Diverged)
    }

    fn lower_decision<'h>(
        &mut self,
        fb: &mut FnBuilder,
        rows: Vec<MatrixRow<'h>>,
        occurrences: Vec<Occurrence>,
        arms: &'h [HirMatchArm],
        sink: Option<ArmSink<'a, '_>>,
        depth: usize,
    ) -> LowerResult<()> {
        // Each round trip through lower_decision and one of
        // lower_bool_switch/lower_variant_switch/lower_literal_chain
        // consumes exactly one occurrence position -- one nesting
        // level of the pattern(s) being decided between -- on this
        // pass's own native call stack. typeck's check_pattern already
        // keeps every pattern the normal pipeline produces shallow
        // enough that this can never fire there, but lower_module is a
        // public entry point a direct caller can invoke with hand-built
        // HIR bypassing typeck entirely, so this needs its own
        // independent bound too, matching hir::lower_pattern's and
        // typeck::is_useful's -- all sharing crate::limits::MAX_PATTERN_DEPTH.
        if depth > MAX_PATTERN_DEPTH {
            return Err(self.internal_error("match decision tree is nested too deeply to lower"));
        }
        if occurrences.is_empty() {
            let Some(winner) = rows.first() else {
                return Err(self.internal_error(
                    "a match's decision tree ran out of candidate arms with no winner",
                ));
            };
            for (local, value) in &winner.bindings {
                fb.local_bindings
                    .insert(*local, LocalBinding::Direct(*value));
            }
            // Every affine payload position this winning row left
            // unclaimed is destroyed right here, before the arm body
            // runs (`rfcs/0012`) -- in *reverse* of the order the
            // decision tree consumed them, which is exactly reverse
            // payload declaration order. Emitting it here, rather than
            // on each way out of the body, is what makes it correct for
            // an arm that returns, raises, propagates with `?`, handles,
            // breaks, or continues without enumerating any of them: by
            // the time the body starts, the discarded payload is
            // already gone, and nothing could have observed it (it was
            // matched by `_`, so it has no name).
            for occ in winner.discarded.iter().rev() {
                if self.is_affine(&occ.ty) {
                    fb.push_instruction(crate::nir::Instruction::Drop { value: occ.value });
                }
            }
            let arm = &arms[winner.arm_index];
            let body_id = match &arm.body {
                HirMatchArmBody::Expr(e) => e.id(),
                HirMatchArmBody::Block(b) => b.id,
            };
            match sink {
                Some(ArmSink::Merge(slot, after)) => {
                    self.lower_branch_moves(fb, |this, fb| {
                        this.lower_arm_body(fb, &arm.body, Some((slot, after)), body_id)
                    })?;
                }
                Some(ArmSink::Return(hint, finish)) => {
                    self.lower_branch_moves(fb, |this, fb| {
                        this.lower_arm_body_into_return_sink(fb, &arm.body, &hint, finish)
                    })?;
                }
                None => {
                    self.lower_branch_moves(fb, |this, fb| {
                        this.lower_arm_body(fb, &arm.body, None, body_id)
                    })?;
                }
            }
            return Ok(());
        }

        // A generic variant's scrutinee/occurrence is `Ty::Applied`, not
        // `Ty::Named` -- `Maybe[bool]` must still dispatch to the same
        // variant-switch lowering a non-generic variant's `Ty::Named`
        // does, or it falls through to the literal chain below and
        // fails the instant it meets its first `Some`/`None` pattern
        // (`rfcs/0008`).
        let scrutinee_variant = match &occurrences[0].ty {
            Ty::Named(item, _) | Ty::Applied(item, _) => Some(*item),
            _ => None,
        };
        if scrutinee_variant.is_some_and(|item| self.variants.contains_key(&item)) {
            self.lower_variant_switch(fb, rows, occurrences, arms, sink, depth)
        } else if matches!(&occurrences[0].ty, Ty::Bool) {
            // `bool` is a closed two-constructor domain (like a
            // variant's finite case set), so it is switched on
            // directly rather than through the open-domain literal
            // chain below -- an exhaustive `match true { true => ..,
            // false => .. }` (no wildcard at all) would otherwise have
            // no catch-all to terminate that chain's recursion on.
            self.lower_bool_switch(fb, rows, occurrences, arms, sink, depth)
        } else {
            self.lower_literal_chain(fb, rows, occurrences, arms, sink, depth)
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_bool_switch<'h>(
        &mut self,
        fb: &mut FnBuilder,
        rows: Vec<MatrixRow<'h>>,
        occurrences: Vec<Occurrence>,
        arms: &'h [HirMatchArm],
        mut sink: Option<ArmSink<'a, '_>>,
        depth: usize,
    ) -> LowerResult<()> {
        let occ = occurrences[0].clone();
        let rest_occ = occurrences[1..].to_vec();

        let any_real_test = rows.iter().any(|r| {
            matches!(
                self.classify(&r.patterns[0]),
                Classified::Literal(LiteralTest::Bool(_))
            )
        });
        if !any_real_test {
            let mut new_rows = Vec::with_capacity(rows.len());
            for r in rows {
                let mut bindings = r.bindings;
                let mut discarded = r.discarded;
                match self.classify(&r.patterns[0]) {
                    Classified::Bind(local) => bindings.push((local, occ.value)),
                    _ => discard_unclaimed(&mut discarded, &r.patterns[0], &occ),
                }
                new_rows.push(MatrixRow {
                    arm_index: r.arm_index,
                    patterns: r.patterns[1..].to_vec(),
                    bindings,
                    discarded,
                });
            }
            return self.lower_decision(fb, new_rows, rest_occ, arms, sink, depth + 1);
        }

        let then_block = fb.new_block();
        let else_block = fb.new_block();
        fb.terminate(Terminator::CondBranch {
            condition: occ.value,
            then_block,
            else_block,
        });

        for (value, block) in [(true, then_block), (false, else_block)] {
            fb.switch_to(block);
            let mut new_rows = Vec::new();
            for r in &rows {
                match self.classify(&r.patterns[0]) {
                    Classified::Literal(LiteralTest::Bool(b)) if b == value => {
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns: r.patterns[1..].to_vec(),
                            bindings: r.bindings.clone(),
                            discarded: r.discarded.clone(),
                        });
                    }
                    Classified::Literal(LiteralTest::Bool(_)) => {}
                    Classified::Bind(local) => {
                        let mut bindings = r.bindings.clone();
                        bindings.push((local, occ.value));
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns: r.patterns[1..].to_vec(),
                            bindings,
                            discarded: r.discarded.clone(),
                        });
                    }
                    Classified::Wildcard => {
                        let mut discarded = r.discarded.clone();
                        discard_unclaimed(&mut discarded, &r.patterns[0], &occ);
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns: r.patterns[1..].to_vec(),
                            bindings: r.bindings.clone(),
                            discarded,
                        });
                    }
                    _ => {}
                }
            }
            if new_rows.is_empty() {
                return Err(
                    self.internal_error("a match's bool switch left a branch with no covering arm")
                );
            }
            self.lower_decision(
                fb,
                new_rows,
                rest_occ.clone(),
                arms,
                sink.as_mut().map(|s| s.reborrow()),
                depth + 1,
            )?;
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_variant_switch<'h>(
        &mut self,
        fb: &mut FnBuilder,
        rows: Vec<MatrixRow<'h>>,
        occurrences: Vec<Occurrence>,
        arms: &'h [HirMatchArm],
        mut sink: Option<ArmSink<'a, '_>>,
        depth: usize,
    ) -> LowerResult<()> {
        let occ = occurrences[0].clone();
        let rest_occ = occurrences[1..].to_vec();
        let (variant_item, concrete_args): (ItemId, Vec<Ty>) = match occ.ty.clone() {
            Ty::Named(item, _) => (item, Vec::new()),
            Ty::Applied(item, args) => (item, args),
            _ => return Err(self.internal_error("expected a variant-typed occurrence")),
        };
        let payload_subst: HashMap<crate::hir::TypeParamId, Ty> = self
            .variants
            .get(&variant_item)
            .map(|v| v.type_params.iter().map(|(id, _)| *id).collect::<Vec<_>>())
            .into_iter()
            .flatten()
            .zip(concrete_args.iter().cloned())
            .collect();

        let any_real_test = rows
            .iter()
            .any(|r| matches!(self.classify(&r.patterns[0]), Classified::Case { .. }));
        if !any_real_test {
            // This occurrence is never decomposed: no case block, no
            // payload extraction. A row that binds it owns the whole
            // value; a row that merely wildcards it owns it too --
            // nothing else will ever destroy it -- so it is discarded
            // here as one opaque whole (the interpreter's own
            // structural drop then destroys whichever case turns out to
            // be live, `rfcs/0012`).
            let mut new_rows = Vec::with_capacity(rows.len());
            for r in rows {
                let mut bindings = r.bindings;
                let mut discarded = r.discarded;
                match self.classify(&r.patterns[0]) {
                    Classified::Bind(local) => bindings.push((local, occ.value)),
                    _ => discard_unclaimed(&mut discarded, &r.patterns[0], &occ),
                }
                new_rows.push(MatrixRow {
                    arm_index: r.arm_index,
                    patterns: r.patterns[1..].to_vec(),
                    bindings,
                    discarded,
                });
            }
            return self.lower_decision(fb, new_rows, rest_occ, arms, sink, depth + 1);
        }

        let num_cases = self
            .variants
            .get(&variant_item)
            .map(|v| v.cases.len())
            .unwrap_or(0);
        let case_blocks: Vec<BlockId> = (0..num_cases).map(|_| fb.new_block()).collect();
        fb.terminate(Terminator::Switch {
            scrutinee: occ.value,
            variant: variant_item,
            cases: case_blocks.clone(),
        });

        for (case_index, case_block) in case_blocks.iter().enumerate() {
            fb.switch_to(*case_block);
            // The declaration's own *symbolic* payload shape (may
            // contain `Ty::Param`), substituted with this occurrence's
            // own concrete type arguments before use -- otherwise a
            // `Some[T]` payload's sub-occurrence would keep the
            // unconstrained `Ty::Param(T)` as its own type, and the next
            // `lower_decision` call would fail to recognize it as e.g.
            // `bool` and route it to the wrong lowering strategy
            // (`rfcs/0008`).
            let payload_types: Vec<Ty> = self.variants[&variant_item].cases[case_index]
                .payload
                .iter()
                .map(|t| crate::types::substitute(t, &payload_subst))
                .collect();
            let arity = payload_types.len();

            let mut new_rows: Vec<MatrixRow<'h>> = Vec::new();
            for r in &rows {
                let rest: Vec<PatternSlot<'h>> = r.patterns[1..].to_vec();
                match self.classify(&r.patterns[0]) {
                    Classified::Case {
                        variant,
                        case,
                        args,
                    } if variant == variant_item && case == case_index => {
                        // typeck's check_pattern (fix for malformed
                        // variant-pattern arity) already rejects an
                        // args-count/declared-arity mismatch before the
                        // normal pipeline ever reaches lowering -- but a
                        // caller that hand-builds HIR and calls this
                        // module directly could still hand it one.
                        // `Vec::resize` would otherwise silently
                        // truncate extra sub-patterns (arity too small)
                        // or accept too few as if the rest were
                        // wildcards (arity too large), fabricating a
                        // decision tree that doesn't match what was
                        // actually written; a structured diagnostic is
                        // required instead, matching this function's
                        // existing unknown-case check just above.
                        if args.len() != arity {
                            return Err(self.internal_error(&format!(
                                "variant pattern for case {case_index} of {variant_item:?} has {} sub-pattern(s), expected {arity}",
                                args.len()
                            )));
                        }
                        let mut patterns: Vec<PatternSlot<'h>> =
                            args.iter().map(PatternSlot::Real).collect();
                        patterns.extend(rest);
                        // The occurrence itself is decomposed here, so
                        // it is *not* discarded: its own payload
                        // positions inherit the obligation, each one
                        // individually.
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns,
                            bindings: r.bindings.clone(),
                            discarded: r.discarded.clone(),
                        });
                    }
                    Classified::Case { .. } => {}
                    Classified::Bind(local) => {
                        let mut bindings = r.bindings.clone();
                        bindings.push((local, occ.value));
                        // The binding owns the whole variant value --
                        // payload included -- so these synthesized
                        // slots are `Owned`, never discardable: the
                        // binding's own scope cleanup already destroys
                        // everything reachable through it.
                        let mut patterns = vec![PatternSlot::Owned; arity];
                        patterns.extend(rest);
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns,
                            bindings,
                            discarded: r.discarded.clone(),
                        });
                    }
                    Classified::Wildcard => {
                        // An unclaimed occurrence that *is* decomposed
                        // hands its obligation down to its own payload
                        // positions; one an ancestor binding already
                        // owns keeps handing that ownership down
                        // instead.
                        let slot = if matches!(r.patterns[0], PatternSlot::Owned) {
                            PatternSlot::Owned
                        } else {
                            PatternSlot::Wildcard
                        };
                        let mut patterns = vec![slot; arity];
                        patterns.extend(rest);
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns,
                            bindings: r.bindings.clone(),
                            discarded: r.discarded.clone(),
                        });
                    }
                    // A literal pattern against a variant-typed
                    // occurrence is rejected by typeck (T0021,
                    // incompatible pattern) before lowering ever runs
                    // in the normal pipeline; excluded here rather than
                    // panicking, matching this module's defense-in-depth
                    // posture for a direct caller that bypasses typeck.
                    Classified::Literal(_) => {}
                }
            }
            if new_rows.is_empty() {
                return Err(self.internal_error(
                    "a match's decision tree left a variant case with no covering arm",
                ));
            }

            let mut payload_occurrences = Vec::with_capacity(arity);
            for (i, ty) in payload_types.iter().enumerate() {
                let v = fb.push_value(
                    ty.clone(),
                    ValueKind::VariantPayload {
                        base: occ.value,
                        variant: variant_item,
                        case: case_index,
                        index: i,
                    },
                );
                payload_occurrences.push(Occurrence {
                    value: v,
                    ty: ty.clone(),
                });
            }

            let mut new_occurrences = payload_occurrences;
            new_occurrences.extend(rest_occ.clone());
            self.lower_decision(
                fb,
                new_rows,
                new_occurrences,
                arms,
                sink.as_mut().map(|s| s.reborrow()),
                depth + 1,
            )?;
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_literal_chain<'h>(
        &mut self,
        fb: &mut FnBuilder,
        rows: Vec<MatrixRow<'h>>,
        occurrences: Vec<Occurrence>,
        arms: &'h [HirMatchArm],
        mut sink: Option<ArmSink<'a, '_>>,
        depth: usize,
    ) -> LowerResult<()> {
        let occ = occurrences[0].clone();
        let rest_occ = occurrences[1..].to_vec();

        let Some(first) = rows.first() else {
            return Err(self.internal_error("a match's literal chain ran out of candidate arms"));
        };
        match self.classify(&first.patterns[0]) {
            Classified::Wildcard => {
                let mut discarded = first.discarded.clone();
                discard_unclaimed(&mut discarded, &first.patterns[0], &occ);
                let new_rows = vec![MatrixRow {
                    arm_index: first.arm_index,
                    patterns: first.patterns[1..].to_vec(),
                    bindings: first.bindings.clone(),
                    discarded,
                }];
                self.lower_decision(fb, new_rows, rest_occ, arms, sink, depth + 1)
            }
            Classified::Bind(local) => {
                let mut bindings = first.bindings.clone();
                bindings.push((local, occ.value));
                let new_rows = vec![MatrixRow {
                    arm_index: first.arm_index,
                    patterns: first.patterns[1..].to_vec(),
                    bindings,
                    discarded: first.discarded.clone(),
                }];
                self.lower_decision(fb, new_rows, rest_occ, arms, sink, depth + 1)
            }
            Classified::Literal(lit) => {
                let const_value = literal_const(fb, &lit, &occ.ty);
                let eq = fb.push_value(Ty::Bool, ValueKind::Eq(occ.value, const_value));
                let then_block = fb.new_block();
                let else_block = fb.new_block();
                fb.terminate(Terminator::CondBranch {
                    condition: eq,
                    then_block,
                    else_block,
                });

                let mut then_rows = Vec::new();
                for r in &rows {
                    match self.classify(&r.patterns[0]) {
                        Classified::Literal(l2) if literal_eq(&lit, &l2) => {
                            then_rows.push(MatrixRow {
                                arm_index: r.arm_index,
                                patterns: r.patterns[1..].to_vec(),
                                bindings: r.bindings.clone(),
                                discarded: r.discarded.clone(),
                            });
                        }
                        Classified::Wildcard => {
                            let mut discarded = r.discarded.clone();
                            discard_unclaimed(&mut discarded, &r.patterns[0], &occ);
                            then_rows.push(MatrixRow {
                                arm_index: r.arm_index,
                                patterns: r.patterns[1..].to_vec(),
                                bindings: r.bindings.clone(),
                                discarded,
                            });
                        }
                        Classified::Bind(local) => {
                            let mut bindings = r.bindings.clone();
                            bindings.push((local, occ.value));
                            then_rows.push(MatrixRow {
                                arm_index: r.arm_index,
                                patterns: r.patterns[1..].to_vec(),
                                bindings,
                                discarded: r.discarded.clone(),
                            });
                        }
                        _ => {}
                    }
                }
                fb.switch_to(then_block);
                self.lower_decision(
                    fb,
                    then_rows,
                    rest_occ.clone(),
                    arms,
                    sink.as_mut().map(|s| s.reborrow()),
                    depth + 1,
                )?;

                let else_rows: Vec<MatrixRow<'h>> = rows
                    .into_iter()
                    .filter(|r| {
                        !matches!(self.classify(&r.patterns[0]), Classified::Literal(l2) if literal_eq(&lit, &l2))
                    })
                    .collect();
                fb.switch_to(else_block);
                if else_rows.is_empty() {
                    return Err(self.internal_error(
                        "a match's literal chain ran out of rows without a catch-all",
                    ));
                }
                let mut all_occ = vec![occ];
                all_occ.extend(rest_occ);
                self.lower_decision(fb, else_rows, all_occ, arms, sink, depth + 1)
            }
            Classified::Case { .. } => Err(self
                .internal_error("a variant pattern was tested against a non-variant occurrence")),
        }
    }

    fn classify<'h>(&self, slot: &PatternSlot<'h>) -> Classified<'h> {
        let pattern = match slot {
            PatternSlot::Wildcard | PatternSlot::Owned => return Classified::Wildcard,
            PatternSlot::Real(p) => *p,
        };
        match pattern {
            HirPattern::Wildcard { .. } => Classified::Wildcard,
            HirPattern::Bind { id, local, .. } => match self.pattern_case.get(id) {
                Some(&(variant, case)) => Classified::Case {
                    variant,
                    case,
                    args: &[],
                },
                None => Classified::Bind(*local),
            },
            HirPattern::Variant { id, args, .. } => match self.pattern_case.get(id) {
                Some(&(variant, case)) => Classified::Case {
                    variant,
                    case,
                    args,
                },
                // Unresolved (typeck-unreachable for a valid program):
                // treated as matching nothing, defensively.
                None => Classified::Case {
                    variant: ItemId(u32::MAX),
                    case: usize::MAX,
                    args,
                },
            },
            HirPattern::Int { value, .. } => Classified::Literal(LiteralTest::Int(*value)),
            HirPattern::Str { value, .. } => Classified::Literal(LiteralTest::Str(value)),
            HirPattern::Char { value, .. } => Classified::Literal(LiteralTest::Char(*value)),
            HirPattern::Bool { value, .. } => Classified::Literal(LiteralTest::Bool(*value)),
        }
    }

    fn internal_error(&self, message: &str) -> Box<Diagnostic> {
        Box::new(Diagnostic::error(
            codes::INTERNAL_INVARIANT_VIOLATED,
            self.source,
            Span::dummy(),
            message.to_string(),
        ))
    }

    /// Reads a callee's own already-resolved signature -- shared by
    /// `lower_call` and `lower_invoke` so the two can never drift into
    /// different fallback behavior for the same missing-metadata case.
    /// Every function/extend method this module's own upfront pass in
    /// `lower_module` actually processed always has an entry here, even
    /// one declaring no type parameters (an empty `Vec`, a legitimate,
    /// already-`Some` value, never confused with a missing entry) --
    /// a missing entry can only mean `item` names a function this
    /// module never itself resolved a signature for at all (a direct
    /// caller's hand-built HIR referencing a nonexistent/foreign
    /// function), which must fail atomically with a structured
    /// diagnostic rather than silently fabricating an empty signature
    /// returning `Ty::Error`.
    #[allow(clippy::type_complexity)]
    fn lookup_function_sig(
        &self,
        item: ItemId,
        context: &str,
    ) -> LowerResult<(Vec<crate::hir::TypeParamId>, Vec<Ty>, Ty)> {
        self.function_sigs.get(&item).cloned().ok_or_else(|| {
            self.internal_error(&format!(
                "{context} targets a function this module never resolved a signature for"
            ))
        })
    }

    /// See [`Self::lookup_function_sig`]'s own doc comment -- same
    /// missing-vs-legitimately-empty distinction, for a callee's own
    /// capability requirements (`rfcs/0009`).
    fn lookup_function_requirements(
        &self,
        item: ItemId,
        context: &str,
    ) -> LowerResult<Vec<CapabilityRequirement>> {
        self.function_requirements
            .get(&item)
            .cloned()
            .ok_or_else(|| {
                self.internal_error(&format!(
                    "{context} targets a function this module never resolved capability requirements for"
                ))
            })
    }

    /// See [`Self::lookup_function_sig`]'s own doc comment -- same
    /// missing-vs-legitimately-empty distinction, for a callee's own
    /// declared raised-effect set (`rfcs/0010`). Only `lower_invoke`
    /// needs this: an ordinary `Call`'s own callee is never fallible, so
    /// `lower_call` never looks its `raises` up at all.
    fn lookup_function_raises(&self, item: ItemId, context: &str) -> LowerResult<Vec<ItemId>> {
        self.function_raises.get(&item).cloned().ok_or_else(|| {
            self.internal_error(&format!(
                "{context} targets a function this module never resolved a raised-effect set for"
            ))
        })
    }

    /// Looks up `resourceck`'s own checked observe-vs-transfer decision
    /// for the exact expression `id` names (`rfcs/0011`) -- a call/
    /// `Invoke` argument, a binding's own initializer, or an
    /// assignment's own value. Always `false` for a non-affine type:
    /// `resourceck` never records anything for one (there is no
    /// ownership to decide), so this never even consults `consume_
    /// sites` for it. For an affine type, a missing entry is a
    /// structural mismatch between this stage and `resourceck` -- never
    /// silently treated as "observe" -- since every affine expression
    /// `resourceck` accepted in a consuming position always has one.
    fn lookup_consume_mode(&self, id: ExprId, ty: &Ty, context: &str) -> LowerResult<bool> {
        if !self.is_affine(ty) {
            return Ok(false);
        }
        match self.consume_sites.get(&id) {
            Some(crate::resourceck::ConsumeInfo::Transfer) => Ok(true),
            Some(crate::resourceck::ConsumeInfo::Observe) => Ok(false),
            None => Err(self.internal_error(&format!(
                "{context} is affine-typed but resourceck recorded no checked consume decision for it"
            ))),
        }
    }

    /// Emits an explicit ownership transfer for a call/`return`/`raise`
    /// operand `resourceck` already proved consumes its own source
    /// (`rfcs/0011`) -- `value`'s own prior identity is invalid
    /// immediately afterward; the returned `ValueId` is the resource's
    /// one current owner from this point on. A no-op (`value` passed
    /// straight through) for a non-affine type, or when `transfers` is
    /// `false` (an ordinary, non-`take` argument's own observation):
    /// `nir::verify` never accepts a `Move` whose own source isn't
    /// resource-typed, and there is nothing to transfer when this exact
    /// operand doesn't consume anything in the first place.
    fn move_if_transferred(
        &mut self,
        fb: &mut FnBuilder,
        value: ValueId,
        ty: &Ty,
        transfers: bool,
    ) -> ValueId {
        if transfers && self.is_affine(ty) {
            fb.push_value(ty.clone(), ValueKind::Move { source: value })
        } else {
            value
        }
    }

    /// Reads `expr_id`'s already-resolved type arguments back from
    /// typeck's `call_type_args` (never re-inferred here, matching every
    /// other type this module reads back rather than re-derives,
    /// `rfcs/0008`) -- the single place all three generic-carrying
    /// lowering sites (a call, a variant construction -- including a
    /// *bare* unit case, which lowers through the same function -- and a
    /// record construction) go through, so none of them can drift into
    /// silently defaulting to an empty argument list on their own.
    ///
    /// Absent metadata is only ever valid when `declared` is empty (a
    /// non-generic reference: no type arguments were ever going to
    /// exist). For a generic reference, missing metadata, or metadata
    /// whose length doesn't match `declared`, means typeck failed to
    /// validate/infer this site's type arguments before lowering ever
    /// saw it -- or a caller lowered hand-built HIR bypassing typeck
    /// entirely -- and is reported as a structured internal-lowering
    /// error, never silently truncated through `Vec::zip` (which would
    /// otherwise just drop the extra/missing arguments with no
    /// diagnostic at all) and never producing a partially-specialized
    /// `Call`/`RecordCreate`/`VariantCreate`.
    fn resolve_call_type_args(
        &self,
        expr_id: ExprId,
        declared: &[crate::hir::TypeParamId],
        what: &str,
    ) -> LowerResult<Vec<Ty>> {
        match self.call_type_args.get(&expr_id) {
            None if declared.is_empty() => Ok(Vec::new()),
            None => Err(self.internal_error(&format!(
                "{what} is generic (declaring {} type parameter(s)) but has no recorded call-site type arguments",
                declared.len()
            ))),
            Some(args) if args.len() == declared.len() => Ok(args.clone()),
            Some(args) => Err(self.internal_error(&format!(
                "{what} declares {} type parameter(s) but has {} recorded call-site type argument(s)",
                declared.len(),
                args.len()
            ))),
        }
    }

    /// Reads `expr_id`'s already-resolved capability evidence back from
    /// typeck's `call_evidence` (`rfcs/0009`), never re-resolved here --
    /// mirrors `resolve_call_type_args` exactly: absent metadata for a
    /// callee with no requirements is a valid empty list; anything else
    /// missing or wrong-arity is a structured internal-lowering error,
    /// never a silent default or a truncating zip.
    fn resolve_call_evidence(
        &self,
        expr_id: ExprId,
        requirements: &[CapabilityRequirement],
        what: &str,
    ) -> LowerResult<Vec<Evidence>> {
        match self.call_evidence.get(&expr_id) {
            None if requirements.is_empty() => Ok(Vec::new()),
            None => Err(self.internal_error(&format!(
                "{what} declares {} capability requirement(s) but has no recorded call-site evidence",
                requirements.len()
            ))),
            Some(evidence) if evidence.len() == requirements.len() => Ok(evidence.clone()),
            Some(evidence) => Err(self.internal_error(&format!(
                "{what} declares {} capability requirement(s) but has {} recorded call-site evidence entries",
                requirements.len(),
                evidence.len()
            ))),
        }
    }
}

/// One pattern slot in a decision-tree matrix row: either a real
/// surface pattern, or a synthetic filler for a newly-introduced
/// occurrence that a wildcard/binding/unit-case row doesn't itself
/// constrain -- keeps every row in one matrix the same length (see
/// `Lowering::lower_decision`'s doc comment).
#[derive(Clone, Copy)]
enum PatternSlot<'h> {
    Real(&'h HirPattern),
    /// A synthesized wildcard for an occurrence *nothing* in this row
    /// claims -- if the occurrence is affine, this row is the one and
    /// only owner of it, and must destroy it (`rfcs/0012`).
    Wildcard,
    /// A synthesized wildcard for an occurrence some *ancestor* pattern
    /// of this row already bound as a whole value. Classified exactly
    /// like [`PatternSlot::Wildcard`] for every matching decision --
    /// the two differ only in ownership: this one's value belongs to
    /// that ancestor binding, so destroying it here would double-drop
    /// the very thing the binding's own scope cleanup is already going
    /// to destroy.
    Owned,
}

#[derive(Clone)]
struct Occurrence {
    value: ValueId,
    ty: Ty,
}

struct MatrixRow<'h> {
    arm_index: usize,
    patterns: Vec<PatternSlot<'h>>,
    bindings: Vec<(LocalId, ValueId)>,
    /// Every occurrence this row reached and left *unclaimed* -- a
    /// payload position matched by `_` (or by a literal), whose parent
    /// was itself decomposed rather than bound whole (`rfcs/0012`).
    /// Accumulated in the order the decision tree consumed them, so
    /// destroying them in reverse gives exactly reverse payload
    /// declaration order. An affine occurrence listed here is destroyed
    /// the instant this row wins, *before* its own arm body runs, so
    /// every way out of that body -- normal completion, `return`,
    /// `raise`, `?`, `handle`, `break`, `continue` -- is covered by
    /// construction rather than by enumerating exits.
    discarded: Vec<Occurrence>,
}

/// Records `occ` as unclaimed by the row whose leading slot is `slot`
/// -- unless that slot is [`PatternSlot::Owned`], meaning an ancestor
/// pattern already bound the value this occurrence came out of, and
/// destroying it here would double-drop what that binding's own scope
/// cleanup already destroys (`rfcs/0012`).
fn discard_unclaimed(discarded: &mut Vec<Occurrence>, slot: &PatternSlot, occ: &Occurrence) {
    if !matches!(slot, PatternSlot::Owned) {
        discarded.push(occ.clone());
    }
}

enum Classified<'h> {
    Wildcard,
    Bind(LocalId),
    Case {
        variant: ItemId,
        case: usize,
        args: &'h [HirPattern],
    },
    Literal(LiteralTest<'h>),
}

enum LiteralTest<'h> {
    Int(u128),
    Str(&'h str),
    Char(char),
    Bool(bool),
}

fn literal_eq(a: &LiteralTest, b: &LiteralTest) -> bool {
    match (a, b) {
        (LiteralTest::Int(x), LiteralTest::Int(y)) => x == y,
        (LiteralTest::Str(x), LiteralTest::Str(y)) => x == y,
        (LiteralTest::Char(x), LiteralTest::Char(y)) => x == y,
        (LiteralTest::Bool(x), LiteralTest::Bool(y)) => x == y,
        _ => false,
    }
}

fn literal_const(fb: &mut FnBuilder, lit: &LiteralTest, ty: &Ty) -> ValueId {
    match lit {
        LiteralTest::Int(v) => fb.push_value(ty.clone(), ValueKind::Const(Const::Int(*v))),
        LiteralTest::Str(s) => {
            fb.push_value(ty.clone(), ValueKind::Const(Const::Str((*s).to_string())))
        }
        LiteralTest::Char(c) => fb.push_value(ty.clone(), ValueKind::Const(Const::Char(*c))),
        LiteralTest::Bool(b) => fb.push_value(ty.clone(), ValueKind::Const(Const::Bool(*b))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::lower_module as lower_hir;
    use crate::lexer::tokenize;
    use crate::nir::Instruction;
    use crate::parser::Parser;
    use crate::source::SourceMap;
    use crate::typeck::check_module;

    fn lower(text: &str) -> Module {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(
            diags.is_empty(),
            "unexpected resolve diagnostics: {diags:?}"
        );
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected type errors: {:?}",
            result.diagnostics
        );
        let resourceck_result = crate::resourceck::check_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &interner,
            &crate::resourceck::AffineContext {
                aggregate_field_types: &result.aggregate_field_types,
                declared_resources: &result.declared_resources,
                item_type_params: &result.item_type_params,
                field_projections: &result.field_projections,
            },
        );
        assert!(
            resourceck_result.diagnostics.is_empty(),
            "unexpected resource errors: {:?}",
            resourceck_result.diagnostics
        );
        lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &resourceck_result.cleanup_edges,
            &resourceck_result.consume_sites,
            &resourceck_result.defer_plans,
            &interner,
            id,
        )
        .expect("expected lowering to succeed")
    }

    /// Like `lower`, but for a program that type-checks cleanly and is
    /// expected to *fail* lowering (e.g. a named aggregate type in an
    /// executable signature) -- returns whatever `lower_module` actually
    /// produces instead of asserting success.
    fn lower_result(text: &str) -> Result<Module, Vec<Diagnostic>> {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(
            diags.is_empty(),
            "unexpected resolve diagnostics: {diags:?}"
        );
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected type errors: {:?}",
            result.diagnostics
        );
        let resourceck_result = crate::resourceck::check_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &interner,
            &crate::resourceck::AffineContext {
                aggregate_field_types: &result.aggregate_field_types,
                declared_resources: &result.declared_resources,
                item_type_params: &result.item_type_params,
                field_projections: &result.field_projections,
            },
        );
        assert!(
            resourceck_result.diagnostics.is_empty(),
            "unexpected resource errors: {:?}",
            resourceck_result.diagnostics
        );
        lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &resourceck_result.cleanup_edges,
            &resourceck_result.consume_sites,
            &resourceck_result.defer_plans,
            &interner,
            id,
        )
    }

    #[test]
    fn a_missing_consume_site_for_an_affine_binding_is_an_internal_error_not_a_silent_observe() {
        // `resourceck` genuinely recorded a checked transfer for this
        // exact binding -- this test discards it before lowering ever
        // sees it, simulating the two stages disagreeing (`rfcs/0011`).
        // Lowering must report a structured internal diagnostic, never
        // silently fall back to treating the initializer as a mere
        // observation.
        // A `mutable` binding's own `Store` always consults its checked
        // consume decision, regardless of the initializer's own shape
        // (unlike an immutable rebind, which only ever needs one for a
        // bare-local source -- there is no `Move` to decide for a fresh
        // construction either way, so nothing would notice its absence).
        let text = "resource File { descriptor: i64 } \
                     func f() { mutable file = File { descriptor: 3 }; drop file; }";
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(
            diags.is_empty(),
            "unexpected resolve diagnostics: {diags:?}"
        );
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected type errors: {:?}",
            result.diagnostics
        );
        let resourceck_result = crate::resourceck::check_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &interner,
            &crate::resourceck::AffineContext {
                aggregate_field_types: &result.aggregate_field_types,
                declared_resources: &result.declared_resources,
                item_type_params: &result.item_type_params,
                field_projections: &result.field_projections,
            },
        );
        assert!(
            resourceck_result.diagnostics.is_empty(),
            "unexpected resource errors: {:?}",
            resourceck_result.diagnostics
        );
        assert!(
            !resourceck_result.consume_sites.is_empty(),
            "expected resourceck to have actually recorded a consume site"
        );
        let outcome = lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &resourceck_result.cleanup_edges,
            // Deliberately empty, discarding resourceck's own real
            // decision, rather than the authentic `consume_sites`.
            &BTreeMap::new(),
            &resourceck_result.defer_plans,
            &interner,
            id,
        );
        let Err(diagnostics) = outcome else {
            panic!("expected lowering to fail with a missing-metadata internal error");
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics[0]
                .message
                .contains("no checked consume decision"),
            "expected a missing-consume-decision internal error, got: {}",
            diagnostics[0].message
        );
    }

    /// Runs a real `defer close(file);` (`take`) program through the
    /// whole front end, asserting every stage is clean, and returns
    /// everything needed to call `lower_module` directly -- for tests
    /// that then deliberately tamper with one field of the checked
    /// `CheckedDeferPlan` this program's own `resourceck` pass recorded,
    /// before lowering, to prove each field is actually validated
    /// (`rfcs/0011`) rather than merely present.
    #[allow(clippy::type_complexity)]
    fn checked_take_defer_pipeline() -> (
        crate::hir::HirModule,
        HashMap<LocalId, Ty>,
        HashMap<ExprId, Ty>,
        HashMap<PatternId, (ItemId, usize)>,
        HashMap<ExprId, Vec<Ty>>,
        crate::resourceck::ResourceCheckResult,
        Interner,
        SourceId,
    ) {
        let text = "resource File { descriptor: i64 } \
                     func close(take file: File) -> unit { drop file; } \
                     func f() { value file = File { descriptor: 3 }; defer close(file); }";
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(
            diags.is_empty(),
            "unexpected resolve diagnostics: {diags:?}"
        );
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected type errors: {:?}",
            result.diagnostics
        );
        let resourceck_result = crate::resourceck::check_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &interner,
            &crate::resourceck::AffineContext {
                aggregate_field_types: &result.aggregate_field_types,
                declared_resources: &result.declared_resources,
                item_type_params: &result.item_type_params,
                field_projections: &result.field_projections,
            },
        );
        assert!(
            resourceck_result.diagnostics.is_empty(),
            "unexpected resource errors: {:?}",
            resourceck_result.diagnostics
        );
        assert_eq!(
            resourceck_result.defer_plans.len(),
            1,
            "expected exactly one checked defer plan: {:?}",
            resourceck_result.defer_plans
        );
        (
            hir,
            result.local_types,
            result.expr_types,
            result.pattern_case,
            result.call_type_args,
            resourceck_result,
            interner,
            id,
        )
    }

    /// Lowers `checked_take_defer_pipeline`'s own program with its sole
    /// `CheckedDeferPlan` replaced by `tamper`'s own result, asserting
    /// lowering fails with a structured internal diagnostic whose
    /// message contains `expected_message_fragment`.
    fn assert_tampered_defer_plan_rejected(
        tamper: impl FnOnce(crate::resourceck::CheckedDeferPlan) -> crate::resourceck::CheckedDeferPlan,
        expected_message_fragment: &str,
    ) {
        let (
            hir,
            local_types,
            expr_types,
            pattern_case,
            call_type_args,
            mut resourceck_result,
            interner,
            id,
        ) = checked_take_defer_pipeline();
        let (defer_id, plan) = resourceck_result
            .defer_plans
            .iter()
            .next()
            .map(|(id, plan)| (*id, plan.clone()))
            .expect("checked above");
        resourceck_result.defer_plans.insert(defer_id, tamper(plan));
        let outcome = lower_module(
            &hir,
            &local_types,
            &expr_types,
            &pattern_case,
            &call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &resourceck_result.cleanup_edges,
            &resourceck_result.consume_sites,
            &resourceck_result.defer_plans,
            &interner,
            id,
        );
        let Err(diagnostics) = outcome else {
            panic!("expected lowering to fail with a tampered-defer-plan internal error");
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics[0].message.contains(expected_message_fragment),
            "expected a message containing {expected_message_fragment:?}, got: {}",
            diagnostics[0].message
        );
    }

    #[test]
    fn a_defer_plan_naming_the_wrong_callee_is_rejected() {
        assert_tampered_defer_plan_rejected(
            |mut plan| {
                plan.callee = ItemId(9999);
                plan
            },
            "a different callee",
        );
    }

    #[test]
    fn a_defer_plan_with_too_few_argument_modes_is_rejected() {
        assert_tampered_defer_plan_rejected(
            |mut plan| {
                plan.arg_modes.clear();
                plan
            },
            "checked argument mode(s)",
        );
    }

    #[test]
    fn a_defer_plan_with_too_many_argument_modes_is_rejected() {
        assert_tampered_defer_plan_rejected(
            |mut plan| {
                plan.arg_modes.push(crate::resourceck::ConsumeInfo::Observe);
                plan
            },
            "checked argument mode(s)",
        );
    }

    #[test]
    fn a_defer_plan_with_too_few_argument_types_is_rejected() {
        assert_tampered_defer_plan_rejected(
            |mut plan| {
                plan.arg_types.clear();
                plan
            },
            "checked argument type(s)",
        );
    }

    #[test]
    fn a_defer_plan_with_too_many_argument_types_is_rejected() {
        assert_tampered_defer_plan_rejected(
            |mut plan| {
                plan.arg_types.push(Ty::I64);
                plan
            },
            "checked argument type(s)",
        );
    }

    #[test]
    fn a_defer_plan_with_the_wrong_argument_type_is_rejected() {
        assert_tampered_defer_plan_rejected(
            |mut plan| {
                plan.arg_types[0] = Ty::I64;
                plan
            },
            "disagrees with its own resolved parameter type",
        );
    }

    #[test]
    fn a_defer_plan_with_the_wrong_return_type_is_rejected() {
        assert_tampered_defer_plan_rejected(
            |mut plan| {
                plan.return_type = Ty::I64;
                plan
            },
            "disagrees with its own resolved signature",
        );
    }

    #[test]
    fn a_defer_plan_with_a_mode_disagreeing_with_its_own_consume_site_is_rejected() {
        assert_tampered_defer_plan_rejected(
            |mut plan| {
                plan.arg_modes[0] = crate::resourceck::ConsumeInfo::Observe;
                plan
            },
            "disagreeing with its own recorded consume site",
        );
    }

    #[test]
    fn a_defer_plan_with_an_out_of_range_registration_order_replay_is_rejected() {
        // A single `defer` in this program is trivially "in order" on
        // its own -- this instead proves the *replay* check itself
        // fires by directly constructing two cleanup actions for the
        // same defer id at decreasing-then-increasing order, exactly
        // the shape `emit_checked_cleanup` must reject.
        let (
            hir,
            local_types,
            expr_types,
            pattern_case,
            call_type_args,
            mut resourceck_result,
            interner,
            id,
        ) = checked_take_defer_pipeline();
        let (defer_id, _) = resourceck_result
            .defer_plans
            .iter()
            .next()
            .map(|(id, plan)| (*id, plan.clone()))
            .expect("checked above");
        for actions in resourceck_result.cleanup_edges.values_mut() {
            let existing: Vec<_> = actions
                .iter()
                .filter(|a| matches!(a, crate::resourceck::CleanupAction::Defer(_)))
                .cloned()
                .collect();
            for action in existing {
                actions.push(action);
            }
        }
        let outcome = lower_module(
            &hir,
            &local_types,
            &expr_types,
            &pattern_case,
            &call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &resourceck_result.cleanup_edges,
            &resourceck_result.consume_sites,
            &resourceck_result.defer_plans,
            &interner,
            id,
        );
        let Err(diagnostics) = outcome else {
            panic!("expected lowering to fail with an out-of-order replay internal error");
        };
        assert!(
            diagnostics.iter().any(
                |d| d.message.contains("own declared LIFO registration order")
                    || d.message.contains("this frame never lowered")
            ),
            "expected an out-of-order or double-replay internal error, got: {diagnostics:?}"
        );
        let _ = defer_id;
    }

    #[test]
    fn a_missing_defer_plan_is_an_internal_error_not_a_silent_fallback() {
        // Same shape as the consume-site regression above, but for a
        // `defer` statement's own checked plan (`rfcs/0011`).
        let text = "resource File { descriptor: i64 } \
                     func close(take file: File) -> unit { drop file; } \
                     func f() { value file = File { descriptor: 3 }; defer close(file); }";
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(
            diags.is_empty(),
            "unexpected resolve diagnostics: {diags:?}"
        );
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected type errors: {:?}",
            result.diagnostics
        );
        let resourceck_result = crate::resourceck::check_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &interner,
            &crate::resourceck::AffineContext {
                aggregate_field_types: &result.aggregate_field_types,
                declared_resources: &result.declared_resources,
                item_type_params: &result.item_type_params,
                field_projections: &result.field_projections,
            },
        );
        assert!(
            resourceck_result.diagnostics.is_empty(),
            "unexpected resource errors: {:?}",
            resourceck_result.diagnostics
        );
        assert!(
            !resourceck_result.defer_plans.is_empty(),
            "expected resourceck to have actually recorded a defer plan"
        );
        let outcome = lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &resourceck_result.cleanup_edges,
            &resourceck_result.consume_sites,
            // Deliberately empty, discarding resourceck's own real plan.
            &BTreeMap::new(),
            &interner,
            id,
        );
        let Err(diagnostics) = outcome else {
            panic!("expected lowering to fail with a missing-metadata internal error");
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics[0].message.contains("no checked argument plan"),
            "expected a missing-defer-plan internal error, got: {}",
            diagnostics[0].message
        );
    }

    #[test]
    fn a_missing_reachable_cleanup_plan_is_an_internal_error_not_a_silent_no_op() {
        // Same shape as the two regressions above, but for
        // `cleanup_edges` itself (`rfcs/0011`): a reachable exit
        // resourceck genuinely recorded a plan for, with its own entry
        // discarded before lowering ever sees it, simulating the two
        // stages disagreeing about whether anything needs cleaning up.
        let text = "resource File { descriptor: i64 } \
                     func f() { value file = File { descriptor: 3 }; drop file; }";
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(
            diags.is_empty(),
            "unexpected resolve diagnostics: {diags:?}"
        );
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected type errors: {:?}",
            result.diagnostics
        );
        let resourceck_result = crate::resourceck::check_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &interner,
            &crate::resourceck::AffineContext {
                aggregate_field_types: &result.aggregate_field_types,
                declared_resources: &result.declared_resources,
                item_type_params: &result.item_type_params,
                field_projections: &result.field_projections,
            },
        );
        assert!(
            resourceck_result.diagnostics.is_empty(),
            "unexpected resource errors: {:?}",
            resourceck_result.diagnostics
        );
        assert!(
            !resourceck_result.cleanup_edges.is_empty(),
            "expected resourceck to have actually recorded a cleanup plan"
        );
        let outcome = lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            // Deliberately empty, discarding resourceck's own real
            // cleanup plan for this function's own reachable exit.
            &BTreeMap::new(),
            &resourceck_result.consume_sites,
            &resourceck_result.defer_plans,
            &interner,
            id,
        );
        let Err(diagnostics) = outcome else {
            panic!("expected lowering to fail with a missing-metadata internal error");
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics[0].message.contains("no checked cleanup plan"),
            "expected a missing-cleanup-plan internal error, got: {}",
            diagnostics[0].message
        );
    }

    /// Like `lower`, but also runs the module through the NIR verifier
    /// (using the same interner/source lowering itself used, unlike a
    /// fresh throwaway one) and returns its diagnostics -- for tests
    /// that need to assert the *verifier* accepts what was produced.
    fn lower_and_verify(text: &str) -> Vec<Diagnostic> {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(
            diags.is_empty(),
            "unexpected resolve diagnostics: {diags:?}"
        );
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected type errors: {:?}",
            result.diagnostics
        );
        let resourceck_result = crate::resourceck::check_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &interner,
            &crate::resourceck::AffineContext {
                aggregate_field_types: &result.aggregate_field_types,
                declared_resources: &result.declared_resources,
                item_type_params: &result.item_type_params,
                field_projections: &result.field_projections,
            },
        );
        assert!(
            resourceck_result.diagnostics.is_empty(),
            "unexpected resource errors: {:?}",
            resourceck_result.diagnostics
        );
        let module = lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &resourceck_result.cleanup_edges,
            &resourceck_result.consume_sites,
            &resourceck_result.defer_plans,
            &interner,
            id,
        )
        .expect("expected lowering to succeed");
        crate::nir::verify_module(&module, id, &interner, &crate::hir::ItemRegistry::default())
    }

    fn drop_count(f: &Function) -> usize {
        f.blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i, Instruction::Drop { .. }))
            .count()
    }

    // -- Loop break moved_out join (loop condition re-evaluation fix) ---

    #[test]
    fn a_resource_taken_on_a_conditional_break_path_is_not_dropped_again_after_the_loop() {
        // The exact regression: sink's own take call already destroyed
        // file on the break path; whatever runs after the loop (here,
        // the function's own implicit end-of-scope cleanup, sharing the
        // same exit block break itself branches to) must not drop it a
        // second time.
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> unit { drop file; } \
             func conditional_break(cond: bool) { \
                 value file = File { descriptor: 1 }; \
                 loop { \
                     if cond { \
                         sink(file); \
                         break; \
                     } \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> unit { drop file; } \
             func conditional_break(cond: bool) { \
                 value file = File { descriptor: 1 }; \
                 loop { \
                     if cond { \
                         sink(file); \
                         break; \
                     } \
                 } \
             }",
        );
        // Declaration order: `sink` first, `conditional_break` second.
        let sink = &module.functions[0];
        let conditional_break = &module.functions[1];
        assert_eq!(
            drop_count(sink),
            1,
            "sink's own take parameter must be dropped exactly once, inside sink itself"
        );
        assert_eq!(
            drop_count(conditional_break),
            0,
            "conditional_break's own scope must not drop a resource the break path already \
             moved into sink's own take parameter"
        );
    }

    #[test]
    fn a_while_conditions_own_moved_out_state_applies_after_the_loop() {
        // Each evaluation of the condition take-consumes `file`; the
        // body reassigns it before looping back, which is exactly what
        // makes the backedge agree with entry again (Moved -> Available
        // is a legal reassignment). Every reachable exit -- there is no
        // `break` here, only the condition's own false edge -- leaves
        // `file` Moved, since the condition itself always runs last.
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func consume_as_bool(take file: File) -> bool { \
                 drop file; \
                 return false; \
             } \
             func second() -> File { return File { descriptor: 2 } } \
             func f() { \
                 mutable file = File { descriptor: 1 }; \
                 while consume_as_bool(file) { \
                     file = second(); \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func consume_as_bool(take file: File) -> bool { \
                 drop file; \
                 return false; \
             } \
             func second() -> File { return File { descriptor: 2 } } \
             func f() { \
                 mutable file = File { descriptor: 1 }; \
                 while consume_as_bool(file) { \
                     file = second(); \
                 } \
             }",
        );
        // Declaration order: `consume_as_bool`, `second`, `f`.
        let consume_as_bool = &module.functions[0];
        let f = &module.functions[2];
        assert_eq!(drop_count(consume_as_bool), 1);
        assert_eq!(
            drop_count(f),
            0,
            "f's own scope must not drop a resource the condition's own last take call \
             already consumed"
        );
    }

    #[test]
    fn a_non_affine_match_returned_alongside_a_take_param_drops_it_exactly_once() {
        // The `match` itself produces `i64`, not a resource: `kind`
        // still propagates `Return` through it while checking, but that
        // must never be mistaken for `file` itself being the thing
        // under compound return-sink treatment -- `file`'s own implicit
        // destruction belongs solely to the `return`'s own
        // whole-function cleanup, replayed once at the shared merge
        // point every arm branches to, never claimed a second time by
        // an arm's own (otherwise-empty) local cleanup list.
        let diags = lower_and_verify(
            "variant Choice { A, B } \
             resource File { descriptor: i64 } \
             func f(c: Choice, take file: File) -> i64 { \
                 return match c { A => 1, B => 2 }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "variant Choice { A, B } \
             resource File { descriptor: i64 } \
             func f(c: Choice, take file: File) -> i64 { \
                 return match c { A => 1, B => 2 }; \
             }",
        );
        let f = &module.functions[0];
        assert_eq!(
            drop_count(f),
            1,
            "file must be dropped exactly once, not once per arm: {f:?}"
        );
    }

    #[test]
    fn a_non_affine_handle_returned_alongside_a_take_param_drops_it_exactly_once() {
        let diags = lower_and_verify(
            "variant OpenError { Invalid } \
             resource File { descriptor: i64 } \
             func open() -> i64 raises OpenError { return 1 } \
             func f(take file: File) -> i64 { \
                 return handle open() { \
                     success n => n, \
                     failure OpenError.Invalid => 0, \
                 }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "variant OpenError { Invalid } \
             resource File { descriptor: i64 } \
             func open() -> i64 raises OpenError { return 1 } \
             func f(take file: File) -> i64 { \
                 return handle open() { \
                     success n => n, \
                     failure OpenError.Invalid => 0, \
                 }; \
             }",
        );
        let f = &module.functions[1];
        assert_eq!(
            drop_count(f),
            1,
            "file must be dropped exactly once, not once per arm: {f:?}"
        );
    }

    #[test]
    fn explicit_drop_lowers_to_a_real_drop_instruction() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func f() { value file = File { descriptor: 3 }; drop file; }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func f() { value file = File { descriptor: 3 }; drop file; }",
        );
        let f = &module.functions[0];
        assert_eq!(drop_count(f), 1, "expected exactly one Drop instruction");
    }

    #[test]
    fn an_unmoved_resource_local_is_implicitly_dropped_at_function_exit() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func f() { value file = File { descriptor: 3 }; }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } func f() { value file = File { descriptor: 3 }; }",
        );
        let f = &module.functions[0];
        assert_eq!(
            drop_count(f),
            1,
            "expected the still-owned resource to be implicitly dropped exactly once"
        );
    }

    #[test]
    fn a_moved_resource_is_not_implicitly_dropped_again() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f() { value file = File { descriptor: 3 }; consume(file); }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f() { value file = File { descriptor: 3 }; consume(file); }",
        );
        // Declaration order: `consume` first, `f` second.
        let callee = &module.functions[0];
        let caller = &module.functions[1];
        assert_eq!(
            drop_count(caller),
            0,
            "the caller must not drop a resource it already moved into a take argument"
        );
        assert_eq!(
            drop_count(callee),
            1,
            "the callee's own take parameter must be dropped exactly once"
        );
    }

    #[test]
    fn defer_and_resource_drops_run_in_declaration_reversed_order() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func touch(file: File) -> unit {} \
             func f() { \
                 value first = File { descriptor: 1 }; \
                 defer touch(first); \
                 value second = File { descriptor: 2 }; \
                 defer touch(second); \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func touch(file: File) -> unit {} \
             func f() { \
                 value first = File { descriptor: 1 }; \
                 defer touch(first); \
                 value second = File { descriptor: 2 }; \
                 defer touch(second); \
             }",
        );
        // Declaration order: `touch` first, `f` second.
        let f = &module.functions[1];
        // Registration order: first, defer(first), second, defer(second).
        // Reversed cleanup order: defer(second), drop(second), defer(first), drop(first).
        let sequence: Vec<&str> = f.blocks[0]
            .instructions
            .iter()
            .filter_map(|i| match i {
                Instruction::Value {
                    kind: crate::nir::ValueKind::Call(..),
                    ..
                } => Some("call"),
                Instruction::Drop { .. } => Some("drop"),
                _ => None,
            })
            .collect();
        assert_eq!(
            sequence,
            vec!["call", "drop", "call", "drop"],
            "expected defer/drop cleanup interleaved in declaration-reversed order, got {sequence:?}"
        );
    }

    #[test]
    fn a_resource_moved_into_a_deferred_take_argument_is_not_also_dropped_by_its_own_scope() {
        // Blocker 6: a resource passed to a deferred `take` parameter
        // transfers ownership into the pending deferred invocation at
        // registration time -- the caller's own scope-exit cleanup
        // must not additionally drop the same resource once the
        // deferred call (which drops its own taken argument) actually
        // runs. This used to double-drop it.
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit { drop file; } \
             func f() { \
                 value file = File { descriptor: 3 }; \
                 defer consume(file); \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit { drop file; } \
             func f() { \
                 value file = File { descriptor: 3 }; \
                 defer consume(file); \
             }",
        );
        // Declaration order: `consume` first, `f` second.
        let consume = &module.functions[0];
        let f = &module.functions[1];
        assert_eq!(
            drop_count(consume),
            1,
            "consume's own take parameter must be dropped exactly once, inside consume itself"
        );
        assert_eq!(
            drop_count(f),
            0,
            "f's own scope must not drop a resource it already moved into the deferred call"
        );
    }

    // -- Resource reassignment (Blocker 5) -------------------------------

    #[test]
    fn reassigning_after_an_explicit_drop_destroys_the_new_value_exactly_once() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func first() -> File { return File { descriptor: 1 } } \
             func second() -> File { return File { descriptor: 2 } } \
             func f() { \
                 mutable target = first(); \
                 drop target; \
                 target = second(); \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func first() -> File { return File { descriptor: 1 } } \
             func second() -> File { return File { descriptor: 2 } } \
             func f() { \
                 mutable target = first(); \
                 drop target; \
                 target = second(); \
             }",
        );
        // Declaration order: `first`, `second`, `f`.
        let f = &module.functions[2];
        assert_eq!(
            drop_count(f),
            2,
            "expected the explicit drop of the first value and the implicit scope-exit drop \
             of the reassigned second value, got a different count entirely"
        );
    }

    #[test]
    fn reassigning_from_a_local_moves_the_source_and_transfers_ownership_to_the_target() {
        // The exact regression from the review: `source`'s own binding
        // must not also be dropped once its value moved into `target`,
        // and `target`'s own new value must still reach exactly one
        // `Drop` -- at the caller, once the returned resource is done
        // with, never inside `f` itself before the `Return`.
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func first() -> File { return File { descriptor: 1 } } \
             func second() -> File { return File { descriptor: 2 } } \
             func f() -> File { \
                 mutable target = first(); \
                 drop target; \
                 value source = second(); \
                 target = source; \
                 return target; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func first() -> File { return File { descriptor: 1 } } \
             func second() -> File { return File { descriptor: 2 } } \
             func f() -> File { \
                 mutable target = first(); \
                 drop target; \
                 value source = second(); \
                 target = source; \
                 return target; \
             }",
        );
        // Declaration order: `first`, `second`, `f`.
        let f = &module.functions[2];
        assert_eq!(
            drop_count(f),
            1,
            "expected only the explicit drop of the first value -- the reassigned resource is \
             returned, not dropped inside f, and `source` must not be independently dropped \
             once its value moved into `target`"
        );
    }

    // -- Resource ownership from patterns (Blocker 4) --------------------

    #[test]
    fn a_handle_success_bindings_resource_returning_a_primitive_is_still_dropped_exactly_once() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func open() -> File raises OpenError { return File { descriptor: 1 } } \
             func f() -> i64 { \
                 return handle open() { \
                     success file => file.descriptor, \
                     failure OpenError.Invalid => 0, \
                 }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func open() -> File raises OpenError { return File { descriptor: 1 } } \
             func f() -> i64 { \
                 return handle open() { \
                     success file => file.descriptor, \
                     failure OpenError.Invalid => 0, \
                 }; \
             }",
        );
        // Declaration order: `open` first, `f` second.
        let f = &module.functions[1];
        assert_eq!(
            drop_count(f),
            1,
            "the success arm's own resource binding must be destroyed exactly once, even \
             though the arm itself only ever reads a primitive field out of it"
        );
    }

    #[test]
    fn a_handle_success_bindings_resource_moved_into_a_take_call_is_not_also_dropped() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func open() -> File raises OpenError { return File { descriptor: 1 } } \
             func consume(take file: File) -> i64 { return 1 } \
             func f() -> i64 { \
                 return handle open() { \
                     success file => consume(file), \
                     failure OpenError.Invalid => 0, \
                 }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func open() -> File raises OpenError { return File { descriptor: 1 } } \
             func consume(take file: File) -> i64 { return 1 } \
             func f() -> i64 { \
                 return handle open() { \
                     success file => consume(file), \
                     failure OpenError.Invalid => 0, \
                 }; \
             }",
        );
        // Declaration order: `open`, `consume`, `f`.
        let f = &module.functions[2];
        assert_eq!(
            drop_count(f),
            0,
            "the success arm's own binding was moved into consume's own take parameter; f's \
             own scope must not also drop it"
        );
    }

    #[test]
    fn a_handle_success_wildcards_resource_is_destroyed_immediately() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func make_file() -> File raises OpenError { return File { descriptor: 1 } } \
             func f() -> i64 { \
                 return handle make_file() { \
                     success _ => 0, \
                     failure OpenError.Invalid => -1, \
                 }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func make_file() -> File raises OpenError { return File { descriptor: 1 } } \
             func f() -> i64 { \
                 return handle make_file() { \
                     success _ => 0, \
                     failure OpenError.Invalid => -1, \
                 }; \
             }",
        );
        // Declaration order: `make_file` first, `f` second.
        let f = &module.functions[1];
        assert_eq!(
            drop_count(f),
            1,
            "the success value bound by `_` must still be destroyed exactly once, immediately, \
             since no local exists to schedule ordinary cleanup for it"
        );
    }

    #[test]
    fn a_handle_success_wildcard_for_a_non_resource_result_emits_no_drop() {
        let module = lower(
            "variant OpenError { Invalid } \
             func make_number() -> i64 raises OpenError { return 1 } \
             func f() -> i64 { \
                 return handle make_number() { \
                     success _ => 0, \
                     failure OpenError.Invalid => -1, \
                 }; \
             }",
        );
        let f = &module.functions[1];
        assert_eq!(
            drop_count(f),
            0,
            "a non-resource success value must never be dropped, even when wildcard-bound"
        );
    }

    // -- Fallible `take` transfer through Invoke (Blocker 1) ------------

    #[test]
    fn a_take_argument_to_a_postfix_try_call_is_not_also_dropped_by_the_caller() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             variant OpenError { Bad } \
             func consume(take file: File) -> i64 raises OpenError { return 1 } \
             func f() -> i64 raises OpenError { \
                 value file = File { descriptor: 3 }; \
                 return consume(file)?; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             variant OpenError { Bad } \
             func consume(take file: File) -> i64 raises OpenError { return 1 } \
             func f() -> i64 raises OpenError { \
                 value file = File { descriptor: 3 }; \
                 return consume(file)?; \
             }",
        );
        // Declaration order: `consume` first, `f` second.
        let f = &module.functions[1];
        assert_eq!(
            drop_count(f),
            0,
            "f's own scope must not drop a resource it already moved into the Invoke, on \
             either edge"
        );
    }

    #[test]
    fn a_take_argument_to_a_handled_call_is_not_also_dropped_by_the_caller() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             variant OpenError { Bad } \
             func consume(take file: File) -> i64 raises OpenError { return 1 } \
             func f() -> i64 { \
                 value file = File { descriptor: 3 }; \
                 return handle consume(file) { \
                     success v => v, \
                     failure OpenError.Bad => 0, \
                 }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             variant OpenError { Bad } \
             func consume(take file: File) -> i64 raises OpenError { return 1 } \
             func f() -> i64 { \
                 value file = File { descriptor: 3 }; \
                 return handle consume(file) { \
                     success v => v, \
                     failure OpenError.Bad => 0, \
                 }; \
             }",
        );
        let f = &module.functions[1];
        assert_eq!(
            drop_count(f),
            0,
            "f's own scope must not drop a resource it already moved into the Invoke, on \
             either edge, and the handled failure arm never received it either"
        );
    }

    #[test]
    fn a_resource_taken_by_a_failing_invoke_is_not_leaked_or_double_dropped() {
        // The callee's own failure edge is reached; the callee is the
        // one now responsible for whatever it did with its taken
        // argument (Blocker 1) -- the caller's own diagnostics/lowering
        // must stay identical regardless of which edge actually runs at
        // runtime, since both are decided the same way, at Invoke-time,
        // before either edge exists.
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             variant OpenError { Bad } \
             func consume(take file: File, fail: bool) -> i64 raises OpenError { \
                 if fail { \
                     drop file; \
                     raise OpenError.Bad; \
                 } \
                 return 1; \
             } \
             func f(fail: bool) -> i64 { \
                 value file = File { descriptor: 3 }; \
                 return handle consume(file, fail) { \
                     success v => v, \
                     failure OpenError.Bad => 0, \
                 }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_deferred_calls_own_non_unit_result_carries_its_real_type() {
        // Blocker 6: the replayed deferred call must carry the
        // callee's own actual return type, never a fabricated
        // `Ty::Unit`, even though the result is always discarded.
        let module = lower(
            "func touch() -> i64 { return 1 } \
             func f() { defer touch(); }",
        );
        // Declaration order: `touch` first, `f` second.
        let f = &module.functions[1];
        let call_value_ty = f
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| match i {
                Instruction::Value {
                    ty,
                    kind: crate::nir::ValueKind::Call(..),
                    ..
                } => Some(ty.clone()),
                _ => None,
            })
            .expect("expected the deferred call's own Value instruction");
        assert_eq!(
            call_value_ty,
            Ty::I64,
            "expected the deferred call's own result to carry touch's real return type"
        );
    }

    #[test]
    fn a_resource_is_cleaned_up_before_an_explicit_raise() {
        let diags = lower_and_verify(
            "variant Failure { Broken } \
             resource File { descriptor: i64 } \
             func f() -> i64 raises Failure { \
                 value file = File { descriptor: 3 }; \
                 raise Failure.Broken; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "variant Failure { Broken } \
             resource File { descriptor: i64 } \
             func f() -> i64 raises Failure { \
                 value file = File { descriptor: 3 }; \
                 raise Failure.Broken; \
             }",
        );
        let f = &module.functions[0];
        assert_eq!(
            drop_count(f),
            1,
            "expected the still-owned resource to be dropped before the raise"
        );
    }

    #[test]
    fn a_resource_is_cleaned_up_before_a_postfix_try_propagates() {
        let diags = lower_and_verify(
            "variant Failure { Broken } \
             resource File { descriptor: i64 } \
             func fail() -> i64 raises Failure { raise Failure.Broken; } \
             func f() -> i64 raises Failure { \
                 value file = File { descriptor: 3 }; \
                 return fail()?; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "variant Failure { Broken } \
             resource File { descriptor: i64 } \
             func fail() -> i64 raises Failure { raise Failure.Broken; } \
             func f() -> i64 raises Failure { \
                 value file = File { descriptor: 3 }; \
                 return fail()?; \
             }",
        );
        // Declaration order: `fail` first, `f` second. Two reachable
        // exit paths out of `f` (the `?`'s own ok edge, continuing to
        // `f`'s own `return`, and its one failure edge, propagating
        // onward) each get their own copy of the cleanup sequence, so
        // two `Drop`s total -- one per path, never a double-drop on
        // either path individually.
        let f = &module.functions[1];
        assert_eq!(
            drop_count(f),
            2,
            "expected the still-owned resource to be dropped on both the ok and the propagating path"
        );
    }

    #[test]
    fn a_resource_declared_inside_an_if_branch_is_cleaned_up_in_its_own_scope() {
        // A resource declared and left unmoved inside one arm of an
        // `if` must be destroyed at that arm's own end, not left for
        // the enclosing function's own cleanup to replay after the
        // join -- the value never dominates anywhere past its own arm,
        // so replaying it there would fail NIR verification (this was
        // a real bug this milestone's own internal review caught: the
        // function-wide cleanup list must have each nested scope's own
        // entries removed once that scope's own cleanup already ran).
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 if cond { \
                     value file = File { descriptor: 3 }; \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 if cond { \
                     value file = File { descriptor: 3 }; \
                 } \
             }",
        );
        let f = &module.functions[0];
        assert_eq!(
            drop_count(f),
            1,
            "expected the if-branch's own resource to be dropped exactly once, inside its own arm"
        );
    }

    #[test]
    fn a_move_inside_one_if_branch_does_not_skip_the_fallthrough_paths_own_cleanup() {
        // Alpha 0.1.7 (Blocker 1): `fb.moved_out` used to be a single
        // function-wide set with no branch isolation, so moving `file`
        // into `sink`'s own `take` parameter inside the `then` branch
        // leaked into the state seen while lowering the code *after*
        // the `if` -- wrongly skipping `file`'s own drop on the
        // fallthrough path where `cond` was false and `file` was never
        // moved at all.
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> i64 { return 1 } \
             func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 if cond { \
                     return sink(file); \
                 } \
                 return 0; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> i64 { return 1 } \
             func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 if cond { \
                     return sink(file); \
                 } \
                 return 0; \
             }",
        );
        // Declaration order: `sink` first, `f` second.
        let sink = &module.functions[0];
        let f = &module.functions[1];
        assert_eq!(
            drop_count(sink),
            1,
            "sink's own take parameter must be dropped exactly once"
        );
        assert_eq!(
            drop_count(f),
            1,
            "expected exactly one drop: `file` moved into `sink` on the taken branch must not \
             be dropped there, but the fallthrough branch never moved it and must still drop it"
        );
    }

    #[test]
    fn a_move_inside_the_else_branch_does_not_skip_the_thens_own_cleanup() {
        // The reverse arrangement of the test above: the move happens in
        // the `else` branch instead of `then`.
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> i64 { return 1 } \
             func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 if cond { \
                     return 0; \
                 } else { \
                     return sink(file); \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> i64 { return 1 } \
             func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 if cond { \
                     return 0; \
                 } else { \
                     return sink(file); \
                 } \
             }",
        );
        let sink = &module.functions[0];
        let f = &module.functions[1];
        assert_eq!(drop_count(sink), 1);
        assert_eq!(
            drop_count(f),
            1,
            "the `then` branch never moved `file` and must still drop it, independent of the \
             `else` branch's own move"
        );
    }

    #[test]
    fn a_move_inside_a_nested_if_branch_does_not_leak_into_a_sibling_match_arm() {
        // A resource move nested two levels deep (an `if` inside one
        // `match` arm) must still be isolated from a sibling arm's own
        // cleanup, not just a directly-adjacent branch.
        let diags = lower_and_verify(
            "variant Choice { A, B } \
             resource File { descriptor: i64 } \
             func sink(take file: File) -> i64 { return 1 } \
             func f(choice: Choice, cond: bool) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 match choice { \
                     A => { \
                         if cond { return sink(file); } \
                         return 1; \
                     } \
                     B => { return 2; } \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "variant Choice { A, B } \
             resource File { descriptor: i64 } \
             func sink(take file: File) -> i64 { return 1 } \
             func f(choice: Choice, cond: bool) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 match choice { \
                     A => { \
                         if cond { return sink(file); } \
                         return 1; \
                     } \
                     B => { return 2; } \
                 } \
             }",
        );
        let sink = &module.functions[0];
        let f = &module.functions[1];
        assert_eq!(drop_count(sink), 1);
        assert_eq!(
            drop_count(f),
            2,
            "expected a drop on the `Choice.A` arm's own non-taken path and one more on the \
             whole `Choice.B` arm, neither poisoned by the nested `if`'s own move"
        );
    }

    #[test]
    fn a_compound_return_drops_the_unchosen_take_parameter_on_each_branch() {
        // Blocker 2: `return if cond { left } else { right }` must drop
        // exactly the *other* parameter on each branch, and never the
        // one it actually returns -- a single post-merge cleanup point
        // cannot represent this (NIR has no phi node), so `lower_if`'s
        // ordinary shared-slot-then-merge path is not used here at all;
        // each branch gets its own `Return` terminator instead.
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func choose(cond: bool, take left: File, take right: File) -> File { \
                 return if cond { left } else { right }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func choose(cond: bool, take left: File, take right: File) -> File { \
                 return if cond { left } else { right }; \
             }",
        );
        let f = &module.functions[0];
        assert_eq!(
            f.blocks.len(),
            3,
            "expected no shared merge block: entry, then, and else, each with their own Return"
        );
        let returns = f
            .blocks
            .iter()
            .filter(|b| matches!(b.terminator, Terminator::Return(Some(_))))
            .count();
        assert_eq!(returns, 2, "expected a distinct Return on each branch");
        assert_eq!(
            drop_count(f),
            2,
            "expected exactly one drop per branch, dropping the unchosen parameter"
        );
    }

    #[test]
    fn an_implicit_compound_tail_return_drops_the_unchosen_take_parameter() {
        // Same as above, but through the function's own implicit tail
        // return rather than an explicit `return` statement.
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func choose(cond: bool, take left: File, take right: File) -> File { \
                 if cond { left } else { right } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func choose(cond: bool, take left: File, take right: File) -> File { \
                 if cond { left } else { right } \
             }",
        );
        let f = &module.functions[0];
        assert_eq!(
            drop_count(f),
            2,
            "expected exactly one drop per branch, dropping the unchosen parameter"
        );
    }

    #[test]
    fn a_non_resource_compound_return_still_uses_a_shared_merge_block() {
        // The per-branch sink is only needed for resource types
        // (Blocker 2) -- a plain value type keeps the ordinary,
        // simpler shared-slot-then-merge shape, unchanged from before.
        let module = lower("func f(cond: bool) -> i64 { return if cond { 1 } else { 2 }; }");
        let f = &module.functions[0];
        assert_eq!(
            f.blocks.len(),
            4,
            "expected entry, then, else, and a shared merge block"
        );
        let returns = f
            .blocks
            .iter()
            .filter(|b| matches!(b.terminator, Terminator::Return(Some(_))))
            .count();
        assert_eq!(returns, 1, "expected exactly one shared Return");
    }

    #[test]
    fn a_named_return_type_lowers_and_verifies_cleanly() {
        // Alpha 0.1.1: records now have a real aggregate runtime
        // representation, so a named type in a function signature is
        // no longer rejected -- it lowers and verifies like any other
        // type.
        let text = "record Point { x: i64 } func identity(p: Point) -> Point { p } \
                    func main() -> i64 { 42 }";
        let diagnostics = lower_and_verify(text);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_named_parameter_type_lowers_successfully() {
        let text = "record Point { x: i64 } func describe(p: Point) -> i64 { 0 } \
                    func main() -> i64 { 42 }";
        assert!(lower_result(text).is_ok());
    }

    #[test]
    fn variant_names_also_resolve_and_lower_successfully() {
        let text = "variant Shape { Circle } \
                    func describe(s: Shape) -> i64 { 0 } \
                    func main() -> i64 { 42 }";
        assert!(lower_result(text).is_ok());
    }

    #[test]
    fn record_create_orders_fields_by_declaration_not_construction_site() {
        // Written `y` first, `x` second; declaration order is `x, y`.
        let module = lower(
            "record Point { x: i64, y: i64 } \
             func f() -> i64 { value p = Point { y: 2, x: 1 }; return p.x }",
        );
        let instructions: Vec<&Instruction> = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .collect();
        let (record, args) = instructions
            .iter()
            .find_map(|i| match i {
                Instruction::Value {
                    kind: ValueKind::RecordCreate(record, _, args),
                    ..
                } => Some((*record, args.clone())),
                _ => None,
            })
            .expect("expected a record.create instruction");
        // The two const instructions, in source order, produced `2`
        // then `1`; record.create's args must be reordered so the
        // first arg is `x`'s value (1) and the second is `y`'s (2).
        let const_values: HashMap<ValueId, i128> = instructions
            .iter()
            .filter_map(|i| match i {
                Instruction::Value {
                    result,
                    kind: ValueKind::Const(Const::Int(v)),
                    ..
                } => Some((*result, *v as i128)),
                _ => None,
            })
            .collect();
        assert_eq!(args.len(), 2);
        assert_eq!(const_values[&args[0]], 1, "expected x's value first");
        assert_eq!(const_values[&args[1]], 2, "expected y's value second");
        let _ = record;
    }

    #[test]
    fn record_field_initializers_evaluate_exactly_once_in_source_order() {
        let module = lower(
            "record Pair { a: i64, b: i64 } \
             func f() -> i64 { value p = Pair { b: 2, a: 1 }; return p.a }",
        );
        let const_count = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .filter(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Const(Const::Int(_)),
                        ..
                    }
                )
            })
            .count();
        assert_eq!(
            const_count, 2,
            "each field initializer must be evaluated exactly once"
        );
    }

    #[test]
    fn record_field_access_lowers_to_a_resolved_projection() {
        let module = lower(
            "record Point { x: i64, y: i64 } \
             func f() -> i64 { value p = Point { x: 1, y: 2 }; return p.y }",
        );
        let has_field_projection = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::RecordField { field: 1, .. },
                        ..
                    }
                )
            });
        assert!(
            has_field_projection,
            "expected a record.field projection at declaration index 1 (y)"
        );
    }

    #[test]
    fn variant_construction_lowers_explicitly() {
        let module = lower(
            "variant Shape { Circle(i64), Empty } \
             func f() -> i64 { value s = Shape.Circle(7); return 0 }",
        );
        let has_variant_create = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::VariantCreate { case: 0, .. },
                        ..
                    }
                )
            });
        assert!(has_variant_create, "expected a variant.create for case 0");
    }

    #[test]
    fn unit_case_construction_allocates_no_payload() {
        let module = lower(
            "variant Shape { Circle(i64), Empty } \
             func f() -> i64 { value s = Shape.Empty; return 0 }",
        );
        let payload_len = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| match i {
                Instruction::Value {
                    kind:
                        ValueKind::VariantCreate {
                            case: 1, payload, ..
                        },
                    ..
                } => Some(payload.len()),
                _ => None,
            })
            .expect("expected a variant.create for the unit case");
        assert_eq!(payload_len, 0);
    }

    #[test]
    fn variant_match_lowers_to_a_deterministic_switch() {
        let text = "variant Shape { Circle(i64), Square(i64) } \
                     func f(s: Shape) -> i64 { return match s { Circle(v) => v, Square(v) => v } }";
        let a = lower(text);
        let b = lower(text);
        let switches_of = |m: &Module| -> Vec<(ItemId, usize)> {
            m.functions[0]
                .blocks
                .iter()
                .filter_map(|blk| match &blk.terminator {
                    Terminator::Switch { variant, cases, .. } => Some((*variant, cases.len())),
                    _ => None,
                })
                .collect()
        };
        assert_eq!(
            switches_of(&a),
            switches_of(&b),
            "switch lowering must be deterministic across runs"
        );
        assert_eq!(switches_of(&a).len(), 1);
        assert_eq!(switches_of(&a)[0].1, 2, "expected one target per case");
    }

    #[test]
    fn nested_variant_pattern_lowers_to_nested_switches() {
        let text = "variant Inner { X, Y } \
                     variant Outer { A(Inner), B } \
                     func f(o: Outer) -> i64 { \
                         return match o { A(X) => 1, A(Y) => 2, B => 3 } \
                     }";
        let module = lower(text);
        let switch_count = module.functions[0]
            .blocks
            .iter()
            .filter(|b| matches!(b.terminator, Terminator::Switch { .. }))
            .count();
        assert_eq!(
            switch_count, 2,
            "expected one switch for Outer and one for the nested Inner pattern"
        );
    }

    #[test]
    fn fully_diverging_match_allocates_no_result_slot() {
        let text = "variant Shape { Circle, Empty } \
                     func f(s: Shape) -> i64 { \
                         match s { Circle => return 1, Empty => return 2 } \
                     }";
        let module = lower(text);
        let has_alloc = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Alloc,
                        ..
                    }
                )
            });
        assert!(
            !has_alloc,
            "a fully diverging match must not allocate a result slot"
        );
        let diagnostics = lower_and_verify(text);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn value_producing_match_allocates_exactly_one_result_slot() {
        let text = "variant Shape { Circle(i64), Empty } \
                     func f(s: Shape) -> i64 { return match s { Circle(v) => v, Empty => 0 } }";
        let module = lower(text);
        let alloc_count = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .filter(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Alloc,
                        ..
                    }
                )
            })
            .count();
        assert_eq!(alloc_count, 1);
        let diagnostics = lower_and_verify(text);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn payload_bindings_dominate_their_arm_body() {
        // Exercised through the verifier's own dominance analysis: a
        // payload extracted in a case's block, used in that same arm's
        // body (however deeply nested), must never be flagged as a
        // dominance violation.
        let text = "variant Shape { Circle(i64) } \
                     func f(s: Shape) -> i64 { \
                         return match s { Circle(v) => if v > 0 { v } else { 0 - v } } \
                     }";
        let diagnostics = lower_and_verify(text);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn simple_function_lowers_with_no_skips() {
        let module = lower("func add(left: i64, right: i64) -> i64 { return left + right }");
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].params.len(), 2);
    }

    #[test]
    fn literal_takes_its_type_from_typeck_not_a_re_derived_default() {
        // `1`'s type comes from expr_types (typeck already unified it
        // with `x: i32`), not NIR re-inferring it as i64 by default.
        let module = lower("func f(x: i32) -> i32 { return x + 1 }");
        let add_ty = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| match i {
                Instruction::Value {
                    ty,
                    kind: ValueKind::Add(..),
                    ..
                } => Some(ty.clone()),
                _ => None,
            })
            .expect("expected an add instruction");
        assert_eq!(add_ty, Ty::I32);
    }

    #[test]
    fn every_block_has_a_terminator() {
        let module = lower("func f(x: i64) -> i64 { if x > 0 { return 1 } else { return 0 } }");
        for block in &module.functions[0].blocks {
            // Just accessing the field is enough: BasicBlock::terminator
            // is not an Option, so a missing terminator would already
            // have failed to compile/construct.
            let _ = &block.terminator;
        }
    }

    #[test]
    fn finish_blocks_reports_a_missing_terminator_instead_of_panicking() {
        // Every real HIR program this session's fixes could reach is
        // covered by the dedicated CFG tests above; this exercises
        // FnBuilder in isolation to confirm the underlying invariant
        // check itself is a structured error, not a panic, in case a
        // future construct manages to violate it in some other way.
        let mut fb = FnBuilder::new(Ty::Unit);
        // Leaves the entry block (bb0) terminated but this new block
        // (bb1) permanently without one.
        let _dangling = fb.new_block();
        fb.terminate(Terminator::Return(None));
        assert!(
            fb.finish_blocks().is_err(),
            "a block with no terminator must be reported, not silently accepted"
        );
    }

    #[test]
    fn if_expression_lowers_with_cond_branch_and_merge_block() {
        let module = lower("func f(x: bool) -> i64 { return if x { 1 } else { 2 } }");
        let blocks = &module.functions[0].blocks;
        assert!(
            blocks.len() >= 4,
            "expected entry + then + else + merge blocks"
        );
    }

    /// Item 1: an ordinary value-producing `if/else` allocates exactly
    /// one result slot, stores each branch's value into that same slot,
    /// and loads that same slot's value back at the merge point -- the
    /// three instructions must agree on one `ValueId`, not merely exist
    /// somewhere in the function.
    #[test]
    fn if_else_with_real_values_allocates_stores_and_loads_the_same_slot() {
        let module = lower("func f(x: bool) -> i64 { return if x { 1 } else { 2 } }");
        let instructions: Vec<&Instruction> = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .collect();

        let allocs: Vec<ValueId> = instructions
            .iter()
            .filter_map(|i| match i {
                Instruction::Value {
                    result,
                    kind: ValueKind::Alloc,
                    ty: Ty::I64,
                } => Some(*result),
                _ => None,
            })
            .collect();
        assert_eq!(
            allocs.len(),
            1,
            "expected exactly one i64 result slot, found {instructions:?}"
        );
        let slot = allocs[0];

        let stores: Vec<&Instruction> = instructions
            .iter()
            .filter(|i| matches!(i, Instruction::Store { slot: s, .. } if *s == slot))
            .copied()
            .collect();
        assert_eq!(
            stores.len(),
            2,
            "expected one store per branch into the result slot, found {instructions:?}"
        );

        let loads_result_slot = instructions.iter().any(|i| {
            matches!(
                i,
                Instruction::Value { kind: ValueKind::Load(s), .. } if *s == slot
            )
        });
        assert!(
            loads_result_slot,
            "expected the merge block to load the result slot, found {instructions:?}"
        );
    }

    #[test]
    fn if_where_both_branches_diverge_has_no_orphaned_unterminated_block() {
        // Both branches of this `if` return, so its merge block has no
        // predecessor and nothing is ever stored into its result slot --
        // every block must still end in exactly one terminator, and none
        // may load from a slot nothing ever wrote to.
        let module = lower("func f(x: bool) -> i64 { if x { return 1 } else { return 2 } }");
        for block in &module.functions[0].blocks {
            let _ = &block.terminator;
        }
        let has_load_from_result_slot = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Load(_),
                        ..
                    }
                )
            });
        assert!(
            !has_load_from_result_slot,
            "an unreachable merge block must never load a value nothing stored"
        );
    }

    /// Items 5 & 6: a fully diverging `if` produces no result slot at
    /// all -- no `alloc` (of `never` or of anything else attributable
    /// to the `if`'s result), no `store` of a fabricated value, and no
    /// `load` -- and lowers to exactly the entry, then, and else
    /// blocks; no extra merge block is created to be immediately
    /// unreachable.
    #[test]
    fn if_where_both_branches_diverge_allocates_no_result_slot() {
        let module = lower("func f(x: bool) -> i64 { if x { return 1 } else { return 2 } }");
        let blocks = &module.functions[0].blocks;
        assert_eq!(
            blocks.len(),
            3,
            "expected exactly entry + then + else, no merge block: {blocks:?}"
        );

        let instructions: Vec<&Instruction> = blocks.iter().flat_map(|b| &b.instructions).collect();
        assert!(
            !instructions.iter().any(|i| matches!(
                i,
                Instruction::Value {
                    kind: ValueKind::Alloc,
                    ..
                }
            )),
            "a fully diverging `if` must not allocate any result slot: {instructions:?}"
        );
        assert!(
            !instructions
                .iter()
                .any(|i| matches!(i, Instruction::Store { .. })),
            "a fully diverging `if` must not store a fabricated merge value: {instructions:?}"
        );
        assert!(
            !instructions.iter().any(|i| matches!(
                i,
                Instruction::Value {
                    kind: ValueKind::Load(_),
                    ..
                }
            )),
            "a fully diverging `if` must not load a result nothing produced: {instructions:?}"
        );
    }

    /// Item 5 (propagation): when a fully diverging `if` is used as a
    /// statement rather than the function's tail, `LoweredExpr::Diverged`
    /// must stop the surrounding block from lowering anything after it
    /// -- if it didn't, the `99` tail below would still appear as a
    /// `const.i64` instruction in the output.
    #[test]
    fn a_fully_diverging_if_statement_makes_the_rest_of_the_block_unreachable() {
        let module =
            lower("func f(flag: bool) -> i64 { if flag { return 1 } else { return 2 } 99 }");
        let has_99 = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Const(Const::Int(99)),
                        ..
                    }
                )
            });
        assert!(
            !has_99,
            "code after a fully diverging `if` statement must never be lowered"
        );
    }

    /// Item 8: the verifier independently accepts every CFG shape this
    /// fix produces -- real values, an else-less `if`, and a fully
    /// diverging `if` alike.
    #[test]
    fn the_verifier_accepts_every_if_lowering_shape() {
        for text in [
            "func f(x: bool) -> i64 { return if x { 1 } else { 2 } }",
            "func main() { if true { 1 } }",
            "func f(x: bool) -> i64 { if x { return 1 } else { return 2 } }",
            "func f(x: bool) -> i64 { if x { return 1 } else { return 2 } return 0 }",
        ] {
            let diagnostics = lower_and_verify(text);
            assert!(
                diagnostics.is_empty(),
                "unexpected diagnostics for {text:?}: {diagnostics:?}"
            );
        }
    }

    /// Item 9: the builder's own append-after-terminate guard (the
    /// safeguard `fix(nir): enforce block termination invariants` adds
    /// right at the `FnBuilder` API boundary) must actually fire if a
    /// future lowering bug reintroduces this shape -- exercised here by
    /// calling the builder directly, bypassing all real lowering.
    #[test]
    #[should_panic(expected = "already terminated")]
    fn appending_a_value_after_terminate_is_caught_by_the_builder_invariant() {
        let mut fb = FnBuilder::new(Ty::Unit);
        fb.terminate(Terminator::Return(None));
        fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit));
    }

    #[test]
    #[should_panic(expected = "already terminated")]
    fn appending_a_store_after_terminate_is_caught_by_the_builder_invariant() {
        let mut fb = FnBuilder::new(Ty::Unit);
        let slot = fb.alloc_slot(Ty::I64);
        let value = fb.push_value(Ty::I64, ValueKind::Const(Const::Int(1)));
        fb.terminate(Terminator::Return(None));
        fb.push_store(slot, value, crate::nir::OwnershipMode::Observe);
    }

    #[test]
    #[should_panic(expected = "terminated twice")]
    fn terminating_a_block_twice_is_caught_by_the_builder_invariant() {
        let mut fb = FnBuilder::new(Ty::Unit);
        fb.terminate(Terminator::Return(None));
        fb.terminate(Terminator::Return(None));
    }

    #[test]
    fn while_loop_lowers_with_header_body_and_exit_blocks() {
        let module =
            lower("func f() -> i64 { mutable x = 0; while x < 10 { x = x + 1; } return x }");
        assert!(module.functions[0].blocks.len() >= 3);
    }

    #[test]
    fn break_drops_a_resource_declared_earlier_in_the_same_iteration() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 while cond { \
                     value file = File { descriptor: 1 }; \
                     if cond { break; } \
                     drop file; \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 while cond { \
                     value file = File { descriptor: 1 }; \
                     if cond { break; } \
                     drop file; \
                 } \
             }",
        );
        let f = &module.functions[0];
        assert_eq!(
            drop_count(f),
            2,
            "expected one drop on the break path and one on the fallthrough path"
        );
    }

    #[test]
    fn continue_drops_a_resource_declared_earlier_in_the_same_iteration() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 while cond { \
                     value file = File { descriptor: 1 }; \
                     continue; \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 while cond { \
                     value file = File { descriptor: 1 }; \
                     continue; \
                 } \
             }",
        );
        let f = &module.functions[0];
        assert_eq!(
            drop_count(f),
            1,
            "expected the resource to be dropped exactly once, before continue loops back"
        );
    }

    #[test]
    fn a_resource_declared_in_a_nested_block_inside_a_loop_is_dropped_by_break() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 while cond { \
                     { \
                         value file = File { descriptor: 1 }; \
                         if cond { break; } \
                     } \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 while cond { \
                     { \
                         value file = File { descriptor: 1 }; \
                         if cond { break; } \
                     } \
                 } \
             }",
        );
        let f = &module.functions[0];
        assert_eq!(
            drop_count(f),
            2,
            "expected one drop on the break path and one at the nested block's own normal exit"
        );
    }

    #[test]
    fn break_and_a_pending_defer_both_run_in_declaration_reversed_order() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func touch(file: File) -> unit {} \
             func f(cond: bool) { \
                 while cond { \
                     value file = File { descriptor: 1 }; \
                     defer touch(file); \
                     value other = File { descriptor: 2 }; \
                     if cond { break; } \
                     drop other; \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func touch(file: File) -> unit {} \
             func f(cond: bool) { \
                 while cond { \
                     value file = File { descriptor: 1 }; \
                     defer touch(file); \
                     value other = File { descriptor: 2 }; \
                     if cond { break; } \
                     drop other; \
                 } \
             }",
        );
        // Declaration order: `touch` first, `f` second. Registration
        // order within one iteration: file, defer(file), other.
        // Reversed cleanup on *each* exit path (break, and the
        // fallthrough back-edge): drop(other), call(touch), drop(file)
        // -- checked per-block, since a block-level assertion (rather
        // than a whole-function instruction count) is the only way to
        // confirm the ordering rather than merely the totals.
        let f = &module.functions[1];
        let mut saw_correct_sequence_block = false;
        for block in &f.blocks {
            let sequence: Vec<&str> = block
                .instructions
                .iter()
                .filter_map(|i| match i {
                    Instruction::Value {
                        kind: crate::nir::ValueKind::Call(..),
                        ..
                    } => Some("call"),
                    Instruction::Drop { .. } => Some("drop"),
                    _ => None,
                })
                .collect();
            if sequence == vec!["drop", "call", "drop"] {
                saw_correct_sequence_block = true;
            } else if !sequence.is_empty() {
                panic!(
                    "expected only the correct drop/call/drop sequence per exit block, found {sequence:?}"
                );
            }
        }
        assert!(
            saw_correct_sequence_block,
            "expected at least one exit block with other's own drop, then the deferred call, \
             then file's own drop"
        );
    }

    #[test]
    fn break_from_an_inner_loop_does_not_clean_up_the_outer_loops_live_resource() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 while cond { \
                     value outer = File { descriptor: 1 }; \
                     while cond { \
                         if cond { break; } \
                     } \
                     drop outer; \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 while cond { \
                     value outer = File { descriptor: 1 }; \
                     while cond { \
                         if cond { break; } \
                     } \
                     drop outer; \
                 } \
             }",
        );
        let f = &module.functions[0];
        assert_eq!(
            drop_count(f),
            1,
            "the inner loop's own break must not drop the outer loop's still-live resource"
        );
    }

    #[test]
    fn break_and_continue_inside_branches_each_clean_up_correctly() {
        let diags = lower_and_verify(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 while cond { \
                     value file = File { descriptor: 1 }; \
                     if cond { \
                         break; \
                     } else { \
                         continue; \
                     } \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

        let module = lower(
            "resource File { descriptor: i64 } \
             func f(cond: bool) { \
                 while cond { \
                     value file = File { descriptor: 1 }; \
                     if cond { \
                         break; \
                     } else { \
                         continue; \
                     } \
                 } \
             }",
        );
        let f = &module.functions[0];
        assert_eq!(
            drop_count(f),
            2,
            "expected one drop on the break path and one on the continue path, no duplicates"
        );
    }

    #[test]
    fn while_with_a_diverging_condition_lowers_without_orphaned_blocks() {
        // The condition itself always diverges (`return;`), so the loop
        // body and exit blocks are never reachable at all -- lowering
        // must not create them and then leave them without a
        // terminator. `lower()` panics if `finish_blocks` ever finds an
        // untermined block, so simply succeeding is most of this test;
        // the block-count and verifier checks pin down that this
        // particular CFG shape (one block, no dangling successors) is
        // what actually gets produced.
        let module = lower("func main() { while { return; } {} }");
        // bb0 (entry, branches straight to the header) + bb1 (header,
        // terminated by the diverging `return;`) -- and nothing else:
        // the loop body/exit blocks must never be created at all, not
        // created and then left orphaned.
        assert_eq!(
            module.functions[0].blocks.len(),
            2,
            "unexpected block set: {:?}",
            module.functions[0].blocks
        );
        let diagnostics = lower_and_verify("func main() { while { return; } {} }");
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn if_without_else_discards_the_then_value_and_stores_unit() {
        // The then-branch produces an `i64`, but an `if` without `else`
        // is always `unit`-typed (spec/0002); storing the then-branch's
        // real value into the unit-declared merge slot would be a type
        // mismatch the verifier must never see in valid NIR.
        let diagnostics = lower_and_verify("func main() { if true { 1 } }");
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn choose_never_join_is_symmetric_regardless_of_which_branch_diverges() {
        for text in [
            "func choose(flag: bool) -> i64 { if flag { return 1 } else { 2 } } \
             func main() -> i64 { return choose(false) }",
            "func choose(flag: bool) -> i64 { if flag { 2 } else { return 1 } } \
             func main() -> i64 { return choose(true) }",
        ] {
            let diagnostics = lower_and_verify(text);
            assert!(
                diagnostics.is_empty(),
                "unexpected diagnostics for {text:?}: {diagnostics:?}"
            );
        }
    }

    #[test]
    fn a_binding_whose_initializer_diverges_never_gets_a_slot_or_store() {
        // `x`'s initializer diverges before the binding ever completes,
        // so lowering must never allocate a slot for it or store into
        // one -- and the unreachable `x = 2; return x;` after it must
        // never be lowered either.
        let module = lower("func f() -> i64 { mutable x = return 1; x = 2; return x }");
        let has_alloc_or_store = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Alloc,
                        ..
                    } | Instruction::Store { .. }
                )
            });
        assert!(!has_alloc_or_store);
    }

    #[test]
    fn recursive_call_lowers_to_a_call_instruction() {
        let module =
            lower("func fact(n: i64) -> i64 { if n == 0 { return 1 } return n * fact(n - 1) }");
        let has_call = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Call(..),
                        ..
                    }
                )
            });
        assert!(has_call);
    }

    #[test]
    fn mutable_binding_uses_a_slot_immutable_binding_does_not() {
        let module = lower("func f() -> i64 { value a = 1; mutable b = 2; return a + b }");
        let allocs = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .filter(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Alloc,
                        ..
                    }
                )
            })
            .count();
        // Only `b` (mutable) should have allocated a slot; `a` (value)
        // is referenced directly with no alloc/load round-trip.
        assert_eq!(allocs, 1);
    }

    /// Runs the full pipeline through `check_module` but, unlike `lower`
    /// or `lower_result`, does *not* assert that typeck's own
    /// diagnostics are empty -- typeck already gates every construct
    /// tested here with its own diagnostic before lowering would
    /// normally ever run, so this deliberately bypasses that gate to
    /// exercise NIR's own defense-in-depth for a direct caller that
    /// skips typeck entirely (e.g. a tool driving `hir`/`nir` directly).
    fn lower_bypassing_typeck(text: &str) -> Result<Module, Vec<Diagnostic>> {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(
            diags.is_empty(),
            "unexpected resolve diagnostics: {diags:?}"
        );
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            id,
        )
    }

    fn assert_fails_with_i0001(text: &str, expect_in_message: &str) {
        let Err(diagnostics) = lower_bypassing_typeck(text) else {
            panic!("expected lowering to fail for: {text:?}");
        };
        assert!(
            diagnostics.iter().any(|d| d.code == "I0001"),
            "expected an I0001 diagnostic for {text:?}, got {diagnostics:?}"
        );
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains(expect_in_message)),
            "expected a diagnostic mentioning {expect_in_message:?} for {text:?}, got {diagnostics:?}"
        );
    }

    #[test]
    fn record_construction_missing_a_field_fails_lowering_with_i0002_not_a_panic() {
        // hir::lower itself diagnoses a missing field (R0009) but does
        // not synthesize one, so a caller that lowers past *that*
        // diagnostic too (not just typeck's, unlike every other test in
        // this module) reaches NIR lowering with a genuinely incomplete
        // field list. Must fail atomically with a structured
        // diagnostic, never panic and never fabricate the missing
        // field's value.
        let text = "record Point { x: i64, y: i64 } \
                    func f() { value p = Point { x: 1 }; }";
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, resolve_diags) = lower_hir(&module, id, &interner);
        assert!(
            resolve_diags.iter().any(|d| d.code == "R0009"),
            "expected a missing-field diagnostic from hir::lower: {resolve_diags:?}"
        );
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        let outcome = lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            id,
        );
        let Err(diagnostics) = outcome else {
            panic!("expected lowering to fail for a record literal missing a field")
        };
        assert!(
            diagnostics.iter().any(|d| d.code == "I0002"),
            "expected an I0002 diagnostic, got {diagnostics:?}"
        );
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains("missing field")),
            "expected a diagnostic mentioning the missing field, got {diagnostics:?}"
        );
    }

    #[test]
    fn variant_pattern_arity_mismatch_fails_lowering_with_i0002_not_a_silent_truncation() {
        // typeck reports T0002 for this arity mismatch and the normal
        // driver never lowers past it, but a caller that lowers anyway
        // (bypassing that diagnostic gate, like every test in this
        // module using `lower_bypassing_typeck`) must not have the
        // extra sub-pattern silently dropped by a bare `Vec::resize` --
        // it must fail atomically with a structured diagnostic instead.
        let text = "variant Pair { Two(i64, i64) } \
                    func f(p: Pair) -> i64 { return match p { Two(a, b, c) => a } }";
        assert_fails_with_i0002(text, "sub-pattern");
    }

    fn assert_fails_with_i0002(text: &str, expect_in_message: &str) {
        let Err(diagnostics) = lower_bypassing_typeck(text) else {
            panic!("expected lowering to fail for: {text:?}");
        };
        assert!(
            diagnostics.iter().any(|d| d.code == "I0002"),
            "expected an I0002 diagnostic for {text:?}, got {diagnostics:?}"
        );
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains(expect_in_message)),
            "expected a diagnostic mentioning {expect_in_message:?} for {text:?}, got {diagnostics:?}"
        );
    }

    /// A trivial, otherwise-valid `HirFunction` (no params, no return
    /// type, an empty body) -- only its own `id`/`name` matter for the
    /// item-identity tests below, which fail before this function's
    /// body is ever lowered.
    fn minimal_function(id: ItemId, name: Symbol, source: SourceId) -> HirFunction {
        HirFunction {
            id,
            name,
            name_span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            params: vec![],
            return_type: None,
            uses: vec![],
            requirements: Vec::new(),
            raises: vec![],
            body: HirBlock {
                id: ExprId(0),
                statements: vec![],
                tail: None,
                span: Span::dummy(),
            },
            span: Span::dummy(),
        }
    }

    fn minimal_record(id: ItemId, name: Symbol, source: SourceId) -> crate::hir::HirRecord {
        crate::hir::HirRecord {
            id,
            name,
            span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            fields: vec![],
            affine: false,
        }
    }

    fn minimal_variant(id: ItemId, name: Symbol, source: SourceId) -> crate::hir::HirVariant {
        crate::hir::HirVariant {
            id,
            name,
            span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            cases: vec![],
        }
    }

    #[allow(clippy::type_complexity)]
    fn empty_maps() -> (
        HashMap<LocalId, Ty>,
        HashMap<ExprId, Ty>,
        HashMap<PatternId, (ItemId, usize)>,
    ) {
        (HashMap::new(), HashMap::new(), HashMap::new())
    }

    /// A trivial function whose body's tail is `tail_expr` -- used by
    /// the bare-`CaseRef` tests below, which need a real function body
    /// to place a hand-built `HirExpr::CaseRef` in.
    fn function_with_tail(
        id: ItemId,
        name: Symbol,
        tail_expr: HirExpr,
        source: SourceId,
    ) -> HirFunction {
        HirFunction {
            id,
            name,
            name_span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            params: vec![],
            return_type: None,
            uses: vec![],
            requirements: Vec::new(),
            raises: vec![],
            body: HirBlock {
                id: ExprId(100),
                statements: vec![],
                tail: Some(Box::new(tail_expr)),
                span: Span::dummy(),
            },
            span: Span::dummy(),
        }
    }

    #[test]
    fn a_local_never_bound_by_a_param_or_a_let_fails_lowering_not_a_panic() {
        // `local` names no parameter and no preceding `let`-style
        // statement in this function's own body -- `hir::lower`'s own
        // name resolution already rules this out for the ordinary
        // pipeline, but a direct caller hand-building HIR bypasses it.
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let f = interner.intern("f");
        let x = interner.intern("x");
        let unbound_local = LocalId(0);
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function_with_tail(
                ItemId(1),
                f,
                HirExpr::Local {
                    id: ExprId(0),
                    local: unbound_local,
                    name: x,
                    span: Span::dummy(),
                },
                source,
            )],
            records: vec![],
            variants: vec![],
            other_items: vec![],
        };
        let mut expr_types = HashMap::new();
        expr_types.insert(ExprId(0), Ty::I64);
        let (local_types, _, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected lowering to fail for a read of a never-bound local")
        };
        assert!(diagnostics.iter().any(|d| d.code == "I0002"));
    }

    #[test]
    fn assigning_to_an_immutable_local_fails_lowering_not_a_panic() {
        // typeck rejects assigning to a binding that isn't `mutable`
        // before the ordinary pipeline ever reaches lowering, but a
        // direct caller hand-building HIR can still construct one --
        // `x` here is bound as an ordinary (immutable) parameter, never
        // given a slot to assign into.
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let f = interner.intern("f");
        let x = interner.intern("x");
        let x_local = LocalId(0);
        let mut function = function_with_tail(
            ItemId(1),
            f,
            HirExpr::Assign {
                id: ExprId(0),
                target: Box::new(HirExpr::Local {
                    id: ExprId(1),
                    local: x_local,
                    name: x,
                    span: Span::dummy(),
                }),
                op: AssignOp::Assign,
                value: Box::new(HirExpr::Int {
                    id: ExprId(2),
                    value: 1,
                    base: crate::lexer::IntBase::Decimal,
                    span: Span::dummy(),
                }),
                span: Span::dummy(),
            },
            source,
        );
        function.params = vec![crate::hir::HirParam {
            local: x_local,
            name: x,
            span: Span::dummy(),
            ty: crate::hir::HirType::Unresolved {
                name: interner.intern("i64"),
                span: Span::dummy(),
            },
            take: false,
        }];
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: vec![],
            variants: vec![],
            other_items: vec![],
        };
        let mut local_types = HashMap::new();
        local_types.insert(x_local, Ty::I64);
        let mut expr_types = HashMap::new();
        expr_types.insert(ExprId(0), Ty::Unit);
        expr_types.insert(ExprId(1), Ty::I64);
        expr_types.insert(ExprId(2), Ty::I64);
        let pattern_case = HashMap::new();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected lowering to fail for an assignment to an immutable local")
        };
        assert!(diagnostics.iter().any(|d| d.code == "I0002"));
    }

    #[test]
    fn an_else_less_if_typed_as_never_fails_lowering_not_a_panic() {
        // `expr_types` is caller-supplied data a direct caller controls
        // directly -- an else-less `if` can never actually type as
        // `Ty::Never` through the ordinary pipeline (there is no
        // diverging else branch to justify it), but nothing stops a
        // hand-built caller from claiming it does anyway.
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let f = interner.intern("f");
        let if_expr = HirExpr::If {
            id: ExprId(0),
            condition: Box::new(HirExpr::Bool {
                id: ExprId(1),
                value: true,
                span: Span::dummy(),
            }),
            then_branch: HirBlock {
                id: ExprId(2),
                statements: vec![],
                tail: None,
                span: Span::dummy(),
            },
            else_branch: None,
            span: Span::dummy(),
        };
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function_with_tail(ItemId(1), f, if_expr, source)],
            records: vec![],
            variants: vec![],
            other_items: vec![],
        };
        let mut expr_types = HashMap::new();
        expr_types.insert(ExprId(0), Ty::Never);
        expr_types.insert(ExprId(1), Ty::Bool);
        let (local_types, _, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected lowering to fail for an else-less if wrongly typed as never")
        };
        assert!(diagnostics.iter().any(|d| d.code == "I0002"));
    }

    fn case_ref(variant: ItemId, case: usize, name: Symbol) -> HirExpr {
        HirExpr::CaseRef {
            id: ExprId(0),
            variant,
            case,
            name,
            type_args: Vec::new(),
            span: Span::dummy(),
        }
    }

    #[test]
    fn bare_case_ref_to_an_unknown_variant_fails_lowering_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let f = interner.intern("f");
        let case_name = interner.intern("Empty");
        let unknown_variant = ItemId(0);
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function_with_tail(
                ItemId(1),
                f,
                case_ref(unknown_variant, 0, case_name),
                source,
            )],
            records: vec![],
            variants: vec![],
            other_items: vec![],
        };
        let mut expr_types = HashMap::new();
        expr_types.insert(ExprId(0), Ty::Named(unknown_variant, case_name));
        let local_types = HashMap::new();
        let pattern_case = HashMap::new();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a bare case ref to an unknown variant to fail lowering")
        };
        assert!(diagnostics.iter().any(|d| d.code == "I0002"));
    }

    #[test]
    fn bare_case_ref_with_an_invalid_case_index_fails_lowering_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let f = interner.intern("f");
        let variant_sym = interner.intern("Shape");
        let case_name = interner.intern("Empty");
        let variant_item = ItemId(0);
        let variant = minimal_variant(variant_item, variant_sym, source);
        // Case index 7 does not exist -- the variant declares no cases
        // at all.
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function_with_tail(
                ItemId(1),
                f,
                case_ref(variant_item, 7, case_name),
                source,
            )],
            records: vec![],
            variants: vec![variant],
            other_items: vec![],
        };
        let mut expr_types = HashMap::new();
        expr_types.insert(ExprId(0), Ty::Named(variant_item, variant_sym));
        let local_types = HashMap::new();
        let pattern_case = HashMap::new();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a bare case ref with an invalid case index to fail lowering")
        };
        assert!(diagnostics.iter().any(|d| d.code == "I0002"));
    }

    #[test]
    fn bare_case_ref_to_a_payload_carrying_case_fails_lowering_not_a_panic() {
        // `Shape.Circle` written bare (no call parens) against a case
        // that actually carries a payload must be rejected, not
        // silently construct it with an empty payload.
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let f = interner.intern("f");
        let variant_sym = interner.intern("Shape");
        let case_name = interner.intern("Circle");
        let variant_item = ItemId(0);
        let variant = crate::hir::HirVariant {
            id: variant_item,
            name: variant_sym,
            span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            cases: vec![crate::hir::HirCase {
                name: case_name,
                span: Span::dummy(),
                payload: vec![crate::hir::HirType::Unresolved {
                    name: interner.intern("i64"),
                    span: Span::dummy(),
                }],
            }],
        };
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function_with_tail(
                ItemId(1),
                f,
                case_ref(variant_item, 0, case_name),
                source,
            )],
            records: vec![],
            variants: vec![variant],
            other_items: vec![],
        };
        let mut expr_types = HashMap::new();
        expr_types.insert(ExprId(0), Ty::Named(variant_item, variant_sym));
        let local_types = HashMap::new();
        let pattern_case = HashMap::new();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a bare case ref to a payload-carrying case to fail lowering")
        };
        assert!(diagnostics.iter().any(|d| d.code == "I0002"));
    }

    /// Two variants named `Err`, one declared in module `a` and one in
    /// module `b`, raised by the same function -- `canonical_raises`
    /// must order them by their *declaring module's own path*, never by
    /// declaration order (of either the `variants` list or the
    /// function's own `raises` clause) and never by raw `ItemId`. Run
    /// with the module-list order and the `raises`-clause order each
    /// reversed relative to the other, both must produce the identical
    /// canonical order.
    fn assert_err_variants_canonicalize_by_module_path(
        variants_in_b_then_a_order: bool,
        raises_in_b_then_a_order: bool,
    ) {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source_a = map.add_file("a.npt", "");
        let source_b = map.add_file("b.npt", "");
        let manifest_source = map.add_file("main.npt", "");
        let err_name = interner.intern("Err");
        let f_name = interner.intern("f");
        let item_a = ItemId(0);
        let item_b = ItemId(1);
        let variant_a = minimal_variant(item_a, err_name, source_a);
        let variant_b = minimal_variant(item_b, err_name, source_b);
        let variants = if variants_in_b_then_a_order {
            vec![variant_b, variant_a]
        } else {
            vec![variant_a, variant_b]
        };
        let mut module_path_of = HashMap::new();
        module_path_of.insert(source_a, "a".to_string());
        module_path_of.insert(source_b, "b".to_string());

        let entry_a = crate::hir::HirRaisesEntry {
            variant: item_a,
            name: err_name,
            span: Span::dummy(),
        };
        let entry_b = crate::hir::HirRaisesEntry {
            variant: item_b,
            name: err_name,
            span: Span::dummy(),
        };
        let mut function = function_with_tail(
            ItemId(2),
            f_name,
            HirExpr::Int {
                id: ExprId(0),
                value: 0,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            },
            manifest_source,
        );
        function.raises = if raises_in_b_then_a_order {
            vec![entry_b, entry_a]
        } else {
            vec![entry_a, entry_b]
        };

        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: vec![],
            variants,
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let empty_affine = crate::resourceck::AffineContext {
            aggregate_field_types: &HashMap::new(),
            declared_resources: &HashSet::new(),
            item_type_params: &HashMap::new(),
            field_projections: &HashMap::new(),
        };
        let resourceck_result = crate::resourceck::check_module(
            &module,
            &local_types,
            &expr_types,
            &interner,
            &empty_affine,
        );
        let result = lower_module_with_paths(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &resourceck_result.cleanup_edges,
            &resourceck_result.consume_sites,
            &resourceck_result.defer_plans,
            &interner,
            manifest_source,
            &module_path_of,
        )
        .expect("lowering with two distinct-module, same-name variants should succeed");
        let f = result
            .functions
            .iter()
            .find(|f| f.id == ItemId(2))
            .expect("lowered function must be present");
        assert_eq!(
            f.raises,
            vec![item_a, item_b],
            "module `a`'s variant must sort before module `b`'s regardless of declaration order"
        );
    }

    #[test]
    fn canonical_raises_orders_by_module_path_with_b_declared_before_a() {
        assert_err_variants_canonicalize_by_module_path(true, true);
    }

    #[test]
    fn canonical_raises_orders_by_module_path_with_a_declared_before_b() {
        assert_err_variants_canonicalize_by_module_path(false, false);
    }

    #[test]
    fn a_raises_entry_missing_its_project_module_path_entry_is_a_diagnostic_not_an_empty_path() {
        // `module_path_of` here is non-empty (as it always is in real
        // project compilation, `project::compile`), but has no entry at
        // all for `source_a`, the raised variant's own declaring module
        // -- unreachable through the ordinary pipeline (project::compile
        // always builds one entry per module it actually loaded), but a
        // direct caller of `lower_module_with_paths` could still hand
        // this an incomplete table. Distinct from single-file mode
        // (`module_path_of` empty), where every path is legitimately
        // empty: here a missing entry must fail atomically with I0002,
        // never silently canonicalize as though the variant belonged to
        // the project's root module.
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source_a = map.add_file("a.npt", "");
        let source_b = map.add_file("b.npt", "");
        let manifest_source = map.add_file("main.npt", "");
        let err_name = interner.intern("Err");
        let f_name = interner.intern("f");
        let item_a = ItemId(0);
        let variant_a = minimal_variant(item_a, err_name, source_a);
        // Non-empty (this is project mode), but deliberately missing
        // `source_a`'s own entry -- only `source_b`'s is present, e.g.
        // some unrelated sibling module in the same project.
        let mut module_path_of = HashMap::new();
        module_path_of.insert(source_b, "b".to_string());

        let entry_a = crate::hir::HirRaisesEntry {
            variant: item_a,
            name: err_name,
            span: Span::dummy(),
        };
        let mut function = function_with_tail(
            ItemId(1),
            f_name,
            HirExpr::Int {
                id: ExprId(0),
                value: 0,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            },
            manifest_source,
        );
        function.raises = vec![entry_a];

        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: vec![],
            variants: vec![variant_a],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module_with_paths(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            manifest_source,
            &module_path_of,
        );
        let Err(diagnostics) = result else {
            panic!("expected a missing project module-path entry to fail lowering")
        };
        assert!(
            diagnostics.iter().any(|d| d.code == "I0002"),
            "expected I0002, got {diagnostics:?}"
        );
    }

    #[test]
    fn lower_module_with_paths_given_a_completely_empty_map_is_still_project_mode() {
        // `lower_module_with_paths` always runs in `ModulePathMode::
        // Project`, even when its own `module_path_of` happens to be
        // completely empty -- an `is_empty()` sentinel would have
        // treated this identically to `lower_module`'s own single-file
        // mode and silently canonicalized with an empty path; here it
        // must instead fail atomically with I0002, since a real project
        // caller's table is never actually empty (`project::compile`
        // always builds one entry per loaded module) and an empty one
        // can only mean a genuine gap.
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source_a = map.add_file("a.npt", "");
        let manifest_source = map.add_file("main.npt", "");
        let err_name = interner.intern("Err");
        let f_name = interner.intern("f");
        let item_a = ItemId(0);
        let variant_a = minimal_variant(item_a, err_name, source_a);

        let entry_a = crate::hir::HirRaisesEntry {
            variant: item_a,
            name: err_name,
            span: Span::dummy(),
        };
        let mut function = function_with_tail(
            ItemId(1),
            f_name,
            HirExpr::Int {
                id: ExprId(0),
                value: 0,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            },
            manifest_source,
        );
        function.raises = vec![entry_a];

        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: vec![],
            variants: vec![variant_a],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module_with_paths(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            manifest_source,
            &HashMap::new(),
        );
        let Err(diagnostics) = result else {
            panic!("expected a completely empty project module-path map to fail lowering")
        };
        assert!(
            diagnostics.iter().any(|d| d.code == "I0002"),
            "expected I0002, got {diagnostics:?}"
        );
    }

    #[test]
    fn duplicate_record_id_fails_lowering_atomically_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![],
            records: vec![
                minimal_record(ItemId(0), a, source),
                minimal_record(ItemId(0), b, source),
            ],
            variants: vec![],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a duplicate record id to fail lowering")
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert_eq!(diagnostics[0].code, "I0002");
        assert!(diagnostics[0].message.contains("record"));
    }

    #[test]
    fn duplicate_variant_id_fails_lowering_atomically_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![],
            records: vec![],
            variants: vec![
                minimal_variant(ItemId(0), a, source),
                minimal_variant(ItemId(0), b, source),
            ],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a duplicate variant id to fail lowering")
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert_eq!(diagnostics[0].code, "I0002");
        assert!(diagnostics[0].message.contains("variant"));
    }

    #[test]
    fn duplicate_function_id_fails_lowering_atomically_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let f = interner.intern("f");
        let g = interner.intern("g");
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![
                minimal_function(ItemId(0), f, source),
                minimal_function(ItemId(0), g, source),
            ],
            records: vec![],
            variants: vec![],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a duplicate function id to fail lowering")
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert_eq!(diagnostics[0].code, "I0002");
        assert!(diagnostics[0].message.contains("function"));
    }

    #[test]
    fn record_variant_id_collision_fails_lowering_atomically_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![],
            records: vec![minimal_record(ItemId(0), a, source)],
            variants: vec![minimal_variant(ItemId(0), b, source)],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a record/variant id collision to fail lowering")
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert_eq!(diagnostics[0].code, "I0002");
        assert!(
            diagnostics[0].message.contains("record") && diagnostics[0].message.contains("variant")
        );
    }

    #[test]
    fn function_aggregate_id_collision_fails_lowering_atomically_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let f = interner.intern("f");
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![minimal_function(ItemId(0), f, source)],
            records: vec![minimal_record(ItemId(0), a, source)],
            variants: vec![],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a function/record id collision to fail lowering")
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert_eq!(diagnostics[0].code, "I0002");
        assert!(
            diagnostics[0].message.contains("function")
                && diagnostics[0].message.contains("record")
        );
    }

    #[test]
    fn multiple_id_collisions_produce_deterministic_diagnostics_in_declaration_order() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let c = interner.intern("C");
        let d = interner.intern("D");
        // Two independent collisions: records 0/0, then variants 1/1.
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![],
            records: vec![
                minimal_record(ItemId(0), a, source),
                minimal_record(ItemId(0), b, source),
            ],
            variants: vec![
                minimal_variant(ItemId(1), c, source),
                minimal_variant(ItemId(1), d, source),
            ],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let build = || {
            lower_module(
                &module,
                &local_types,
                &expr_types,
                &pattern_case,
                &HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &interner,
                source,
            )
        };
        let Err(first) = build() else {
            panic!("expected multiple id collisions to fail lowering")
        };
        assert_eq!(first.len(), 2, "unexpected diagnostics: {first:?}");
        assert!(first.iter().all(|d| d.code == "I0002"));
        // Declaration order (records before variants), run twice to
        // confirm it is the same order every time -- never a HashMap's
        // iteration order.
        let Err(second) = build() else {
            panic!("expected the second run to fail lowering too")
        };
        let first_messages: Vec<&str> = first.iter().map(|d| d.message.as_str()).collect();
        let second_messages: Vec<&str> = second.iter().map(|d| d.message.as_str()).collect();
        assert_eq!(first_messages, second_messages);
        assert!(first_messages[0].contains("record"));
        assert!(first_messages[1].contains("variant"));
    }

    /// Builds a `Lowering` directly (bypassing the whole lex/parse/hir/
    /// typeck pipeline entirely, not just typeck's diagnostic gate) so a
    /// single aggregate-lowering method can be exercised with an
    /// out-of-range index no real frontend ever produces -- the only way
    /// to reach these defense-in-depth paths at all, since `hir::lower`'s
    /// own name resolution never emits a case/field index outside its
    /// declaration's real range.
    fn direct_lowering<'a>(
        source: SourceId,
        interner: &'a Interner,
        local_types: &'a HashMap<LocalId, Ty>,
        expr_types: &'a HashMap<ExprId, Ty>,
        pattern_case: &'a HashMap<PatternId, (ItemId, usize)>,
        records: HashMap<ItemId, RecordLayout>,
        variants: HashMap<ItemId, VariantLayout>,
    ) -> Lowering<'a> {
        Lowering {
            local_types,
            expr_types,
            pattern_case,
            interner,
            source,
            module_path_mode: ModulePathMode::SingleFile,
            records,
            variants,
            variant_source: HashMap::new(),
            function_sigs: HashMap::new(),
            call_type_args: Box::leak(Box::new(HashMap::new())),
            call_evidence: Box::leak(Box::new(HashMap::new())),
            protocol_call_evidence: Box::leak(Box::new(HashMap::new())),
            function_requirements: HashMap::new(),
            function_raises: HashMap::new(),
            function_named_type_params: HashMap::new(),
            cleanup_edges: Box::leak(Box::new(BTreeMap::new())),
            consume_sites: Box::leak(Box::new(BTreeMap::new())),
            defer_plans: Box::leak(Box::new(BTreeMap::new())),
        }
    }

    /// Like `direct_lowering`, but with a caller-supplied `function_sigs`
    /// and `call_type_args`, for tests that need to control exactly what
    /// generic call-site metadata (or lack of it) a direct lowering call
    /// sees.
    #[allow(clippy::too_many_arguments)]
    fn direct_lowering_with_generics<'a>(
        source: SourceId,
        interner: &'a Interner,
        local_types: &'a HashMap<LocalId, Ty>,
        expr_types: &'a HashMap<ExprId, Ty>,
        pattern_case: &'a HashMap<PatternId, (ItemId, usize)>,
        records: HashMap<ItemId, RecordLayout>,
        variants: HashMap<ItemId, VariantLayout>,
        function_sigs: HashMap<ItemId, (Vec<crate::hir::TypeParamId>, Vec<Ty>, Ty)>,
        call_type_args: &'a HashMap<ExprId, Vec<Ty>>,
    ) -> Lowering<'a> {
        Lowering {
            local_types,
            expr_types,
            pattern_case,
            interner,
            source,
            module_path_mode: ModulePathMode::SingleFile,
            records,
            variants,
            variant_source: HashMap::new(),
            function_sigs,
            call_type_args,
            call_evidence: Box::leak(Box::new(HashMap::new())),
            protocol_call_evidence: Box::leak(Box::new(HashMap::new())),
            function_requirements: HashMap::new(),
            function_raises: HashMap::new(),
            function_named_type_params: HashMap::new(),
            cleanup_edges: Box::leak(Box::new(BTreeMap::new())),
            consume_sites: Box::leak(Box::new(BTreeMap::new())),
            defer_plans: Box::leak(Box::new(BTreeMap::new())),
        }
    }

    #[test]
    fn a_generic_call_missing_its_recorded_type_arguments_fails_with_i0002_not_a_panic() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let callee_item = ItemId(0);
        let t = crate::hir::TypeParamId(0);
        let mut function_sigs = HashMap::new();
        function_sigs.insert(
            callee_item,
            (
                vec![t],
                vec![Ty::Param(t, interner.intern("T"))],
                Ty::Param(t, interner.intern("T")),
            ),
        );
        let g_name = interner.intern("g");
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
            function_sigs,
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let callee = HirExpr::Function {
            id: ExprId(0),
            item: callee_item,
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        let call_expr = HirExpr::Call {
            id: ExprId(1),
            callee: Box::new(callee.clone()),
            args: Vec::new(),
            span: Span::dummy(),
        };
        let result = lowering.lower_call(&mut fb, &callee, &[], &call_expr);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for a generic call with no recorded type arguments")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_generic_call_with_the_wrong_number_of_recorded_type_arguments_fails_with_i0002() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let callee_item = ItemId(0);
        let t = crate::hir::TypeParamId(0);
        let mut function_sigs = HashMap::new();
        function_sigs.insert(
            callee_item,
            (
                vec![t],
                vec![Ty::Param(t, interner.intern("T"))],
                Ty::Param(t, interner.intern("T")),
            ),
        );
        let g_name = interner.intern("g");
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_expr_id = ExprId(1);
        let mut call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        // `g` declares one type parameter; two are recorded here.
        call_type_args.insert(call_expr_id, vec![Ty::I64, Ty::Bool]);
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
            function_sigs,
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let callee = HirExpr::Function {
            id: ExprId(0),
            item: callee_item,
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        let call_expr = HirExpr::Call {
            id: call_expr_id,
            callee: Box::new(callee.clone()),
            args: Vec::new(),
            span: Span::dummy(),
        };
        let result = lowering.lower_call(&mut fb, &callee, &[], &call_expr);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for a call with mismatched type-argument arity")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_generic_variant_construction_missing_its_recorded_type_arguments_fails_with_i0002() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let variant_item = ItemId(0);
        let t = crate::hir::TypeParamId(0);
        let mut variants = HashMap::new();
        variants.insert(
            variant_item,
            VariantLayout {
                name: interner.intern("Maybe"),
                type_params: vec![(t, interner.intern("T"))],
                cases: vec![CaseLayout {
                    name: interner.intern("Some"),
                    payload: vec![Ty::Param(t, interner.intern("T"))],
                }],
            },
        );
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            variants,
            HashMap::new(),
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let arg = HirExpr::Int {
            id: ExprId(1),
            value: 1,
            base: crate::lexer::IntBase::Decimal,
            span: Span::dummy(),
        };
        let args = vec![arg];
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_variant_construct(&mut fb, variant_item, 0, &args, &probe);
        let Err(diagnostic) = result else {
            panic!(
                "expected lowering to fail for a generic variant construction with no recorded type arguments"
            )
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_bare_generic_unit_case_missing_its_recorded_type_arguments_fails_with_i0002() {
        // The same lowering path a `Some(...)` call goes through above,
        // exercised via a *bare* unit-case reference instead (no call
        // syntax, empty argument list) -- `Maybe[i64].None` must be
        // rejected here exactly the same way, never silently defaulting
        // to an empty (and therefore wrong-arity) type-argument list.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let variant_item = ItemId(0);
        let t = crate::hir::TypeParamId(0);
        let mut variants = HashMap::new();
        variants.insert(
            variant_item,
            VariantLayout {
                name: interner.intern("Maybe"),
                type_params: vec![(t, interner.intern("T"))],
                cases: vec![CaseLayout {
                    name: interner.intern("None"),
                    payload: vec![],
                }],
            },
        );
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            variants,
            HashMap::new(),
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_variant_construct(&mut fb, variant_item, 0, &[], &probe);
        let Err(diagnostic) = result else {
            panic!(
                "expected lowering to fail for a bare generic unit case with no recorded type arguments"
            )
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_generic_record_construction_with_the_wrong_number_of_recorded_type_arguments_fails() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let record_item = ItemId(0);
        let t = crate::hir::TypeParamId(0);
        let mut records = HashMap::new();
        records.insert(
            record_item,
            RecordLayout {
                name: interner.intern("Box"),
                type_params: vec![(t, interner.intern("T"))],
                fields: vec![(interner.intern("value"), Ty::Param(t, interner.intern("T")))],
                affine: false,
            },
        );
        let (local_types, expr_types, pattern_case) = empty_maps();
        let literal_expr_id = ExprId(1);
        let mut call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        // `Box` declares one type parameter; two are recorded here.
        call_type_args.insert(literal_expr_id, vec![Ty::I64, Ty::Bool]);
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            records,
            HashMap::new(),
            HashMap::new(),
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let init = HirFieldInit {
            field_index: 0,
            value: HirExpr::Int {
                id: ExprId(2),
                value: 1,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            },
            span: Span::dummy(),
        };
        let probe = HirExpr::Bool {
            id: literal_expr_id,
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_record_literal(&mut fb, record_item, &[init], &probe);
        let Err(diagnostic) = result else {
            panic!(
                "expected lowering to fail for a record construction with mismatched type-argument arity"
            )
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_non_generic_call_missing_type_argument_metadata_still_lowers() {
        // No declared type parameters at all -- absent call_type_args
        // metadata is exactly the valid, expected case here (an empty
        // argument list), never an error.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let callee_item = ItemId(0);
        let mut function_sigs = HashMap::new();
        function_sigs.insert(callee_item, (Vec::new(), Vec::new(), Ty::I64));
        let g_name = interner.intern("g");
        let (local_types, _, pattern_case) = empty_maps();
        let mut expr_types: HashMap<ExprId, Ty> = HashMap::new();
        expr_types.insert(ExprId(1), Ty::I64);
        let call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
            function_sigs,
            &call_type_args,
        );
        // A genuinely infallible, requirement-free callee still needs
        // its own (empty) entry registered -- lower_call/lower_invoke's
        // shared lookup helpers never fabricate one for a missing entry
        // (Fix 6), so this test declares it explicitly rather than
        // relying on the test harness's own otherwise-empty default map.
        lowering
            .function_requirements
            .insert(callee_item, Vec::new());
        lowering.function_raises.insert(callee_item, Vec::new());
        let mut fb = FnBuilder::new(Ty::I64);
        let callee = HirExpr::Function {
            id: ExprId(0),
            item: callee_item,
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        let call_expr = HirExpr::Call {
            id: ExprId(1),
            callee: Box::new(callee.clone()),
            args: Vec::new(),
            span: Span::dummy(),
        };
        let result = lowering.lower_call(&mut fb, &callee, &[], &call_expr);
        assert!(
            result.is_ok(),
            "a non-generic call must lower cleanly with no recorded type arguments: {result:?}"
        );
    }

    // -- Fix 6: no fake metadata fallbacks in lower_call/lower_invoke ---

    #[test]
    fn a_call_to_a_function_with_no_registered_signature_fails_lowering_atomically() {
        // `function_sigs` never has an entry for `callee_item` at all --
        // must fail with a structured diagnostic, never silently
        // fabricate a zero-argument, `Ty::Error`-returning signature.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let callee_item = ItemId(0);
        let g_name = interner.intern("g");
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let callee = HirExpr::Function {
            id: ExprId(0),
            item: callee_item,
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        let call_expr = HirExpr::Call {
            id: ExprId(1),
            callee: Box::new(callee.clone()),
            args: Vec::new(),
            span: Span::dummy(),
        };
        let result = lowering.lower_call(&mut fb, &callee, &[], &call_expr);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for a call with no registered signature")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_call_to_a_function_missing_capability_requirement_metadata_fails_lowering_atomically() {
        // `function_sigs` has a real entry, but `function_requirements`
        // was never populated for it at all -- distinct from genuinely
        // declaring an empty requirement list (`Some(vec![])`), and must
        // fail rather than silently treat "missing" the same as "none".
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let callee_item = ItemId(0);
        let mut function_sigs = HashMap::new();
        function_sigs.insert(callee_item, (Vec::new(), Vec::new(), Ty::I64));
        let g_name = interner.intern("g");
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
            function_sigs,
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let callee = HirExpr::Function {
            id: ExprId(0),
            item: callee_item,
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        let call_expr = HirExpr::Call {
            id: ExprId(1),
            callee: Box::new(callee.clone()),
            args: Vec::new(),
            span: Span::dummy(),
        };
        let result = lowering.lower_call(&mut fb, &callee, &[], &call_expr);
        let Err(diagnostic) = result else {
            panic!(
                "expected lowering to fail for a call whose callee has no registered capability requirements"
            )
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn an_invoke_of_a_function_missing_raised_effect_metadata_fails_lowering_atomically() {
        // `function_sigs`/`function_requirements` both have real
        // (empty) entries, but `function_raises` was never populated at
        // all -- must fail rather than silently treat this callee as
        // infallible.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let callee_item = ItemId(0);
        let mut function_sigs = HashMap::new();
        function_sigs.insert(callee_item, (Vec::new(), Vec::new(), Ty::I64));
        let g_name = interner.intern("g");
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
            function_sigs,
            &call_type_args,
        );
        lowering
            .function_requirements
            .insert(callee_item, Vec::new());
        let mut fb = FnBuilder::new(Ty::I64);
        let callee = HirExpr::Function {
            id: ExprId(0),
            item: callee_item,
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        let operand = HirExpr::Call {
            id: ExprId(1),
            callee: Box::new(callee),
            args: Vec::new(),
            span: Span::dummy(),
        };
        let result = lowering.lower_invoke(&mut fb, &operand, "postfix `?`", None);
        let Err(diagnostic) = result else {
            panic!(
                "expected lowering to fail for an invoke whose callee has no registered raises metadata"
            )
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_valid_fallible_generic_call_lowers_through_invoke_with_no_diagnostics() {
        // A generic callee declaring a real (non-empty) raises set, all
        // three metadata maps genuinely populated -- the positive
        // counterpart to the three failing cases above, confirming the
        // strict lookups don't reject a legitimately well-formed invoke.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let callee_item = ItemId(0);
        let error_item = ItemId(1);
        let t = crate::hir::TypeParamId(0);
        let t_symbol = interner.intern("T");
        let mut function_sigs = HashMap::new();
        function_sigs.insert(
            callee_item,
            (
                vec![t],
                vec![Ty::Param(t, t_symbol)],
                Ty::Param(t, t_symbol),
            ),
        );
        let mut variants = HashMap::new();
        let error_name = interner.intern("Failure");
        let case_name = interner.intern("Broken");
        variants.insert(
            error_item,
            VariantLayout {
                name: error_name,
                type_params: Vec::new(),
                cases: vec![CaseLayout {
                    name: case_name,
                    payload: Vec::new(),
                }],
            },
        );
        let g_name = interner.intern("g");
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_expr_id = ExprId(1);
        let mut call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        call_type_args.insert(call_expr_id, vec![Ty::I64]);
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            variants,
            function_sigs,
            &call_type_args,
        );
        lowering
            .function_requirements
            .insert(callee_item, Vec::new());
        lowering
            .function_raises
            .insert(callee_item, vec![error_item]);
        let mut fb = FnBuilder::new(Ty::I64);
        let callee = HirExpr::Function {
            id: ExprId(0),
            item: callee_item,
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        let arg = HirExpr::Int {
            id: ExprId(2),
            value: 0,
            base: crate::lexer::IntBase::Decimal,
            span: Span::dummy(),
        };
        let operand = HirExpr::Call {
            id: call_expr_id,
            callee: Box::new(callee),
            args: vec![arg],
            span: Span::dummy(),
        };
        let result = lowering.lower_invoke(&mut fb, &operand, "postfix `?`", None);
        let Ok(Some((ret_ty, _, _, err_blocks, _))) = result else {
            panic!("expected a valid fallible generic invoke to lower successfully: {result:?}")
        };
        assert_eq!(ret_ty, Ty::I64);
        assert_eq!(err_blocks.len(), 1);
        assert_eq!(err_blocks[0].0, error_item);
    }

    #[test]
    fn direct_variant_construction_with_an_unknown_case_index_fails_with_i0002_not_a_panic() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let variant_item = ItemId(0);
        let mut variants = HashMap::new();
        variants.insert(
            variant_item,
            VariantLayout {
                name: interner.intern("V"),
                type_params: Vec::new(),
                cases: vec![CaseLayout {
                    name: interner.intern("A"),
                    payload: vec![Ty::I64],
                }],
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            variants,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        // Case index 7 does not exist on a variant with a single case.
        let result = lowering.lower_variant_construct(&mut fb, variant_item, 7, &[], &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for an unknown case index")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn direct_record_construction_with_an_out_of_range_field_index_fails_with_i0002_not_a_panic() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let record_item = ItemId(0);
        let mut records = HashMap::new();
        records.insert(
            record_item,
            RecordLayout {
                name: interner.intern("Point"),
                type_params: Vec::new(),
                fields: vec![(interner.intern("x"), Ty::I64)],
                affine: false,
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            records,
            HashMap::new(),
        );
        let mut fb = FnBuilder::new(Ty::I64);
        // Field index 9 does not exist on a record with a single field
        // -- rejected up front, before its initializer is ever
        // evaluated, rather than silently dropped into nowhere.
        let bad_init = HirFieldInit {
            field_index: 9,
            value: HirExpr::Bool {
                id: ExprId(1),
                value: true,
                span: Span::dummy(),
            },
            span: Span::dummy(),
        };
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_record_literal(&mut fb, record_item, &[bad_init], &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for an out-of-range field index")
        };
        assert_eq!(diagnostic.code, "I0002");
        assert!(
            diagnostic.message.contains("out of range"),
            "expected an out-of-range diagnostic, got: {}",
            diagnostic.message
        );
    }

    #[test]
    fn all_valid_record_fields_plus_one_out_of_range_field_fails_atomically() {
        // Every genuinely declared field is present and correct; the
        // one extra field beyond the record's own layout must still
        // reject the whole construction, not just be ignored while the
        // rest lowers successfully.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let record_item = ItemId(0);
        let mut records = HashMap::new();
        records.insert(
            record_item,
            RecordLayout {
                name: interner.intern("Point"),
                type_params: Vec::new(),
                fields: vec![
                    (interner.intern("x"), Ty::I64),
                    (interner.intern("y"), Ty::I64),
                ],
                affine: false,
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            records,
            HashMap::new(),
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let init = |field_index: usize, id: u32| HirFieldInit {
            field_index,
            value: HirExpr::Int {
                id: ExprId(id),
                value: 1,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            },
            span: Span::dummy(),
        };
        let fields = vec![init(0, 1), init(1, 2), init(2, 3)];
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_record_literal(&mut fb, record_item, &fields, &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for an extra out-of-range field")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn duplicate_field_index_with_every_other_field_present_fails_atomically() {
        // Every field index the record actually declares is covered --
        // 0 is just covered twice, at the cost of 1 never being
        // written -- so this can't be caught as "missing" without also
        // catching the duplicate itself; the second write to index 0
        // must never silently overwrite the first's already-lowered
        // value in its temporary slot.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let record_item = ItemId(0);
        let mut records = HashMap::new();
        records.insert(
            record_item,
            RecordLayout {
                name: interner.intern("Point"),
                type_params: Vec::new(),
                fields: vec![
                    (interner.intern("x"), Ty::I64),
                    (interner.intern("y"), Ty::I64),
                ],
                affine: false,
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            records,
            HashMap::new(),
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let init = |field_index: usize, id: u32| HirFieldInit {
            field_index,
            value: HirExpr::Int {
                id: ExprId(id),
                value: 1,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            },
            span: Span::dummy(),
        };
        let fields = vec![init(0, 1), init(0, 2)];
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_record_literal(&mut fb, record_item, &fields, &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for a duplicate field index")
        };
        assert_eq!(diagnostic.code, "I0002");
        assert!(
            diagnostic.message.contains("more than once"),
            "expected a duplicate-index diagnostic, got: {}",
            diagnostic.message
        );
    }

    #[test]
    fn unknown_record_id_fails_lowering_instead_of_using_the_provided_field_count() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let interner = Interner::new();
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_record_literal(&mut fb, ItemId(0), &[], &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for an unknown record")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn too_many_variant_payload_arguments_fails_lowering_instead_of_a_longer_payload() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let variant_item = ItemId(0);
        let mut variants = HashMap::new();
        variants.insert(
            variant_item,
            VariantLayout {
                name: interner.intern("V"),
                type_params: Vec::new(),
                cases: vec![CaseLayout {
                    name: interner.intern("A"),
                    payload: vec![Ty::I64],
                }],
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            variants,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let arg = |id: u32| HirExpr::Int {
            id: ExprId(id),
            value: 1,
            base: crate::lexer::IntBase::Decimal,
            span: Span::dummy(),
        };
        let args = vec![arg(1), arg(2)];
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_variant_construct(&mut fb, variant_item, 0, &args, &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for too many payload arguments")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn too_few_variant_payload_arguments_fails_lowering_instead_of_a_shorter_payload() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let variant_item = ItemId(0);
        let mut variants = HashMap::new();
        variants.insert(
            variant_item,
            VariantLayout {
                name: interner.intern("V"),
                type_params: Vec::new(),
                cases: vec![CaseLayout {
                    name: interner.intern("A"),
                    payload: vec![Ty::I64, Ty::I64],
                }],
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            variants,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let args = vec![HirExpr::Int {
            id: ExprId(1),
            value: 1,
            base: crate::lexer::IntBase::Decimal,
            span: Span::dummy(),
        }];
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_variant_construct(&mut fb, variant_item, 0, &args, &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for too few payload arguments")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn deeply_nested_hand_built_match_pattern_fails_lowering_with_i0002_not_a_stack_overflow() {
        // The parser's own crate::limits::MAX_PATTERN_DEPTH bound keeps
        // any real parser output shallow enough that lower_decision's
        // own bound can never fire through the normal pipeline
        // (typeck's matching bound also stops it before NIR lowering is
        // ever reached) -- so this exercises it the only way possible:
        // a hand-built HirModule that bypasses the parser, hir::lower,
        // and typeck entirely, calling the public nir::lower_module
        // entry point a direct caller would, and asserting the whole
        // module fails atomically rather than calling only the private
        // lower_match helper.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let wrap_name = interner.intern("Wrap");
        let leaf_name = interner.intern("Leaf");
        let variant_item = ItemId(0);
        let variant_sym = interner.intern("Rec");
        let variant_ty_name = crate::hir::HirType::Aggregate {
            item: variant_item,
            kind: crate::hir::AggregateKind::Variant,
            name: variant_sym,
            args: Vec::new(),
            span: Span::dummy(),
        };
        let i64_name = crate::hir::HirType::Unresolved {
            name: interner.intern("i64"),
            span: Span::dummy(),
        };
        let variant = crate::hir::HirVariant {
            id: variant_item,
            name: variant_sym,
            span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            cases: vec![
                crate::hir::HirCase {
                    name: wrap_name,
                    span: Span::dummy(),
                    payload: vec![variant_ty_name.clone()],
                },
                crate::hir::HirCase {
                    name: leaf_name,
                    span: Span::dummy(),
                    payload: vec![],
                },
            ],
        };

        let depth = MAX_PATTERN_DEPTH + 50;
        let mut pattern_case = HashMap::new();
        let mut pattern = HirPattern::Wildcard {
            id: PatternId(0),
            span: Span::dummy(),
        };
        for i in 0..depth {
            let id = PatternId(i as u32 + 1);
            pattern_case.insert(id, (variant_item, 0usize));
            pattern = HirPattern::Variant {
                id,
                name: wrap_name,
                args: vec![pattern],
                span: Span::dummy(),
            };
        }

        let param_local = LocalId(0);
        let scrutinee_id = ExprId(0);
        let scrutinee = HirExpr::Local {
            id: scrutinee_id,
            local: param_local,
            name: variant_sym,
            span: Span::dummy(),
        };
        let arms = vec![HirMatchArm {
            pattern,
            body: HirMatchArmBody::Expr(HirExpr::Int {
                id: ExprId(1),
                value: 0,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            }),
            span: Span::dummy(),
        }];
        let match_expr = HirExpr::Match {
            id: ExprId(2),
            scrutinee: Box::new(scrutinee),
            arms,
            span: Span::dummy(),
        };
        let function = HirFunction {
            id: ItemId(1),
            name: interner.intern("f"),
            name_span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            params: vec![crate::hir::HirParam {
                local: param_local,
                name: variant_sym,
                span: Span::dummy(),
                ty: variant_ty_name,
                take: false,
            }],
            return_type: Some(i64_name),
            uses: vec![],
            requirements: Vec::new(),
            raises: vec![],
            body: HirBlock {
                id: ExprId(3),
                statements: vec![],
                tail: Some(Box::new(match_expr)),
                span: Span::dummy(),
            },
            span: Span::dummy(),
        };
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: vec![],
            variants: vec![variant],
            other_items: vec![],
        };

        let mut local_types = HashMap::new();
        local_types.insert(param_local, Ty::Named(variant_item, variant_sym));
        let mut expr_types = HashMap::new();
        expr_types.insert(scrutinee_id, Ty::Named(variant_item, variant_sym));

        let call_type_args = HashMap::new();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!(
                "expected the whole module to fail lowering for a match nested past the depth limit"
            )
        };
        assert!(
            diagnostics.iter().any(|d| d.code == "I0002"),
            "expected an I0002 diagnostic, got {diagnostics:?}"
        );
    }

    #[test]
    fn match_expression_now_lowers_successfully() {
        // Alpha 0.1.1: `match` has real NIR lowering (a decision tree
        // over `variant.switch`/`condbr`), so it no longer fails with
        // I0001.
        let module = lower("func f(x: i64) -> i64 { return match x { _ => 0 } }");
        assert_eq!(module.functions.len(), 1);
    }

    #[test]
    fn cast_fails_lowering_instead_of_forwarding_the_unconverted_value() {
        // Must never be lowered as identity: `as` performs no runtime
        // conversion in this milestone, so silently forwarding the
        // inner value would let a cast "succeed" while lying about what
        // it does.
        assert_fails_with_i0001("func f() -> f64 { value x = 1; return x as f64 }", "as");
    }

    #[test]
    fn postfix_try_on_a_non_call_operand_fails_lowering_instead_of_forwarding_the_inner_value() {
        // typeck's own TRY_ON_INFALLIBLE already rejects `?` on anything
        // but a direct call to a fallible function; a caller that lowers
        // past that gate anyway must not have `?` silently become a
        // no-op forwarding `x` unchanged.
        assert_fails_with_i0002(
            "func f(x: i64) -> i64 { return x? }",
            "not a direct call to a fallible function",
        );
    }

    #[test]
    fn range_expression_fails_lowering_instead_of_becoming_its_left_endpoint() {
        // Must never be lowered as "just the left endpoint": that would
        // silently misrepresent what the expression means, not merely
        // leave it unsupported.
        assert_fails_with_i0001("func f() { value r = 1..10; }", "range");
    }

    #[test]
    fn inclusive_range_expression_fails_lowering() {
        assert_fails_with_i0001("func f() { value r = 1..=10; }", "range");
    }

    #[test]
    fn defer_fails_lowering_instead_of_being_silently_dropped() {
        assert_fails_with_i0001("func f() { value x = 1; defer x + 1; }", "defer");
    }

    #[test]
    fn calling_a_non_function_value_fails_lowering_instead_of_a_fabricated_error_value() {
        // typeck already rejects a call whose callee isn't an actual
        // function reference; reaching lower_call with one anyway (a
        // hand-built HirExpr::Call over a plain Local, bypassing
        // typeck) must fail atomically rather than silently return a
        // fabricated Ty::Error/Const::Unit value as if the call had
        // "succeeded".
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let x_name = interner.intern("x");
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let placeholder = fb.push_value(Ty::I64, ValueKind::Alloc);
        fb.local_bindings
            .insert(LocalId(0), LocalBinding::Direct(placeholder));
        let callee = HirExpr::Local {
            id: ExprId(1),
            local: LocalId(0),
            name: x_name,
            span: Span::dummy(),
        };
        let call_expr = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_call(&mut fb, &callee, &[], &call_expr);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for a call to a non-function value")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn function_used_as_a_value_fails_lowering_instead_of_a_fabricated_error_value() {
        assert_fails_with_i0001(
            "func add(a: i64, b: i64) -> i64 { return a + b } \
             func f() -> i64 { value g = add; return g }",
            "add",
        );
    }

    #[test]
    fn break_with_a_value_fails_lowering_instead_of_discarding_it_silently() {
        assert_fails_with_i0001("func f() { loop { break 1; } }", "break");
    }

    #[test]
    fn break_with_a_unit_value_still_fails_lowering() {
        // Not just a non-unit value: *every* value-carrying break must
        // fail, regardless of the value's own type.
        assert_fails_with_i0001("func f() { loop { break {}; } }", "break");
    }

    #[test]
    fn one_function_failing_to_lower_fails_the_whole_module_atomically() {
        // `add` alone would lower cleanly, but `bad` (bypassing typeck's
        // gate, as above) cannot. Lowering must not return a `Module`
        // containing just `add` -- either everything lowers, or nothing
        // does.
        let text = "func add(left: i64, right: i64) -> i64 { return left + right } \
                    func bad(x: i64) -> i64 { return x? }";
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty());
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty());
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(diags.is_empty());
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        let outcome = lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &interner,
            id,
        );
        assert!(
            outcome.is_err(),
            "expected the whole module to fail lowering"
        );
    }

    #[test]
    fn short_circuit_and_does_not_evaluate_right_side_unconditionally() {
        let module = lower("func f(a: bool, b: bool) -> bool { return a && b }");
        // A branch must exist: short-circuiting is implemented via
        // control flow, not a plain eager `and` instruction.
        let has_condbr = module.functions[0]
            .blocks
            .iter()
            .any(|b| matches!(b.terminator, Terminator::CondBranch { .. }));
        assert!(has_condbr);
    }

    // -- Generic lowering (`rfcs/0008`) ---------------------------------

    #[test]
    fn a_generic_function_lowers_exactly_once_with_symbolic_param_types() {
        // `identity[T]` must lower to one `Function` whose own parameter
        // is typed by its own `Ty::Param`, never a per-call-site clone.
        let module = lower(
            "func identity[T](x: T) -> T { return x } \
             func main() -> i64 { return identity[i64](1) + identity[i64](2) }",
        );
        assert_eq!(
            module
                .functions
                .iter()
                .filter(|f| f.params.len() == 1)
                .count(),
            1,
            "identity must lower exactly once regardless of how many call sites instantiate it"
        );
        let identity = module
            .functions
            .iter()
            .find(|f| f.params.len() == 1)
            .unwrap();
        assert!(matches!(identity.params[0].ty, Ty::Param(..)));
        assert!(matches!(identity.return_type, Ty::Param(..)));
        assert_eq!(identity.type_params.len(), 1);
    }

    #[test]
    fn a_call_to_a_generic_function_records_its_own_concrete_type_arguments() {
        let module = lower(
            "func identity[T](x: T) -> T { return x } func main() -> i64 { return identity[i64](42) }",
        );
        let main = module
            .functions
            .iter()
            .find(|f| f.params.is_empty())
            .unwrap();
        let call_type_args = main
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| {
                if let Instruction::Value {
                    kind: ValueKind::Call(_, type_args, _, _),
                    ..
                } = i
                {
                    Some(type_args.clone())
                } else {
                    None
                }
            });
        assert_eq!(call_type_args, Some(vec![Ty::I64]));
    }

    #[test]
    fn a_generic_record_construction_records_its_own_concrete_type_arguments() {
        let module = lower(
            "record Box[T] { payload: T } \
             func main() -> i64 { value b = Box[i64] { payload: 42 }; return b.payload }",
        );
        let main = module
            .functions
            .iter()
            .find(|f| f.params.is_empty())
            .unwrap();
        let create_type_args = main
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| {
                if let Instruction::Value {
                    kind: ValueKind::RecordCreate(_, type_args, _),
                    ..
                } = i
                {
                    Some(type_args.clone())
                } else {
                    None
                }
            });
        assert_eq!(create_type_args, Some(vec![Ty::I64]));
    }

    #[test]
    fn a_generic_variant_construction_records_its_own_concrete_type_arguments() {
        let module = lower(
            "variant Maybe[T] { Some(T), None } \
             func main() -> i64 { \
                 return match Maybe[i64].Some(42) { \
                     Some(n) => n, \
                     None => 0, \
                 } \
             }",
        );
        let main = module
            .functions
            .iter()
            .find(|f| f.params.is_empty())
            .unwrap();
        let create_type_args = main
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| {
                if let Instruction::Value {
                    kind: ValueKind::VariantCreate { type_args, .. },
                    ..
                } = i
                {
                    Some(type_args.clone())
                } else {
                    None
                }
            });
        assert_eq!(create_type_args, Some(vec![Ty::I64]));
    }

    #[test]
    fn a_bare_generic_unit_case_records_its_own_concrete_type_arguments() {
        // Regression: `Maybe[i64].None` (no call syntax at all) must
        // still record its type argument -- `check_case_ref` threading
        // its own `ExprId` into `call_type_args` is what this exercises.
        let module = lower(
            "variant Maybe[T] { Some(T), None } \
             func main() -> i64 { \
                 return match Maybe[i64].None { \
                     Some(n) => n, \
                     None => 0, \
                 } \
             }",
        );
        let main = module
            .functions
            .iter()
            .find(|f| f.params.is_empty())
            .unwrap();
        let create_type_args = main
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| {
                if let Instruction::Value {
                    kind: ValueKind::VariantCreate { type_args, .. },
                    ..
                } = i
                {
                    Some(type_args.clone())
                } else {
                    None
                }
            });
        assert_eq!(
            create_type_args,
            Some(vec![Ty::I64]),
            "a bare generic unit case must not silently default to an empty type argument list"
        );
    }

    // -- Fix 3: diverging operands under `?`/`handle` (`rfcs/0010`) -----

    #[test]
    fn postfix_try_with_a_diverging_argument_lowers_with_no_invoke() {
        let module = lower(
            "variant FileError { Missing }
             func read(path: str) -> str raises FileError {
                 if path == \"\" { raise FileError.Missing }
                 return \"ok\"
             }
             func f() -> i64 {
                 return read({ return 7 })?
             }",
        );
        let f = module
            .functions
            .iter()
            .find(|f| f.params.is_empty())
            .unwrap();
        assert!(
            f.blocks
                .iter()
                .all(|b| !matches!(b.terminator, Terminator::Invoke { .. })),
            "a diverging argument means the fallible call is never reached, so no Invoke should ever be built: {:?}",
            f.blocks
        );
    }

    #[test]
    fn handle_with_a_diverging_argument_lowers_with_no_invoke() {
        let module = lower(
            "variant FileError { Missing }
             func read(path: str) -> str raises FileError {
                 if path == \"\" { raise FileError.Missing }
                 return \"ok\"
             }
             func f() -> i64 {
                 return handle read({ return 7 }) {
                     success v => 1,
                     failure FileError.Missing => 2,
                 }
             }",
        );
        let f = module
            .functions
            .iter()
            .find(|f| f.params.is_empty())
            .unwrap();
        assert!(
            f.blocks
                .iter()
                .all(|b| !matches!(b.terminator, Terminator::Invoke { .. })),
            "a diverging argument means the fallible call is never reached, so no Invoke should ever be built: {:?}",
            f.blocks
        );
    }
}
