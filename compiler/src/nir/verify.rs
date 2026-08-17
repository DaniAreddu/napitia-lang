//! Verifies structural and type invariants of already-lowered NIR.
//!
//! `nir::lower` assumes its input already passed type-checking, and is
//! trusted to produce consistent NIR for a well-typed program -- but
//! trusting that silently is exactly the kind of gap this project's
//! correctness pass exists to close. This pass re-checks the NIR itself,
//! independently of how it was built, and reports every problem it finds
//! as a structured diagnostic rather than letting a malformed module
//! reach the interpreter (where it could panic or silently misbehave).
//! It runs once, after lowering and before interpretation.

use std::collections::{HashMap, HashSet};

use crate::diagnostics::Diagnostic;
use crate::hir::{ItemId, ItemRegistry, TypeParamId};
use crate::limits::MAX_GENERIC_DEPTH;
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
use crate::types::{CapabilityRequirement, Ty, is_integer, is_numeric, substitute};

use super::block::{BasicBlock, BlockId, Terminator};
use super::instruction::{Const, Instruction, ValueId, ValueKind};
use super::{ExtendLayout, Function, Module, ProtocolLayout, RecordLayout, VariantLayout};

mod codes {
    pub const DUPLICATE_FUNCTION_ID: &str = "V0001";
    pub const DUPLICATE_BLOCK_ID: &str = "V0002";
    pub const EMPTY_FUNCTION: &str = "V0003";
    pub const UNKNOWN_BRANCH_TARGET: &str = "V0004";
    pub const UNKNOWN_FUNCTION_REF: &str = "V0005";
    pub const UNKNOWN_VALUE: &str = "V0006";
    pub const UNKNOWN_SLOT: &str = "V0007";
    pub const STORE_TYPE_MISMATCH: &str = "V0008";
    pub const NON_BOOL_CONDITION: &str = "V0009";
    pub const RETURN_TYPE_MISMATCH: &str = "V0010";
    pub const OPERAND_TYPE_MISMATCH: &str = "V0011";
    pub const UNRESOLVED_TYPE_VARIABLE: &str = "V0012";
    pub const UNEXPECTED_ERROR_TYPE: &str = "V0013";
    pub const ARITY_MISMATCH: &str = "V0014";
    /// A function's blocks don't include one with id `BlockId(0)`. The
    /// interpreter (and this verifier's own dominance analysis) treats
    /// `BlockId(0)` as *the* entry block by definition, regardless of
    /// where it sits in the block vector -- a function without one has
    /// no defined starting point at all.
    pub const MISSING_ENTRY_BLOCK: &str = "V0015";
    /// Two definitions (some combination of a parameter and/or an
    /// instruction result) claim the same `ValueId`. Every SSA value
    /// must have exactly one definition; silently letting the second
    /// one win (as a plain `HashMap::insert` would) hides a real
    /// structural bug in whatever produced this NIR.
    pub const DUPLICATE_VALUE_DEFINITION: &str = "V0016";
    /// A value is used earlier in a block than the instruction that
    /// defines it -- a forward reference within the same block, which
    /// no valid lowering ever produces (every instruction is appended
    /// only after everything it depends on already exists).
    pub const USE_BEFORE_DEFINITION: &str = "V0017";
    /// A value is used in a block that its definition does not
    /// dominate: there is at least one path from the entry block to
    /// this use that never passes through the block that defines it.
    /// Reading it on that path would read a value that was never
    /// actually produced.
    pub const NON_DOMINATING_DEFINITION: &str = "V0018";
    pub const UNKNOWN_RECORD: &str = "V0019";
    pub const RECORD_FIELDS_NOT_INITIALIZED_ONCE_EACH: &str = "V0020";
    pub const UNKNOWN_FIELD: &str = "V0021";
    pub const UNKNOWN_VARIANT_OR_CASE: &str = "V0022";
    pub const SWITCH_CASE_COVERAGE: &str = "V0023";
    pub const PAYLOAD_OUTSIDE_REFINEMENT: &str = "V0024";
    pub const SWITCH_SCRUTINEE_TYPE_MISMATCH: &str = "V0025";
    /// Two records in the same module declare the same `ItemId`. Every
    /// module-level item's id must be globally unique -- a plain
    /// `HashMap::insert` would silently let the second layout win,
    /// hiding a real structural bug in whatever produced this NIR.
    pub const DUPLICATE_RECORD_ID: &str = "V0026";
    pub const DUPLICATE_VARIANT_ID: &str = "V0027";
    /// The same `ItemId` is used by two different *kinds* of
    /// module-level item (a function and a record, a record and a
    /// variant, ...). `Ty::Named` compares/hashes by `ItemId` alone, so
    /// a collision like this would let a value constructed as one kind
    /// be silently accepted as the other wherever nominal identity is
    /// the only thing checked.
    pub const ITEM_ID_KIND_COLLISION: &str = "V0028";
    /// A `Ty::Named` refers to an `ItemId` that matches no declared
    /// record or variant in this module.
    pub const UNKNOWN_NAMED_TYPE: &str = "V0029";
    /// A `Ty::Named`'s carried display symbol does not match its own
    /// declaration's name. Nominal identity itself only ever depends on
    /// the `ItemId`, so this can never change what a program *does* --
    /// but it means diagnostics and textual NIR referencing this type
    /// would print the wrong name.
    pub const NAMED_TYPE_SYMBOL_MISMATCH: &str = "V0030";
    /// A `Call`/`RecordCreate`/`VariantCreate`/type application supplies a
    /// number of type arguments that does not match the number of type
    /// parameters its callee/record/variant declares (`rfcs/0008`).
    pub const GENERIC_ARITY_MISMATCH: &str = "V0031";
    /// A `Ty::Param` appears somewhere outside the body/layout of the
    /// generic declaration that actually declares it -- e.g. a function
    /// with no type parameters of its own using another declaration's
    /// symbolic parameter as if it were a concrete type. Symbolic
    /// parameters are only ever meaningful within the one declaration
    /// that binds them; anywhere else, lowering has a bug and one must
    /// never reach the interpreter.
    pub const ESCAPING_TYPE_PARAMETER: &str = "V0032";
    /// A `Ty::Named` refers to a record/variant that declares one or
    /// more type parameters, used without any applied type arguments
    /// (`rfcs/0008` requires every reference to a generic declaration to
    /// be a `Ty::Applied`; there is no raw/default/partially-applied
    /// generic type).
    pub const UNAPPLIED_GENERIC_TYPE: &str = "V0033";
    /// A function/record/variant declares the same `TypeParamId` more
    /// than once in its own type parameter list. Every declaration's own
    /// parameters must be pairwise distinct -- a duplicate would make a
    /// call/construction site's positional type-argument list ambiguous
    /// about which argument substitutes which occurrence.
    pub const DUPLICATE_TYPE_PARAMETER: &str = "V0034";
    /// A type nested deeper than `crate::limits::MAX_GENERIC_DEPTH`,
    /// found at *any* type root this verifier checks: a record field, a
    /// variant case payload, a function parameter or return type, an
    /// instruction's result type, or a `Call`/`RecordCreate`/
    /// `VariantCreate` type argument. Reported once per root, never once
    /// per nested level -- a real, structured diagnostic in place of the
    /// silent early return every other depth-bounded check in this
    /// module still falls back to past this same bound (defense in
    /// depth for those, since this check runs first and rejects the
    /// type outright before they would ever need to).
    pub const GENERIC_DEPTH_EXCEEDED: &str = "V0035";
    /// A protocol or extend reuses an id already used by another
    /// protocol/extend in this module (`rfcs/0009`). Independent
    /// evidence/signature verification for `Call`/`protocol.call`
    /// (V0036 and up) lands in a follow-up commit.
    pub const DUPLICATE_PROTOCOL_ID: &str = "V0045";
    pub const DUPLICATE_EXTEND_ID: &str = "V0046";
}

/// Every function this module's `Call` instructions might reference,
/// along with the signature the verifier checks calls against.
struct KnownFunction {
    /// This function's own declared type parameters, in declaration
    /// order -- a `Call`'s type arguments are substituted into `params`/
    /// `return_type` positionally against this same order before being
    /// checked against the call's actual argument/result types.
    type_params: Vec<TypeParamId>,
    params: Vec<Ty>,
    return_type: Ty,
    /// This function's own capability requirements (`rfcs/0009`), in
    /// declared order -- a `Call` targeting it must carry exactly this
    /// many evidence entries. Not yet read: independent evidence
    /// verification (arity/forwarded-index/extend-identity/depth-budget
    /// checks, V0036 and up) is a tracked follow-up, not implemented in
    /// this commit -- see this module's own `ValueKind::Call` arm.
    #[allow(dead_code)]
    requirements: Vec<CapabilityRequirement>,
}

/// Every declared record's/variant's/protocol's/extend's layout, by
/// `ItemId`, for validating an operation against the module's own
/// declared shape rather than trusting whatever instruction happened to
/// be built with.
struct AggregateContext<'a> {
    records: HashMap<ItemId, &'a RecordLayout>,
    variants: HashMap<ItemId, &'a VariantLayout>,
    /// Not yet read outside registration -- reserved for the same
    /// follow-up evidence verification as `KnownFunction::requirements`.
    #[allow(dead_code)]
    protocols: HashMap<ItemId, &'a ProtocolLayout>,
    #[allow(dead_code)]
    extends: HashMap<ItemId, &'a ExtendLayout>,
}

/// Verifies every function in `module`, collecting every diagnostic it
/// can rather than stopping at the first problem (mirroring `typeck`'s
/// own style) -- an empty result means the module is safe to interpret.
pub fn verify_module(
    module: &Module,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    // `ItemId` is required to be globally unique across every
    // module-level item this NIR represents (functions, records,
    // variants) -- not just unique within its own kind. Two different
    // kinds of item sharing an id is exactly the gap that would let a
    // value constructed as one kind (say, a record) be silently
    // switched over as another (a variant) sharing that id, since
    // `Ty::Named` only ever compares by `ItemId`. Tracked independently
    // of `known_functions`/`agg` below (which use plain `HashMap`s and
    // would otherwise silently let a duplicate's later entry win).
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum ItemRole {
        Function,
        Record,
        Variant,
        Protocol,
        Extend,
    }
    let mut item_roles: HashMap<ItemId, ItemRole> = HashMap::new();
    let mut check_item_identity =
        |id: ItemId, role: ItemRole, name: &str, diagnostics: &mut Vec<Diagnostic>| {
            if let Some(&existing) = item_roles.get(&id) {
                if existing != role {
                    diagnostics.push(Diagnostic::error(
                    codes::ITEM_ID_KIND_COLLISION,
                    source,
                    Span::dummy(),
                    format!(
                        "`{name}` reuses an id already used by a different kind of item in this module"
                    ),
                ));
                }
            } else {
                item_roles.insert(id, role);
            }
        };

    let mut known_functions: HashMap<ItemId, KnownFunction> = HashMap::new();
    let mut seen_function_ids = HashSet::new();
    for function in &module.functions {
        let name = registry.qualified_name(function.id, interner);
        if !seen_function_ids.insert(function.id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_FUNCTION_ID,
                source,
                Span::dummy(),
                format!(
                    "function `{name}` reuses an id already used by another function in this module"
                ),
            ));
        }
        check_item_identity(function.id, ItemRole::Function, &name, &mut diagnostics);
        known_functions.insert(
            function.id,
            KnownFunction {
                type_params: function.type_params.iter().map(|(id, _)| *id).collect(),
                params: function.params.iter().map(|p| p.ty.clone()).collect(),
                return_type: function.return_type.clone(),
                requirements: function.requirements.clone(),
            },
        );
    }

    let mut seen_record_ids = HashSet::new();
    for (id, _record) in &module.records {
        let name = registry.qualified_name(*id, interner);
        if !seen_record_ids.insert(*id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_RECORD_ID,
                source,
                Span::dummy(),
                format!(
                    "record `{name}` reuses an id already used by another record in this module"
                ),
            ));
        }
        check_item_identity(*id, ItemRole::Record, &name, &mut diagnostics);
    }
    let mut seen_variant_ids = HashSet::new();
    for (id, _variant) in &module.variants {
        let name = registry.qualified_name(*id, interner);
        if !seen_variant_ids.insert(*id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_VARIANT_ID,
                source,
                Span::dummy(),
                format!(
                    "variant `{name}` reuses an id already used by another variant in this module"
                ),
            ));
        }
        check_item_identity(*id, ItemRole::Variant, &name, &mut diagnostics);
    }
    let mut seen_protocol_ids = HashSet::new();
    for (id, _protocol) in &module.protocols {
        let name = registry.qualified_name(*id, interner);
        if !seen_protocol_ids.insert(*id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_PROTOCOL_ID,
                source,
                Span::dummy(),
                format!(
                    "protocol `{name}` reuses an id already used by another protocol in this module"
                ),
            ));
        }
        check_item_identity(*id, ItemRole::Protocol, &name, &mut diagnostics);
    }
    let mut seen_extend_ids = HashSet::new();
    for (id, _extend) in &module.extends {
        let name = format!("extend #{}", id.0);
        if !seen_extend_ids.insert(*id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_EXTEND_ID,
                source,
                Span::dummy(),
                format!("{name} reuses an id already used by another extend in this module"),
            ));
        }
        check_item_identity(*id, ItemRole::Extend, &name, &mut diagnostics);
    }

    let agg = AggregateContext {
        records: module.records.iter().map(|(id, r)| (*id, r)).collect(),
        variants: module.variants.iter().map(|(id, v)| (*id, v)).collect(),
        protocols: module.protocols.iter().map(|(id, p)| (*id, p)).collect(),
        extends: module.extends.iter().map(|(id, e)| (*id, e)).collect(),
    };

    // Every record field's and every variant case payload's own
    // declared type must be independently valid -- unresolved,
    // erroneous, or dangling-named types are never allowed to hide
    // inside an aggregate's layout just because nothing ever
    // constructs one.
    for (id, record) in &module.records {
        let context = format!("record `{}`", registry.qualified_name(*id, interner));
        check_no_duplicate_type_params(&record.type_params, source, &context, &mut diagnostics);
        let own_params: HashSet<TypeParamId> =
            record.type_params.iter().map(|(id, _)| *id).collect();
        for (field_name, ty) in &record.fields {
            let field_context = format!("{context}'s field `{}`", interner.resolve(*field_name));
            check_type_root(
                ty,
                &agg,
                &own_params,
                source,
                interner,
                registry,
                &field_context,
                &mut diagnostics,
            );
        }
    }
    for (id, variant) in &module.variants {
        let context = format!("variant `{}`", registry.qualified_name(*id, interner));
        check_no_duplicate_type_params(&variant.type_params, source, &context, &mut diagnostics);
        let own_params: HashSet<TypeParamId> =
            variant.type_params.iter().map(|(id, _)| *id).collect();
        for case in &variant.cases {
            for (i, ty) in case.payload.iter().enumerate() {
                let payload_context = format!(
                    "{context}'s case `{}` payload position {i}",
                    interner.resolve(case.name)
                );
                check_type_root(
                    ty,
                    &agg,
                    &own_params,
                    source,
                    interner,
                    registry,
                    &payload_context,
                    &mut diagnostics,
                );
            }
        }
    }

    for function in &module.functions {
        verify_function(
            function,
            &known_functions,
            &agg,
            source,
            interner,
            registry,
            &mut diagnostics,
        );
    }

    diagnostics
}

fn verify_function(
    function: &Function,
    known_functions: &HashMap<ItemId, KnownFunction>,
    agg: &AggregateContext,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Computed once, as the item's canonical qualified name
    // (`rfcs/0007`) -- every message below that names this function
    // (including the ones built deeper in verify_dominance/
    // verify_payload_refinement/verify_value_kind, which only ever see
    // this same string) automatically stays qualified and alias-
    // independent without needing its own registry lookup.
    let name = registry.qualified_name(function.id, interner);

    if function.blocks.is_empty() {
        diagnostics.push(Diagnostic::error(
            codes::EMPTY_FUNCTION,
            source,
            Span::dummy(),
            format!("function `{name}` has no basic blocks (no entry block)"),
        ));
        return;
    }
    // `BlockId(0)` is the entry block by definition (the interpreter
    // starts there explicitly, not at whatever happens to be first in
    // the vector) -- a function whose blocks don't include one has no
    // defined starting point, regardless of vector ordering.
    if !function.blocks.iter().any(|b| b.id == BlockId(0)) {
        diagnostics.push(Diagnostic::error(
            codes::MISSING_ENTRY_BLOCK,
            source,
            Span::dummy(),
            format!("function `{name}` has no block with id bb0 (the required entry block)"),
        ));
        return;
    }

    let fn_context = format!("function `{name}`");
    check_no_duplicate_type_params(&function.type_params, source, &fn_context, diagnostics);
    let own_params: HashSet<TypeParamId> = function.type_params.iter().map(|(id, _)| *id).collect();
    check_type_root(
        &function.return_type,
        agg,
        &own_params,
        source,
        interner,
        registry,
        &fn_context,
        diagnostics,
    );
    for param in &function.params {
        check_type_root(
            &param.ty,
            agg,
            &own_params,
            source,
            interner,
            registry,
            &fn_context,
            diagnostics,
        );
    }

    let known_blocks: HashSet<BlockId> = function.blocks.iter().map(|b| b.id).collect();
    let mut seen_block_ids = HashSet::new();
    for block in &function.blocks {
        if !seen_block_ids.insert(block.id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_BLOCK_ID,
                source,
                Span::dummy(),
                format!(
                    "function `{name}` has two blocks with the same id (bb{})",
                    block.id.0
                ),
            ));
        }
    }

    // Every value this function ever defines (params, every
    // instruction's result), and its declared type -- built once so
    // every later check is a lookup, never a re-derivation. Tracked
    // through `seen_value_ids` rather than relying on `value_types`
    // itself, since a plain `HashMap::insert` silently accepts a
    // duplicate key (the second definition would just overwrite the
    // first with no diagnostic) -- every SSA value must have exactly
    // one definition, across parameters *and* instruction results,
    // regardless of which block they're in.
    let mut value_types: HashMap<ValueId, Ty> = HashMap::new();
    let mut alloc_slots: HashSet<ValueId> = HashSet::new();
    let mut seen_value_ids: HashSet<ValueId> = HashSet::new();
    let mut param_values: HashSet<ValueId> = HashSet::new();
    for param in &function.params {
        param_values.insert(param.value);
        if !seen_value_ids.insert(param.value) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_VALUE_DEFINITION,
                source,
                Span::dummy(),
                format!(
                    "function `{name}` has a parameter reusing value id %{}, already defined elsewhere in this function",
                    param.value.0
                ),
            ));
        }
        value_types.insert(param.value, param.ty.clone());
    }
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value { result, ty, kind } = instruction {
                if !seen_value_ids.insert(*result) {
                    diagnostics.push(Diagnostic::error(
                        codes::DUPLICATE_VALUE_DEFINITION,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` has an instruction reusing value id %{}, already defined elsewhere in this function",
                            result.0
                        ),
                    ));
                }
                value_types.insert(*result, ty.clone());
                if matches!(kind, ValueKind::Alloc) {
                    alloc_slots.insert(*result);
                }
            }
        }
    }

    let known_values: HashSet<ValueId> = value_types.keys().copied().collect();
    let mut require_value = |id: ValueId, diagnostics: &mut Vec<Diagnostic>| {
        if !known_values.contains(&id) {
            diagnostics.push(Diagnostic::error(
                codes::UNKNOWN_VALUE,
                source,
                Span::dummy(),
                format!(
                    "function `{name}` references value %{} which is never defined",
                    id.0
                ),
            ));
        }
    };

    for block in &function.blocks {
        for instruction in &block.instructions {
            match instruction {
                Instruction::Value { result, ty, kind } => {
                    check_type_root(
                        ty,
                        agg,
                        &own_params,
                        source,
                        interner,
                        registry,
                        &fn_context,
                        diagnostics,
                    );
                    verify_value_kind(
                        *result,
                        ty,
                        kind,
                        &value_types,
                        &alloc_slots,
                        known_functions,
                        agg,
                        &own_params,
                        source,
                        &name,
                        interner,
                        registry,
                        diagnostics,
                        &mut require_value,
                    );
                }
                Instruction::Store { slot, value } => {
                    require_value(*slot, diagnostics);
                    require_value(*value, diagnostics);
                    if !alloc_slots.contains(slot) {
                        diagnostics.push(Diagnostic::error(
                            codes::UNKNOWN_SLOT,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}` stores into %{} which was never allocated with `alloc`",
                                slot.0
                            ),
                        ));
                    } else if let (Some(slot_ty), Some(value_ty)) =
                        (value_types.get(slot), value_types.get(value))
                        && slot_ty != value_ty
                    {
                        diagnostics.push(Diagnostic::error(
                            codes::STORE_TYPE_MISMATCH,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}` stores a value of type `{}` into a slot declared `{}`",
                                crate::types::display_ty(value_ty, interner),
                                crate::types::display_ty(slot_ty, interner)
                            ),
                        ));
                    }
                }
            }
        }

        match &block.terminator {
            Terminator::Return(None) => {
                if function.return_type != Ty::Unit {
                    diagnostics.push(Diagnostic::error(
                        codes::RETURN_TYPE_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` returns no value from a block, but its declared return type is `{}`",
                            crate::types::display_ty(&function.return_type, interner)
                        ),
                    ));
                }
            }
            Terminator::Return(Some(v)) => {
                require_value(*v, diagnostics);
                if let Some(ty) = value_types.get(v)
                    && *ty != function.return_type
                {
                    diagnostics.push(Diagnostic::error(
                        codes::RETURN_TYPE_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` returns a value of type `{}`, but its declared return type is `{}`",
                            crate::types::display_ty(ty, interner),
                            crate::types::display_ty(&function.return_type, interner)
                        ),
                    ));
                }
            }
            Terminator::Branch(target) => {
                if !known_blocks.contains(target) {
                    diagnostics.push(Diagnostic::error(
                        codes::UNKNOWN_BRANCH_TARGET,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` branches to bb{}, which does not exist",
                            target.0
                        ),
                    ));
                }
            }
            Terminator::CondBranch {
                condition,
                then_block,
                else_block,
            } => {
                require_value(*condition, diagnostics);
                if let Some(ty) = value_types.get(condition)
                    && *ty != Ty::Bool
                {
                    diagnostics.push(Diagnostic::error(
                        codes::NON_BOOL_CONDITION,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` branches on a condition of type `{}`, which is not `bool`",
                            crate::types::display_ty(ty, interner)
                        ),
                    ));
                }
                for target in [then_block, else_block] {
                    if !known_blocks.contains(target) {
                        diagnostics.push(Diagnostic::error(
                            codes::UNKNOWN_BRANCH_TARGET,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}` branches to bb{}, which does not exist",
                                target.0
                            ),
                        ));
                    }
                }
            }
            Terminator::Switch {
                scrutinee,
                variant,
                cases,
            } => {
                require_value(*scrutinee, diagnostics);
                if let Some(ty) = value_types.get(scrutinee)
                    && !matches!(ty, Ty::Named(v, _) | Ty::Applied(v, _) if v == variant)
                {
                    diagnostics.push(Diagnostic::error(
                        codes::SWITCH_SCRUTINEE_TYPE_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` switches on a value of type `{}`, which is not the declared variant",
                            crate::types::display_ty(ty, interner)
                        ),
                    ));
                }
                let Some(layout) = agg.variants.get(variant) else {
                    diagnostics.push(Diagnostic::error(
                        codes::UNKNOWN_VARIANT_OR_CASE,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` switches on unknown variant id {}",
                            variant.0
                        ),
                    ));
                    continue;
                };
                if cases.len() != layout.cases.len() {
                    diagnostics.push(Diagnostic::error(
                        codes::SWITCH_CASE_COVERAGE,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` switches on `{}` with {} target(s), but it has {} case(s)",
                            registry.qualified_name(*variant, interner),
                            cases.len(),
                            layout.cases.len()
                        ),
                    ));
                }
                for target in cases {
                    if !known_blocks.contains(target) {
                        diagnostics.push(Diagnostic::error(
                            codes::UNKNOWN_BRANCH_TARGET,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}` switches to bb{}, which does not exist",
                                target.0
                            ),
                        ));
                    }
                }
            }
        }
    }

    verify_payload_refinement(function, agg, source, &name, diagnostics);
    verify_dominance(function, &param_values, source, &name, diagnostics);
}

/// A value used anywhere in `function` must be either a parameter, or
/// an instruction result whose defining block *dominates* the block of
/// the use (every control-flow path from the entry block to the use
/// passes through the definition first) -- and if the definition is in
/// the very same block as the use, it must come strictly earlier in
/// that block's instruction list. This is what actually backs up
/// "every value used exists" with "and was actually produced on every
/// path that could reach this use", which a plain existence check
/// (`require_value`) cannot tell apart from a value that only happens
/// to exist somewhere else in the function, e.g. in a sibling `if`
/// branch that never ran.
fn verify_dominance(
    function: &Function,
    param_values: &HashSet<ValueId>,
    source: SourceId,
    name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // (block, index within that block's instruction list) of each
    // value's *first* definition. A duplicate definition is already
    // reported on its own (V0016); picking one arbitrarily here just
    // keeps this pass from also cascading into confusing double
    // reports about the same underlying problem.
    let mut def_site: HashMap<ValueId, (BlockId, usize)> = HashMap::new();
    for block in &function.blocks {
        for (idx, instruction) in block.instructions.iter().enumerate() {
            if let Instruction::Value { result, .. } = instruction {
                def_site.entry(*result).or_insert((block.id, idx));
            }
        }
    }

    let dom = compute_dominators(function);

    let check_use = |v: ValueId,
                     current_block: BlockId,
                     current_idx: usize,
                     diagnostics: &mut Vec<Diagnostic>| {
        if param_values.contains(&v) {
            // Parameters are defined at function entry and dominate
            // every reachable block.
            return;
        }
        let Some(&(def_block, def_idx)) = def_site.get(&v) else {
            // Not defined anywhere at all -- already reported as
            // V0006 by the existence check elsewhere; nothing further
            // to say about its dominance.
            return;
        };
        if def_block == current_block {
            if def_idx >= current_idx {
                diagnostics.push(Diagnostic::error(
                    codes::USE_BEFORE_DEFINITION,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{name}` uses %{} in bb{} before it is defined later in the same block",
                        v.0, current_block.0
                    ),
                ));
            }
            return;
        }
        let dominates = dom
            .get(&current_block)
            .is_some_and(|d| d.contains(&def_block));
        if !dominates {
            diagnostics.push(Diagnostic::error(
                codes::NON_DOMINATING_DEFINITION,
                source,
                Span::dummy(),
                format!(
                    "function `{name}` uses %{} in bb{}, but its definition in bb{} does not dominate that use (some path reaches bb{} without ever defining %{})",
                    v.0, current_block.0, def_block.0, current_block.0, v.0
                ),
            ));
        }
    };

    for block in &function.blocks {
        for (idx, instruction) in block.instructions.iter().enumerate() {
            match instruction {
                Instruction::Value { kind, .. } => {
                    for operand in operands_of(kind) {
                        check_use(operand, block.id, idx, diagnostics);
                    }
                }
                Instruction::Store { slot, value } => {
                    check_use(*slot, block.id, idx, diagnostics);
                    check_use(*value, block.id, idx, diagnostics);
                }
            }
        }
        // Terminator operands are treated as occurring after every
        // instruction in the block: any same-block definition, at any
        // instruction index, dominates the terminator that ends it.
        let after_all = block.instructions.len();
        match &block.terminator {
            Terminator::Return(Some(v)) => check_use(*v, block.id, after_all, diagnostics),
            Terminator::CondBranch { condition, .. } => {
                check_use(*condition, block.id, after_all, diagnostics);
            }
            Terminator::Switch { scrutinee, .. } => {
                check_use(*scrutinee, block.id, after_all, diagnostics);
            }
            Terminator::Return(None) | Terminator::Branch(_) => {}
        }
    }
}

/// Every `ValueId` a `ValueKind` reads as an operand (not the value it
/// itself produces).
fn operands_of(kind: &ValueKind) -> Vec<ValueId> {
    match kind {
        ValueKind::Alloc | ValueKind::Const(_) => Vec::new(),
        ValueKind::Load(slot) => vec![*slot],
        ValueKind::Neg(a) | ValueKind::Not(a) => vec![*a],
        ValueKind::Add(a, b)
        | ValueKind::Sub(a, b)
        | ValueKind::Mul(a, b)
        | ValueKind::Div(a, b)
        | ValueKind::Rem(a, b)
        | ValueKind::And(a, b)
        | ValueKind::Or(a, b)
        | ValueKind::Xor(a, b)
        | ValueKind::Shl(a, b)
        | ValueKind::Shr(a, b)
        | ValueKind::Eq(a, b)
        | ValueKind::Ne(a, b)
        | ValueKind::Lt(a, b)
        | ValueKind::Le(a, b)
        | ValueKind::Gt(a, b)
        | ValueKind::Ge(a, b) => vec![*a, *b],
        ValueKind::Call(_, _, args, _) => args.clone(),
        ValueKind::RecordCreate(_, _, fields) => fields.clone(),
        ValueKind::RecordField { base, .. } => vec![*base],
        ValueKind::VariantCreate { payload, .. } => payload.clone(),
        ValueKind::VariantPayload { base, .. } => vec![*base],
        ValueKind::ProtocolCall { args, .. } => args.clone(),
    }
}

/// Computes, for every block in `function`, the set of blocks that
/// dominate it (including itself) -- the standard iterative
/// meet-over-predecessors fixpoint, restricted to blocks actually
/// reachable from the entry block (`BlockId(0)`).
///
/// A block never reached from the entry is deliberately *not* folded
/// into that fixpoint: a cycle purely among unreachable blocks (e.g. a
/// dead merge block that branches to itself) would otherwise never
/// converge below its pessimistic initial value using plain
/// intersection, which would let it dominate -- and therefore
/// silently accept -- a reference to literally anything else in the
/// function. An unreachable block is instead defined to be dominated
/// only by itself, so any operand it uses that isn't its own local
/// definition is correctly flagged as non-dominating.
fn compute_dominators(function: &Function) -> HashMap<BlockId, HashSet<BlockId>> {
    let entry = BlockId(0);
    let all_ids: HashSet<BlockId> = function.blocks.iter().map(|b| b.id).collect();
    if !all_ids.contains(&entry) {
        // Already reported as V0015; there is no meaningful entry to
        // compute dominance from.
        return HashMap::new();
    }

    let block_by_id: HashMap<BlockId, &BasicBlock> =
        function.blocks.iter().map(|b| (b.id, b)).collect();
    let successors = |id: BlockId| -> Vec<BlockId> {
        match &block_by_id[&id].terminator {
            Terminator::Return(_) => Vec::new(),
            Terminator::Branch(target) => vec![*target],
            Terminator::CondBranch {
                then_block,
                else_block,
                ..
            } => vec![*then_block, *else_block],
            Terminator::Switch { cases, .. } => cases.clone(),
        }
    };

    let mut reachable: HashSet<BlockId> = HashSet::from([entry]);
    let mut worklist = vec![entry];
    while let Some(id) = worklist.pop() {
        for succ in successors(id) {
            if all_ids.contains(&succ) && reachable.insert(succ) {
                worklist.push(succ);
            }
        }
    }

    let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for &id in &reachable {
        for succ in successors(id) {
            if reachable.contains(&succ) {
                preds.entry(succ).or_default().push(id);
            }
        }
    }

    let mut dom: HashMap<BlockId, HashSet<BlockId>> = HashMap::new();
    for &id in &all_ids {
        if !reachable.contains(&id) {
            dom.insert(id, HashSet::from([id]));
        } else if id == entry {
            dom.insert(id, HashSet::from([entry]));
        } else {
            dom.insert(id, reachable.clone());
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for &id in &reachable {
            if id == entry {
                continue;
            }
            let no_preds = Vec::new();
            let ps = preds.get(&id).unwrap_or(&no_preds);
            let mut new_dom = match ps.split_first() {
                None => HashSet::from([id]),
                Some((first, rest)) => {
                    let mut acc = dom[first].clone();
                    for p in rest {
                        acc = acc.intersection(&dom[p]).copied().collect();
                    }
                    acc.insert(id);
                    acc
                }
            };
            let existing = dom.get_mut(&id).unwrap();
            if new_dom != *existing {
                std::mem::swap(existing, &mut new_dom);
                changed = true;
            }
        }
    }
    dom
}

/// A type that can never legally appear in NIR the verifier accepts: an
/// unresolved type variable (typeck must have already resolved every
/// one before lowering ever saw this expression) or `Ty::Error` (a
/// well-typed program that reached lowering should never carry one).
/// A declaration's own `type_params` list must never repeat the same
/// `TypeParamId` -- a duplicate would make positional substitution
/// ambiguous about which call-site argument binds which occurrence, and
/// silently collapsing it into a `HashMap`/`HashSet` (as every
/// substitution site here does) would otherwise just drop one binding
/// with no diagnostic at all.
fn check_no_duplicate_type_params(
    type_params: &[(TypeParamId, Symbol)],
    source: SourceId,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut seen: HashSet<TypeParamId> = HashSet::new();
    for (id, _) in type_params {
        if !seen.insert(*id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_TYPE_PARAMETER,
                source,
                Span::dummy(),
                format!("{context} declares the same type parameter more than once"),
            ));
        }
    }
}

fn check_no_bad_type(ty: &Ty, source: SourceId, context: &str, diagnostics: &mut Vec<Diagnostic>) {
    check_no_bad_type_at_depth(ty, source, context, diagnostics, 0);
}

/// `depth`-bounded the same way every other stage that walks a nested
/// type application is (`crate::limits::MAX_GENERIC_DEPTH`). Recurses
/// into `Ty::Applied`'s own argument list -- an unresolved `Ty::Var` or
/// `Ty::Error` buried *inside* a generic argument (`Box[Ty::Error]`)
/// must be rejected exactly as surely as one at the top level, never
/// silently passed through because only the outer `Ty::Applied` was
/// ever inspected (`rfcs/0008`).
fn check_no_bad_type_at_depth(
    ty: &Ty,
    source: SourceId,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
    depth: usize,
) {
    if depth > MAX_GENERIC_DEPTH {
        return;
    }
    match ty {
        Ty::Var(_) => diagnostics.push(Diagnostic::error(
            codes::UNRESOLVED_TYPE_VARIABLE,
            source,
            Span::dummy(),
            format!(
                "{context} contains an unresolved type variable; typeck must fully resolve \
                 every type before lowering"
            ),
        )),
        Ty::Error => diagnostics.push(Diagnostic::error(
            codes::UNEXPECTED_ERROR_TYPE,
            source,
            Span::dummy(),
            format!(
                "{context} contains an error type in executable NIR; an ill-typed program \
                 should never reach lowering"
            ),
        )),
        Ty::Applied(_, args) => {
            for arg in args {
                check_no_bad_type_at_depth(arg, source, context, diagnostics, depth + 1);
            }
        }
        _ => {}
    }
}

/// Checks that a `Ty::Named` refers to an actually-declared record or
/// variant in this module, and that its carried display symbol matches
/// that declaration's own name. Nominal identity itself only ever
/// depends on the `ItemId` (see `Ty`'s hand-written `PartialEq`/`Hash`),
/// so neither check can change what a well-formed program does -- but
/// an unknown id is a dangling reference no valid lowering produces,
/// and a mismatched symbol means diagnostics/textual NIR referencing
/// this type would print the wrong name.
fn check_named_type_identity(
    ty: &Ty,
    agg: &AggregateContext,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    check_named_type_identity_at_depth(
        ty,
        agg,
        source,
        interner,
        registry,
        context,
        diagnostics,
        0,
    );
}

/// `depth` bounds recursion into nested `Ty::Applied` arguments the same
/// way every other stage that walks a type application does
/// (`crate::limits::MAX_GENERIC_DEPTH`) -- this verifier is a public
/// entry point a direct caller can invoke with hand-built NIR that
/// bypasses every earlier stage's own depth guard entirely, so it never
/// trusts them to have already bounded the input (`rfcs/0008`). Past the
/// bound, recursion simply stops rather than checking (or rejecting)
/// anything deeper -- a type that deep is already malformed by
/// construction and would have been rejected with its own diagnostic far
/// earlier in any lowering that did not itself bypass every guard.
#[allow(clippy::too_many_arguments)]
fn check_named_type_identity_at_depth(
    ty: &Ty,
    agg: &AggregateContext,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
    depth: usize,
) {
    if depth > MAX_GENERIC_DEPTH {
        return;
    }
    match ty {
        Ty::Named(item, symbol) => {
            let declared = agg
                .records
                .get(item)
                .map(|r| (r.name, r.type_params.len()))
                .or_else(|| {
                    agg.variants
                        .get(item)
                        .map(|v| (v.name, v.type_params.len()))
                });
            match declared {
                None => diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_NAMED_TYPE,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} names a type that matches no declared record or variant in this module"
                    ),
                )),
                Some((name, _)) if name != *symbol => diagnostics.push(Diagnostic::error(
                    codes::NAMED_TYPE_SYMBOL_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} names its type `{}`, but its declaration is actually named `{}`",
                        interner.resolve(*symbol),
                        registry.qualified_name(*item, interner)
                    ),
                )),
                Some((_, type_param_count)) if type_param_count > 0 => {
                    diagnostics.push(Diagnostic::error(
                        codes::UNAPPLIED_GENERIC_TYPE,
                        source,
                        Span::dummy(),
                        format!(
                            "{context} names `{}` without type arguments, but it declares {type_param_count} type parameter(s)",
                            registry.qualified_name(*item, interner)
                        ),
                    ))
                }
                Some(_) => {}
            }
        }
        Ty::Applied(item, args) => {
            let declared_param_count = agg
                .records
                .get(item)
                .map(|r| r.type_params.len())
                .or_else(|| agg.variants.get(item).map(|v| v.type_params.len()));
            match declared_param_count {
                None => diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_NAMED_TYPE,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} names a type that matches no declared record or variant in this module"
                    ),
                )),
                Some(count) if count != args.len() => diagnostics.push(Diagnostic::error(
                    codes::GENERIC_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} applies {} type argument(s) to `{}`, which declares {count}",
                        args.len(),
                        registry.qualified_name(*item, interner)
                    ),
                )),
                Some(0) => diagnostics.push(Diagnostic::error(
                    codes::GENERIC_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} applies type arguments to `{}`, which is not generic",
                        registry.qualified_name(*item, interner)
                    ),
                )),
                Some(_) => {}
            }
            for arg in args {
                check_named_type_identity_at_depth(
                    arg,
                    agg,
                    source,
                    interner,
                    registry,
                    context,
                    diagnostics,
                    depth + 1,
                );
            }
        }
        _ => {}
    }
}

/// A `Ty::Param` is only ever meaningful within the one generic
/// declaration that binds it (`rfcs/0008`) -- it must never appear as a
/// concrete type anywhere else (a non-generic function's own signature,
/// another declaration's field/payload types, a call's type arguments in
/// a context that doesn't itself declare that parameter). `own_params` is
/// the set of `TypeParamId`s the *current* declaration (function, record,
/// or variant) itself declares; any `Ty::Param` found outside that set has
/// escaped its owning declaration, which no valid lowering ever produces.
fn check_type_param_scope(
    ty: &Ty,
    own_params: &HashSet<TypeParamId>,
    source: SourceId,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    check_type_param_scope_at_depth(ty, own_params, source, context, diagnostics, 0);
}

/// `depth`-bounded the same way [`check_named_type_identity_at_depth`]
/// is, and for the same reason: this verifier must never trust a
/// hand-built `Ty::Applied` to already be shallow.
fn check_type_param_scope_at_depth(
    ty: &Ty,
    own_params: &HashSet<TypeParamId>,
    source: SourceId,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
    depth: usize,
) {
    if depth > MAX_GENERIC_DEPTH {
        return;
    }
    match ty {
        Ty::Param(id, _) => {
            if !own_params.contains(id) {
                diagnostics.push(Diagnostic::error(
                    codes::ESCAPING_TYPE_PARAMETER,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} uses a symbolic type parameter that does not belong to this declaration"
                    ),
                ));
            }
        }
        Ty::Applied(_, args) => {
            for arg in args {
                check_type_param_scope_at_depth(
                    arg,
                    own_params,
                    source,
                    context,
                    diagnostics,
                    depth + 1,
                );
            }
        }
        _ => {}
    }
}

/// Whether `ty`'s own nested `Ty::Applied` structure goes deeper than
/// `MAX_GENERIC_DEPTH` -- stops descending the instant the bound is
/// exceeded rather than computing the type's true depth beyond that
/// point, so *measuring* a pathologically deep hand-built type can never
/// itself overflow the native stack.
fn exceeds_generic_depth(ty: &Ty, depth: usize) -> bool {
    if depth > MAX_GENERIC_DEPTH {
        return true;
    }
    match ty {
        Ty::Applied(_, args) => args.iter().any(|a| exceeds_generic_depth(a, depth + 1)),
        _ => false,
    }
}

/// The single, shared check every type root `verify_module` inspects
/// goes through -- a record field, a variant case payload, a function
/// parameter or return type, an instruction's result type, or a
/// `Call`/`RecordCreate`/`VariantCreate` type argument. One place
/// validating everything any of these must satisfy, so no call site can
/// ever drift into checking a different subset of these, and no root is
/// ever checked by only some of them:
///
/// - not nested deeper than `MAX_GENERIC_DEPTH` (checked first, and
///   reported as its own dedicated diagnostic rather than the silent
///   early return every check below still falls back to past this same
///   bound as defense in depth -- a controlled single diagnostic for the
///   whole root, never one per nested level, and no further checks run
///   on a root already rejected this way);
/// - no `Ty::Error` or unresolved `Ty::Var`, however deeply nested
///   (`check_no_bad_type`);
/// - valid named/applied aggregate identity and correct nested generic
///   arity, including rejecting an unapplied reference to a generic
///   declaration (`check_named_type_identity`);
/// - no symbolic type parameter escaping the declaration that binds it
///   (`check_type_param_scope`).
///
/// This is the module's one authoritative type-integrity path: it never
/// trusts the parser, HIR, type checker, or lowering to have already
/// rejected an over-deep or otherwise malformed type, since every caller
/// here is a `verify_module` entry point that hand-built NIR can reach
/// directly, bypassing every earlier stage entirely (`rfcs/0008`).
#[allow(clippy::too_many_arguments)]
fn check_type_root(
    ty: &Ty,
    agg: &AggregateContext,
    own_params: &HashSet<TypeParamId>,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if exceeds_generic_depth(ty, 0) {
        diagnostics.push(Diagnostic::error(
            codes::GENERIC_DEPTH_EXCEEDED,
            source,
            Span::dummy(),
            format!(
                "{context} is nested deeper than the maximum generic depth of {MAX_GENERIC_DEPTH}"
            ),
        ));
        return;
    }
    check_no_bad_type(ty, source, context, diagnostics);
    check_named_type_identity(ty, agg, source, interner, registry, context, diagnostics);
    check_type_param_scope(ty, own_params, source, context, diagnostics);
}

#[allow(clippy::too_many_arguments)]
fn verify_value_kind(
    result: ValueId,
    result_ty: &Ty,
    kind: &ValueKind,
    value_types: &HashMap<ValueId, Ty>,
    alloc_slots: &HashSet<ValueId>,
    known_functions: &HashMap<ItemId, KnownFunction>,
    agg: &AggregateContext,
    own_params: &HashSet<TypeParamId>,
    source: SourceId,
    function_name: &str,
    interner: &Interner,
    registry: &ItemRegistry,
    diagnostics: &mut Vec<Diagnostic>,
    require_value: &mut impl FnMut(ValueId, &mut Vec<Diagnostic>),
) {
    let operand_mismatch = |diagnostics: &mut Vec<Diagnostic>, detail: String| {
        diagnostics.push(Diagnostic::error(
            codes::OPERAND_TYPE_MISMATCH,
            source,
            Span::dummy(),
            format!("function `{function_name}`: %{} {detail}", result.0),
        ));
    };

    let ty_of = |v: ValueId| value_types.get(&v).cloned();
    let ty_name = |ty: &Ty| crate::types::display_ty(ty, interner);

    match kind {
        ValueKind::Alloc => {}
        ValueKind::Const(c) => {
            let ok = match c {
                Const::Int(_) => is_integer(result_ty),
                Const::Float(_) => matches!(result_ty, Ty::F32 | Ty::F64),
                Const::Bool(_) => matches!(result_ty, Ty::Bool),
                Const::Char(_) => matches!(result_ty, Ty::Char),
                Const::Str(_) => matches!(result_ty, Ty::Str),
                Const::Unit => matches!(result_ty, Ty::Unit),
            };
            if !ok {
                operand_mismatch(
                    diagnostics,
                    format!("is a {c:?} constant declared with an incompatible type"),
                );
            }
        }
        ValueKind::Load(slot) => {
            require_value(*slot, diagnostics);
            if !alloc_slots.contains(slot) {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_SLOT,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}` loads from %{} which was never allocated with `alloc`",
                        slot.0
                    ),
                ));
            } else if let Some(slot_ty) = ty_of(*slot)
                && slot_ty != *result_ty
            {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "loads a slot declared `{}` but is itself declared `{}`",
                        ty_name(&slot_ty),
                        ty_name(result_ty)
                    ),
                );
            }
        }
        ValueKind::Add(a, b)
        | ValueKind::Sub(a, b)
        | ValueKind::Mul(a, b)
        | ValueKind::Div(a, b)
        | ValueKind::Rem(a, b) => {
            require_value(*a, diagnostics);
            require_value(*b, diagnostics);
            if !is_numeric(result_ty) {
                operand_mismatch(
                    diagnostics,
                    "is an arithmetic result but not numeric".into(),
                );
            }
            check_same_as_result(
                *a,
                *b,
                result_ty,
                value_types,
                &operand_mismatch,
                diagnostics,
            );
        }
        ValueKind::And(a, b) | ValueKind::Or(a, b) | ValueKind::Xor(a, b) => {
            require_value(*a, diagnostics);
            require_value(*b, diagnostics);
            if !is_integer(result_ty) {
                operand_mismatch(diagnostics, "is a bitwise result but not an integer".into());
            }
            check_same_as_result(
                *a,
                *b,
                result_ty,
                value_types,
                &operand_mismatch,
                diagnostics,
            );
        }
        ValueKind::Shl(a, b) | ValueKind::Shr(a, b) => {
            require_value(*a, diagnostics);
            require_value(*b, diagnostics);
            if !is_integer(result_ty) {
                operand_mismatch(diagnostics, "is a shift result but not an integer".into());
            }
            check_same_as_result(
                *a,
                *b,
                result_ty,
                value_types,
                &operand_mismatch,
                diagnostics,
            );
        }
        ValueKind::Neg(a) => {
            require_value(*a, diagnostics);
            if !is_numeric(result_ty) {
                operand_mismatch(diagnostics, "negates a value but is not numeric".into());
            }
            if let Some(ty) = ty_of(*a)
                && ty != *result_ty
            {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "negates an operand of type `{}` but is declared `{}`",
                        ty_name(&ty),
                        ty_name(result_ty)
                    ),
                );
            }
        }
        ValueKind::Not(a) => {
            require_value(*a, diagnostics);
            if !(is_integer(result_ty) || matches!(result_ty, Ty::Bool)) {
                operand_mismatch(
                    diagnostics,
                    "applies `not` but is neither an integer nor a bool".into(),
                );
            }
            if let Some(ty) = ty_of(*a)
                && ty != *result_ty
            {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "applies `not` to an operand of type `{}` but is declared `{}`",
                        ty_name(&ty),
                        ty_name(result_ty)
                    ),
                );
            }
        }
        ValueKind::Eq(a, b)
        | ValueKind::Ne(a, b)
        | ValueKind::Lt(a, b)
        | ValueKind::Le(a, b)
        | ValueKind::Gt(a, b)
        | ValueKind::Ge(a, b) => {
            require_value(*a, diagnostics);
            require_value(*b, diagnostics);
            if !matches!(result_ty, Ty::Bool) {
                operand_mismatch(
                    diagnostics,
                    "is a comparison but not declared `bool`".into(),
                );
            }
            if let (Some(at), Some(bt)) = (ty_of(*a), ty_of(*b))
                && at != bt
            {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "compares operands of different types `{}` and `{}`",
                        ty_name(&at),
                        ty_name(&bt)
                    ),
                );
            }
        }
        // TODO(rfcs/0009): `_evidence` is not yet independently verified
        // here (evidence arity/type/forwarded-index/cycle checks land in
        // a follow-up commit) -- tracked, not silently forgotten.
        ValueKind::Call(callee, type_args, args, _evidence) => {
            for arg in args {
                require_value(*arg, diagnostics);
            }
            let Some(sig) = known_functions.get(callee) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_FUNCTION_REF,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}` calls a function with id {}, which does not exist in this module",
                        callee.0
                    ),
                ));
                return;
            };
            let call_context = format!(
                "function `{function_name}`: %{}'s call type argument",
                result.0
            );
            for t in type_args {
                check_type_root(
                    t,
                    agg,
                    own_params,
                    source,
                    interner,
                    registry,
                    &call_context,
                    diagnostics,
                );
            }
            let (return_ty, param_tys): (Ty, Vec<Ty>) = if type_args.len() == sig.type_params.len()
            {
                let subst: HashMap<TypeParamId, Ty> = sig
                    .type_params
                    .iter()
                    .copied()
                    .zip(type_args.iter().cloned())
                    .collect();
                (
                    substitute(&sig.return_type, &subst),
                    sig.params.iter().map(|p| substitute(p, &subst)).collect(),
                )
            } else {
                diagnostics.push(Diagnostic::error(
                    codes::GENERIC_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} calls a function declaring {} type parameter(s) with {} type argument(s)",
                        result.0,
                        sig.type_params.len(),
                        type_args.len()
                    ),
                ));
                (sig.return_type.clone(), sig.params.clone())
            };
            if return_ty != *result_ty {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "calls a function returning `{}` but is itself declared `{}`",
                        ty_name(&return_ty),
                        ty_name(result_ty)
                    ),
                );
            }
            if param_tys.len() != args.len() {
                diagnostics.push(Diagnostic::error(
                    codes::ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}` calls a function expecting {} argument(s) with {}",
                        param_tys.len(),
                        args.len()
                    ),
                ));
            } else {
                for (param_ty, arg) in param_tys.iter().zip(args.iter()) {
                    if let Some(arg_ty) = ty_of(*arg)
                        && arg_ty != *param_ty
                    {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "passes an argument of type `{}` where `{}` was expected",
                                ty_name(&arg_ty),
                                ty_name(param_ty)
                            ),
                        );
                    }
                }
            }
        }
        ValueKind::RecordCreate(record, type_args, fields) => {
            for f in fields {
                require_value(*f, diagnostics);
            }
            let Some(layout) = agg.records.get(record) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_RECORD,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs unknown record id {}",
                        result.0, record.0
                    ),
                ));
                return;
            };
            let construct_context = format!(
                "function `{function_name}`: %{}'s record construction type argument",
                result.0
            );
            for t in type_args {
                check_type_root(
                    t,
                    agg,
                    own_params,
                    source,
                    interner,
                    registry,
                    &construct_context,
                    diagnostics,
                );
            }
            let arity_ok = type_args.len() == layout.type_params.len();
            if !arity_ok {
                diagnostics.push(Diagnostic::error(
                    codes::GENERIC_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs `{}` (declaring {} type parameter(s)) with {} type argument(s)",
                        result.0,
                        registry.qualified_name(*record, interner),
                        layout.type_params.len(),
                        type_args.len()
                    ),
                ));
            } else {
                let expected_ty = if type_args.is_empty() {
                    Ty::Named(*record, layout.name)
                } else {
                    Ty::Applied(*record, type_args.clone())
                };
                if *result_ty != expected_ty {
                    operand_mismatch(
                        diagnostics,
                        format!(
                            "constructs record `{}` but is declared `{}`",
                            registry.qualified_name(*record, interner),
                            ty_name(result_ty)
                        ),
                    );
                }
            }
            let subst: HashMap<TypeParamId, Ty> = if arity_ok {
                layout
                    .type_params
                    .iter()
                    .map(|(id, _)| *id)
                    .zip(type_args.iter().cloned())
                    .collect()
            } else {
                HashMap::new()
            };
            if fields.len() != layout.fields.len() {
                diagnostics.push(Diagnostic::error(
                    codes::RECORD_FIELDS_NOT_INITIALIZED_ONCE_EACH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs `{}` with {} field value(s), but it has {} field(s)",
                        result.0,
                        registry.qualified_name(*record, interner),
                        fields.len(),
                        layout.fields.len()
                    ),
                ));
            } else {
                for (i, (field_value, (_, declared_ty))) in
                    fields.iter().zip(layout.fields.iter()).enumerate()
                {
                    let expected = substitute(declared_ty, &subst);
                    if let Some(ty) = ty_of(*field_value)
                        && ty != expected
                    {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "field {i} has type `{}` but is declared `{}`",
                                ty_name(&ty),
                                ty_name(&expected)
                            ),
                        );
                    }
                }
            }
        }
        ValueKind::RecordField {
            base,
            record,
            field,
        } => {
            require_value(*base, diagnostics);
            let Some(layout) = agg.records.get(record) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_RECORD,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} projects a field of unknown record id {}",
                        result.0, record.0
                    ),
                ));
                return;
            };
            let base_ty = ty_of(*base);
            let base_args: Option<&[Ty]> = match &base_ty {
                Some(Ty::Named(r, _)) if r == record => Some(&[]),
                Some(Ty::Applied(r, args)) if r == record => Some(args.as_slice()),
                Some(other) => {
                    operand_mismatch(
                        diagnostics,
                        format!(
                            "projects a field of `{}` from a base of type `{}`",
                            registry.qualified_name(*record, interner),
                            ty_name(other)
                        ),
                    );
                    None
                }
                None => None,
            };
            let subst: HashMap<TypeParamId, Ty> = match base_args {
                Some(args) if args.len() == layout.type_params.len() => layout
                    .type_params
                    .iter()
                    .map(|(id, _)| *id)
                    .zip(args.iter().cloned())
                    .collect(),
                _ => HashMap::new(),
            };
            match layout.fields.get(*field) {
                Some((_, declared_ty)) => {
                    let expected = substitute(declared_ty, &subst);
                    if expected != *result_ty {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "projects field {field} of type `{}` but is declared `{}`",
                                ty_name(&expected),
                                ty_name(result_ty)
                            ),
                        );
                    }
                }
                None => diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_FIELD,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} projects field index {field} of `{}`, which has {} field(s)",
                        result.0,
                        registry.qualified_name(*record, interner),
                        layout.fields.len()
                    ),
                )),
            }
        }
        ValueKind::VariantCreate {
            variant,
            case,
            type_args,
            payload,
        } => {
            for p in payload {
                require_value(*p, diagnostics);
            }
            let Some(layout) = agg.variants.get(variant) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_VARIANT_OR_CASE,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs unknown variant id {}",
                        result.0, variant.0
                    ),
                ));
                return;
            };
            let construct_context = format!(
                "function `{function_name}`: %{}'s variant construction type argument",
                result.0
            );
            for t in type_args {
                check_type_root(
                    t,
                    agg,
                    own_params,
                    source,
                    interner,
                    registry,
                    &construct_context,
                    diagnostics,
                );
            }
            let arity_ok = type_args.len() == layout.type_params.len();
            if !arity_ok {
                diagnostics.push(Diagnostic::error(
                    codes::GENERIC_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs `{}` (declaring {} type parameter(s)) with {} type argument(s)",
                        result.0,
                        registry.qualified_name(*variant, interner),
                        layout.type_params.len(),
                        type_args.len()
                    ),
                ));
            } else {
                let expected_ty = if type_args.is_empty() {
                    Ty::Named(*variant, layout.name)
                } else {
                    Ty::Applied(*variant, type_args.clone())
                };
                if *result_ty != expected_ty {
                    operand_mismatch(
                        diagnostics,
                        format!(
                            "constructs variant `{}` but is declared `{}`",
                            registry.qualified_name(*variant, interner),
                            ty_name(result_ty)
                        ),
                    );
                }
            }
            let subst: HashMap<TypeParamId, Ty> = if arity_ok {
                layout
                    .type_params
                    .iter()
                    .map(|(id, _)| *id)
                    .zip(type_args.iter().cloned())
                    .collect()
            } else {
                HashMap::new()
            };
            let Some(case_layout) = layout.cases.get(*case) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_VARIANT_OR_CASE,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs unknown case index {case} of `{}`",
                        result.0,
                        registry.qualified_name(*variant, interner)
                    ),
                ));
                return;
            };
            if payload.len() != case_layout.payload.len() {
                diagnostics.push(Diagnostic::error(
                    codes::ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs case `{}` with {} payload value(s), but it expects {}",
                        result.0,
                        interner.resolve(case_layout.name),
                        payload.len(),
                        case_layout.payload.len()
                    ),
                ));
            } else {
                for (i, (value, declared_ty)) in
                    payload.iter().zip(case_layout.payload.iter()).enumerate()
                {
                    let expected = substitute(declared_ty, &subst);
                    if let Some(ty) = ty_of(*value)
                        && ty != expected
                    {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "payload {i} has type `{}` but is declared `{}`",
                                ty_name(&ty),
                                ty_name(&expected)
                            ),
                        );
                    }
                }
            }
        }
        ValueKind::VariantPayload {
            base,
            variant,
            case,
            index,
        } => {
            require_value(*base, diagnostics);
            let Some(layout) = agg.variants.get(variant) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_VARIANT_OR_CASE,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} projects a payload of unknown variant id {}",
                        result.0, variant.0
                    ),
                ));
                return;
            };
            let base_ty = ty_of(*base);
            let base_args: Option<&[Ty]> = match &base_ty {
                Some(Ty::Named(v, _)) if v == variant => Some(&[]),
                Some(Ty::Applied(v, args)) if v == variant => Some(args.as_slice()),
                Some(other) => {
                    operand_mismatch(
                        diagnostics,
                        format!(
                            "projects a payload of `{}` from a base of type `{}`",
                            registry.qualified_name(*variant, interner),
                            ty_name(other)
                        ),
                    );
                    None
                }
                None => None,
            };
            let subst: HashMap<TypeParamId, Ty> = match base_args {
                Some(args) if args.len() == layout.type_params.len() => layout
                    .type_params
                    .iter()
                    .map(|(id, _)| *id)
                    .zip(args.iter().cloned())
                    .collect(),
                _ => HashMap::new(),
            };
            match layout.cases.get(*case).and_then(|c| c.payload.get(*index)) {
                Some(declared_ty) => {
                    let expected = substitute(declared_ty, &subst);
                    if expected != *result_ty {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "projects payload {index} of case {case} with type `{}` but is declared `{}`",
                                ty_name(&expected),
                                ty_name(result_ty)
                            ),
                        );
                    }
                }
                None => diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_VARIANT_OR_CASE,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} projects payload index {index} of case {case} of `{}`, which does not have it",
                        result.0,
                        registry.qualified_name(*variant, interner)
                    ),
                )),
            }
        }
        // TODO(rfcs/0009): protocol/method/evidence validation for
        // protocol.call is not yet implemented (tracked as a follow-up
        // commit) -- operands are still checked generically by this
        // function's own caller via `operands_of`, but this specific
        // instruction kind has no independent semantic check here yet.
        ValueKind::ProtocolCall { .. } => {}
    }
}

/// A `variant.payload` instruction is only legal in a block reached
/// through the matching case's own `Terminator::Switch` edge -- this
/// re-derives that from the CFG itself (which block is a direct switch
/// target for which `(scrutinee, variant, case)`), independent of how
/// lowering happened to build it.
/// A single guaranteed fact: the value `.0` is known to be case `.2` of
/// variant `.1`.
type RefinementFact = (ValueId, ItemId, usize);

fn verify_payload_refinement(
    function: &Function,
    agg: &AggregateContext,
    source: SourceId,
    function_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let _ = agg;
    // Every incoming edge into each block, tracked as its own
    // independent fact-set: empty for a plain branch/condbr edge
    // (which guarantees no case refinement at all), or a single
    // `(scrutinee, variant, case)` fact for a switch-case edge. Two
    // edges into the same block -- even two cases of the same switch,
    // or two different switches -- are kept as separate list entries:
    // a target block reachable through more than one case of the same
    // switch is genuinely reachable via either case, so nothing about
    // that specific case can be assumed from having reached the block
    // at all.
    let mut incoming: HashMap<BlockId, Vec<HashSet<RefinementFact>>> = HashMap::new();
    for block in &function.blocks {
        match &block.terminator {
            Terminator::Branch(target) => {
                incoming.entry(*target).or_default().push(HashSet::new());
            }
            Terminator::CondBranch {
                then_block,
                else_block,
                ..
            } => {
                incoming
                    .entry(*then_block)
                    .or_default()
                    .push(HashSet::new());
                incoming
                    .entry(*else_block)
                    .or_default()
                    .push(HashSet::new());
            }
            Terminator::Switch {
                scrutinee,
                variant,
                cases,
            } => {
                for (case_index, target) in cases.iter().enumerate() {
                    let mut fact = HashSet::new();
                    fact.insert((*scrutinee, *variant, case_index));
                    incoming.entry(*target).or_default().push(fact);
                }
            }
            Terminator::Return(_) => {}
        }
    }

    // A payload extraction is only sound when the SAME fact is
    // guaranteed by EVERY incoming edge -- intersection, never union.
    // A block with no recorded incoming edges at all (the entry block,
    // or an otherwise-unreachable block) guarantees nothing, matching
    // an empty intersection's identity (the universal set) only in the
    // abstract; concretely there is no edge to ever have proven a case
    // refinement on, so nothing is ever allowed there.
    let guaranteed = |block_id: BlockId| -> HashSet<RefinementFact> {
        let Some(edges) = incoming.get(&block_id) else {
            return HashSet::new();
        };
        let mut edges = edges.iter();
        let Some(first) = edges.next() else {
            return HashSet::new();
        };
        let mut acc = first.clone();
        for edge in edges {
            acc.retain(|fact| edge.contains(fact));
        }
        acc
    };

    for block in &function.blocks {
        let allowed = guaranteed(block.id);
        for instruction in &block.instructions {
            if let Instruction::Value {
                kind:
                    ValueKind::VariantPayload {
                        base,
                        variant,
                        case,
                        ..
                    },
                ..
            } = instruction
                && !allowed.contains(&(*base, *variant, *case))
            {
                diagnostics.push(Diagnostic::error(
                    codes::PAYLOAD_OUTSIDE_REFINEMENT,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}` extracts a variant payload outside the control-flow edge for its case (bb{})",
                        block.id.0
                    ),
                ));
            }
        }
    }
}

fn check_same_as_result(
    a: ValueId,
    b: ValueId,
    result_ty: &Ty,
    value_types: &HashMap<ValueId, Ty>,
    operand_mismatch: &impl Fn(&mut Vec<Diagnostic>, String),
    diagnostics: &mut Vec<Diagnostic>,
) {
    for (label, v) in [("left", a), ("right", b)] {
        if let Some(ty) = value_types.get(&v)
            && ty != result_ty
        {
            operand_mismatch(
                diagnostics,
                format!("has a {label} operand of a different type than its own declared type"),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nir::{BasicBlock, CaseLayout};
    use crate::source::SourceMap;
    use crate::symbol::Symbol;

    /// `func f() -> i64 { return 1 }`, built directly (bypassing
    /// `nir::lower`) so each test can mutate exactly one thing about an
    /// otherwise-valid module and confirm the verifier catches it.
    fn valid_function(id: ItemId, name: Symbol) -> Function {
        Function {
            id,
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::I64,
                    kind: ValueKind::Const(Const::Int(1)),
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        }
    }

    fn codes_of(diagnostics: &[Diagnostic]) -> Vec<&str> {
        diagnostics.iter().map(|d| d.code).collect()
    }

    #[test]
    fn a_valid_module_has_no_diagnostics() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![valid_function(ItemId(0), name)],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn duplicate_function_ids_are_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let a = interner.intern("a");
        let b = interner.intern("b");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![valid_function(ItemId(0), a), valid_function(ItemId(0), b)],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_FUNCTION_ID));
    }

    #[test]
    fn duplicate_block_ids_are_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks.push(BasicBlock {
            id: BlockId(0),
            instructions: Vec::new(),
            terminator: Terminator::Return(None),
        });
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_BLOCK_ID));
    }

    #[test]
    fn a_function_with_no_blocks_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks.clear();
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert_eq!(codes_of(&diagnostics), vec![codes::EMPTY_FUNCTION]);
    }

    #[test]
    fn branching_to_a_nonexistent_block_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].terminator = Terminator::Branch(BlockId(99));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_BRANCH_TARGET));
    }

    #[test]
    fn calling_a_nonexistent_function_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            kind: ValueKind::Call(ItemId(42), Vec::new(), Vec::new(), Vec::new()),
        });
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_FUNCTION_REF));
    }

    #[test]
    fn referencing_an_undefined_value_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        // %99 is never defined anywhere in this function.
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(99)));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_VALUE));
    }

    #[test]
    fn loading_a_value_never_allocated_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        // %0 is a Const, not an Alloc; loading from it is invalid.
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            kind: ValueKind::Load(ValueId(0)),
        });
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_SLOT));
    }

    #[test]
    fn storing_a_mismatched_type_into_a_slot_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Bool,
                kind: ValueKind::Const(Const::Bool(true)),
            },
            Instruction::Store {
                slot: ValueId(0),
                value: ValueId(1),
            },
        ];
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(1)));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::STORE_TYPE_MISMATCH));
    }

    #[test]
    fn a_non_bool_condition_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].terminator = Terminator::CondBranch {
            condition: ValueId(0), // declared i64, not bool
            then_block: BlockId(0),
            else_block: BlockId(0),
        };
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::NON_BOOL_CONDITION));
    }

    #[test]
    fn a_return_value_not_matching_the_declared_return_type_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Bool; // body still returns an i64
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::RETURN_TYPE_MISMATCH));
    }

    #[test]
    fn mismatched_operand_types_are_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Bool,
                kind: ValueKind::Const(Const::Bool(true)),
            },
            // Declared i64, but the right operand is a bool.
            Instruction::Value {
                result: ValueId(2),
                ty: Ty::I64,
                kind: ValueKind::Add(ValueId(0), ValueId(1)),
            },
        ];
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(2)));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::OPERAND_TYPE_MISMATCH));
    }

    #[test]
    fn an_unresolved_type_variable_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Var(crate::types::TyVar(0));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNRESOLVED_TYPE_VARIABLE));
    }

    #[test]
    fn an_error_type_in_executable_nir_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Error;
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNEXPECTED_ERROR_TYPE));
    }

    #[test]
    fn a_call_with_the_wrong_argument_count_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            // `g` takes zero parameters; this call passes one.
            kind: ValueKind::Call(ItemId(0), Vec::new(), vec![ValueId(0)], Vec::new()),
        });
        let callee = valid_function(ItemId(0), g_name);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::ARITY_MISMATCH));
    }

    fn verify_one(function: Function, interner: &Interner) -> Vec<Diagnostic> {
        verify_one_with_aggregates(function, Vec::new(), Vec::new(), interner)
    }

    fn verify_one_with_aggregates(
        function: Function,
        records: Vec<(ItemId, RecordLayout)>,
        variants: Vec<(ItemId, VariantLayout)>,
        interner: &Interner,
    ) -> Vec<Diagnostic> {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records,
            variants,
        };
        verify_module(&module, source, interner, &ItemRegistry::default())
    }

    /// A `record Point { x: i64 }` layout, and a matching `func f() ->
    /// i64 { %0 = record.create @Point(%c); %1 = record.field
    /// @Point.0 %0; ret %1 }`-shaped valid function, for tests that
    /// mutate exactly one thing about it.
    fn record_point(interner: &mut Interner) -> (ItemId, RecordLayout, Symbol) {
        let point = interner.intern("Point");
        let x = interner.intern("x");
        (
            ItemId(100),
            RecordLayout {
                name: point,
                type_params: Vec::new(),
                fields: vec![(x, Ty::I64)],
            },
            point,
        )
    }

    fn valid_record_function(
        id: ItemId,
        name: Symbol,
        record: ItemId,
        ty_name: Symbol,
    ) -> Function {
        Function {
            id,
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(1)),
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::Named(record, ty_name),
                        kind: ValueKind::RecordCreate(record, Vec::new(), vec![ValueId(0)]),
                    },
                    Instruction::Value {
                        result: ValueId(2),
                        ty: Ty::I64,
                        kind: ValueKind::RecordField {
                            base: ValueId(1),
                            record,
                            field: 0,
                        },
                    },
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        }
    }

    #[test]
    fn valid_record_create_and_field_access_has_no_diagnostics() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout, ty_name) = record_point(&mut interner);
        let function = valid_record_function(ItemId(0), name, record, ty_name);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn record_create_referencing_an_unknown_record_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let unknown_record = ItemId(999);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Named(unknown_record, interner.intern("Ghost")),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(1)),
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::Named(unknown_record, interner.intern("Ghost")),
                        kind: ValueKind::RecordCreate(unknown_record, Vec::new(), vec![ValueId(0)]),
                    },
                ],
                terminator: Terminator::Return(Some(ValueId(1))),
            }],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_RECORD));
    }

    #[test]
    fn record_create_with_the_wrong_field_count_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout, ty_name) = record_point(&mut interner);
        let mut function = valid_record_function(ItemId(0), name, record, ty_name);
        // Point has one field, but this supplies two values.
        function.blocks[0].instructions[1] = Instruction::Value {
            result: ValueId(1),
            ty: Ty::Named(record, ty_name),
            kind: ValueKind::RecordCreate(record, Vec::new(), vec![ValueId(0), ValueId(0)]),
        };
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::RECORD_FIELDS_NOT_INITIALIZED_ONCE_EACH));
    }

    #[test]
    fn record_create_with_a_mismatched_field_type_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout, ty_name) = record_point(&mut interner);
        let mut function = valid_record_function(ItemId(0), name, record, ty_name);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::Bool,
            kind: ValueKind::Const(Const::Bool(true)),
        };
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::OPERAND_TYPE_MISMATCH));
    }

    #[test]
    fn record_field_with_an_out_of_range_index_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout, ty_name) = record_point(&mut interner);
        let mut function = valid_record_function(ItemId(0), name, record, ty_name);
        function.blocks[0].instructions[2] = Instruction::Value {
            result: ValueId(2),
            ty: Ty::I64,
            kind: ValueKind::RecordField {
                base: ValueId(1),
                record,
                field: 5,
            },
        };
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_FIELD));
    }

    /// A `variant Shape { Circle(i64), Empty }` layout.
    fn variant_shape(interner: &mut Interner) -> (ItemId, VariantLayout, Symbol) {
        let shape = interner.intern("Shape");
        let circle = interner.intern("Circle");
        let empty = interner.intern("Empty");
        (
            ItemId(200),
            VariantLayout {
                name: shape,
                type_params: Vec::new(),
                cases: vec![
                    CaseLayout {
                        name: circle,
                        payload: vec![Ty::I64],
                    },
                    CaseLayout {
                        name: empty,
                        payload: vec![],
                    },
                ],
            },
            shape,
        )
    }

    fn valid_variant_switch_function(
        id: ItemId,
        name: Symbol,
        variant: ItemId,
        ty_name: Symbol,
    ) -> Function {
        Function {
            id,
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(1)),
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::Named(variant, ty_name),
                            kind: ValueKind::VariantCreate {
                                variant,
                                case: 0,
                                type_args: Vec::new(),
                                payload: vec![ValueId(0)],
                            },
                        },
                    ],
                    terminator: Terminator::Switch {
                        scrutinee: ValueId(1),
                        variant,
                        cases: vec![BlockId(1), BlockId(2)],
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![Instruction::Value {
                        result: ValueId(2),
                        ty: Ty::I64,
                        kind: ValueKind::VariantPayload {
                            base: ValueId(1),
                            variant,
                            case: 0,
                            index: 0,
                        },
                    }],
                    terminator: Terminator::Return(Some(ValueId(2))),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![Instruction::Value {
                        result: ValueId(3),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(0)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(3))),
                },
            ],
        }
    }

    #[test]
    fn valid_variant_switch_and_payload_extraction_has_no_diagnostics() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn variant_create_referencing_an_unknown_variant_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let unknown_variant = ItemId(999);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Named(unknown_variant, interner.intern("Ghost")),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::Named(unknown_variant, interner.intern("Ghost")),
                    kind: ValueKind::VariantCreate {
                        variant: unknown_variant,
                        case: 0,
                        type_args: Vec::new(),
                        payload: vec![],
                    },
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_VARIANT_OR_CASE));
    }

    #[test]
    fn variant_create_with_an_out_of_range_case_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Named(variant, ty_name),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::Named(variant, ty_name),
                    kind: ValueKind::VariantCreate {
                        variant,
                        case: 9,
                        type_args: Vec::new(),
                        payload: vec![],
                    },
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_VARIANT_OR_CASE));
    }

    #[test]
    fn variant_create_with_the_wrong_payload_count_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Named(variant, ty_name),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::Named(variant, ty_name),
                    kind: ValueKind::VariantCreate {
                        variant,
                        case: 0,
                        type_args: Vec::new(),
                        payload: vec![],
                    },
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::ARITY_MISMATCH));
    }

    #[test]
    fn switch_with_too_few_case_targets_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        function.blocks[0].terminator = Terminator::Switch {
            scrutinee: ValueId(1),
            variant,
            cases: vec![BlockId(1)],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::SWITCH_CASE_COVERAGE));
    }

    #[test]
    fn switch_targeting_a_nonexistent_block_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        function.blocks[0].terminator = Terminator::Switch {
            scrutinee: ValueId(1),
            variant,
            cases: vec![BlockId(1), BlockId(99)],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_BRANCH_TARGET));
    }

    #[test]
    fn payload_extraction_outside_its_case_refinement_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        // bb2 (the `Empty` case's own block) illegally extracts the
        // `Circle` case's payload -- never reached via that case's
        // switch edge.
        function.blocks[2].instructions.push(Instruction::Value {
            result: ValueId(4),
            ty: Ty::I64,
            kind: ValueKind::VariantPayload {
                base: ValueId(1),
                variant,
                case: 0,
                index: 0,
            },
        });
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::PAYLOAD_OUTSIDE_REFINEMENT));
    }

    #[test]
    fn two_switch_cases_sharing_one_block_reject_case_specific_payload_extraction() {
        // Both cases of the switch target bb1 -- reachable via either
        // case 0 or case 1, so nothing case-specific can be assumed
        // just from having reached it. A case-0 payload extraction
        // there must be rejected even though it's the very block the
        // switch's own case-0 edge points to.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        function.blocks[0].terminator = Terminator::Switch {
            scrutinee: ValueId(1),
            variant,
            cases: vec![BlockId(1), BlockId(1)],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::PAYLOAD_OUTSIDE_REFINEMENT));
    }

    #[test]
    fn a_case_refined_target_with_an_additional_ordinary_predecessor_is_rejected() {
        // bb1 (the `Circle` case's own block, legally extracting its
        // own payload under the switch alone) also gets a plain branch
        // predecessor from a third block -- that edge guarantees
        // nothing, so the intersection across bb1's predecessors must
        // now be empty and the extraction must be rejected.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        function.blocks.push(BasicBlock {
            id: BlockId(3),
            instructions: Vec::new(),
            terminator: Terminator::Branch(BlockId(1)),
        });
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::PAYLOAD_OUTSIDE_REFINEMENT));
    }

    #[test]
    fn two_predecessors_carrying_the_same_refinement_are_accepted() {
        // bb2 (the `Empty` case's own block, dominated by bb0's
        // definition of the scrutinee like every block here) also
        // switches on the same scrutinee value instead of returning
        // directly -- a second, different edge into bb1, but one that
        // guarantees the exact same fact as the original switch's
        // case-0 edge. The intersection across both is still that one
        // fact, so bb1's existing case-0 payload extraction remains
        // legal.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        function.blocks[2].terminator = Terminator::Switch {
            scrutinee: ValueId(1),
            variant,
            cases: vec![BlockId(1), BlockId(2)],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn variant_payload_used_by_a_sibling_case_block_violates_dominance() {
        // Even if a payload extraction happened to be legal under its
        // own case's refinement, using its *result* in an unrelated
        // sibling block must still be caught by ordinary dominance --
        // this exercises that the aggregate-instruction additions
        // didn't bypass the existing dominance analysis.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        // bb2 returns %2, which is only defined in bb1.
        function.blocks[2].terminator = Terminator::Return(Some(ValueId(2)));
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::NON_DOMINATING_DEFINITION));
    }

    #[test]
    fn missing_entry_block_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        // Only block is bb1, not bb0.
        function.blocks[0].id = BlockId(1);
        function.blocks[0].terminator = Terminator::Return(None);
        function.blocks[0].instructions.clear();
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::MISSING_ENTRY_BLOCK));
    }

    #[test]
    fn a_reordered_bb0_is_still_a_valid_entry_block() {
        // bb0 exists but isn't first in the vector; entry status must
        // come from the id, never from vector position.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            blocks: vec![
                BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(0)),
                },
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(1)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(0))),
                },
            ],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn duplicate_parameter_value_ids_are_rejected() {
        use crate::nir::Param;
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.params = vec![
            Param {
                value: ValueId(0),
                ty: Ty::I64,
            },
            Param {
                value: ValueId(0),
                ty: Ty::Bool,
            },
        ];
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_VALUE_DEFINITION));
    }

    #[test]
    fn duplicate_instruction_result_ids_are_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        // %0 is already defined by `valid_function`'s single instruction;
        // add a second instruction that reuses it.
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(2)),
        });
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_VALUE_DEFINITION));
    }

    #[test]
    fn a_parameter_colliding_with_an_instruction_result_is_rejected() {
        use crate::nir::Param;
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        // `valid_function`'s single instruction already produces %0;
        // adding a parameter that also claims %0 is a collision across
        // the two different kinds of definition.
        function.params = vec![Param {
            value: ValueId(0),
            ty: Ty::I64,
        }];
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_VALUE_DEFINITION));
    }

    #[test]
    fn a_forward_reference_within_one_block_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions = vec![
            // %0 used here, before it is defined below.
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::I64,
                kind: ValueKind::Neg(ValueId(0)),
            },
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            },
        ];
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(1)));
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::USE_BEFORE_DEFINITION));
    }

    #[test]
    fn a_value_defined_in_a_sibling_branch_is_rejected() {
        // bb0 branches to bb1 or bb2; bb1 defines %1, bb2 uses it via
        // its return terminator despite never having executed bb1.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::Bool,
                        kind: ValueKind::Const(Const::Bool(true)),
                    }],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(1)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(1))),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    // %1 was only ever defined in the sibling bb1.
                    terminator: Terminator::Return(Some(ValueId(1))),
                },
            ],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::NON_DOMINATING_DEFINITION));
    }

    #[test]
    fn loading_a_slot_only_allocated_in_one_branch_is_rejected() {
        // bb1 allocates and stores a slot; bb2 (the sibling) never
        // does; bb3 (their merge) loads it regardless.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::Bool,
                        kind: ValueKind::Const(Const::Bool(true)),
                    }],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::I64,
                            kind: ValueKind::Alloc,
                        },
                        Instruction::Value {
                            result: ValueId(2),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(1)),
                        },
                        Instruction::Store {
                            slot: ValueId(1),
                            value: ValueId(2),
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    // %1 (the alloc) does not dominate bb3: the else
                    // path (bb2) reaches it without ever allocating it.
                    instructions: vec![Instruction::Value {
                        result: ValueId(3),
                        ty: Ty::I64,
                        kind: ValueKind::Load(ValueId(1)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(3))),
                },
            ],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::NON_DOMINATING_DEFINITION));
    }

    #[test]
    fn a_valid_loop_cfg_has_no_diagnostics() {
        // Standard header/body/exit shape: a mutable counter allocated
        // in the entry, loaded/compared/incremented in the header and
        // body, with a back-edge from body to header.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: Ty::I64,
                            kind: ValueKind::Alloc,
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(0)),
                        },
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(2),
                            ty: Ty::I64,
                            kind: ValueKind::Load(ValueId(0)),
                        },
                        Instruction::Value {
                            result: ValueId(3),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(10)),
                        },
                        Instruction::Value {
                            result: ValueId(4),
                            ty: Ty::Bool,
                            kind: ValueKind::Lt(ValueId(2), ValueId(3)),
                        },
                    ],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(4),
                        then_block: BlockId(2),
                        else_block: BlockId(3),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(5),
                            ty: Ty::I64,
                            kind: ValueKind::Load(ValueId(0)),
                        },
                        Instruction::Value {
                            result: ValueId(6),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(1)),
                        },
                        Instruction::Value {
                            result: ValueId(7),
                            ty: Ty::I64,
                            kind: ValueKind::Add(ValueId(5), ValueId(6)),
                        },
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(7),
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![Instruction::Value {
                        result: ValueId(8),
                        ty: Ty::I64,
                        kind: ValueKind::Load(ValueId(0)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(8))),
                },
            ],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_valid_conditional_cfg_with_an_entry_allocation_used_in_both_branches_has_no_diagnostics() {
        // The slot is allocated once in the entry block (which
        // dominates every other block), then both the then- and
        // else-branches store into it before a shared merge block loads
        // it back -- exactly the shape if/else lowering actually
        // produces.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: Ty::Bool,
                            kind: ValueKind::Const(Const::Bool(true)),
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::I64,
                            kind: ValueKind::Alloc,
                        },
                    ],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(2),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(1)),
                        },
                        Instruction::Store {
                            slot: ValueId(1),
                            value: ValueId(2),
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(3),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(2)),
                        },
                        Instruction::Store {
                            slot: ValueId(1),
                            value: ValueId(3),
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![Instruction::Value {
                        result: ValueId(4),
                        ty: Ty::I64,
                        kind: ValueKind::Load(ValueId(1)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(4))),
                },
            ],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    // -- Generic type-argument validation (`rfcs/0008`) -----------------

    #[test]
    fn a_type_parameter_escaping_a_non_generic_function_is_rejected() {
        // A `Ty::Param` belonging to *no* declaration this function
        // itself declares -- no valid lowering ever produces this; only
        // a hand-built (malformed) NIR module can.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let foreign_t = interner.intern("T");
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Param(TypeParamId(999), foreign_t);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::Param(TypeParamId(999), foreign_t),
            kind: ValueKind::Const(Const::Int(1)),
        };
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(0)));
        let diagnostics = verify_one(function, &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::ESCAPING_TYPE_PARAMETER),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_type_parameter_matching_the_functions_own_declaration_is_accepted() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let t = interner.intern("T");
        let mut function = valid_function(ItemId(0), name);
        function.type_params = vec![(TypeParamId(0), t)];
        function.return_type = Ty::Param(TypeParamId(0), t);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::Param(TypeParamId(0), t),
            kind: ValueKind::Const(Const::Int(1)),
        };
        // A `Ty::Param`-typed constant is itself a defense-in-depth
        // impossibility (no valid lowering emits one), but this test
        // only cares about the parameter-scope check specifically; the
        // const/type mismatch it also happens to trip is not what is
        // being asserted here.
        let diagnostics = verify_one(function, &interner);
        assert!(
            !codes_of(&diagnostics).contains(&codes::ESCAPING_TYPE_PARAMETER),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_duplicate_type_parameter_in_a_function_declaration_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let t = interner.intern("T");
        let mut function = valid_function(ItemId(0), name);
        function.type_params = vec![(TypeParamId(0), t), (TypeParamId(0), t)];
        let diagnostics = verify_one(function, &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::DUPLICATE_TYPE_PARAMETER),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_duplicate_type_parameter_in_a_record_declaration_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let point = interner.intern("Point");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: point,
            type_params: vec![(TypeParamId(0), t), (TypeParamId(0), t)],
            fields: vec![],
        };
        let function = valid_function(ItemId(0), name);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::DUPLICATE_TYPE_PARAMETER),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_duplicate_type_parameter_in_a_variant_declaration_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let shape = interner.intern("Shape");
        let t = interner.intern("T");
        let variant = ItemId(200);
        let layout = VariantLayout {
            name: shape,
            type_params: vec![(TypeParamId(0), t), (TypeParamId(0), t)],
            cases: vec![],
        };
        let function = valid_function(ItemId(0), name);
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::DUPLICATE_TYPE_PARAMETER),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_unresolved_type_variable_nested_inside_an_applied_type_is_rejected() {
        // `Ty::Var` buried *inside* a `Ty::Applied`'s own argument list
        // (`Box[Var(0)]`), not just at the top level -- a hand-built NIR
        // module bypassing typeck's own resolution is the only way this
        // is ever reachable.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: boxed,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![],
        };
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Applied(record, vec![Ty::Var(crate::types::TyVar(0))]);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::UNRESOLVED_TYPE_VARIABLE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_error_type_nested_inside_an_applied_type_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: boxed,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![],
        };
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Applied(record, vec![Ty::Error]);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::UNEXPECTED_ERROR_TYPE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn generic_arity_mismatch_nested_inside_an_applied_types_own_argument_is_rejected() {
        // `Outer[Pair[i64]]`, where `Pair` itself declares two type
        // parameters -- the arity problem is one level *inside* the
        // outer application's own argument, not at `Outer` itself, so
        // recursive validation (not just a top-level check) is required
        // to catch it.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let outer_name = interner.intern("Outer");
        let pair_name = interner.intern("Pair");
        let t = interner.intern("T");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let outer = ItemId(100);
        let pair = ItemId(101);
        let outer_layout = RecordLayout {
            name: outer_name,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![],
        };
        let pair_layout = RecordLayout {
            name: pair_name,
            type_params: vec![(TypeParamId(1), a), (TypeParamId(2), b)],
            fields: vec![],
        };
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Applied(outer, vec![Ty::Applied(pair, vec![Ty::I64])]);
        let diagnostics = verify_one_with_aggregates(
            function,
            vec![(outer, outer_layout), (pair, pair_layout)],
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_ARITY_MISMATCH),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_call_supplying_the_wrong_number_of_type_arguments_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let mut callee = valid_function(ItemId(0), g_name);
        callee.type_params = vec![(TypeParamId(0), t)];
        callee.return_type = Ty::Param(TypeParamId(0), t);
        callee.params = vec![crate::nir::Param {
            value: ValueId(0),
            ty: Ty::Param(TypeParamId(0), t),
        }];
        callee.blocks[0].instructions.clear();
        callee.blocks[0].terminator = Terminator::Return(Some(ValueId(0)));

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            // `g` declares one type parameter; this call supplies none.
            kind: ValueKind::Call(ItemId(0), Vec::new(), vec![ValueId(0)], Vec::new()),
        });
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_ARITY_MISMATCH),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_valid_generic_call_with_matching_type_argument_count_has_no_diagnostics() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let mut callee = valid_function(ItemId(0), g_name);
        callee.type_params = vec![(TypeParamId(0), t)];
        callee.return_type = Ty::Param(TypeParamId(0), t);
        callee.params = vec![crate::nir::Param {
            value: ValueId(0),
            ty: Ty::Param(TypeParamId(0), t),
        }];
        callee.blocks[0].instructions.clear();
        callee.blocks[0].terminator = Terminator::Return(Some(ValueId(0)));

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(1)),
        };
        caller.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            kind: ValueKind::Call(ItemId(0), vec![Ty::I64], vec![ValueId(0)], Vec::new()),
        });
        caller.blocks[0].terminator = Terminator::Return(Some(ValueId(1)));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_phantom_type_parameter_never_occurring_in_params_or_return_is_accepted() {
        // `T` appears in the function's own declared type parameters but
        // nowhere in its params or return type -- a legitimate
        // compile-time-only marker, not a malformed declaration; the
        // verifier must not require every declared parameter to actually
        // occur anywhere.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let t = interner.intern("T");
        let mut function = valid_function(ItemId(0), name);
        function.type_params = vec![(TypeParamId(0), t)];
        let diagnostics = verify_one(function, &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_phantom_type_parameter_on_a_record_never_occurring_in_any_field_is_accepted() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let marker = interner.intern("Marker");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: marker,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![(interner.intern("tag"), Ty::I64)],
        };
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(1)),
        };
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::Applied(record, vec![Ty::Bool]),
            kind: ValueKind::RecordCreate(record, vec![Ty::Bool], vec![ValueId(0)]),
        });
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(0)));
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    /// Built programmatically: a `Ty::Applied` nested well past
    /// `crate::limits::MAX_GENERIC_DEPTH`, used as a function's own
    /// return type. `check_type_root`'s depth check runs before every
    /// recursive check this verifier would otherwise run over a type
    /// (`check_no_bad_type`, `check_named_type_identity`,
    /// `check_type_param_scope`), each of which would otherwise descend
    /// into it once per level. Must terminate (this test finishing at
    /// all is the no-hang assertion), never overflow the native call
    /// stack, and must produce exactly the dedicated `V0035` diagnostic
    /// -- not silently pass, and not one diagnostic per nested level.
    #[test]
    fn a_pathologically_deep_applied_type_does_not_overflow_the_verifier() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: boxed,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![],
        };
        let depth = crate::limits::MAX_GENERIC_DEPTH + 200;
        let mut ty = Ty::I64;
        for _ in 0..depth {
            ty = Ty::Applied(record, vec![ty]);
        }
        let mut function = valid_function(ItemId(0), name);
        function.return_type = ty;
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    // -- `check_type_root` over every type root `verify_module` inspects --

    /// A `record Box[T] { payload: i64 }`-shaped layout (`payload` is
    /// deliberately non-generic; only its *use* as a type root under
    /// test needs to be generic-shaped) reused by every over-depth test
    /// below to build a `Ty::Applied` nested `depth` levels deep.
    fn deeply_applied_type(record: ItemId, depth: usize) -> Ty {
        let mut ty = Ty::I64;
        for _ in 0..depth {
            ty = Ty::Applied(record, vec![ty]);
        }
        ty
    }

    fn box_layout(interner: &mut Interner) -> (ItemId, RecordLayout) {
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        (
            ItemId(100),
            RecordLayout {
                name: boxed,
                type_params: vec![(TypeParamId(0), t)],
                fields: vec![],
            },
        )
    }

    #[test]
    fn an_over_depth_function_parameter_produces_generic_depth_exceeded() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout) = box_layout(&mut interner);
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let mut function = valid_function(ItemId(0), name);
        function.params.push(crate::nir::Param {
            value: ValueId(1),
            ty: deeply_applied_type(record, depth),
        });
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    #[test]
    fn an_over_depth_function_return_type_produces_generic_depth_exceeded() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout) = box_layout(&mut interner);
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let mut function = valid_function(ItemId(0), name);
        function.return_type = deeply_applied_type(record, depth);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    #[test]
    fn an_over_depth_record_field_produces_generic_depth_exceeded() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, mut layout) = box_layout(&mut interner);
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let deep = interner.intern("deep");
        layout
            .fields
            .push((deep, deeply_applied_type(record, depth)));
        let function = valid_function(ItemId(0), name);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    #[test]
    fn an_over_depth_variant_payload_produces_generic_depth_exceeded() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, record_layout) = box_layout(&mut interner);
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let maybe = interner.intern("Maybe");
        let some = interner.intern("Some");
        let variant = ItemId(101);
        let variant_layout = VariantLayout {
            name: maybe,
            type_params: Vec::new(),
            cases: vec![CaseLayout {
                name: some,
                payload: vec![deeply_applied_type(record, depth)],
            }],
        };
        let function = valid_function(ItemId(0), name);
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: vec![(record, record_layout)],
            variants: vec![(variant, variant_layout)],
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    #[test]
    fn an_over_depth_instruction_result_type_produces_generic_depth_exceeded() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout) = box_layout(&mut interner);
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: deeply_applied_type(record, depth),
            kind: ValueKind::Const(Const::Int(1)),
        });
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    /// A type nested *exactly* `MAX_GENERIC_DEPTH` levels deep is still
    /// within bounds -- `exceeds_generic_depth` must reject strictly
    /// past the limit, not at it, so this must produce no `V0035`.
    #[test]
    fn a_type_nested_exactly_at_the_generic_depth_limit_is_accepted() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout) = box_layout(&mut interner);
        let mut function = valid_function(ItemId(0), name);
        function.return_type = deeply_applied_type(record, crate::limits::MAX_GENERIC_DEPTH);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            !codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    // -- Shared type-root validation (`check_type_root`) at use-site generic arguments --

    /// `func g[T](x: i64) -> i64 { return x }` -- `T` occurs in neither
    /// its parameter nor its return type, so the declaration itself is
    /// legitimate (a compile-time-only marker); every *call* to it must
    /// still supply a valid type argument for its own sake.
    fn phantom_generic_callee(id: ItemId, name: Symbol, t: Symbol) -> Function {
        Function {
            id,
            name,
            type_params: vec![(TypeParamId(0), t)],
            requirements: Vec::new(),
            params: vec![crate::nir::Param {
                value: ValueId(0),
                ty: Ty::I64,
            }],
            return_type: Ty::I64,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        }
    }

    /// `func f() -> i64 { ...; return %1 }` calling `g` (id 0) with
    /// `type_arg` as its sole type argument and a single `const.i64 1`
    /// as its sole value argument.
    fn caller_calling_g_with_type_arg(f_name: Symbol, type_arg: Ty) -> Function {
        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            kind: ValueKind::Call(ItemId(0), vec![type_arg], vec![ValueId(0)], Vec::new()),
        });
        caller.blocks[0].terminator = Terminator::Return(Some(ValueId(1)));
        caller
    }

    #[test]
    fn a_call_with_ty_error_as_a_phantom_type_argument_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let caller = caller_calling_g_with_type_arg(f_name, Ty::Error);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::UNEXPECTED_ERROR_TYPE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_call_with_an_unresolved_type_variable_as_a_phantom_type_argument_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let caller = caller_calling_g_with_type_arg(f_name, Ty::Var(crate::types::TyVar(0)));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::UNRESOLVED_TYPE_VARIABLE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_call_with_an_applied_type_naming_an_unknown_declaration_as_a_type_argument_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let unknown = ItemId(9999);
        let caller = caller_calling_g_with_type_arg(f_name, Ty::Applied(unknown, vec![Ty::I64]));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::UNKNOWN_NAMED_TYPE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_call_with_a_nested_wrong_arity_application_as_a_type_argument_is_rejected() {
        // The call's own type argument is `Pair[i64]` -- valid on its
        // own shape, but `Pair` actually declares *two* type parameters,
        // so this arity problem is one level inside the call's own type
        // argument, not at the call itself.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let pair_name = interner.intern("Pair");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let pair = ItemId(100);
        let pair_layout = RecordLayout {
            name: pair_name,
            type_params: vec![(TypeParamId(1), a), (TypeParamId(2), b)],
            fields: vec![],
        };
        let caller = caller_calling_g_with_type_arg(f_name, Ty::Applied(pair, vec![Ty::I64]));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: vec![(pair, pair_layout)],
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_ARITY_MISMATCH),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_call_with_a_type_argument_deeper_than_the_generic_depth_limit_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let boxed = interner.intern("Box");
        let box_t = interner.intern("T");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let box_item = ItemId(100);
        let box_layout = RecordLayout {
            name: boxed,
            type_params: vec![(TypeParamId(1), box_t)],
            fields: vec![],
        };
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let mut deep_ty = Ty::I64;
        for _ in 0..depth {
            deep_ty = Ty::Applied(box_item, vec![deep_ty]);
        }
        let caller = caller_calling_g_with_type_arg(f_name, deep_ty);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: vec![(box_item, box_layout)],
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        // A controlled number of diagnostics, not one per nested level.
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    #[test]
    fn a_valid_phantom_generic_call_still_verifies() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let caller = caller_calling_g_with_type_arg(f_name, Ty::Bool);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_valid_generic_record_construction_with_a_real_field_still_verifies() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: boxed,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![(interner.intern("value"), Ty::Param(TypeParamId(0), t))],
        };
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(1)),
        };
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::Applied(record, vec![Ty::I64]),
            kind: ValueKind::RecordCreate(record, vec![Ty::I64], vec![ValueId(0)]),
        });
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(2),
            ty: Ty::I64,
            kind: ValueKind::RecordField {
                base: ValueId(1),
                record,
                field: 0,
            },
        });
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(2)));
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_valid_generic_variant_construction_still_verifies() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let maybe = interner.intern("Maybe");
        let some_case = interner.intern("Some");
        let t = interner.intern("T");
        let variant = ItemId(200);
        let layout = VariantLayout {
            name: maybe,
            type_params: vec![(TypeParamId(0), t)],
            cases: vec![CaseLayout {
                name: some_case,
                payload: vec![Ty::Param(TypeParamId(0), t)],
            }],
        };
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(1)),
        };
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::Applied(variant, vec![Ty::I64]),
            kind: ValueKind::VariantCreate {
                variant,
                case: 0,
                type_args: vec![Ty::I64],
                payload: vec![ValueId(0)],
            },
        });
        // Not projecting the payload back out here: doing so validly
        // requires a case-refinement edge (a `switch`), which is its own
        // separate, already-covered concern
        // (`valid_variant_switch_and_payload_extraction_has_no_diagnostics`)
        // -- this test is only about construction itself verifying.
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(0)));
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }
}
