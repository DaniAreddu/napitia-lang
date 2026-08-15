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
use crate::hir::ItemId;
use crate::source::{SourceId, Span};
use crate::symbol::Interner;
use crate::types::{Ty, is_integer, is_numeric};

use super::block::{BasicBlock, BlockId, Terminator};
use super::instruction::{Const, Instruction, ValueId, ValueKind};
use super::{Function, Module};

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
}

/// Every function this module's `Call` instructions might reference,
/// along with the signature the verifier checks calls against.
struct KnownFunction {
    params: Vec<Ty>,
    return_type: Ty,
}

/// Verifies every function in `module`, collecting every diagnostic it
/// can rather than stopping at the first problem (mirroring `typeck`'s
/// own style) -- an empty result means the module is safe to interpret.
pub fn verify_module(module: &Module, source: SourceId, interner: &Interner) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    let mut known_functions: HashMap<ItemId, KnownFunction> = HashMap::new();
    let mut seen_function_ids = HashSet::new();
    for function in &module.functions {
        if !seen_function_ids.insert(function.id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_FUNCTION_ID,
                source,
                Span::dummy(),
                format!(
                    "function `{}` reuses an id already used by another function in this module",
                    interner.resolve(function.name)
                ),
            ));
        }
        known_functions.insert(
            function.id,
            KnownFunction {
                params: function.params.iter().map(|p| p.ty.clone()).collect(),
                return_type: function.return_type.clone(),
            },
        );
    }

    for function in &module.functions {
        verify_function(
            function,
            &known_functions,
            source,
            interner,
            &mut diagnostics,
        );
    }

    diagnostics
}

fn verify_function(
    function: &Function,
    known_functions: &HashMap<ItemId, KnownFunction>,
    source: SourceId,
    interner: &Interner,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let name = interner.resolve(function.name);

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

    check_no_bad_type(&function.return_type, source, name, diagnostics);
    for param in &function.params {
        check_no_bad_type(&param.ty, source, name, diagnostics);
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
                    check_no_bad_type(ty, source, name, diagnostics);
                    verify_value_kind(
                        *result,
                        ty,
                        kind,
                        &value_types,
                        &alloc_slots,
                        known_functions,
                        source,
                        name,
                        interner,
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
        }
    }

    verify_dominance(function, &param_values, source, name, diagnostics);
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
        ValueKind::Call(_, args) => args.clone(),
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
fn check_no_bad_type(
    ty: &Ty,
    source: SourceId,
    function_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match ty {
        Ty::Var(_) => diagnostics.push(Diagnostic::error(
            codes::UNRESOLVED_TYPE_VARIABLE,
            source,
            Span::dummy(),
            format!(
                "function `{function_name}` contains an unresolved type variable; typeck must \
                 fully resolve every type before lowering"
            ),
        )),
        Ty::Error => diagnostics.push(Diagnostic::error(
            codes::UNEXPECTED_ERROR_TYPE,
            source,
            Span::dummy(),
            format!(
                "function `{function_name}` contains an error type in executable NIR; an \
                 ill-typed program should never reach lowering"
            ),
        )),
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_value_kind(
    result: ValueId,
    result_ty: &Ty,
    kind: &ValueKind,
    value_types: &HashMap<ValueId, Ty>,
    alloc_slots: &HashSet<ValueId>,
    known_functions: &HashMap<ItemId, KnownFunction>,
    source: SourceId,
    function_name: &str,
    interner: &Interner,
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
        ValueKind::Call(callee, args) => {
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
            if sig.return_type != *result_ty {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "calls a function returning `{}` but is itself declared `{}`",
                        ty_name(&sig.return_type),
                        ty_name(result_ty)
                    ),
                );
            }
            if sig.params.len() != args.len() {
                diagnostics.push(Diagnostic::error(
                    codes::ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}` calls a function expecting {} argument(s) with {}",
                        sig.params.len(),
                        args.len()
                    ),
                ));
            } else {
                for (param_ty, arg) in sig.params.iter().zip(args.iter()) {
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
    use crate::nir::BasicBlock;
    use crate::source::SourceMap;
    use crate::symbol::Symbol;

    /// `func f() -> i64 { return 1 }`, built directly (bypassing
    /// `nir::lower`) so each test can mutate exactly one thing about an
    /// otherwise-valid module and confirm the verifier catches it.
    fn valid_function(id: ItemId, name: Symbol) -> Function {
        Function {
            id,
            name,
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
            functions: vec![valid_function(ItemId(0), name)],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![valid_function(ItemId(0), a), valid_function(ItemId(0), b)],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            kind: ValueKind::Call(ItemId(42), Vec::new()),
        });
        let module = Module {
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            functions: vec![function],
        };
        let diagnostics = verify_module(&module, source, &interner);
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
            kind: ValueKind::Call(ItemId(0), vec![ValueId(0)]),
        });
        let callee = valid_function(ItemId(0), g_name);
        let module = Module {
            functions: vec![callee, caller],
        };
        let diagnostics = verify_module(&module, source, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::ARITY_MISMATCH));
    }

    fn verify_one(function: Function, interner: &Interner) -> Vec<Diagnostic> {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let module = Module {
            functions: vec![function],
        };
        verify_module(&module, source, interner)
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
}
