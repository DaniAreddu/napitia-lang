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

use super::block::{BlockId, Terminator};
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
    // every later check is a lookup, never a re-derivation.
    let mut value_types: HashMap<ValueId, Ty> = HashMap::new();
    let mut alloc_slots: HashSet<ValueId> = HashSet::new();
    for param in &function.params {
        value_types.insert(param.value, param.ty.clone());
    }
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value { result, ty, kind } = instruction {
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
}
