//! Renders NIR as text for debugging, matching `spec/0006`'s format:
//!
//! ```text
//! func @add(%0: i64, %1: i64) -> i64 {
//! bb0:
//!     %2 = add.i64 %0, %1
//!     ret %2
//! }
//! ```
//!
//! Output is deterministic (no pointer- or hash-derived identifiers),
//! which is what makes it usable as golden-output in tests.

use std::collections::HashMap;
use std::fmt::Write as _;

use super::block::{BasicBlock, Terminator};
use super::instruction::{Const, Instruction, ValueId, ValueKind};
use super::{Function, Module};
use crate::symbol::Interner;
use crate::types::{Ty, display_ty};

pub fn print_module(module: &Module, interner: &Interner) -> String {
    let mut out = String::new();
    for (i, function) in module.functions.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        print_function(&mut out, function, interner);
    }
    out
}

fn print_function(out: &mut String, function: &Function, interner: &Interner) {
    let params = function
        .params
        .iter()
        .map(|p| format!("%{}: {}", p.value.0, display_ty(&p.ty, interner)))
        .collect::<Vec<_>>()
        .join(", ");
    let _ = writeln!(
        out,
        "func @{}({params}) -> {} {{",
        interner.resolve(function.name),
        display_ty(&function.return_type, interner)
    );
    // Comparisons produce `bool` but are tagged with their *operand*
    // type (`eq.i64`, not `eq.bool`) per spec/0006; this table lets the
    // printer look that operand type up from the value that produced
    // it, since a comparison instruction's own declared `ty` is `bool`.
    let value_types = collect_value_types(function);
    for block in &function.blocks {
        print_block(out, block, &value_types, interner);
    }
    out.push_str("}\n");
}

fn collect_value_types(function: &Function) -> HashMap<ValueId, Ty> {
    let mut types = HashMap::new();
    for param in &function.params {
        types.insert(param.value, param.ty.clone());
    }
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value { result, ty, .. } = instruction {
                types.insert(*result, ty.clone());
            }
        }
    }
    types
}

fn print_block(
    out: &mut String,
    block: &BasicBlock,
    value_types: &HashMap<ValueId, Ty>,
    interner: &Interner,
) {
    let _ = writeln!(out, "bb{}:", block.id.0);
    for instruction in &block.instructions {
        let _ = writeln!(
            out,
            "    {}",
            format_instruction(instruction, value_types, interner)
        );
    }
    let _ = writeln!(out, "    {}", format_terminator(&block.terminator));
}

fn format_instruction(
    instruction: &Instruction,
    value_types: &HashMap<ValueId, Ty>,
    interner: &Interner,
) -> String {
    match instruction {
        Instruction::Value { result, ty, kind } => {
            format!(
                "%{} = {}",
                result.0,
                format_value_kind(kind, ty, value_types, interner)
            )
        }
        Instruction::Store { slot, value } => format!("store %{}, %{}", slot.0, value.0),
    }
}

/// The operand type for a comparison instruction (looked up from
/// whichever operand's producing instruction is known), falling back to
/// the instruction's own declared type if that lookup fails.
fn operand_ty<'a>(a: ValueId, ty: &'a Ty, value_types: &'a HashMap<ValueId, Ty>) -> &'a Ty {
    value_types.get(&a).unwrap_or(ty)
}

fn format_value_kind(
    kind: &ValueKind,
    ty: &Ty,
    value_types: &HashMap<ValueId, Ty>,
    interner: &Interner,
) -> String {
    let ty_name = display_ty(ty, interner);
    match kind {
        ValueKind::Alloc => format!("alloc.{ty_name}"),
        ValueKind::Const(c) => format!("const.{ty_name} {}", format_const(c)),
        ValueKind::Load(slot) => format!("load %{}", slot.0),
        ValueKind::Add(a, b) => format!("add.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Sub(a, b) => format!("sub.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Mul(a, b) => format!("mul.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Div(a, b) => format!("div.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Rem(a, b) => format!("rem.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Neg(a) => format!("neg.{ty_name} %{}", a.0),
        ValueKind::Not(a) => format!("not.{ty_name} %{}", a.0),
        ValueKind::And(a, b) => format!("and.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Or(a, b) => format!("or.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Xor(a, b) => format!("xor.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Shl(a, b) => format!("shl.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Shr(a, b) => format!("shr.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Eq(a, b) => {
            format!(
                "eq.{} %{}, %{}",
                display_ty(operand_ty(*a, ty, value_types), interner),
                a.0,
                b.0
            )
        }
        ValueKind::Ne(a, b) => {
            format!(
                "ne.{} %{}, %{}",
                display_ty(operand_ty(*a, ty, value_types), interner),
                a.0,
                b.0
            )
        }
        ValueKind::Lt(a, b) => {
            format!(
                "lt.{} %{}, %{}",
                display_ty(operand_ty(*a, ty, value_types), interner),
                a.0,
                b.0
            )
        }
        ValueKind::Le(a, b) => {
            format!(
                "le.{} %{}, %{}",
                display_ty(operand_ty(*a, ty, value_types), interner),
                a.0,
                b.0
            )
        }
        ValueKind::Gt(a, b) => {
            format!(
                "gt.{} %{}, %{}",
                display_ty(operand_ty(*a, ty, value_types), interner),
                a.0,
                b.0
            )
        }
        ValueKind::Ge(a, b) => {
            format!(
                "ge.{} %{}, %{}",
                display_ty(operand_ty(*a, ty, value_types), interner),
                a.0,
                b.0
            )
        }
        ValueKind::Call(function, args) => {
            let args = args
                .iter()
                .map(|v: &ValueId| format!("%{}", v.0))
                .collect::<Vec<_>>()
                .join(", ");
            format!("call @{}({args})", function.0)
        }
    }
}

fn format_const(c: &Const) -> String {
    match c {
        Const::Int(v) => v.to_string(),
        Const::Float(v) => v.to_string(),
        Const::Bool(v) => v.to_string(),
        Const::Char(v) => format!("{v:?}"),
        Const::Str(v) => format!("{v:?}"),
        Const::Unit => "unit".to_string(),
    }
}

fn format_terminator(term: &Terminator) -> String {
    match term {
        Terminator::Return(Some(v)) => format!("ret %{}", v.0),
        Terminator::Return(None) => "ret".to_string(),
        Terminator::Branch(target) => format!("br bb{}", target.0),
        Terminator::CondBranch {
            condition,
            then_block,
            else_block,
        } => {
            format!(
                "condbr %{}, bb{}, bb{}",
                condition.0, then_block.0, else_block.0
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::lower_module as lower_hir;
    use crate::lexer::tokenize;
    use crate::nir::lower_module;
    use crate::parser::Parser;
    use crate::source::SourceMap;
    use crate::typeck::check_module;

    fn print(text: &str) -> String {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "{diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "{diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(diags.is_empty(), "{diags:?}");
        let typeck_result = check_module(&hir, id, &interner);
        assert!(
            typeck_result.diagnostics.is_empty(),
            "{:?}",
            typeck_result.diagnostics
        );
        let (nir, skipped) = lower_module(
            &hir,
            &typeck_result.local_types,
            &typeck_result.expr_types,
            &interner,
        );
        assert!(skipped.is_empty(), "{skipped:?}");
        print_module(&nir, &interner)
    }

    #[test]
    fn prints_add_function_matching_the_spec_example() {
        let text = print("func add(left: i64, right: i64) -> i64 { return left + right }");
        assert!(text.starts_with("func @add(%0: i64, %1: i64) -> i64 {\n"));
        assert!(text.contains("bb0:\n"));
        assert!(text.contains("add.i64"));
        assert!(text.contains("ret"));
    }

    #[test]
    fn printer_output_is_deterministic() {
        let a = print("func f() -> i64 { return 1 + 2 }");
        let b = print("func f() -> i64 { return 1 + 2 }");
        assert_eq!(a, b);
    }

    #[test]
    fn prints_multiple_functions_in_declaration_order() {
        let text = print("func a() -> i64 { return 1 } func b() -> i64 { return 2 }");
        let a_pos = text.find("func @a").unwrap();
        let b_pos = text.find("func @b").unwrap();
        assert!(a_pos < b_pos);
    }

    #[test]
    fn prints_conditional_branches_for_if() {
        let text = print("func f(x: bool) -> i64 { if x { return 1 } return 0 }");
        assert!(text.contains("condbr"));
    }
}
