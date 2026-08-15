//! A small interpreter for the NIR subset this milestone lowers to
//! (`spec/0006`), used to validate language semantics before any native
//! backend exists.
//!
//! Every runtime value is represented uniformly as an `i128`/`f64` pair
//! of kinds regardless of its declared width (`i8` and `i64` both
//! execute as `Value::Int`); this milestone does not model
//! width-specific overflow or truncation behavior. Integer arithmetic
//! wraps on overflow (`wrapping_add` etc.) rather than panicking, since
//! Rust's debug-mode overflow checks would otherwise crash the
//! interpreter on ordinary, valid Napitia programs.

use std::cmp::Ordering;
use std::collections::HashMap;

use crate::nir::{Const, Function, Module, Terminator, ValueId, ValueKind};
use crate::symbol::Interner;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i128),
    Float(f64),
    Bool(bool),
    Char(char),
    Str(String),
    Unit,
}

/// A condition the interpreter detects and reports instead of crashing:
/// division/remainder by zero, or an internal-invariant violation (a
/// value read before it was computed, an operator applied to
/// incompatible value kinds, an unknown function). The latter should
/// never happen for NIR produced by `nir::lower`, but the interpreter
/// still returns a structured error rather than panicking or invoking
/// undefined behavior, per the project's no-panic-on-malformed-input
/// rule.
#[derive(Debug, Clone, PartialEq)]
pub enum InterpreterError {
    DivisionByZero,
    InvalidOperation(String),
}

pub struct Interpreter<'a> {
    module: &'a Module,
}

impl<'a> Interpreter<'a> {
    pub fn new(module: &'a Module) -> Self {
        Interpreter { module }
    }

    /// Calls the function named `name` with no arguments — the shape of
    /// `napitia run`'s entry point (`func main() -> ...`).
    pub fn run(&self, name: &str, interner: &Interner) -> Result<Value, InterpreterError> {
        self.call(name, interner, Vec::new())
    }

    pub fn call(
        &self,
        name: &str,
        interner: &Interner,
        args: Vec<Value>,
    ) -> Result<Value, InterpreterError> {
        let function = self
            .module
            .functions
            .iter()
            .find(|f| interner.resolve(f.name) == name)
            .ok_or_else(|| {
                InterpreterError::InvalidOperation(format!("unknown function `{name}`"))
            })?;
        self.call_function(function, args)
    }

    fn call_function(
        &self,
        function: &Function,
        args: Vec<Value>,
    ) -> Result<Value, InterpreterError> {
        // `Vec::zip` silently truncates to the shorter side: too few
        // arguments would leave the missing parameters unbound (an
        // arbitrary "value not found" error later, from whichever
        // instruction first reads one -- not a clear diagnosis of the
        // actual problem), and too many would just drop the extra ones
        // with no error at all. The verifier does not check call sites
        // against argument *values* (only NIR-to-NIR signatures), so
        // this is the one place a real arity mismatch at the API
        // boundary is still checked before it can do either.
        if function.params.len() != args.len() {
            return Err(InterpreterError::InvalidOperation(format!(
                "function expects {} argument(s), found {}",
                function.params.len(),
                args.len()
            )));
        }
        let mut values: HashMap<ValueId, Value> = HashMap::new();
        for (param, arg) in function.params.iter().zip(args) {
            values.insert(param.value, arg);
        }

        // `BlockId(0)` is the entry block by definition (the verifier
        // requires exactly one to exist -- `nir::verify`), not whichever
        // block happens to be first in the vector.
        let mut block_id = crate::nir::BlockId(0);
        if !function.blocks.iter().any(|b| b.id == block_id) {
            return Err(InterpreterError::InvalidOperation(
                "function has no entry block (bb0)".to_string(),
            ));
        }

        loop {
            let block = function
                .blocks
                .iter()
                .find(|b| b.id == block_id)
                .ok_or_else(|| {
                    InterpreterError::InvalidOperation("branch to unknown block".to_string())
                })?;

            for instruction in &block.instructions {
                match instruction {
                    crate::nir::Instruction::Value { result, kind, .. } => {
                        let value = self.eval(kind, &values)?;
                        values.insert(*result, value);
                    }
                    crate::nir::Instruction::Store { slot, value } => {
                        let v = get(&values, value)?;
                        values.insert(*slot, v);
                    }
                }
            }

            match &block.terminator {
                Terminator::Return(Some(id)) => return get(&values, id),
                Terminator::Return(None) => return Ok(Value::Unit),
                Terminator::Branch(target) => block_id = *target,
                Terminator::CondBranch {
                    condition,
                    then_block,
                    else_block,
                } => {
                    block_id = match get(&values, condition)? {
                        Value::Bool(true) => *then_block,
                        Value::Bool(false) => *else_block,
                        _ => {
                            return Err(InterpreterError::InvalidOperation(
                                "branch condition was not a bool".to_string(),
                            ));
                        }
                    };
                }
            }
        }
    }

    fn eval(
        &self,
        kind: &ValueKind,
        values: &HashMap<ValueId, Value>,
    ) -> Result<Value, InterpreterError> {
        match kind {
            ValueKind::Alloc => Ok(Value::Unit),
            ValueKind::Const(c) => Ok(const_value(c)),
            ValueKind::Load(id) => get(values, id),
            ValueKind::Add(a, b) => arith(
                get(values, a)?,
                get(values, b)?,
                i128::wrapping_add,
                |x, y| x + y,
            ),
            ValueKind::Sub(a, b) => arith(
                get(values, a)?,
                get(values, b)?,
                i128::wrapping_sub,
                |x, y| x - y,
            ),
            ValueKind::Mul(a, b) => arith(
                get(values, a)?,
                get(values, b)?,
                i128::wrapping_mul,
                |x, y| x * y,
            ),
            ValueKind::Div(a, b) => div(get(values, a)?, get(values, b)?, false),
            ValueKind::Rem(a, b) => div(get(values, a)?, get(values, b)?, true),
            ValueKind::Neg(a) => match get(values, a)? {
                Value::Int(x) => Ok(Value::Int(x.wrapping_neg())),
                Value::Float(x) => Ok(Value::Float(-x)),
                other => Err(invalid(format!("cannot negate {}", kind_name(&other)))),
            },
            ValueKind::Not(a) => match get(values, a)? {
                Value::Bool(x) => Ok(Value::Bool(!x)),
                Value::Int(x) => Ok(Value::Int(!x)),
                other => Err(invalid(format!(
                    "cannot apply `not` to {}",
                    kind_name(&other)
                ))),
            },
            ValueKind::And(a, b) => bitop(get(values, a)?, get(values, b)?, |x, y| x & y),
            ValueKind::Or(a, b) => bitop(get(values, a)?, get(values, b)?, |x, y| x | y),
            ValueKind::Xor(a, b) => bitop(get(values, a)?, get(values, b)?, |x, y| x ^ y),
            ValueKind::Shl(a, b) => shift(get(values, a)?, get(values, b)?, i128::checked_shl),
            ValueKind::Shr(a, b) => shift(get(values, a)?, get(values, b)?, i128::checked_shr),
            ValueKind::Eq(a, b) => Ok(Value::Bool(eq(&get(values, a)?, &get(values, b)?)?)),
            ValueKind::Ne(a, b) => Ok(Value::Bool(!eq(&get(values, a)?, &get(values, b)?)?)),
            ValueKind::Lt(a, b) => Ok(Value::Bool(
                ord(&get(values, a)?, &get(values, b)?)? == Ordering::Less,
            )),
            ValueKind::Le(a, b) => Ok(Value::Bool(
                ord(&get(values, a)?, &get(values, b)?)? != Ordering::Greater,
            )),
            ValueKind::Gt(a, b) => Ok(Value::Bool(
                ord(&get(values, a)?, &get(values, b)?)? == Ordering::Greater,
            )),
            ValueKind::Ge(a, b) => Ok(Value::Bool(
                ord(&get(values, a)?, &get(values, b)?)? != Ordering::Less,
            )),
            ValueKind::Call(item, args) => {
                let arg_values = args
                    .iter()
                    .map(|id| get(values, id))
                    .collect::<Result<Vec<_>, _>>()?;
                let callee = self
                    .module
                    .functions
                    .iter()
                    .find(|f| f.id == *item)
                    .ok_or_else(|| invalid("call to a function not present in this module"))?;
                self.call_function(callee, arg_values)
            }
        }
    }
}

fn get(values: &HashMap<ValueId, Value>, id: &ValueId) -> Result<Value, InterpreterError> {
    values
        .get(id)
        .cloned()
        .ok_or_else(|| invalid(format!("%{} was read before it was computed", id.0)))
}

fn invalid(message: impl Into<String>) -> InterpreterError {
    InterpreterError::InvalidOperation(message.into())
}

fn kind_name(value: &Value) -> &'static str {
    match value {
        Value::Int(_) => "an integer",
        Value::Float(_) => "a float",
        Value::Bool(_) => "a bool",
        Value::Char(_) => "a char",
        Value::Str(_) => "a string",
        Value::Unit => "unit",
    }
}

fn const_value(c: &Const) -> Value {
    match c {
        Const::Int(v) => Value::Int(*v as i128),
        Const::Float(v) => Value::Float(*v),
        Const::Bool(v) => Value::Bool(*v),
        Const::Char(v) => Value::Char(*v),
        Const::Str(v) => Value::Str(v.clone()),
        Const::Unit => Value::Unit,
    }
}

fn arith(
    a: Value,
    b: Value,
    int_op: impl Fn(i128, i128) -> i128,
    float_op: impl Fn(f64, f64) -> f64,
) -> Result<Value, InterpreterError> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(int_op(x, y))),
        (Value::Float(x), Value::Float(y)) => Ok(Value::Float(float_op(x, y))),
        (a, b) => Err(invalid(format!(
            "arithmetic between {} and {}",
            kind_name(&a),
            kind_name(&b)
        ))),
    }
}

fn div(a: Value, b: Value, remainder: bool) -> Result<Value, InterpreterError> {
    match (a, b) {
        (Value::Int(_), Value::Int(0)) => Err(InterpreterError::DivisionByZero),
        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(if remainder {
            x.wrapping_rem(y)
        } else {
            x.wrapping_div(y)
        })),
        (Value::Float(x), Value::Float(y)) => {
            Ok(Value::Float(if remainder { x % y } else { x / y }))
        }
        (a, b) => Err(invalid(format!(
            "division between {} and {}",
            kind_name(&a),
            kind_name(&b)
        ))),
    }
}

fn bitop(a: Value, b: Value, op: impl Fn(i128, i128) -> i128) -> Result<Value, InterpreterError> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(op(x, y))),
        (a, b) => Err(invalid(format!(
            "bitwise operator between {} and {}",
            kind_name(&a),
            kind_name(&b)
        ))),
    }
}

fn shift(
    a: Value,
    b: Value,
    op: impl Fn(i128, u32) -> Option<i128>,
) -> Result<Value, InterpreterError> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => {
            let amount = u32::try_from(y).map_err(|_| invalid("shift amount out of range"))?;
            op(x, amount)
                .map(Value::Int)
                .ok_or_else(|| invalid("shift amount out of range"))
        }
        (a, b) => Err(invalid(format!(
            "shift between {} and {}",
            kind_name(&a),
            kind_name(&b)
        ))),
    }
}

fn eq(a: &Value, b: &Value) -> Result<bool, InterpreterError> {
    Ok(match (a, b) {
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Float(x), Value::Float(y)) => x == y,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Char(x), Value::Char(y)) => x == y,
        (Value::Str(x), Value::Str(y)) => x == y,
        (Value::Unit, Value::Unit) => true,
        (a, b) => {
            return Err(invalid(format!(
                "compared {} with {}",
                kind_name(a),
                kind_name(b)
            )));
        }
    })
}

fn ord(a: &Value, b: &Value) -> Result<Ordering, InterpreterError> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Ok(x.cmp(y)),
        (Value::Float(x), Value::Float(y)) => x
            .partial_cmp(y)
            .ok_or_else(|| invalid("comparison involving NaN")),
        (Value::Char(x), Value::Char(y)) => Ok(x.cmp(y)),
        (Value::Str(x), Value::Str(y)) => Ok(x.cmp(y)),
        (Value::Bool(x), Value::Bool(y)) => Ok(x.cmp(y)),
        (a, b) => Err(invalid(format!(
            "ordered comparison of {} with {}",
            kind_name(a),
            kind_name(b)
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::lower_module as lower_hir;
    use crate::lexer::tokenize;
    use crate::nir::lower_module as lower_nir;
    use crate::parser::Parser;
    use crate::source::SourceMap;
    use crate::typeck::check_module;

    fn run(text: &str) -> Result<Value, InterpreterError> {
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
        let result = check_module(&hir, id, &interner);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected type errors: {:?}",
            result.diagnostics
        );
        let nir = lower_nir(&hir, &result.local_types, &result.expr_types, &interner, id)
            .expect("expected lowering to succeed");
        Interpreter::new(&nir).run("main", &interner)
    }

    #[test]
    fn executes_arithmetic() {
        assert_eq!(
            run("func main() -> i64 { return 40 + 2 }"),
            Ok(Value::Int(42))
        );
    }

    #[test]
    fn executes_function_calls() {
        let text = "func add(left: i64, right: i64) -> i64 { return left + right } \
                    func main() -> i64 { return add(40, 2) }";
        assert_eq!(run(text), Ok(Value::Int(42)));
    }

    #[test]
    fn executes_recursive_calls() {
        let text = "func fact(n: i64) -> i64 { if n == 0 { return 1 } return n * fact(n - 1) } \
                    func main() -> i64 { return fact(5) }";
        assert_eq!(run(text), Ok(Value::Int(120)));
    }

    #[test]
    fn executes_if_else() {
        let text = "func main() -> i64 { \
                        value answer = 42; \
                        if answer == 42 { return answer } else { return 0 } \
                    }";
        assert_eq!(run(text), Ok(Value::Int(42)));
    }

    #[test]
    fn executes_while_loop() {
        let text = "func main() -> i64 { \
                        mutable total = 0; \
                        mutable i = 0; \
                        while i < 5 { total = total + i; i = i + 1; } \
                        return total \
                    }";
        assert_eq!(run(text), Ok(Value::Int(10)));
    }

    #[test]
    fn executes_loop_with_break() {
        let text = "func main() -> i64 { \
                        mutable i = 0; \
                        loop { \
                            if i == 3 { break; } \
                            i = i + 1; \
                        } \
                        return i \
                    }";
        assert_eq!(run(text), Ok(Value::Int(3)));
    }

    #[test]
    fn executes_continue() {
        let text = "func main() -> i64 { \
                        mutable i = 0; \
                        mutable total = 0; \
                        while i < 5 { \
                            i = i + 1; \
                            if i == 3 { continue; } \
                            total = total + i; \
                        } \
                        return total \
                    }";
        // i runs 1..=5, skipping the total += step only when i == 3:
        // 1 + 2 + 4 + 5 = 12.
        assert_eq!(run(text), Ok(Value::Int(12)));
    }

    #[test]
    fn detects_division_by_zero() {
        let text = "func main() -> i64 { value z = 0; return 1 / z }";
        assert_eq!(run(text), Err(InterpreterError::DivisionByZero));
    }

    #[test]
    fn detects_remainder_by_zero() {
        let text = "func main() -> i64 { value z = 0; return 1 % z }";
        assert_eq!(run(text), Err(InterpreterError::DivisionByZero));
    }

    #[test]
    fn float_division_by_zero_is_infinity_not_an_error() {
        let text = "func main() -> f64 { value z = 0.0; return 1.0 / z }";
        assert_eq!(run(text), Ok(Value::Float(f64::INFINITY)));
    }

    #[test]
    fn short_circuit_and_skips_the_right_operand() {
        // If && were not short-circuiting (or divided eagerly), this
        // would panic/error on division by zero instead of returning
        // false.
        let text = "func main() -> bool { \
                        value z = 0; \
                        return false && (1 / z == 1) \
                    }";
        assert_eq!(run(text), Ok(Value::Bool(false)));
    }

    #[test]
    fn short_circuit_or_skips_the_right_operand() {
        let text = "func main() -> bool { \
                        value z = 0; \
                        return true || (1 / z == 1) \
                    }";
        assert_eq!(run(text), Ok(Value::Bool(true)));
    }

    #[test]
    fn executes_bitwise_and_shift_operators() {
        assert_eq!(
            run("func main() -> i64 { return 6 & 3 }"),
            Ok(Value::Int(2))
        );
        assert_eq!(
            run("func main() -> i64 { return 6 | 1 }"),
            Ok(Value::Int(7))
        );
        assert_eq!(
            run("func main() -> i64 { return 5 ^ 1 }"),
            Ok(Value::Int(4))
        );
        assert_eq!(
            run("func main() -> i64 { return 1 << 4 }"),
            Ok(Value::Int(16))
        );
        assert_eq!(
            run("func main() -> i64 { return 16 >> 2 }"),
            Ok(Value::Int(4))
        );
    }

    #[test]
    fn executes_comparisons() {
        assert_eq!(
            run("func main() -> bool { return 1 < 2 }"),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run("func main() -> bool { return 2 <= 2 }"),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run("func main() -> bool { return 3 > 2 }"),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run("func main() -> bool { return 2 >= 3 }"),
            Ok(Value::Bool(false))
        );
    }

    #[test]
    fn executes_unary_negation_and_not() {
        assert_eq!(run("func main() -> i64 { return -5 }"), Ok(Value::Int(-5)));
        assert_eq!(
            run("func main() -> bool { return !false }"),
            Ok(Value::Bool(true))
        );
    }

    #[test]
    fn executes_compound_assignment() {
        let text = "func main() -> i64 { mutable x = 10; x += 5; return x }";
        assert_eq!(run(text), Ok(Value::Int(15)));
    }

    #[test]
    fn integer_overflow_wraps_instead_of_panicking() {
        let text = format!(
            "func main() -> i64 {{ value m = {}; return m + 1 }}",
            i64::MAX
        );
        // Must not panic; wrapping semantics are a documented
        // simplification of this milestone's interpreter.
        assert!(run(&text).is_ok());
    }

    #[test]
    fn diverging_initializer_short_circuits_the_rest_of_the_block() {
        // The initializer of `x` diverges before the binding ever
        // completes, so `x` never exists; the rest of the block (`x =
        // 99; return x`) is unreachable and must never run -- if NIR
        // lowering had appended instructions after the diverging
        // `return 1`'s terminator (the bug this guards against), this
        // would either panic or return 99 instead of 1.
        let text = "func main() -> i64 { mutable x = return 1; x = 99; return x }";
        assert_eq!(run(text), Ok(Value::Int(1)));
    }

    #[test]
    fn diverging_while_condition_runs_and_returns_unit() {
        // The condition always returns before the loop can ever run;
        // the whole statement -- and the function -- must simply
        // complete with `unit`, not panic or hang.
        let text = "func main() { while { return; } {} }";
        assert_eq!(run(text), Ok(Value::Unit));
    }

    #[test]
    fn if_without_else_evaluates_the_branch_but_returns_unit() {
        let text = "func main() { if true { 1 } }";
        assert_eq!(run(text), Ok(Value::Unit));
    }

    #[test]
    fn if_else_join_returns_the_non_diverging_value_when_then_diverges() {
        let text = "func choose(flag: bool) -> i64 { if flag { return 1 } else { 2 } } \
                    func main() -> i64 { return choose(false) }";
        assert_eq!(run(text), Ok(Value::Int(2)));
    }

    #[test]
    fn if_else_join_returns_the_non_diverging_value_when_else_diverges() {
        let text = "func choose(flag: bool) -> i64 { if flag { 2 } else { return 1 } } \
                    func main() -> i64 { return choose(true) }";
        assert_eq!(run(text), Ok(Value::Int(2)));
    }

    #[test]
    fn unary_not_on_a_diverging_operand_returns_the_divergent_value() {
        let text = "func main() -> i64 { !{ return 7 } }";
        assert_eq!(run(text), Ok(Value::Int(7)));
    }

    #[test]
    fn comparison_with_a_diverging_right_operand_returns_the_divergent_value() {
        let text = "func main() -> i64 { 1 == { return 7 } }";
        assert_eq!(run(text), Ok(Value::Int(7)));
    }

    #[test]
    fn assignment_with_a_diverging_right_hand_side_returns_the_divergent_value() {
        let text = "func main() -> i64 { mutable x = 0; x = { return 7 }; }";
        assert_eq!(run(text), Ok(Value::Int(7)));
    }

    #[test]
    fn calling_an_unknown_function_is_an_error_not_a_panic() {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", "func main() -> i64 { return 0 }");
        let mut interner = Interner::new();
        let (tokens, _) = tokenize(map.get(id).content(), id, &mut interner);
        let (module, _) = Parser::new(tokens, id, &mut interner).parse_module();
        let (hir, _) = lower_hir(&module, id, &interner);
        let result = check_module(&hir, id, &interner);
        let nir = lower_nir(&hir, &result.local_types, &result.expr_types, &interner, id)
            .expect("expected lowering to succeed");
        let outcome = Interpreter::new(&nir).run("does_not_exist", &interner);
        assert!(matches!(
            outcome,
            Err(InterpreterError::InvalidOperation(_))
        ));
    }

    #[test]
    fn calling_with_too_few_arguments_is_an_error_not_a_silent_partial_bind() {
        // `Vec::zip` would otherwise silently truncate to the shorter
        // side, leaving the missing parameter unbound instead of
        // reporting the actual problem.
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Function, Param, Terminator};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let name = interner.intern("f");
        let module = Module {
            functions: vec![Function {
                id: ItemId(0),
                name,
                params: vec![
                    Param {
                        value: ValueId(0),
                        ty: Ty::I64,
                    },
                    Param {
                        value: ValueId(1),
                        ty: Ty::I64,
                    },
                ],
                return_type: Ty::I64,
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Return(Some(ValueId(0))),
                }],
            }],
        };
        let outcome = Interpreter::new(&module).call("f", &interner, vec![Value::Int(1)]);
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected an arity-mismatch error, got {outcome:?}"
        );
    }

    #[test]
    fn calling_with_too_many_arguments_is_an_error_not_a_silent_drop() {
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Function, Param, Terminator};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let name = interner.intern("f");
        let module = Module {
            functions: vec![Function {
                id: ItemId(0),
                name,
                params: vec![Param {
                    value: ValueId(0),
                    ty: Ty::I64,
                }],
                return_type: Ty::I64,
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Return(Some(ValueId(0))),
                }],
            }],
        };
        let outcome =
            Interpreter::new(&module).call("f", &interner, vec![Value::Int(1), Value::Int(2)]);
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected an arity-mismatch error, got {outcome:?}"
        );
    }

    #[test]
    fn a_function_missing_its_entry_block_is_an_error_not_a_panic() {
        // `function.blocks.first()` would previously accept whichever
        // block happened to be first in the vector, regardless of its
        // id; entry status must come from being `bb0` specifically.
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Function, Terminator};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let name = interner.intern("f");
        let module = Module {
            functions: vec![Function {
                id: ItemId(0),
                name,
                params: Vec::new(),
                return_type: Ty::Unit,
                blocks: vec![BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::Return(None),
                }],
            }],
        };
        let outcome = Interpreter::new(&module).call("f", &interner, Vec::new());
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected a missing-entry-block error, got {outcome:?}"
        );
    }
}
