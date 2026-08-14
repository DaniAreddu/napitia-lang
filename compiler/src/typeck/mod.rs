//! The local type checker.

pub mod context;
pub mod unify;

use std::collections::HashMap;

use context::{TypeContext, VarKind};
use unify::unify;

use crate::diagnostics::Diagnostic;
use crate::hir::{
    HirBlock, HirElse, HirExpr, HirFunction, HirMatchArm, HirMatchArmBody, HirModule, HirPattern,
    HirStmt, ItemId, LocalId, OtherItemKind,
};
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
use crate::syntax::ast::{self, AssignOp, BinaryOp, UnaryOp};
use crate::types::{Ty, TyVar, display_ty, is_integer, is_numeric, primitive_from_name};

mod codes {
    pub const TYPE_MISMATCH: &str = "T0001";
    pub const ARITY_MISMATCH: &str = "T0002";
    pub const IMMUTABLE_ASSIGN: &str = "T0003";
    pub const EXPECTED_NUMERIC: &str = "T0004";
    pub const EXPECTED_INTEGER: &str = "T0005";
    pub const UNKNOWN_TYPE: &str = "T0006";
}

#[derive(Clone)]
struct FunctionSig {
    params: Vec<Ty>,
    ret: Ty,
    span: Span,
}

#[derive(Clone)]
struct LocalInfo {
    ty: Ty,
    mutable: bool,
}

/// Every diagnostic produced by checking a module, plus the final
/// resolved type of every local binding (parameters, `value`/`mutable`
/// statements, and match-arm pattern bindings). `local_types` is what
/// lets NIR lowering (`nir::lower`) know a local's concrete type without
/// re-running unification: by the time checking finishes, every local
/// that isn't part of an ill-typed program has a fully resolved type
/// (literal defaults included).
pub struct TypeckResult {
    pub diagnostics: Vec<Diagnostic>,
    pub local_types: HashMap<LocalId, Ty>,
}

/// Type-checks an already name-resolved [`HirModule`]. Checking one
/// function never stops at the first error: each expression is still
/// visited (so later independent errors in the same function are still
/// reported), and `Ty::Error`/`Ty::Never` unify with anything so one bad
/// expression does not cascade into unrelated type mismatches.
pub fn check_module(hir: &HirModule, source: SourceId, interner: &Interner) -> TypeckResult {
    // The module's type namespace: primitives (spec/0003) plus every
    // declared `record`/`variant` name. A named type that resolves
    // against neither is genuinely unknown and must be diagnosed at its
    // own span, never silently treated as `Ty::Error` -- see
    // `resolve_named_type`.
    let type_names = hir
        .other_items
        .iter()
        .filter(|item| matches!(item.kind, OtherItemKind::Record | OtherItemKind::Variant))
        .map(|item| (item.name, item.id))
        .collect();

    let mut checker = Checker {
        source,
        interner,
        ctx: TypeContext::new(),
        diagnostics: Vec::new(),
        functions: HashMap::new(),
        locals: HashMap::new(),
        pending_defaults: Vec::new(),
        current_return_type: Ty::Unit,
        type_names,
    };
    checker.build_signatures(hir);
    for function in &hir.functions {
        checker.check_function(function);
    }
    checker.finalize_defaults();

    let local_types = checker
        .locals
        .iter()
        .map(|(id, info)| (*id, checker.ctx.resolve(&info.ty)))
        .collect();

    TypeckResult {
        diagnostics: checker.diagnostics,
        local_types,
    }
}

struct Checker<'a> {
    source: SourceId,
    interner: &'a Interner,
    ctx: TypeContext,
    diagnostics: Vec<Diagnostic>,
    functions: HashMap<ItemId, FunctionSig>,
    locals: HashMap<LocalId, LocalInfo>,
    pending_defaults: Vec<(TyVar, Ty)>,
    current_return_type: Ty,
    /// The module's named-type namespace: declared `record`/`variant`
    /// names, by their surface name, to the item they refer to.
    type_names: HashMap<Symbol, ItemId>,
}

impl<'a> Checker<'a> {
    fn build_signatures(&mut self, hir: &HirModule) {
        for f in &hir.functions {
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
            self.functions.insert(
                f.id,
                FunctionSig {
                    params,
                    ret,
                    span: f.span,
                },
            );
        }
    }

    /// Resolves a written type name against the module's type namespace:
    /// primitives first, then declared `record`/`variant` names. An
    /// unknown name is a diagnostic at the type's own span -- `Ty::Error`
    /// is only ever returned *after* recording why, never as a silent
    /// wildcard for "some type we don't recognize".
    fn resolve_named_type(&mut self, ty: &ast::Type) -> Ty {
        let text = self.interner.resolve(ty.name.symbol);
        if let Some(prim) = primitive_from_name(text) {
            return prim;
        }
        if let Some(&item) = self.type_names.get(&ty.name.symbol) {
            return Ty::Named(item, ty.name.symbol);
        }
        self.diagnostics.push(
            Diagnostic::error(
                codes::UNKNOWN_TYPE,
                self.source,
                ty.name.span,
                format!("cannot find type `{text}` in this scope"),
            )
            .with_primary_label("unknown type"),
        );
        Ty::Error
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
        let body_ty = self.check_block(&f.body);
        self.unify_report(
            &sig.ret,
            &body_ty,
            f.body.span,
            "the function's body does not match its declared return type",
        );
    }

    fn check_block(&mut self, block: &HirBlock) -> Ty {
        for stmt in &block.statements {
            self.check_stmt(stmt);
        }
        match &block.tail {
            Some(expr) => self.check_expr(expr),
            None => Ty::Unit,
        }
    }

    fn check_stmt(&mut self, stmt: &HirStmt) {
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
                    None => value_ty,
                };
                self.locals.insert(
                    b.local,
                    LocalInfo {
                        ty: final_ty,
                        mutable: b.mutable,
                    },
                );
            }
            HirStmt::Expr(e) => {
                self.check_expr(e);
            }
            HirStmt::Defer { expr, .. } => {
                self.check_expr(expr);
            }
            HirStmt::While {
                condition, body, ..
            } => {
                let cond_ty = self.check_expr(condition);
                self.expect_bool(&cond_ty, condition.span());
                self.check_block(body);
            }
            HirStmt::Loop { body, .. } => {
                self.check_block(body);
            }
        }
    }

    fn check_expr(&mut self, expr: &HirExpr) -> Ty {
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
            // only Call special-cases a Function callee directly.
            HirExpr::Function { .. } => Ty::Error,
            HirExpr::Unary { op, operand, span } => self.check_unary(*op, operand, *span),
            HirExpr::Binary {
                op,
                left,
                right,
                span,
            } => self.check_binary(*op, left, right, *span),
            HirExpr::Assign {
                target,
                op,
                value,
                span,
            } => self.check_assign(target, *op, value, *span),
            HirExpr::Call { callee, args, span } => self.check_call(callee, args, *span),
            HirExpr::Field { base, .. } => {
                self.check_expr(base);
                Ty::Error
            }
            HirExpr::Cast { expr, ty, .. } => {
                self.check_expr(expr);
                self.resolve_named_type(ty)
            }
            HirExpr::Try { expr, .. } => self.check_expr(expr),
            HirExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => self.check_if(condition, then_branch, else_branch),
            HirExpr::Match {
                scrutinee, arms, ..
            } => self.check_match(scrutinee, arms),
            HirExpr::Block(block) => self.check_block(block),
            HirExpr::Return { value, span } => {
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
            HirExpr::Break { value, span } => {
                if let Some(v) = value {
                    let value_ty = self.check_expr(v);
                    self.unify_report(
                        &value_ty,
                        &Ty::Unit,
                        *span,
                        "break with a value is not supported yet: loop-as-expression is accepted \
                         direction, not implemented (spec/0002)",
                    );
                }
                Ty::Never
            }
            HirExpr::Continue { .. } => Ty::Never,
            HirExpr::Error { .. } => Ty::Error,
        }
    }

    fn check_unary(&mut self, op: UnaryOp, operand: &HirExpr, span: Span) -> Ty {
        let ty = self.check_expr(operand);
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
        let rt = self.check_expr(right);
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
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge => {
                self.unify_report(
                    &lt,
                    &rt,
                    span,
                    "operands of a comparison must have the same type",
                );
                Ty::Bool
            }
            BinaryOp::And | BinaryOp::Or => {
                self.expect_bool(&lt, span);
                self.expect_bool(&rt, span);
                Ty::Bool
            }
            BinaryOp::Range | BinaryOp::RangeInclusive => {
                self.unify_report(&lt, &rt, span, "range endpoints must have the same type");
                self.require_integer(&lt, span);
                lt
            }
        }
    }

    fn check_assign(&mut self, target: &HirExpr, op: AssignOp, value: &HirExpr, span: Span) -> Ty {
        let target_ty = self.check_expr(target);
        if let HirExpr::Local { local, name, .. } = target
            && let Some(info) = self.locals.get(local)
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

        Ty::Unit
    }

    fn check_call(&mut self, callee: &HirExpr, args: &[HirExpr], span: Span) -> Ty {
        let arg_tys: Vec<Ty> = args.iter().map(|a| self.check_expr(a)).collect();

        let HirExpr::Function { item, name, .. } = callee else {
            self.check_expr(callee);
            return Ty::Error;
        };

        let Some(sig) = self.functions.get(item).cloned() else {
            return Ty::Error;
        };

        if sig.params.len() != args.len() {
            let text = self.interner.resolve(*name);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::ARITY_MISMATCH,
                    self.source,
                    span,
                    format!(
                        "`{text}` expects {} argument(s), found {}",
                        sig.params.len(),
                        args.len()
                    ),
                )
                .with_primary_label("wrong number of arguments")
                .with_label(sig.span, "function defined here"),
            );
        } else {
            for (arg_ty, param_ty) in arg_tys.iter().zip(sig.params.iter()) {
                self.unify_report(
                    param_ty,
                    arg_ty,
                    span,
                    "argument type does not match the parameter's declared type",
                );
            }
        }

        sig.ret
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
        match else_branch {
            Some(HirElse::Block(b)) => {
                let else_ty = self.check_block(b);
                self.unify_report(
                    &then_ty,
                    &else_ty,
                    b.span,
                    "if/else branches must have the same type",
                );
                then_ty
            }
            Some(HirElse::If(inner)) => {
                let else_ty = self.check_expr(inner);
                let span = inner.span();
                self.unify_report(
                    &then_ty,
                    &else_ty,
                    span,
                    "if/else branches must have the same type",
                );
                then_ty
            }
            None => Ty::Unit,
        }
    }

    fn check_match(&mut self, scrutinee: &HirExpr, arms: &[HirMatchArm]) -> Ty {
        let scrutinee_ty = self.check_expr(scrutinee);
        let mut result: Option<Ty> = None;
        for arm in arms {
            self.bind_pattern(&arm.pattern, &scrutinee_ty);
            let body_ty = match &arm.body {
                HirMatchArmBody::Expr(e) => self.check_expr(e),
                HirMatchArmBody::Block(b) => self.check_block(b),
            };
            match &result {
                Some(r) => {
                    self.unify_report(r, &body_ty, arm.span, "match arms must have the same type")
                }
                None => result = Some(body_ty),
            }
        }
        result.unwrap_or(Ty::Unit)
    }

    fn bind_pattern(&mut self, pattern: &HirPattern, scrutinee_ty: &Ty) {
        match pattern {
            HirPattern::Wildcard { .. } => {}
            HirPattern::Bind { local, .. } => {
                self.locals.insert(
                    *local,
                    LocalInfo {
                        ty: scrutinee_ty.clone(),
                        mutable: false,
                    },
                );
            }
            HirPattern::Variant { args, .. } => {
                for arg in args {
                    self.bind_pattern(arg, &Ty::Error);
                }
            }
            HirPattern::Int { .. }
            | HirPattern::Str { .. }
            | HirPattern::Char { .. }
            | HirPattern::Bool { .. } => {}
        }
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
    fn unify_report(&mut self, expected: &Ty, actual: &Ty, span: Span, message: &str) {
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
        }
    }

    /// Like [`display_ty`], but shows a still-unresolved literal type
    /// variable as the default it would take (`i64`/`f64`) rather than
    /// `_` — unification failing is exactly what stops that default from
    /// ever being applied, so the plain resolved form would otherwise
    /// show a placeholder instead of the type the literal actually meant.
    fn display_for_diagnostic(&self, ty: &Ty) -> String {
        if let Ty::Var(v) = ty {
            match self.ctx.kind_of(*v) {
                Some(VarKind::Integer) => return display_ty(&Ty::I64, self.interner),
                Some(VarKind::Float) => return display_ty(&Ty::F64, self.interner),
                None => {}
            }
        }
        display_ty(ty, self.interner)
    }

    fn expect_bool(&mut self, ty: &Ty, span: Span) {
        self.unify_report(&Ty::Bool, ty, span, "expected a boolean expression");
    }

    fn require_numeric(&mut self, ty: &Ty, span: Span) {
        let resolved = self.ctx.resolve(ty);
        if matches!(resolved, Ty::Var(_) | Ty::Error | Ty::Never) || is_numeric(&resolved) {
            return;
        }
        self.diagnostics.push(Diagnostic::error(
            codes::EXPECTED_NUMERIC,
            self.source,
            span,
            format!(
                "expected a numeric type, found `{}`",
                display_ty(&resolved, self.interner)
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
        self.diagnostics.push(Diagnostic::error(
            codes::EXPECTED_INTEGER,
            self.source,
            span,
            format!(
                "expected an integer type, found `{}`",
                display_ty(&resolved, self.interner)
            ),
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::lower_module;
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
        check_module(&hir, id, &interner).diagnostics
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
    fn match_arms_must_agree_in_type() {
        let diags = check("func f(x: i64) -> i64 { return match x { 1 => 10, _ => true } }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "T0001");
    }

    #[test]
    fn well_typed_match_has_no_diagnostics() {
        let diags = check("func f(x: i64) -> i64 { return match x { 1 => 10, n => n, _ => 0 } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn recursive_function_type_checks() {
        let diags =
            check("func fact(n: i64) -> i64 { if n == 0 { return 1 } return n * fact(n - 1) }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn cast_expression_takes_the_target_type() {
        let diags = check("func f() -> f64 { value x = 1; return x as f64 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
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
        assert_eq!(diags[0].code, "T0001");
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
}
