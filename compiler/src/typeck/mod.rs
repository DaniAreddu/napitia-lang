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
    HirPattern, HirStmt, ItemId, LocalId,
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
        .records
        .iter()
        .map(|r| (r.name, r.id))
        .chain(hir.variants.iter().map(|v| (v.name, v.id)))
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
        records: HashMap::new(),
        variants: HashMap::new(),
        variant_display: HashMap::new(),
        loop_depth: 0,
        expr_types: HashMap::new(),
        pattern_case: HashMap::new(),
    };
    checker.build_aggregate_info(hir);
    checker.check_aggregate_cycles(hir);
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
    // Resolved the same way as local_types, and for the same reason:
    // an expression's raw recorded type can still be an unresolved
    // `Ty::Var` at the point check_expr ran (unification may settle it
    // later, or finalize_defaults may only just now be applying its
    // literal default) -- this is the one place that's collapsed away
    // before anything outside typeck ever sees these types.
    let expr_types = checker
        .expr_types
        .iter()
        .map(|(id, ty)| (*id, checker.ctx.resolve(ty)))
        .collect();

    TypeckResult {
        diagnostics: checker.diagnostics,
        local_types,
        expr_types,
        pattern_case: checker.pattern_case,
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
}

#[derive(Clone)]
struct RecordInfo {
    /// `(field name, declared type)`, in declaration order.
    fields: Vec<(Symbol, Ty)>,
}

#[derive(Clone)]
struct VariantInfo {
    /// The variant's own declaration symbol -- e.g. `LookupResult`, not
    /// one of its case names -- carried so `Ty::Named` can always be
    /// built with the declaration's own name (see `named_variant_ty`).
    name: Symbol,
    /// `(case name, declared payload types)`, in declaration order.
    cases: Vec<(Symbol, Vec<Ty>)>,
}

impl<'a> Checker<'a> {
    /// Resolves every declared record's field types and every declared
    /// variant's case payload types, once, before any function body or
    /// the aggregate-cycle check runs -- both need every item's fields/
    /// payloads already resolved to `Ty`.
    fn build_aggregate_info(&mut self, hir: &HirModule) {
        for r in &hir.records {
            let fields = r
                .fields
                .iter()
                .map(|f| (f.name, self.resolve_named_type(&f.ty)))
                .collect();
            self.records.insert(r.id, RecordInfo { fields });
        }
        for v in &hir.variants {
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
            .map(|(id, info)| (*id, info.fields.iter().map(|(_, ty)| ty.clone()).collect()))
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
            self.source,
            self.interner,
        ));
    }

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
        if !f.uses.is_empty() || !f.raises.is_empty() {
            self.push_unsupported(f.name_span, "`uses`/`raises` effect and error clauses");
        }
        // `napitia run` always calls `main` with zero arguments (`cli.rs`
        // hardcodes the entry point's name, not its arity), so a `main`
        // declared with parameters can never actually receive them --
        // that must be caught here, not discovered as missing values at
        // interpretation time.
        if self.interner.resolve(f.name) == "main" && !f.params.is_empty() {
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
            // A bare (uncalled) reference to a variant case constructor
            // is itself a complete value only when the case carries no
            // payload; `Call`'s own arm handles a `CaseRef` used as a
            // callee, so reaching this arm bare means the case was
            // referenced directly, e.g. `LookupResult.Missing`.
            HirExpr::CaseRef {
                variant,
                case,
                span,
                ..
            } => self.check_case_ref(*variant, *case, *span),
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
                callee, args, span, ..
            } => self.check_call(callee, args, *span),
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
                record,
                fields,
                span,
                ..
            } => self.check_record_literal(*record, fields, *span),
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

    fn check_call(&mut self, callee: &HirExpr, args: &[HirExpr], span: Span) -> Ty {
        if let HirExpr::CaseRef { variant, case, .. } = callee {
            return self.check_variant_construct(*variant, *case, args, span);
        }

        let arg_tys: Vec<Ty> = args.iter().map(|a| self.check_expr(a)).collect();
        let any_arg_never = arg_tys.iter().any(|t| matches!(t, Ty::Never));

        let HirExpr::Function { item, name, .. } = callee else {
            let callee_ty = self.check_expr(callee);
            // Error/Never already trace back to a diagnostic recorded
            // elsewhere (an unresolved name, an unsupported feature, a
            // divergent expression) -- piling "not callable" on top
            // would just be noise about the same underlying problem.
            if !matches!(callee_ty, Ty::Error | Ty::Never) {
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

        // A call is strict in its arguments: every one of them is
        // evaluated before the call itself ever happens, so any
        // argument that never produces a value means the call is never
        // actually reached.
        if any_arg_never { Ty::Never } else { sig.ret }
    }

    /// A bare (uncalled) variant-case reference: only valid when that
    /// case carries no payload, in which case it is itself a complete
    /// value of the variant's type -- `LookupResult.Missing` needs no
    /// call syntax at all, matching a unit case allocating no
    /// fabricated payload.
    fn check_case_ref(&mut self, variant: ItemId, case: usize, span: Span) -> Ty {
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
        self.named_variant_ty(variant)
    }

    fn check_variant_construct(
        &mut self,
        variant: ItemId,
        case: usize,
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
                self.unify_report(
                    payload_ty,
                    arg_ty,
                    span,
                    "payload argument type does not match the case's declared type",
                );
            }
        }

        if any_arg_never {
            Ty::Never
        } else {
            self.named_variant_ty(variant)
        }
    }

    /// `TypeName { field: expr, ... }`. `hir::lower` already resolved
    /// every field name to its declaration index and every field's
    /// presence/duplication (`R0007`-`R0010`); this only needs to check
    /// each field's initializer against its declared type, in source
    /// order, propagating `never` exactly like a record's fields are
    /// evaluated (RFC 0005).
    fn check_record_literal(
        &mut self,
        record: ItemId,
        fields: &[crate::hir::HirFieldInit],
        span: Span,
    ) -> Ty {
        let Some(info) = self.records.get(&record).cloned() else {
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
            let (_, declared_ty) = &info.fields[f.field_index];
            self.unify_report(
                declared_ty,
                &field_ty,
                f.span,
                "the field's initializer does not match its declared type",
            );
        }
        let _ = span;
        if diverged {
            Ty::Never
        } else {
            self.named_record_ty(record)
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
        let Ty::Named(item, _) = &base_ty else {
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
        };
        let Some(info) = self.records.get(item).cloned() else {
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
        match info.fields.iter().find(|(n, _)| *n == name) {
            Some((_, ty)) => ty.clone(),
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
        matches!(resolved, Ty::Named(item, _) if self.records.contains_key(&item) || self.variants.contains_key(&item))
    }

    /// Builds `Ty::Named` for a record item, resolving a display symbol
    /// from the module's type namespace (the same one `resolve_named_type`
    /// already searches) rather than requiring every call site to thread
    /// the record's own `Symbol` through separately.
    fn named_record_ty(&self, record: ItemId) -> Ty {
        let symbol = self
            .type_names
            .iter()
            .find(|(_, id)| **id == record)
            .map(|(name, _)| *name)
            .expect("internal invariant: a resolved record ItemId is always in type_names");
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
        // arity mismatch, an unknown case, ...) already has its own
        // diagnostic; the coverage matrix built from a fabricated
        // stand-in for it can't be trusted to prove exhaustiveness or
        // unreachability, so that analysis -- and its own diagnostics --
        // are skipped entirely rather than risk a misleading cascade.
        let unreachable: Vec<usize> = if any_pattern_invalid {
            Vec::new()
        } else {
            self.check_match_exhaustiveness(&scrutinee_ty, &resolved_patterns, arms, span)
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
    /// diagnostics, returning the indices of unreachable arms (empty if
    /// the budget was exceeded, since nothing it found can be trusted
    /// either).
    fn check_match_exhaustiveness(
        &mut self,
        scrutinee_ty: &Ty,
        resolved_patterns: &[ResolvedPattern],
        arms: &[HirMatchArm],
        span: Span,
    ) -> Vec<usize> {
        let resolved_scrutinee = self.ctx.resolve(scrutinee_ty);
        if matches!(resolved_scrutinee, Ty::Error) {
            return Vec::new();
        }
        let variant_payloads: HashMap<ItemId, Vec<Vec<Ty>>> = self
            .variants
            .iter()
            .map(|(id, info)| (*id, info.cases.iter().map(|(_, p)| p.clone()).collect()))
            .collect();
        let space = VariantSpace {
            payloads: variant_payloads,
        };
        let analysis = exhaustive::analyze_match(&resolved_scrutinee, resolved_patterns, &space);

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
            return Vec::new();
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

        analysis.unreachable
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
        let resolved_scrutinee = self.ctx.resolve(scrutinee_ty);
        match pattern {
            HirPattern::Wildcard { .. } => (ResolvedPattern::Wildcard, true),
            HirPattern::Bind {
                id, local, name, ..
            } => {
                if let Ty::Named(item, _) = &resolved_scrutinee
                    && let Some(info) = self.variants.get(item)
                    && let Some(case_index) = info
                        .cases
                        .iter()
                        .position(|(case_name, payload)| case_name == name && payload.is_empty())
                {
                    self.pattern_case.insert(*id, (*item, case_index));
                    return (
                        ResolvedPattern::Variant {
                            variant: *item,
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
                let Ty::Named(item, _) = &resolved_scrutinee else {
                    if !matches!(resolved_scrutinee, Ty::Error) {
                        self.push_incompatible_pattern(*span, &resolved_scrutinee);
                    }
                    for a in args {
                        self.check_pattern(a, &Ty::Error);
                    }
                    return (ResolvedPattern::Wildcard, false);
                };
                let Some(info) = self.variants.get(item).cloned() else {
                    for a in args {
                        self.check_pattern(a, &Ty::Error);
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
                        self.check_pattern(a, &Ty::Error);
                    }
                    return (ResolvedPattern::Wildcard, false);
                };
                self.pattern_case.insert(*id, (*item, case_index));
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
                    match args.get(i) {
                        Some(a) => {
                            let (resolved, arg_valid) = self.check_pattern(a, payload_ty);
                            valid &= arg_valid;
                            resolved_args.push(resolved);
                        }
                        None => resolved_args.push(ResolvedPattern::Wildcard),
                    }
                }
                for extra in args.iter().skip(payload.len()) {
                    self.check_pattern(extra, &Ty::Error);
                }
                (
                    ResolvedPattern::Variant {
                        variant: *item,
                        case: case_index,
                        args: resolved_args,
                    },
                    valid,
                )
            }
            HirPattern::Int { value, span, .. } => {
                let literal_ty = self.fresh_default(Ty::I64, VarKind::Integer);
                self.unify_report(
                    &resolved_scrutinee,
                    &literal_ty,
                    *span,
                    "pattern does not match the scrutinee's type",
                );
                (ResolvedPattern::Literal(LiteralKey::Int(*value)), true)
            }
            HirPattern::Str { value, span, .. } => {
                self.unify_report(
                    &resolved_scrutinee,
                    &Ty::Str,
                    *span,
                    "pattern does not match the scrutinee's type",
                );
                (
                    ResolvedPattern::Literal(LiteralKey::Str(value.clone())),
                    true,
                )
            }
            HirPattern::Char { value, span, .. } => {
                self.unify_report(
                    &resolved_scrutinee,
                    &Ty::Char,
                    *span,
                    "pattern does not match the scrutinee's type",
                );
                (ResolvedPattern::Literal(LiteralKey::Char(*value)), true)
            }
            HirPattern::Bool { value, span, .. } => {
                self.unify_report(
                    &resolved_scrutinee,
                    &Ty::Bool,
                    *span,
                    "pattern does not match the scrutinee's type",
                );
                (ResolvedPattern::Bool(*value), true)
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
        check_module(&hir, id, &interner)
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
        let result = check_module(&hir, id, &interner);
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
}
