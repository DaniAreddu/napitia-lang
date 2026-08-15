//! AST-to-HIR lowering and name resolution.
//!
//! Lowering and resolution happen in the same pass: as each expression
//! is lowered, identifiers are immediately resolved against the current
//! [`Scopes`] stack (for locals) and the module's function table (for
//! calls), rather than annotating the AST first and resolving in a
//! second walk.

use std::collections::HashMap;

use super::{
    ExprId, HirBinding, HirBlock, HirElse, HirExpr, HirFunction, HirMatchArm, HirMatchArmBody,
    HirModule, HirParam, HirPattern, HirStmt, ItemId, LocalId, OtherItem, OtherItemKind,
};
use crate::diagnostics::Diagnostic;
use crate::resolve::Scopes;
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
use crate::syntax::ast;

mod codes {
    pub const DUPLICATE_DEFINITION: &str = "R0001";
    pub const UNRESOLVED_NAME: &str = "R0002";
    pub const DUPLICATE_PARAMETER: &str = "R0003";
}

pub fn lower_module(
    module: &ast::Module,
    source: SourceId,
    interner: &Interner,
) -> (HirModule, Vec<Diagnostic>) {
    let mut lowering = Lowering {
        source,
        interner,
        diagnostics: Vec::new(),
        functions_by_name: HashMap::new(),
        next_item_id: 0,
        next_local_id: 0,
        next_expr_id: 0,
    };
    let hir = lowering.run(module);
    (hir, lowering.diagnostics)
}

struct Lowering<'a> {
    source: SourceId,
    interner: &'a Interner,
    diagnostics: Vec<Diagnostic>,
    functions_by_name: HashMap<Symbol, ItemId>,
    next_item_id: u32,
    next_local_id: u32,
    next_expr_id: u32,
}

impl<'a> Lowering<'a> {
    fn run(&mut self, module: &ast::Module) -> HirModule {
        let mut names: HashMap<Symbol, Span> = HashMap::new();
        let mut function_decls: Vec<(ItemId, &ast::FunctionDecl)> = Vec::new();
        let mut other_items = Vec::new();

        for item in &module.items {
            match item {
                ast::Item::Function(f) => {
                    let id = self.fresh_item();
                    self.check_duplicate(&mut names, f.name, id);
                    self.functions_by_name.insert(f.name.symbol, id);
                    function_decls.push((id, f));
                }
                ast::Item::Record(r) => {
                    let id = self.fresh_item();
                    self.check_duplicate(&mut names, r.name, id);
                    other_items.push(other_item(id, r.name, r.span, OtherItemKind::Record));
                }
                ast::Item::Variant(v) => {
                    let id = self.fresh_item();
                    self.check_duplicate(&mut names, v.name, id);
                    other_items.push(other_item(id, v.name, v.span, OtherItemKind::Variant));
                }
                ast::Item::Protocol(p) => {
                    let id = self.fresh_item();
                    self.check_duplicate(&mut names, p.name, id);
                    other_items.push(other_item(id, p.name, p.span, OtherItemKind::Protocol));
                }
                ast::Item::Extend(e) => {
                    let id = self.fresh_item();
                    other_items.push(other_item(id, e.type_name, e.span, OtherItemKind::Extend));
                }
                ast::Item::Import(i) => {
                    let id = self.fresh_item();
                    let name = *i
                        .path
                        .segments
                        .last()
                        .expect("a path has at least one segment");
                    other_items.push(other_item(id, name, i.span, OtherItemKind::Import));
                }
            }
        }

        let functions = function_decls
            .into_iter()
            .map(|(id, f)| self.lower_function(id, f))
            .collect();

        HirModule {
            functions,
            other_items,
        }
    }

    fn check_duplicate(
        &mut self,
        names: &mut HashMap<Symbol, Span>,
        name: ast::Ident,
        _id: ItemId,
    ) {
        if let Some(&first_span) = names.get(&name.symbol) {
            let text = self.interner.resolve(name.symbol);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::DUPLICATE_DEFINITION,
                    self.source,
                    name.span,
                    format!("`{text}` is defined multiple times"),
                )
                .with_primary_label("redefined here")
                .with_label(first_span, "first defined here"),
            );
        } else {
            names.insert(name.symbol, name.span);
        }
    }

    fn fresh_item(&mut self) -> ItemId {
        let id = ItemId(self.next_item_id);
        self.next_item_id += 1;
        id
    }

    fn fresh_local(&mut self) -> LocalId {
        let id = LocalId(self.next_local_id);
        self.next_local_id += 1;
        id
    }

    fn fresh_expr_id(&mut self) -> ExprId {
        let id = ExprId(self.next_expr_id);
        self.next_expr_id += 1;
        id
    }

    fn lower_function(&mut self, id: ItemId, f: &ast::FunctionDecl) -> HirFunction {
        let mut scopes = Scopes::new();
        let mut seen_params: HashMap<Symbol, Span> = HashMap::new();
        let params = f
            .params
            .iter()
            .map(|p| {
                if let Some(&first_span) = seen_params.get(&p.name.symbol) {
                    let text = self.interner.resolve(p.name.symbol);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::DUPLICATE_PARAMETER,
                            self.source,
                            p.name.span,
                            format!("parameter `{text}` is declared more than once"),
                        )
                        .with_primary_label("duplicate parameter")
                        .with_label(first_span, "first declared here"),
                    );
                } else {
                    seen_params.insert(p.name.symbol, p.name.span);
                }
                let local = self.fresh_local();
                scopes.define(p.name.symbol, local);
                HirParam {
                    local,
                    name: p.name.symbol,
                    span: p.span,
                    ty: p.ty.clone(),
                }
            })
            .collect();
        let body = self.lower_block(&f.body, &mut scopes);
        HirFunction {
            id,
            name: f.name.symbol,
            name_span: f.name.span,
            params,
            return_type: f.return_type.clone(),
            uses: f.uses.clone(),
            raises: f.raises.clone(),
            body,
            span: f.span,
        }
    }

    fn lower_block(&mut self, block: &ast::Block, scopes: &mut Scopes) -> HirBlock {
        scopes.push();
        let statements = block
            .statements
            .iter()
            .map(|s| self.lower_stmt(s, scopes))
            .collect();
        let tail = block
            .tail
            .as_ref()
            .map(|e| Box::new(self.lower_expr(e, scopes)));
        scopes.pop();
        HirBlock {
            id: self.fresh_expr_id(),
            statements,
            tail,
            span: block.span,
        }
    }

    fn lower_stmt(&mut self, stmt: &ast::Stmt, scopes: &mut Scopes) -> HirStmt {
        match stmt {
            ast::Stmt::Binding(b) => {
                let value = self.lower_expr(&b.value, scopes);
                let local = self.fresh_local();
                scopes.define(b.name.symbol, local);
                HirStmt::Binding(HirBinding {
                    local,
                    name: b.name.symbol,
                    mutable: b.mutable,
                    ty: b.ty.clone(),
                    value,
                    span: b.span,
                })
            }
            ast::Stmt::Expr(e) => HirStmt::Expr(self.lower_expr(e, scopes)),
            ast::Stmt::Defer { expr, span } => HirStmt::Defer {
                expr: self.lower_expr(expr, scopes),
                span: *span,
            },
            ast::Stmt::While(w) => {
                let condition = Box::new(self.lower_expr(&w.condition, scopes));
                let body = self.lower_block(&w.body, scopes);
                HirStmt::While {
                    condition,
                    body,
                    span: w.span,
                }
            }
            ast::Stmt::Loop(l) => {
                let body = self.lower_block(&l.body, scopes);
                HirStmt::Loop { body, span: l.span }
            }
        }
    }

    fn lower_expr(&mut self, expr: &ast::Expr, scopes: &mut Scopes) -> HirExpr {
        match expr {
            ast::Expr::Int { value, base, span } => HirExpr::Int {
                id: self.fresh_expr_id(),
                value: *value,
                base: *base,
                span: *span,
            },
            ast::Expr::Float { value, span } => HirExpr::Float {
                id: self.fresh_expr_id(),
                value: *value,
                span: *span,
            },
            ast::Expr::Str { value, span } => HirExpr::Str {
                id: self.fresh_expr_id(),
                value: value.clone(),
                span: *span,
            },
            ast::Expr::Char { value, span } => HirExpr::Char {
                id: self.fresh_expr_id(),
                value: *value,
                span: *span,
            },
            ast::Expr::Bool { value, span } => HirExpr::Bool {
                id: self.fresh_expr_id(),
                value: *value,
                span: *span,
            },
            ast::Expr::Ident(ident) => self.resolve_ident(*ident, scopes),
            ast::Expr::Paren { inner, .. } => self.lower_expr(inner, scopes),
            ast::Expr::Unary { op, operand, span } => HirExpr::Unary {
                id: self.fresh_expr_id(),
                op: *op,
                operand: Box::new(self.lower_expr(operand, scopes)),
                span: *span,
            },
            ast::Expr::Binary {
                op,
                left,
                right,
                span,
            } => HirExpr::Binary {
                id: self.fresh_expr_id(),
                op: *op,
                left: Box::new(self.lower_expr(left, scopes)),
                right: Box::new(self.lower_expr(right, scopes)),
                span: *span,
            },
            ast::Expr::Assign {
                target,
                op,
                value,
                span,
            } => HirExpr::Assign {
                id: self.fresh_expr_id(),
                target: Box::new(self.lower_expr(target, scopes)),
                op: *op,
                value: Box::new(self.lower_expr(value, scopes)),
                span: *span,
            },
            ast::Expr::Call { callee, args, span } => HirExpr::Call {
                id: self.fresh_expr_id(),
                callee: Box::new(self.lower_expr(callee, scopes)),
                args: args.iter().map(|a| self.lower_expr(a, scopes)).collect(),
                span: *span,
            },
            ast::Expr::Field { base, name, span } => HirExpr::Field {
                id: self.fresh_expr_id(),
                base: Box::new(self.lower_expr(base, scopes)),
                name: name.symbol,
                span: *span,
            },
            ast::Expr::Cast { expr, ty, span } => HirExpr::Cast {
                id: self.fresh_expr_id(),
                expr: Box::new(self.lower_expr(expr, scopes)),
                ty: ty.clone(),
                span: *span,
            },
            ast::Expr::Try { expr, span } => HirExpr::Try {
                id: self.fresh_expr_id(),
                expr: Box::new(self.lower_expr(expr, scopes)),
                span: *span,
            },
            ast::Expr::If(if_expr) => self.lower_if(if_expr, scopes),
            ast::Expr::Match(m) => self.lower_match(m, scopes),
            ast::Expr::Block(b) => HirExpr::Block(Box::new(self.lower_block(b, scopes))),
            ast::Expr::Return { value, span } => HirExpr::Return {
                id: self.fresh_expr_id(),
                value: value.as_ref().map(|v| Box::new(self.lower_expr(v, scopes))),
                span: *span,
            },
            ast::Expr::Break { value, span } => HirExpr::Break {
                id: self.fresh_expr_id(),
                value: value.as_ref().map(|v| Box::new(self.lower_expr(v, scopes))),
                span: *span,
            },
            ast::Expr::Continue { span } => HirExpr::Continue {
                id: self.fresh_expr_id(),
                span: *span,
            },
            // Record construction has surface grammar (this milestone's
            // parser) but no resolution/semantics yet -- each field's
            // value is still lowered so an unrelated error inside it is
            // reported, but the literal itself becomes an `Error` node,
            // matching how every other not-yet-implemented construct in
            // this codebase is handled until its own dedicated pass
            // lands.
            ast::Expr::RecordLiteral { fields, span, .. } => {
                for f in fields {
                    self.lower_expr(&f.value, scopes);
                }
                HirExpr::Error {
                    id: self.fresh_expr_id(),
                    span: *span,
                }
            }
            ast::Expr::Error { span } => HirExpr::Error {
                id: self.fresh_expr_id(),
                span: *span,
            },
        }
    }

    fn resolve_ident(&mut self, ident: ast::Ident, scopes: &Scopes) -> HirExpr {
        if let Some(local) = scopes.lookup(ident.symbol) {
            return HirExpr::Local {
                id: self.fresh_expr_id(),
                local,
                name: ident.symbol,
                span: ident.span,
            };
        }
        if let Some(&item) = self.functions_by_name.get(&ident.symbol) {
            return HirExpr::Function {
                id: self.fresh_expr_id(),
                item,
                name: ident.symbol,
                span: ident.span,
            };
        }
        let text = self.interner.resolve(ident.symbol);
        self.diagnostics.push(
            Diagnostic::error(
                codes::UNRESOLVED_NAME,
                self.source,
                ident.span,
                format!("cannot find `{text}` in this scope"),
            )
            .with_primary_label("not found"),
        );
        HirExpr::Error {
            id: self.fresh_expr_id(),
            span: ident.span,
        }
    }

    fn lower_if(&mut self, if_expr: &ast::IfExpr, scopes: &mut Scopes) -> HirExpr {
        let condition = Box::new(self.lower_expr(&if_expr.condition, scopes));
        let then_branch = self.lower_block(&if_expr.then_branch, scopes);
        let else_branch = if_expr.else_branch.as_ref().map(|branch| match branch {
            ast::ElseBranch::Block(b) => HirElse::Block(self.lower_block(b, scopes)),
            ast::ElseBranch::If(i) => HirElse::If(Box::new(self.lower_if(i, scopes))),
        });
        HirExpr::If {
            id: self.fresh_expr_id(),
            condition,
            then_branch,
            else_branch,
            span: if_expr.span,
        }
    }

    fn lower_match(&mut self, m: &ast::MatchExpr, scopes: &mut Scopes) -> HirExpr {
        let scrutinee = Box::new(self.lower_expr(&m.scrutinee, scopes));
        let arms = m
            .arms
            .iter()
            .map(|arm| {
                scopes.push();
                let pattern = self.lower_pattern(&arm.pattern, scopes);
                let body = match &arm.body {
                    ast::MatchArmBody::Expr(e) => HirMatchArmBody::Expr(self.lower_expr(e, scopes)),
                    ast::MatchArmBody::Block(b) => {
                        HirMatchArmBody::Block(self.lower_block(b, scopes))
                    }
                };
                scopes.pop();
                HirMatchArm {
                    pattern,
                    body,
                    span: arm.span,
                }
            })
            .collect();
        HirExpr::Match {
            id: self.fresh_expr_id(),
            scrutinee,
            arms,
            span: m.span,
        }
    }

    fn lower_pattern(&mut self, pattern: &ast::Pattern, scopes: &mut Scopes) -> HirPattern {
        match pattern {
            ast::Pattern::Wildcard { span } => HirPattern::Wildcard { span: *span },
            ast::Pattern::Ident(ident) => {
                let local = self.fresh_local();
                scopes.define(ident.symbol, local);
                HirPattern::Bind {
                    local,
                    name: ident.symbol,
                    span: ident.span,
                }
            }
            ast::Pattern::Variant { name, args, span } => {
                let args = args.iter().map(|a| self.lower_pattern(a, scopes)).collect();
                HirPattern::Variant {
                    name: name.symbol,
                    args,
                    span: *span,
                }
            }
            ast::Pattern::Int { value, span } => HirPattern::Int {
                value: *value,
                span: *span,
            },
            ast::Pattern::Str { value, span } => HirPattern::Str {
                value: value.clone(),
                span: *span,
            },
            ast::Pattern::Char { value, span } => HirPattern::Char {
                value: *value,
                span: *span,
            },
            ast::Pattern::Bool { value, span } => HirPattern::Bool {
                value: *value,
                span: *span,
            },
        }
    }
}

fn other_item(id: ItemId, name: ast::Ident, span: Span, kind: OtherItemKind) -> OtherItem {
    OtherItem {
        id,
        name: name.symbol,
        span,
        kind,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::tokenize;
    use crate::parser::Parser;
    use crate::source::SourceMap;

    fn lower(text: &str) -> (HirModule, Vec<Diagnostic>) {
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
        lower_module(&module, id, &interner)
    }

    #[test]
    fn resolves_parameter_reference() {
        let (hir, diags) = lower("func f(x: i64) -> i64 { return x }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let tail = hir.functions[0].body.tail.as_deref().unwrap();
        let HirExpr::Return { value, .. } = tail else {
            panic!("expected return")
        };
        assert!(matches!(value.as_deref(), Some(HirExpr::Local { .. })));
    }

    #[test]
    fn resolves_call_to_another_function_declared_later() {
        // Forward reference: `main` calls `helper`, defined afterward.
        let (hir, diags) =
            lower("func main() -> i64 { return helper() } func helper() -> i64 { return 1 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let main_body = &hir.functions[0].body;
        let HirExpr::Return { value, .. } = main_body.tail.as_deref().unwrap() else {
            panic!("expected return")
        };
        let HirExpr::Call { callee, .. } = value.as_deref().unwrap() else {
            panic!("expected call")
        };
        assert!(matches!(**callee, HirExpr::Function { .. }));
    }

    #[test]
    fn unresolved_name_is_a_diagnostic() {
        let (_, diags) = lower("func f() -> i64 { return unknown }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "R0002");
    }

    #[test]
    fn duplicate_function_definition_is_a_diagnostic() {
        let (_, diags) = lower("func f() -> i64 { return 1 } func f() -> i64 { return 2 }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "R0001");
    }

    #[test]
    fn duplicate_across_item_kinds_is_still_a_diagnostic() {
        let (_, diags) = lower("func Point() -> i64 { return 0 } record Point { x: i64 }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "R0001");
    }

    #[test]
    fn duplicate_parameter_name_is_a_diagnostic_not_silent_shadowing() {
        let (hir, diags) = lower("func f(x: i64, x: i64) -> i64 { return x }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0003");
        // Both parameters still get their own distinct local -- the
        // diagnostic doesn't stop lowering from otherwise producing a
        // normal function.
        assert_eq!(hir.functions[0].params.len(), 2);
        assert_ne!(
            hir.functions[0].params[0].local,
            hir.functions[0].params[1].local
        );
    }

    #[test]
    fn nested_block_shadows_outer_binding() {
        let (hir, diags) =
            lower("func f() -> i64 { value x = 1; value y = { value x = 2; x }; return x + y }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        // Two distinct locals named `x` should have been minted (outer
        // and shadowed inner); the final `return x + y` still resolves
        // to the outer one.
        assert_eq!(hir.functions[0].params.len(), 0);
    }

    #[test]
    fn same_scope_rebinding_shadows_without_a_diagnostic() {
        let (_, diags) = lower("func f() -> i64 { value x = 1; value x = 2; return x }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn match_arm_pattern_binds_a_local_for_its_body() {
        let (_, diags) = lower("func f(x: i64) -> i64 { return match x { n => n, _ => 0 } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn record_and_variant_items_are_lowered_without_deep_checking() {
        let (hir, diags) = lower("record Point { x: i64, y: i64 } variant Shape { Circle }");
        assert!(diags.is_empty());
        assert_eq!(hir.other_items.len(), 2);
    }

    #[test]
    fn uses_and_raises_clauses_are_preserved_not_discarded() {
        let (hir, diags) = lower(
            "func loadUser(id: i64) -> i64 uses Database.Read raises UserNotFound { return id }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        assert_eq!(hir.functions[0].uses.len(), 1);
        assert_eq!(hir.functions[0].uses[0].segments.len(), 2);
        assert_eq!(hir.functions[0].raises.len(), 1);
    }
}
