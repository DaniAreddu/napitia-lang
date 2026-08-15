//! AST-to-HIR lowering and name resolution.
//!
//! Lowering and resolution happen in the same pass: as each expression
//! is lowered, identifiers are immediately resolved against the current
//! [`Scopes`] stack (for locals), the module's function table (for
//! calls), and the module's type/field/case namespaces (for record
//! construction and variant constructors), rather than annotating the
//! AST first and resolving in a second walk.

use std::collections::HashMap;

use super::{
    ExprId, HirBinding, HirBlock, HirCase, HirElse, HirExpr, HirField, HirFieldInit, HirFunction,
    HirMatchArm, HirMatchArmBody, HirModule, HirParam, HirPattern, HirRecord, HirStmt, HirVariant,
    ItemId, LocalId, OtherItem, OtherItemKind, PatternId,
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
    pub const DUPLICATE_FIELD_DECL: &str = "R0004";
    pub const DUPLICATE_CASE_DECL: &str = "R0005";
    pub const AMBIGUOUS_CONSTRUCTOR: &str = "R0006";
    pub const UNKNOWN_RECORD_TYPE: &str = "R0007";
    pub const UNKNOWN_FIELD_IN_CONSTRUCTION: &str = "R0008";
    pub const MISSING_FIELD: &str = "R0009";
    pub const DUPLICATE_FIELD_INIT: &str = "R0010";
    pub const UNKNOWN_VARIANT_TYPE: &str = "R0011";
    pub const UNKNOWN_VARIANT_CASE: &str = "R0012";
    pub const WRONG_VARIANT: &str = "R0013";
    pub const DUPLICATE_PATTERN_BINDING: &str = "R0014";
}

/// Which kind of item a name in the type namespace refers to -- needed
/// to tell "unknown record type" (named a variant, or nothing) apart
/// from "unknown variant type" (named a record, or nothing) with an
/// accurate diagnostic either way.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum TypeNameKind {
    Record,
    Variant,
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
        type_names: HashMap::new(),
        record_fields: HashMap::new(),
        variant_cases: HashMap::new(),
        case_lookup: HashMap::new(),
        next_item_id: 0,
        next_local_id: 0,
        next_expr_id: 0,
        next_pattern_id: 0,
    };
    let hir = lowering.run(module);
    (hir, lowering.diagnostics)
}

struct Lowering<'a> {
    source: SourceId,
    interner: &'a Interner,
    diagnostics: Vec<Diagnostic>,
    functions_by_name: HashMap<Symbol, ItemId>,
    /// The module's type namespace: every declared `record`/`variant`
    /// name (primitives live entirely in `typeck`/`nir::lower`'s own
    /// copy of this concept, since they need no `ItemId`).
    type_names: HashMap<Symbol, (ItemId, TypeNameKind)>,
    /// Per-record field name -> declaration index, for resolving a
    /// record literal's field initializers.
    record_fields: HashMap<ItemId, HashMap<Symbol, usize>>,
    /// Per-variant case name -> declaration index, for resolving a
    /// qualified (`Variant.Case`) or scrutinee-typed pattern reference.
    variant_cases: HashMap<ItemId, HashMap<Symbol, usize>>,
    /// Case name -> every `(variant, case index)` it names anywhere in
    /// the module, for resolving an *unqualified* constructor reference
    /// and detecting ambiguity when it names more than one variant.
    case_lookup: HashMap<Symbol, Vec<(ItemId, usize)>>,
    next_item_id: u32,
    next_local_id: u32,
    next_expr_id: u32,
    next_pattern_id: u32,
}

impl<'a> Lowering<'a> {
    fn run(&mut self, module: &ast::Module) -> HirModule {
        let mut names: HashMap<Symbol, Span> = HashMap::new();
        let mut function_decls: Vec<(ItemId, &ast::FunctionDecl)> = Vec::new();
        let mut record_decls: Vec<(ItemId, &ast::RecordDecl)> = Vec::new();
        let mut variant_decls: Vec<(ItemId, &ast::VariantDecl)> = Vec::new();
        let mut other_items = Vec::new();

        // First pass: mint every item's `ItemId` and populate the
        // module-wide namespaces (functions, types, fields, cases)
        // *before* lowering any function body or record/variant
        // internals -- a forward reference (a field typed with a
        // record declared later, a function calling one declared
        // later) must resolve exactly like Alpha 0.1's existing
        // forward-referenced function calls already do.
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
                    self.type_names
                        .insert(r.name.symbol, (id, TypeNameKind::Record));
                    record_decls.push((id, r));
                }
                ast::Item::Variant(v) => {
                    let id = self.fresh_item();
                    self.check_duplicate(&mut names, v.name, id);
                    self.type_names
                        .insert(v.name.symbol, (id, TypeNameKind::Variant));
                    variant_decls.push((id, v));
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

        let records: Vec<HirRecord> = record_decls
            .into_iter()
            .map(|(id, r)| self.lower_record(id, r))
            .collect();
        let variants: Vec<HirVariant> = variant_decls
            .into_iter()
            .map(|(id, v)| self.lower_variant(id, v))
            .collect();
        let functions = function_decls
            .into_iter()
            .map(|(id, f)| self.lower_function(id, f))
            .collect();

        HirModule {
            functions,
            records,
            variants,
            other_items,
        }
    }

    fn lower_record(&mut self, id: ItemId, r: &ast::RecordDecl) -> HirRecord {
        let mut seen: HashMap<Symbol, usize> = HashMap::new();
        let mut fields = Vec::new();
        for field in &r.fields {
            if let Some(&first_index) = seen.get(&field.name.symbol) {
                let text = self.interner.resolve(field.name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::DUPLICATE_FIELD_DECL,
                        self.source,
                        field.name.span,
                        format!("field `{text}` is declared more than once"),
                    )
                    .with_primary_label("duplicate field")
                    .with_label(r.fields[first_index].name.span, "first declared here"),
                );
                continue;
            }
            seen.insert(field.name.symbol, fields.len());
            fields.push(HirField {
                name: field.name.symbol,
                span: field.span,
                ty: field.ty.clone(),
            });
        }
        self.record_fields.insert(id, seen);
        HirRecord {
            id,
            name: r.name.symbol,
            span: r.span,
            fields,
        }
    }

    fn lower_variant(&mut self, id: ItemId, v: &ast::VariantDecl) -> HirVariant {
        let mut seen: HashMap<Symbol, usize> = HashMap::new();
        let mut cases = Vec::new();
        for case in &v.cases {
            if let Some(&first_index) = seen.get(&case.name.symbol) {
                let text = self.interner.resolve(case.name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::DUPLICATE_CASE_DECL,
                        self.source,
                        case.name.span,
                        format!("case `{text}` is declared more than once"),
                    )
                    .with_primary_label("duplicate case")
                    .with_label(v.cases[first_index].name.span, "first declared here"),
                );
                continue;
            }
            let index = cases.len();
            seen.insert(case.name.symbol, index);
            self.case_lookup
                .entry(case.name.symbol)
                .or_default()
                .push((id, index));
            cases.push(HirCase {
                name: case.name.symbol,
                span: case.span,
                payload: case.payload.clone(),
            });
        }
        self.variant_cases.insert(id, seen);
        HirVariant {
            id,
            name: v.name.symbol,
            span: v.span,
            cases,
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

    fn fresh_pattern_id(&mut self) -> PatternId {
        let id = PatternId(self.next_pattern_id);
        self.next_pattern_id += 1;
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
            ast::Expr::Field { base, name, span } => self.lower_field(base, *name, *span, scopes),
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
            ast::Expr::RecordLiteral {
                type_name,
                fields,
                span,
            } => self.lower_record_literal(*type_name, fields, *span, scopes),
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
        // Not a local or a function: an unqualified reference to a
        // variant case constructor is accepted when its name is
        // unambiguous across every declared variant in the module (see
        // RFC 0005's "Namespaces" section).
        if let Some(candidates) = self.case_lookup.get(&ident.symbol) {
            return self.resolve_case_candidates(ident, candidates.clone());
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

    fn resolve_case_candidates(
        &mut self,
        ident: ast::Ident,
        candidates: Vec<(ItemId, usize)>,
    ) -> HirExpr {
        if candidates.len() > 1 {
            let text = self.interner.resolve(ident.symbol);
            let variant_names: Vec<&str> = candidates
                .iter()
                .map(|(variant, _)| self.variant_name(*variant))
                .collect();
            self.diagnostics.push(
                Diagnostic::error(
                    codes::AMBIGUOUS_CONSTRUCTOR,
                    self.source,
                    ident.span,
                    format!(
                        "`{text}` is ambiguous: it names a case in more than one variant ({}); \
                         use a qualified path (`Variant.{text}`)",
                        variant_names.join(", ")
                    ),
                )
                .with_primary_label("ambiguous constructor"),
            );
            return HirExpr::Error {
                id: self.fresh_expr_id(),
                span: ident.span,
            };
        }
        let (variant, case) = candidates[0];
        HirExpr::CaseRef {
            id: self.fresh_expr_id(),
            variant,
            case,
            name: ident.symbol,
            span: ident.span,
        }
    }

    /// Looks up a declared item's name for use inside another
    /// diagnostic's message; every `ItemId` reaching this function came
    /// from this module's own `type_names`/`case_lookup` tables, so the
    /// name is always present.
    fn variant_name(&self, item: ItemId) -> &'a str {
        let symbol = self
            .type_names
            .iter()
            .find(|(_, (id, kind))| *id == item && *kind == TypeNameKind::Variant)
            .map(|(name, _)| *name)
            .expect("internal invariant: every case_lookup entry names a known variant");
        self.interner.resolve(symbol)
    }

    /// Lowers `base.name`, distinguishing three shapes: ordinary field
    /// access on a value, a qualified variant constructor
    /// (`Variant.Case`), and a qualified reference into a record's
    /// namespace (rejected -- records have no "cases").
    fn lower_field(
        &mut self,
        base: &ast::Expr,
        name: ast::Ident,
        span: Span,
        scopes: &mut Scopes,
    ) -> HirExpr {
        if let ast::Expr::Ident(base_ident) = base
            && scopes.lookup(base_ident.symbol).is_none()
            && !self.functions_by_name.contains_key(&base_ident.symbol)
            && let Some(&(item, kind)) = self.type_names.get(&base_ident.symbol)
        {
            return match kind {
                TypeNameKind::Variant => self.resolve_qualified_case(item, *base_ident, name),
                TypeNameKind::Record => {
                    let base_text = self.interner.resolve(base_ident.symbol);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::UNKNOWN_VARIANT_TYPE,
                            self.source,
                            base_ident.span,
                            format!("`{base_text}` is a record, which has no cases to qualify"),
                        )
                        .with_primary_label("not a variant type"),
                    );
                    HirExpr::Error {
                        id: self.fresh_expr_id(),
                        span,
                    }
                }
            };
        }
        HirExpr::Field {
            id: self.fresh_expr_id(),
            base: Box::new(self.lower_expr(base, scopes)),
            name: name.symbol,
            span,
        }
    }

    fn resolve_qualified_case(
        &mut self,
        variant: ItemId,
        base_ident: ast::Ident,
        case_name: ast::Ident,
    ) -> HirExpr {
        let span = base_ident.span.join(case_name.span);
        if let Some(&index) = self
            .variant_cases
            .get(&variant)
            .and_then(|cases| cases.get(&case_name.symbol))
        {
            return HirExpr::CaseRef {
                id: self.fresh_expr_id(),
                variant,
                case: index,
                name: case_name.symbol,
                span,
            };
        }
        let case_text = self.interner.resolve(case_name.symbol);
        let variant_text = self.interner.resolve(base_ident.symbol);
        if let Some(elsewhere) = self.case_lookup.get(&case_name.symbol) {
            let owner = elsewhere
                .iter()
                .find(|(v, _)| *v != variant)
                .map(|(v, _)| self.variant_name(*v));
            if let Some(owner_name) = owner {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::WRONG_VARIANT,
                        self.source,
                        case_name.span,
                        format!(
                            "`{case_text}` is a case of variant `{owner_name}`, not `{variant_text}`"
                        ),
                    )
                    .with_primary_label("wrong variant"),
                );
                return HirExpr::Error {
                    id: self.fresh_expr_id(),
                    span,
                };
            }
        }
        self.diagnostics.push(
            Diagnostic::error(
                codes::UNKNOWN_VARIANT_CASE,
                self.source,
                case_name.span,
                format!("variant `{variant_text}` has no case named `{case_text}`"),
            )
            .with_primary_label("unknown case"),
        );
        HirExpr::Error {
            id: self.fresh_expr_id(),
            span,
        }
    }

    fn lower_record_literal(
        &mut self,
        type_name: ast::Ident,
        fields: &[ast::FieldInit],
        span: Span,
        scopes: &mut Scopes,
    ) -> HirExpr {
        let record = match self.type_names.get(&type_name.symbol) {
            Some(&(item, TypeNameKind::Record)) => item,
            Some(&(_, TypeNameKind::Variant)) => {
                let text = self.interner.resolve(type_name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::UNKNOWN_RECORD_TYPE,
                        self.source,
                        type_name.span,
                        format!("`{text}` is a variant, which is constructed with `.Case(...)`, not `{{ ... }}`"),
                    )
                    .with_primary_label("not a record type"),
                );
                // Still lower every field's value expression, for
                // cascading diagnostics, before giving up.
                for f in fields {
                    self.lower_expr(&f.value, scopes);
                }
                return HirExpr::Error {
                    id: self.fresh_expr_id(),
                    span,
                };
            }
            None => {
                let text = self.interner.resolve(type_name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::UNKNOWN_RECORD_TYPE,
                        self.source,
                        type_name.span,
                        format!("cannot find record type `{text}` in this scope"),
                    )
                    .with_primary_label("unknown record type"),
                );
                for f in fields {
                    self.lower_expr(&f.value, scopes);
                }
                return HirExpr::Error {
                    id: self.fresh_expr_id(),
                    span,
                };
            }
        };

        let field_indices = self.record_fields.get(&record).cloned().unwrap_or_default();
        let mut seen: HashMap<Symbol, Span> = HashMap::new();
        let mut resolved = Vec::with_capacity(fields.len());
        for f in fields {
            let value = self.lower_expr(&f.value, scopes);
            if let Some(&first_span) = seen.get(&f.name.symbol) {
                let text = self.interner.resolve(f.name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::DUPLICATE_FIELD_INIT,
                        self.source,
                        f.name.span,
                        format!("field `{text}` is initialized more than once"),
                    )
                    .with_primary_label("duplicate initializer")
                    .with_label(first_span, "first initialized here"),
                );
                continue;
            }
            seen.insert(f.name.symbol, f.name.span);
            match field_indices.get(&f.name.symbol) {
                Some(&field_index) => resolved.push(HirFieldInit {
                    field_index,
                    value,
                    span: f.span,
                }),
                None => {
                    let text = self.interner.resolve(f.name.symbol);
                    let record_text = self.interner.resolve(type_name.symbol);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::UNKNOWN_FIELD_IN_CONSTRUCTION,
                            self.source,
                            f.name.span,
                            format!("record `{record_text}` has no field named `{text}`"),
                        )
                        .with_primary_label("unknown field"),
                    );
                }
            }
        }

        // `field_indices` is a `HashMap`, whose iteration order is not
        // itself meaningful -- but its value *is* each field's
        // declaration index, so sorting by that recovers exact
        // declaration order without needing a separately-threaded
        // ordered field list. Diagnostic text must never depend on
        // HashMap iteration order: it is not deterministic across runs.
        let mut missing: Vec<(usize, &str)> = field_indices
            .iter()
            .filter(|(name, _)| !seen.contains_key(*name))
            .map(|(name, &index)| (index, self.interner.resolve(*name)))
            .collect();
        missing.sort_by_key(|(index, _)| *index);
        let missing: Vec<&str> = missing.into_iter().map(|(_, name)| name).collect();
        if !missing.is_empty() {
            let record_text = self.interner.resolve(type_name.symbol);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::MISSING_FIELD,
                    self.source,
                    span,
                    format!(
                        "missing field(s) in construction of `{record_text}`: {}",
                        missing.join(", ")
                    ),
                )
                .with_primary_label("missing field(s)"),
            );
        }

        HirExpr::RecordLiteral {
            id: self.fresh_expr_id(),
            record,
            fields: resolved,
            span,
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
                let mut bound: HashMap<Symbol, Span> = HashMap::new();
                let pattern = self.lower_pattern(&arm.pattern, scopes, &mut bound);
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

    /// Lowers one pattern, minting a fresh [`PatternId`] and detecting a
    /// name bound more than once within the *same* pattern tree (`bound`
    /// is reset per-arm by the caller, and threaded through recursive
    /// calls into `Variant` sub-patterns so `Found(user, user)` is
    /// caught across positions, not just siblings at the same level).
    fn lower_pattern(
        &mut self,
        pattern: &ast::Pattern,
        scopes: &mut Scopes,
        bound: &mut HashMap<Symbol, Span>,
    ) -> HirPattern {
        match pattern {
            ast::Pattern::Wildcard { span } => HirPattern::Wildcard {
                id: self.fresh_pattern_id(),
                span: *span,
            },
            ast::Pattern::Ident(ident) => {
                if let Some(&first_span) = bound.get(&ident.symbol) {
                    let text = self.interner.resolve(ident.symbol);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::DUPLICATE_PATTERN_BINDING,
                            self.source,
                            ident.span,
                            format!("`{text}` is bound more than once in this pattern"),
                        )
                        .with_primary_label("duplicate binding")
                        .with_label(first_span, "first bound here"),
                    );
                } else {
                    bound.insert(ident.symbol, ident.span);
                }
                let local = self.fresh_local();
                scopes.define(ident.symbol, local);
                HirPattern::Bind {
                    id: self.fresh_pattern_id(),
                    local,
                    name: ident.symbol,
                    span: ident.span,
                }
            }
            ast::Pattern::Variant { name, args, span } => {
                let args = args
                    .iter()
                    .map(|a| self.lower_pattern(a, scopes, bound))
                    .collect();
                HirPattern::Variant {
                    id: self.fresh_pattern_id(),
                    name: name.symbol,
                    args,
                    span: *span,
                }
            }
            ast::Pattern::Int { value, span } => HirPattern::Int {
                id: self.fresh_pattern_id(),
                value: *value,
                span: *span,
            },
            ast::Pattern::Str { value, span } => HirPattern::Str {
                id: self.fresh_pattern_id(),
                value: value.clone(),
                span: *span,
            },
            ast::Pattern::Char { value, span } => HirPattern::Char {
                id: self.fresh_pattern_id(),
                value: *value,
                span: *span,
            },
            ast::Pattern::Bool { value, span } => HirPattern::Bool {
                id: self.fresh_pattern_id(),
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
    fn a_pattern_binding_does_not_leak_into_another_arm() {
        // `v`, bound in the first arm's pattern, must not be visible in
        // the second arm's body -- each arm gets its own scope.
        let (_, diags) = lower(
            "variant Shape { Circle(i64), Empty } \
             func f(s: Shape) -> i64 { return match s { Circle(v) => v, Empty => v } }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0002");
    }

    #[test]
    fn record_and_variant_items_are_lowered_with_their_full_structure() {
        let (hir, diags) = lower("record Point { x: i64, y: i64 } variant Shape { Circle }");
        assert!(diags.is_empty());
        assert_eq!(hir.records.len(), 1);
        assert_eq!(hir.records[0].fields.len(), 2);
        assert_eq!(hir.variants.len(), 1);
        assert_eq!(hir.variants[0].cases.len(), 1);
        assert!(hir.other_items.is_empty());
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

    #[test]
    fn duplicate_record_field_declaration_is_a_diagnostic() {
        let (hir, diags) = lower("record Point { x: i64, x: i64 }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0004");
        assert_eq!(hir.records[0].fields.len(), 1);
    }

    #[test]
    fn duplicate_variant_case_declaration_is_a_diagnostic() {
        let (hir, diags) = lower("variant Shape { Circle, Circle }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0005");
        assert_eq!(hir.variants[0].cases.len(), 1);
    }

    #[test]
    fn record_literal_resolves_fields_to_declaration_indices() {
        let (hir, diags) = lower(
            "record Point { x: i64, y: i64 } \
             func f() -> i64 { value p = Point { y: 2, x: 1 }; return 0 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let HirStmt::Binding(binding) = &hir.functions[0].body.statements[0] else {
            panic!("expected binding")
        };
        let HirExpr::RecordLiteral { fields, .. } = &binding.value else {
            panic!("expected record literal")
        };
        // Written in source order (y, then x), each resolved to its
        // declaration index (y=1, x=0).
        assert_eq!(fields[0].field_index, 1);
        assert_eq!(fields[1].field_index, 0);
    }

    #[test]
    fn unknown_record_type_is_a_diagnostic() {
        let (_, diags) = lower("func f() { value p = Banana { x: 1 }; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0007");
    }

    #[test]
    fn unknown_field_in_construction_is_a_diagnostic() {
        let (_, diags) =
            lower("record Point { x: i64 } func f() { value p = Point { x: 1, z: 2 }; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0008");
    }

    #[test]
    fn missing_field_in_construction_is_a_diagnostic() {
        let (_, diags) =
            lower("record Point { x: i64, y: i64 } func f() { value p = Point { x: 1 }; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0009");
    }

    #[test]
    fn missing_fields_are_reported_in_declaration_order() {
        // Three missing fields, named so alphabetical/insertion order
        // would disagree with declaration order if either leaked
        // through: declaration order is z, a, m.
        let record = "record Point { z: i64, a: i64, m: i64, x: i64 } ";
        let ctor = "func f() { value p = Point { x: 1 }; }";
        let (_, diags) = lower(&format!("{record}{ctor}"));
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0009");
        assert!(
            diags[0].message.contains("z, a, m"),
            "expected declaration-order field list, got: {}",
            diags[0].message
        );
    }

    #[test]
    fn missing_field_diagnostic_text_is_identical_across_repeated_runs() {
        let text = "record Point { z: i64, a: i64, m: i64, x: i64 } \
                    func f() { value p = Point { x: 1 }; }";
        let first = lower(text).1[0].message.clone();
        for _ in 0..10 {
            let (_, diags) = lower(text);
            assert_eq!(diags[0].message, first);
        }
    }

    #[test]
    fn missing_field_order_is_declaration_order_not_construction_site_order() {
        // The construction site never mentions any of the missing
        // fields, so its own (empty) order can't influence anything;
        // this instead confirms that field declaration order -- not
        // HashMap iteration order, which this test's field names are
        // chosen to disagree with alphabetically -- is what's reported.
        let record = "record Point { z: i64, a: i64, m: i64 } ";
        let ctor = "func f() { value p = Point {}; }";
        let (_, diags) = lower(&format!("{record}{ctor}"));
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert!(
            diags[0].message.contains("z, a, m"),
            "expected declaration-order field list, got: {}",
            diags[0].message
        );
    }

    #[test]
    fn duplicate_field_initializer_is_a_diagnostic() {
        let (_, diags) =
            lower("record Point { x: i64 } func f() { value p = Point { x: 1, x: 2 }; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0010");
    }

    #[test]
    fn qualified_variant_constructor_resolves_to_a_case_ref() {
        let (hir, diags) = lower(
            "variant Shape { Circle(i64), Empty } \
             func f() -> i64 { value s = Shape.Circle(1); return 0 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let HirStmt::Binding(binding) = &hir.functions[0].body.statements[0] else {
            panic!("expected binding")
        };
        let HirExpr::Call { callee, args, .. } = &binding.value else {
            panic!("expected call")
        };
        assert!(matches!(**callee, HirExpr::CaseRef { case: 0, .. }));
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn qualified_unit_case_resolves_without_a_call() {
        let (hir, diags) = lower(
            "variant Shape { Circle(i64), Empty } \
             func f() -> i64 { value s = Shape.Empty; return 0 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let HirStmt::Binding(binding) = &hir.functions[0].body.statements[0] else {
            panic!("expected binding")
        };
        assert!(matches!(binding.value, HirExpr::CaseRef { case: 1, .. }));
    }

    #[test]
    fn unqualified_unambiguous_constructor_resolves() {
        let (hir, diags) = lower(
            "variant Shape { Circle(i64), Empty } \
             func f() -> i64 { value s = Circle(1); return 0 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let HirStmt::Binding(binding) = &hir.functions[0].body.statements[0] else {
            panic!("expected binding")
        };
        let HirExpr::Call { callee, .. } = &binding.value else {
            panic!("expected call")
        };
        assert!(matches!(**callee, HirExpr::CaseRef { .. }));
    }

    #[test]
    fn ambiguous_unqualified_constructor_is_a_diagnostic() {
        let (_, diags) = lower(
            "variant A { Found(i64) } variant B { Found(i64) } \
             func f() -> i64 { value s = Found(1); return 0 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0006");
    }

    #[test]
    fn qualified_unknown_case_is_a_diagnostic() {
        let (_, diags) = lower(
            "variant Shape { Circle(i64) } \
             func f() -> i64 { value s = Shape.Square; return 0 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0012");
    }

    #[test]
    fn qualified_case_from_a_different_variant_is_a_diagnostic() {
        let (_, diags) = lower(
            "variant A { Found(i64) } variant B { Missing } \
             func f() -> i64 { value s = B.Found; return 0 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0013");
    }

    #[test]
    fn duplicate_pattern_binding_is_a_diagnostic() {
        let (_, diags) = lower(
            "variant Pair { Both(i64, i64) } \
             func f(p: Pair) -> i64 { return match p { Both(a, a) => a } }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0014");
    }

    #[test]
    fn record_name_still_lowers_cleanly_when_used_as_a_parameter_type() {
        // Regression: pulling record/variant metadata out of
        // `other_items` must not break the item's own name/id still
        // being usable in a type position downstream (typeck rebuilds
        // its own type namespace from `hir.records`/`hir.variants`).
        let (hir, diags) = lower("record Point { x: i64 } func f(p: Point) -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        assert_eq!(hir.records.len(), 1);
        assert_eq!(hir.functions[0].params.len(), 1);
    }
}
