//! Item, statement, and declaration parsing.

use super::{Parser, recovery};
use crate::lexer::TokenKind;
use crate::syntax::ast::{
    Block, Case, Expr, ExtendDecl, Field, FunctionDecl, Ident, ImportDecl, Item, LoopStmt, Param,
    Path, ProtocolDecl, ProtocolMember, RecordDecl, Stmt, Type, VariantDecl, WhileStmt,
};

/// Whether `expr`'s surface syntax already ends in a `}` (`if`/`match`/
/// a bare block), which makes a trailing `;` after it, as a statement,
/// optional rather than mandatory.
fn ends_with_brace(expr: &Expr) -> bool {
    matches!(expr, Expr::If(_) | Expr::Match(_) | Expr::Block(_))
}

impl<'a> Parser<'a> {
    /// Consumes a leading `public` or `private` visibility modifier, if
    /// present. `private` is npt's default visibility -- writing it
    /// explicitly is accepted (and consumed) rather than left as an
    /// unparsed, reserved-but-useless keyword that would otherwise choke
    /// the parser the moment a program actually used it.
    fn parse_visibility(&mut self) -> bool {
        if self.eat(&TokenKind::Public) {
            true
        } else {
            self.eat(&TokenKind::Private);
            false
        }
    }

    pub(super) fn parse_item(&mut self) -> Option<Item> {
        let public = self.parse_visibility();
        match self.current() {
            TokenKind::Func => self.parse_function(public).map(Item::Function),
            TokenKind::Record => self.parse_record(public).map(Item::Record),
            TokenKind::Variant => self.parse_variant(public).map(Item::Variant),
            TokenKind::Protocol => self.parse_protocol(public).map(Item::Protocol),
            TokenKind::Extend => self.parse_extend().map(Item::Extend),
            TokenKind::Import => self.parse_import().map(Item::Import),
            _ => {
                self.error_expected("an item (func, record, variant, protocol, extend, or import)");
                None
            }
        }
    }

    fn parse_function(&mut self, public: bool) -> Option<FunctionDecl> {
        let start = self.current_span();
        self.advance(); // 'func'
        let name = self.expect_ident("a function name")?;
        self.expect(&TokenKind::LParen, "`(`")?;
        let params = self.parse_param_list()?;
        self.expect(&TokenKind::RParen, "`)`")?;
        let return_type = if self.eat(&TokenKind::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        let uses = if self.eat(&TokenKind::Uses) {
            self.parse_path_list()?
        } else {
            Vec::new()
        };
        let raises = if self.eat(&TokenKind::Raises) {
            self.parse_ident_list()?
        } else {
            Vec::new()
        };
        let body = self.parse_block();
        let span = start.join(body.span);
        Some(FunctionDecl {
            public,
            name,
            params,
            return_type,
            uses,
            raises,
            body,
            span,
        })
    }

    /// A `func` signature with no body, used inside `protocol` blocks.
    fn parse_protocol_member(&mut self) -> Option<ProtocolMember> {
        let start = self.current_span();
        self.expect(&TokenKind::Func, "`func`")?;
        let name = self.expect_ident("a function name")?;
        self.expect(&TokenKind::LParen, "`(`")?;
        let params = self.parse_param_list()?;
        self.expect(&TokenKind::RParen, "`)`")?;
        let return_type = if self.eat(&TokenKind::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        let end = self
            .expect(&TokenKind::Semi, "`;`")
            .map(|t| t.span)
            .unwrap_or(start);
        Some(ProtocolMember {
            name,
            params,
            return_type,
            span: start.join(end),
        })
    }

    fn parse_param_list(&mut self) -> Option<Vec<Param>> {
        let mut params = Vec::new();
        if self.check(&TokenKind::RParen) {
            return Some(params);
        }
        loop {
            let name = self.expect_ident("a parameter name")?;
            self.expect(&TokenKind::Colon, "`:`")?;
            let ty = self.parse_type()?;
            let span = name.span.join(ty.span());
            params.push(Param { name, ty, span });
            if self.eat(&TokenKind::Comma) {
                if self.check(&TokenKind::RParen) {
                    break;
                }
                continue;
            }
            break;
        }
        Some(params)
    }

    pub(super) fn parse_type(&mut self) -> Option<Type> {
        let name = self.expect_ident("a type name")?;
        Some(Type { name })
    }

    fn parse_path(&mut self) -> Option<Path> {
        let first = self.expect_ident("a name")?;
        let mut span = first.span;
        let mut segments = vec![first];
        while self.check(&TokenKind::Dot) {
            self.advance();
            let seg = self.expect_ident("a path segment")?;
            span = span.join(seg.span);
            segments.push(seg);
        }
        Some(Path { segments, span })
    }

    fn parse_path_list(&mut self) -> Option<Vec<Path>> {
        let mut paths = vec![self.parse_path()?];
        while self.eat(&TokenKind::Comma) {
            paths.push(self.parse_path()?);
        }
        Some(paths)
    }

    fn parse_ident_list(&mut self) -> Option<Vec<Ident>> {
        let mut idents = vec![self.expect_ident("an error name")?];
        while self.eat(&TokenKind::Comma) {
            idents.push(self.expect_ident("an error name")?);
        }
        Some(idents)
    }

    fn parse_record(&mut self, public: bool) -> Option<RecordDecl> {
        let start = self.current_span();
        self.advance(); // 'record'
        let name = self.expect_ident("a record name")?;
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut fields = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let field_public = self.parse_visibility();
            let Some(fname) = self.expect_ident("a field name") else {
                recovery::synchronize_to_stmt(self);
                continue;
            };
            self.expect(&TokenKind::Colon, "`:`");
            let Some(ty) = self.parse_type() else {
                recovery::synchronize_to_stmt(self);
                continue;
            };
            let fspan = fname.span.join(ty.span());
            fields.push(Field {
                public: field_public,
                name: fname,
                ty,
                span: fspan,
            });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        let end = self
            .expect(&TokenKind::RBrace, "`}`")
            .map(|t| t.span)
            .unwrap_or(self.current_span());
        Some(RecordDecl {
            public,
            name,
            fields,
            span: start.join(end),
        })
    }

    fn parse_variant(&mut self, public: bool) -> Option<VariantDecl> {
        let start = self.current_span();
        self.advance(); // 'variant'
        let name = self.expect_ident("a variant name")?;
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut cases = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let Some(cname) = self.expect_ident("a case name") else {
                recovery::synchronize_to_stmt(self);
                continue;
            };
            let mut payload = Vec::new();
            let mut span = cname.span;
            if self.eat(&TokenKind::LParen) {
                if !self.check(&TokenKind::RParen) {
                    loop {
                        if let Some(ty) = self.parse_type() {
                            span = span.join(ty.span());
                            payload.push(ty);
                        }
                        if self.eat(&TokenKind::Comma) {
                            if self.check(&TokenKind::RParen) {
                                break;
                            }
                            continue;
                        }
                        break;
                    }
                }
                if let Some(tok) = self.expect(&TokenKind::RParen, "`)`") {
                    span = span.join(tok.span);
                }
            }
            cases.push(Case {
                name: cname,
                payload,
                span,
            });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        let end = self
            .expect(&TokenKind::RBrace, "`}`")
            .map(|t| t.span)
            .unwrap_or(self.current_span());
        Some(VariantDecl {
            public,
            name,
            cases,
            span: start.join(end),
        })
    }

    fn parse_protocol(&mut self, public: bool) -> Option<ProtocolDecl> {
        let start = self.current_span();
        self.advance(); // 'protocol'
        let name = self.expect_ident("a protocol name")?;
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut members = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let before = self.pos;
            if let Some(member) = self.parse_protocol_member() {
                members.push(member);
            }
            if self.pos == before {
                recovery::synchronize_to_stmt(self);
            }
        }
        let end = self
            .expect(&TokenKind::RBrace, "`}`")
            .map(|t| t.span)
            .unwrap_or(self.current_span());
        Some(ProtocolDecl {
            public,
            name,
            members,
            span: start.join(end),
        })
    }

    fn parse_extend(&mut self) -> Option<ExtendDecl> {
        let start = self.current_span();
        self.advance(); // 'extend'
        let type_name = self.expect_ident("a type name")?;
        let protocol = if self.eat(&TokenKind::With) {
            Some(self.parse_path()?)
        } else {
            None
        };
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut functions = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let before = self.pos;
            if let Some(func) = self.parse_function(false) {
                functions.push(func);
            }
            if self.pos == before {
                recovery::synchronize_to_stmt(self);
            }
        }
        let end = self
            .expect(&TokenKind::RBrace, "`}`")
            .map(|t| t.span)
            .unwrap_or(self.current_span());
        Some(ExtendDecl {
            type_name,
            protocol,
            functions,
            span: start.join(end),
        })
    }

    fn parse_import(&mut self) -> Option<ImportDecl> {
        let start = self.current_span();
        self.advance(); // 'import'
        let path = self.parse_path()?;
        let end = self
            .expect(&TokenKind::Semi, "`;`")
            .map(|t| t.span)
            .unwrap_or(path.span);
        Some(ImportDecl {
            path,
            span: start.join(end),
        })
    }

    pub(super) fn parse_block(&mut self) -> Block {
        let start = self.current_span();
        if !self.eat(&TokenKind::LBrace) {
            self.error_expected("`{`");
            return Block {
                statements: Vec::new(),
                tail: None,
                span: start,
            };
        }

        let mut statements = Vec::new();
        let mut tail = None;
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let before = self.pos;
            match self.parse_statement_or_tail() {
                StmtOrTail::Stmt(stmt) => statements.push(stmt),
                StmtOrTail::Tail(expr) => {
                    tail = Some(Box::new(expr));
                    break;
                }
                StmtOrTail::Recover => recovery::synchronize_to_stmt(self),
            }
            if self.pos == before {
                self.advance();
            }
        }

        let end = self
            .expect(&TokenKind::RBrace, "`}`")
            .map(|t| t.span)
            .unwrap_or(self.current_span());
        Block {
            statements,
            tail,
            span: start.join(end),
        }
    }

    fn parse_statement_or_tail(&mut self) -> StmtOrTail {
        match self.current() {
            TokenKind::Value | TokenKind::Mutable => StmtOrTail::Stmt(self.parse_binding_stmt()),
            TokenKind::Defer => StmtOrTail::Stmt(self.parse_defer_stmt()),
            TokenKind::While => StmtOrTail::Stmt(Stmt::While(self.parse_while_stmt())),
            TokenKind::Loop => StmtOrTail::Stmt(Stmt::Loop(self.parse_loop_stmt())),
            _ => {
                let expr = self.parse_expression();
                if self.eat(&TokenKind::Semi) {
                    StmtOrTail::Stmt(Stmt::Expr(expr))
                } else if self.check(&TokenKind::RBrace) || self.at_eof() {
                    StmtOrTail::Tail(expr)
                } else if ends_with_brace(&expr) {
                    // if/match/block already end in `}`; requiring an
                    // extra `;` after one used as a statement (as
                    // opposed to a block's tail) would be needless
                    // ceremony, so it's optional here, matching how most
                    // brace-delimited languages treat this case.
                    StmtOrTail::Stmt(Stmt::Expr(expr))
                } else {
                    self.error_expected("`;`");
                    StmtOrTail::Recover
                }
            }
        }
    }

    fn parse_binding_stmt(&mut self) -> Stmt {
        let start = self.current_span();
        let mutable = matches!(self.current(), TokenKind::Mutable);
        self.advance(); // 'value' or 'mutable'
        let name = self.expect_ident("a binding name").unwrap_or_else(|| {
            let span = self.current_span();
            Ident {
                symbol: self.placeholder_symbol(),
                span,
            }
        });
        let ty = if self.eat(&TokenKind::Colon) {
            self.parse_type()
        } else {
            None
        };
        self.expect(&TokenKind::Eq, "`=`");
        let value = self.parse_expression();
        let value_span = value.span();
        self.expect(&TokenKind::Semi, "`;`");
        Stmt::Binding(crate::syntax::ast::BindingStmt {
            mutable,
            name,
            ty,
            value,
            span: start.join(value_span),
        })
    }

    fn parse_defer_stmt(&mut self) -> Stmt {
        let start = self.current_span();
        self.advance(); // 'defer'
        let expr = self.parse_expression();
        let expr_span = expr.span();
        self.expect(&TokenKind::Semi, "`;`");
        Stmt::Defer {
            expr,
            span: start.join(expr_span),
        }
    }

    fn parse_while_stmt(&mut self) -> WhileStmt {
        let start = self.current_span();
        self.advance(); // 'while'
        let condition = Box::new(self.parse_expression_no_struct_literal());
        let body = self.parse_block();
        WhileStmt {
            condition,
            span: start.join(body.span),
            body,
        }
    }

    fn parse_loop_stmt(&mut self) -> LoopStmt {
        let start = self.current_span();
        self.advance(); // 'loop'
        let body = self.parse_block();
        LoopStmt {
            span: start.join(body.span),
            body,
        }
    }

    fn placeholder_symbol(&mut self) -> crate::symbol::Symbol {
        self.interner.intern("<error>")
    }
}

enum StmtOrTail {
    Stmt(Stmt),
    Tail(crate::syntax::ast::Expr),
    /// The statement failed to parse in a way that needs the block loop
    /// to resynchronize (e.g. a missing `;` before an unrelated token).
    Recover,
}

#[cfg(test)]
mod tests {
    use super::super::tests::parse;
    use crate::syntax::ast::Item;

    #[test]
    fn parses_function_with_params_and_return_type() {
        let (module, diags) =
            parse("func add(left: i64, right: i64) -> i64 { return left + right }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        assert_eq!(module.items.len(), 1);
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.params.len(), 2);
        assert!(f.return_type.is_some());
        assert!(!f.public);
    }

    #[test]
    fn parses_public_function() {
        let (module, diags) = parse("public func main() -> i64 { return 0 }");
        assert!(diags.is_empty());
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert!(f.public);
    }

    #[test]
    fn parses_private_function() {
        // `private` is reserved but was never actually consumed by the
        // parser; a program using it explicitly (rather than just
        // omitting `public`) must not fail to parse.
        let (module, diags) = parse("private func main() -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert!(!f.public);
    }

    #[test]
    fn parses_private_record_field() {
        let (module, diags) = parse("record Point { private x: i64, y: i64 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Record(r) = &module.items[0] else {
            panic!("expected record")
        };
        assert!(!r.fields[0].public);
        assert!(!r.fields[1].public);
    }

    #[test]
    fn parses_function_with_uses_and_raises_clauses() {
        let (module, diags) = parse(
            "func loadUser(id: i64) -> i64 uses Database.Read raises UserNotFound { return id }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.uses.len(), 1);
        assert_eq!(f.uses[0].segments.len(), 2);
        assert_eq!(f.raises.len(), 1);
    }

    #[test]
    fn parses_record_declaration() {
        let (module, diags) = parse("record Point { x: i64, y: i64 }");
        assert!(diags.is_empty());
        let Item::Record(r) = &module.items[0] else {
            panic!("expected record")
        };
        assert_eq!(r.fields.len(), 2);
    }

    #[test]
    fn parses_variant_declaration_with_payloads() {
        let (module, diags) = parse("variant Shape { Circle(i64), Square(i64), Empty }");
        assert!(diags.is_empty());
        let Item::Variant(v) = &module.items[0] else {
            panic!("expected variant")
        };
        assert_eq!(v.cases.len(), 3);
        assert_eq!(v.cases[0].payload.len(), 1);
        assert_eq!(v.cases[2].payload.len(), 0);
    }

    #[test]
    fn parses_protocol_declaration() {
        let (module, diags) = parse("protocol Encodable { func encode() -> str; }");
        assert!(diags.is_empty());
        let Item::Protocol(p) = &module.items[0] else {
            panic!("expected protocol")
        };
        assert_eq!(p.members.len(), 1);
    }

    #[test]
    fn parses_extend_with_protocol() {
        let (module, diags) =
            parse("extend Point with Printable { func show() -> str { return \"\" } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Extend(e) = &module.items[0] else {
            panic!("expected extend")
        };
        assert!(e.protocol.is_some());
        assert_eq!(e.functions.len(), 1);
    }

    #[test]
    fn parses_extend_without_protocol() {
        let (module, diags) = parse("extend Point { func origin() -> i64 { return 0 } }");
        assert!(diags.is_empty());
        let Item::Extend(e) = &module.items[0] else {
            panic!("expected extend")
        };
        assert!(e.protocol.is_none());
    }

    #[test]
    fn parses_import_declaration() {
        let (module, diags) = parse("import std.io;");
        assert!(diags.is_empty());
        let Item::Import(i) = &module.items[0] else {
            panic!("expected import")
        };
        assert_eq!(i.path.segments.len(), 2);
    }

    #[test]
    fn parses_value_and_mutable_bindings() {
        let (module, diags) = parse("func f() { value a = 1; mutable b = 2; }");
        assert!(diags.is_empty());
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.body.statements.len(), 2);
    }

    #[test]
    fn parses_while_and_loop_statements() {
        let (module, diags) = parse("func f() { while true { break; } loop { break; } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.body.statements.len(), 2);
    }

    #[test]
    fn block_tail_expression_has_no_trailing_semicolon() {
        let (module, diags) = parse("func f() -> i64 { value x = 1; x }");
        assert!(diags.is_empty());
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.body.statements.len(), 1);
        assert!(f.body.tail.is_some());
    }

    #[test]
    fn missing_closing_brace_is_a_diagnostic_not_a_panic() {
        let (_, diags) = parse("func f() -> i64 { return 0");
        assert!(!diags.is_empty());
    }

    #[test]
    fn missing_semicolon_recovers_to_next_statement() {
        let (module, diags) = parse("func f() { value a = 1 value b = 2; }");
        assert!(!diags.is_empty());
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        // Despite the missing `;`, both bindings should still be recovered.
        assert_eq!(f.body.statements.len(), 2);
    }
}
