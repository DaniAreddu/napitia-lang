//! Item, statement, and declaration parsing.

use super::{Parser, recovery};
use crate::lexer::TokenKind;
use crate::source::Span;
use crate::syntax::ast::{
    Block, Case, Expr, ExtendDecl, Field, FunctionDecl, Ident, ImportDecl, Item, LoopStmt, Param,
    Path, ProtocolDecl, ProtocolMember, RecordDecl, ResourceDecl, Stmt, Type, UsesClause,
    VariantDecl, WhileStmt,
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
            TokenKind::Resource => self.parse_resource(public).map(Item::Resource),
            _ => {
                self.error_expected(
                    "an item (func, record, variant, protocol, extend, resource, or import)",
                );
                None
            }
        }
    }

    fn parse_function(&mut self, public: bool) -> Option<FunctionDecl> {
        let start = self.current_span();
        self.advance(); // 'func'
        let name = self.expect_ident("a function name")?;
        let type_params = if self.check(&TokenKind::LBracket) {
            self.parse_type_param_list()?
        } else {
            Vec::new()
        };
        self.expect(&TokenKind::LParen, "`(`")?;
        let params = self.parse_param_list()?;
        self.expect(&TokenKind::RParen, "`)`")?;
        let return_type = if self.eat(&TokenKind::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        let uses = if self.eat(&TokenKind::Uses) {
            self.parse_uses_list()?
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
            type_params,
            params,
            return_type,
            uses,
            raises,
            body,
            span,
        })
    }

    /// `[T, U]` after a `func`/`record`/`variant` name -- the
    /// declaration's own generic parameters (`rfcs/0008`). Every entry is
    /// a plain identifier; an empty `[]` is itself malformed (if a
    /// declaration isn't generic, the brackets are simply omitted) but
    /// still recovers rather than aborting the whole declaration. A
    /// trailing comma (`[T,]`) is accepted, matching every other
    /// comma-separated list in this grammar.
    fn parse_type_param_list(&mut self) -> Option<Vec<Ident>> {
        self.expect(&TokenKind::LBracket, "`[`")?;
        let mut params = Vec::new();
        if self.check(&TokenKind::RBracket) {
            self.error_expected("a type parameter");
        } else {
            loop {
                let name = self.expect_ident("a type parameter name")?;
                params.push(name);
                if self.eat(&TokenKind::Comma) {
                    if self.check(&TokenKind::RBracket) {
                        break;
                    }
                    continue;
                }
                break;
            }
        }
        self.expect(&TokenKind::RBracket, "`]`");
        Some(params)
    }

    /// `[i64, str]`, in either type position (`Box[i64]`) or expression
    /// position (`identity[i64]`, `Maybe[i64]`) -- `rfcs/0008`. Same
    /// empty-list-is-malformed, trailing-comma-is-fine rules as
    /// [`Self::parse_type_param_list`]. Returns the parsed arguments
    /// alongside the whole `[...]`'s own span (from `[` through `]`),
    /// distinct from any one argument's span, so an arity diagnostic can
    /// underline the complete application.
    pub(super) fn parse_type_arg_list(&mut self) -> Option<(Vec<Type>, Span)> {
        self.parse_type_arg_list_at_depth(0)
    }

    /// `depth` counts how many `[...]` applications deep parsing has
    /// already descended -- the one thing that grows this parser's own
    /// native call stack per level of nested generic syntax
    /// (`Box[Box[Box[...]]]`). Enforced *before* descending into another
    /// type argument, using the same `crate::limits::MAX_GENERIC_DEPTH`
    /// every other stage that walks a nested type application is bounded
    /// by (`hir::lower`'s own R0019, the verifier, the printer), so a
    /// malformed-looking but syntactically valid chain fails here with a
    /// structured diagnostic, never by exhausting the stack.
    fn parse_type_arg_list_at_depth(&mut self, depth: usize) -> Option<(Vec<Type>, Span)> {
        let lbracket_span = self.expect(&TokenKind::LBracket, "`[`")?.span;
        if depth > crate::limits::MAX_GENERIC_DEPTH {
            self.error_type_too_deep(lbracket_span);
            recovery::synchronize_to_bracket_list_item(self);
            let end = self
                .expect(&TokenKind::RBracket, "`]`")
                .map(|t| t.span)
                .unwrap_or(self.current_span());
            return Some((Vec::new(), lbracket_span.join(end)));
        }
        let mut args = Vec::new();
        if self.check(&TokenKind::RBracket) {
            self.error_expected("a type argument");
        } else {
            loop {
                match self.parse_type_at_depth(depth) {
                    Some(ty) => args.push(ty),
                    None => {
                        recovery::synchronize_to_bracket_list_item(self);
                        if self.check(&TokenKind::RBracket) || self.at_eof() {
                            break;
                        }
                        continue;
                    }
                }
                if self.eat(&TokenKind::Comma) {
                    if self.check(&TokenKind::RBracket) {
                        break;
                    }
                    continue;
                }
                break;
            }
        }
        let end = self
            .expect(&TokenKind::RBracket, "`]`")
            .map(|t| t.span)
            .unwrap_or(self.current_span());
        Some((args, lbracket_span.join(end)))
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
            let take_span = self.check(&TokenKind::Take).then(|| self.current_span());
            let take = take_span.is_some();
            if take {
                self.advance();
            }
            let name = self.expect_ident("a parameter name")?;
            self.expect(&TokenKind::Colon, "`:`")?;
            let ty = self.parse_type()?;
            let span = take_span.unwrap_or(name.span).join(ty.span());
            params.push(Param {
                name,
                ty,
                take,
                span,
            });
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
        self.parse_type_at_depth(0)
    }

    /// `depth` counts type-application nesting only (see
    /// [`Self::parse_type_arg_list_at_depth`]'s own doc comment) --
    /// incremented exactly once per `[...]` this type reference itself
    /// opens, before parsing what is inside it.
    fn parse_type_at_depth(&mut self, depth: usize) -> Option<Type> {
        let name = self.expect_ident("a type name")?;
        let mut span = name.span;
        let args = if self.check(&TokenKind::LBracket) {
            let (args, bracket_span) = self.parse_type_arg_list_at_depth(depth + 1)?;
            span = span.join(bracket_span);
            args
        } else {
            Vec::new()
        };
        Some(Type { name, args, span })
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

    /// One `uses` clause entry: a dotted path, optionally followed by a
    /// bracketed type-argument list (`Equal[T]`, `rfcs/0009`). A bare
    /// dotted path with no brackets is `spec/0005`'s pre-existing,
    /// still-unchecked effect declaration (`Database.Read`); which of
    /// the two this is is left for a later stage to decide from
    /// `args.is_empty()`, not this parse.
    fn parse_uses_clause(&mut self) -> Option<UsesClause> {
        let path = self.parse_path()?;
        let mut span = path.span;
        let args = if self.check(&TokenKind::LBracket) {
            let (args, bracket_span) = self.parse_type_arg_list()?;
            span = span.join(bracket_span);
            args
        } else {
            Vec::new()
        };
        Some(UsesClause { path, args, span })
    }

    fn parse_uses_list(&mut self) -> Option<Vec<UsesClause>> {
        let mut clauses = vec![self.parse_uses_clause()?];
        while self.eat(&TokenKind::Comma) {
            clauses.push(self.parse_uses_clause()?);
        }
        Some(clauses)
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
        let type_params = if self.check(&TokenKind::LBracket) {
            self.parse_type_param_list()?
        } else {
            Vec::new()
        };
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut fields = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let field_public = self.parse_visibility();
            let Some(fname) = self.expect_ident("a field name") else {
                recovery::synchronize_to_list_item(self);
                continue;
            };
            self.expect(&TokenKind::Colon, "`:`");
            let Some(ty) = self.parse_type() else {
                recovery::synchronize_to_list_item(self);
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
            type_params,
            fields,
            span: start.join(end),
        })
    }

    /// `resource File { descriptor: i64 }` (`rfcs/0011`). Deliberately
    /// has no type-parameter list: generic resources are out of scope
    /// this milestone, so unlike `parse_record`/`parse_variant` there is
    /// no `[T, U]` production to even attempt here.
    fn parse_resource(&mut self, public: bool) -> Option<ResourceDecl> {
        let start = self.current_span();
        self.advance(); // 'resource'
        let name = self.expect_ident("a resource name")?;
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut fields = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let field_public = self.parse_visibility();
            let Some(fname) = self.expect_ident("a field name") else {
                recovery::synchronize_to_list_item(self);
                continue;
            };
            self.expect(&TokenKind::Colon, "`:`");
            let Some(ty) = self.parse_type() else {
                recovery::synchronize_to_list_item(self);
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
        Some(ResourceDecl {
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
        let type_params = if self.check(&TokenKind::LBracket) {
            self.parse_type_param_list()?
        } else {
            Vec::new()
        };
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut cases = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let Some(cname) = self.expect_ident("a case name") else {
                recovery::synchronize_to_list_item(self);
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
            type_params,
            cases,
            span: start.join(end),
        })
    }

    fn parse_protocol(&mut self, public: bool) -> Option<ProtocolDecl> {
        let start = self.current_span();
        self.advance(); // 'protocol'
        let name = self.expect_ident("a protocol name")?;
        let type_params = self.parse_type_param_list()?;
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut members = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let before = self.pos;
            if let Some(member) = self.parse_protocol_member() {
                members.push(member);
            }
            if self.pos == before {
                recovery::synchronize_to_member_start(self);
            }
        }
        let end = self
            .expect(&TokenKind::RBrace, "`}`")
            .map(|t| t.span)
            .unwrap_or(self.current_span());
        Some(ProtocolDecl {
            public,
            name,
            type_params,
            members,
            span: start.join(end),
        })
    }

    /// `extend Equal[i64] { ... }` or `extend[T] Equal[Box[T]] uses
    /// Equal[T] { ... }` (`rfcs/0009`). `[T]` right after `extend` is
    /// this extension's *own* explicit type parameters -- never inferred
    /// from an otherwise-unknown name inside `protocol`'s own argument
    /// list, which instead fails to resolve later, in `hir::lower`, the
    /// same way any other unknown type name would.
    fn parse_extend(&mut self) -> Option<ExtendDecl> {
        let start = self.current_span();
        self.advance(); // 'extend'
        let type_params = if self.check(&TokenKind::LBracket) {
            self.parse_type_param_list()?
        } else {
            Vec::new()
        };
        let protocol = self.parse_type()?;
        let uses = if self.eat(&TokenKind::Uses) {
            self.parse_uses_list()?
        } else {
            Vec::new()
        };
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut functions = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let before = self.pos;
            if let Some(func) = self.parse_function(false) {
                functions.push(func);
            }
            if self.pos == before {
                recovery::synchronize_to_member_start(self);
            }
        }
        let end = self
            .expect(&TokenKind::RBrace, "`}`")
            .map(|t| t.span)
            .unwrap_or(self.current_span());
        Some(ExtendDecl {
            type_params,
            protocol,
            uses,
            functions,
            span: start.join(end),
        })
    }

    fn parse_import(&mut self) -> Option<ImportDecl> {
        let start = self.current_span();
        self.advance(); // 'import'
        let path = self.parse_path()?;
        let alias = if self.eat(&TokenKind::As) {
            Some(self.expect_ident("an alias name")?)
        } else {
            None
        };
        let last_span = alias.map_or(path.span, |a| a.span);
        let end = self
            .expect(&TokenKind::Semi, "`;`")
            .map(|t| t.span)
            .unwrap_or(last_span);
        Some(ImportDecl {
            path,
            alias,
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
            TokenKind::Drop => StmtOrTail::Stmt(self.parse_drop_stmt()),
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

    fn parse_drop_stmt(&mut self) -> Stmt {
        let start = self.current_span();
        self.advance(); // 'drop'
        let expr = self.parse_expression();
        let expr_span = expr.span();
        self.expect(&TokenKind::Semi, "`;`");
        Stmt::Drop {
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
    use crate::syntax::ast::{Item, Stmt};

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
        assert_eq!(f.uses[0].path.segments.len(), 2);
        assert!(f.uses[0].args.is_empty());
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
    fn malformed_record_field_recovers_and_still_parses_the_rest() {
        // A field missing its `:` type annotation must not abort the
        // whole declaration -- recovery should still pick up `y`.
        let (module, diags) = parse("record Point { x, y: i64 }");
        assert!(!diags.is_empty());
        let Item::Record(r) = &module.items[0] else {
            panic!("expected record")
        };
        assert_eq!(r.fields.len(), 1, "expected only `y` to survive recovery");
    }

    #[test]
    fn parses_resource_declaration() {
        let (module, diags) = parse("resource File { descriptor: i64 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Resource(r) = &module.items[0] else {
            panic!("expected resource")
        };
        assert_eq!(r.fields.len(), 1);
        assert!(!r.public);
    }

    #[test]
    fn parses_public_resource_with_a_public_field() {
        let (module, diags) = parse("public resource File { public descriptor: i64 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Resource(r) = &module.items[0] else {
            panic!("expected resource")
        };
        assert!(r.public);
        assert!(r.fields[0].public);
    }

    #[test]
    fn malformed_resource_field_recovers_and_still_parses_the_rest() {
        let (module, diags) = parse("resource File { x, descriptor: i64 }");
        assert!(!diags.is_empty());
        let Item::Resource(r) = &module.items[0] else {
            panic!("expected resource")
        };
        assert_eq!(
            r.fields.len(),
            1,
            "expected only `descriptor` to survive recovery"
        );
    }

    #[test]
    fn a_resource_declaration_never_parses_a_type_parameter_list() {
        // Generic resources are out of scope this milestone
        // (`rfcs/0011`) -- the grammar simply never looks for `[...]`
        // after a resource's own name, so `resource Box[T] { .. }`
        // fails to parse (a diagnostic, never a panic or a silently
        // accepted generic resource).
        let (_, diags) = parse("resource Box[T] { value: T }");
        assert!(!diags.is_empty());
    }

    #[test]
    fn parses_take_parameter() {
        let (module, diags) = parse("func consume(take file: File) -> unit { }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert!(f.params[0].take);
    }

    #[test]
    fn an_ordinary_parameter_is_not_take() {
        let (module, diags) = parse("func inspect(file: File) -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert!(!f.params[0].take);
    }

    #[test]
    fn parses_drop_statement() {
        let (module, diags) = parse("func f() { drop file; }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert!(matches!(f.body.statements[0], Stmt::Drop { .. }));
    }

    #[test]
    fn a_drop_statement_missing_its_expression_is_a_diagnostic_not_a_hang() {
        let (_, diags) = parse("func f() { drop ; }");
        assert!(!diags.is_empty());
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
    fn malformed_variant_case_recovers_and_still_parses_the_rest() {
        // A stray token where a case name is expected must not abort
        // the whole declaration -- recovery should still pick up
        // `Empty`.
        let (module, diags) = parse("variant Shape { 1, Empty }");
        assert!(!diags.is_empty());
        let Item::Variant(v) = &module.items[0] else {
            panic!("expected variant")
        };
        assert_eq!(
            v.cases.len(),
            1,
            "expected only `Empty` to survive recovery"
        );
    }

    #[test]
    fn parses_protocol_declaration() {
        let (module, diags) = parse("protocol Encodable[T] { func encode(target: T) -> str; }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Protocol(p) = &module.items[0] else {
            panic!("expected protocol")
        };
        assert_eq!(p.type_params.len(), 1);
        assert_eq!(p.members.len(), 1);
    }

    #[test]
    fn a_protocol_with_no_type_parameters_is_a_parse_error() {
        let (_module, diags) = parse("protocol Encodable { func encode() -> str; }");
        assert!(
            diags.iter().any(|d| d.code == "P0001"),
            "unexpected diagnostics: {diags:?}"
        );
    }

    #[test]
    fn parses_a_concrete_extend_declaration() {
        let (module, diags) = parse(
            "extend Equal[i64] { func equal(left: i64, right: i64) -> bool { return left == right } }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Extend(e) = &module.items[0] else {
            panic!("expected extend")
        };
        assert!(e.type_params.is_empty());
        assert_eq!(e.uses.len(), 0);
        assert_eq!(e.functions.len(), 1);
    }

    #[test]
    fn parses_a_conditional_generic_extend_declaration_with_a_uses_clause() {
        let (module, diags) = parse(
            "extend[T] Equal[Box[T]] uses Equal[T] { func equal(left: Box[T], right: Box[T]) -> bool { return true } }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Extend(e) = &module.items[0] else {
            panic!("expected extend")
        };
        assert_eq!(e.type_params.len(), 1);
        assert_eq!(e.protocol.args.len(), 1);
        assert_eq!(e.uses.len(), 1);
        assert_eq!(e.uses[0].args.len(), 1);
    }

    #[test]
    fn parses_import_declaration() {
        let (module, diags) = parse("import std.io;");
        assert!(diags.is_empty());
        let Item::Import(i) = &module.items[0] else {
            panic!("expected import")
        };
        assert_eq!(i.path.segments.len(), 2);
        assert!(i.alias.is_none());
    }

    #[test]
    fn parses_aliased_import_declaration() {
        let (module, diags) = parse("import sales.user.User as SalesUser;");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Import(i) = &module.items[0] else {
            panic!("expected import")
        };
        assert_eq!(i.path.segments.len(), 3);
        let alias = i.alias.expect("expected an alias");
        // The alias's own span must be distinct from the imported name's
        // (the path's last segment) -- they're two different tokens.
        let imported_name = i.path.segments.last().unwrap();
        assert_ne!(alias.span, imported_name.span);
    }

    #[test]
    fn missing_alias_identifier_is_a_diagnostic_not_a_panic() {
        let (module, diags) = parse("import sales.user.User as; func f() -> i64 { return 0 }");
        assert!(!diags.is_empty(), "expected a diagnostic");
        assert_eq!(diags[0].code, "P0001");
        // Recovery must still reach the function after the malformed
        // import, not abandon the rest of the file.
        assert!(
            module
                .items
                .iter()
                .any(|item| matches!(item, Item::Function(_))),
            "expected recovery to still parse the function: {module:?}"
        );
    }

    #[test]
    fn invalid_alias_token_recovers() {
        let (module, diags) = parse("import sales.user.User as 42; func f() -> i64 { return 0 }");
        assert!(!diags.is_empty(), "expected a diagnostic");
        assert_eq!(diags[0].code, "P0001");
        assert!(
            module
                .items
                .iter()
                .any(|item| matches!(item, Item::Function(_))),
            "expected recovery to still parse the function: {module:?}"
        );
    }

    #[test]
    fn trailing_tokens_after_an_alias_are_rejected_not_silently_accepted() {
        let (module, diags) =
            parse("import sales.user.User as SalesUser extra; func f() -> i64 { return 0 }");
        assert!(
            !diags.is_empty(),
            "a trailing token after the alias must be diagnosed"
        );
        assert!(diags.iter().all(|d| d.code == "P0001"));
        // The import itself, alias included, must still have parsed --
        // only the unexpected trailing token (and whatever follows it
        // until recovery resynchronizes) is rejected.
        let Item::Import(i) = &module.items[0] else {
            panic!("expected import")
        };
        assert!(i.alias.is_some(), "expected the alias to still parse");
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

    // -- Generic syntax (`rfcs/0008`) -----------------------------------

    #[test]
    fn parses_generic_function_type_parameters() {
        let (module, diags) = parse("func identity[T](x: T) -> T { return x }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.type_params.len(), 1);
        assert_eq!(f.params.len(), 1);
    }

    #[test]
    fn parses_generic_function_with_multiple_type_parameters() {
        let (module, diags) = parse("func pair[A, B](left: A, right: B) -> A { return left }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.type_params.len(), 2);
    }

    #[test]
    fn parses_generic_record_declaration() {
        let (module, diags) = parse("record Box[T] { payload: T }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Record(r) = &module.items[0] else {
            panic!("expected record")
        };
        assert_eq!(r.type_params.len(), 1);
        assert_eq!(r.fields.len(), 1);
    }

    #[test]
    fn parses_generic_variant_declaration() {
        let (module, diags) = parse("variant Maybe[T] { Some(T), None }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Variant(v) = &module.items[0] else {
            panic!("expected variant")
        };
        assert_eq!(v.type_params.len(), 1);
        assert_eq!(v.cases.len(), 2);
    }

    #[test]
    fn parses_applied_type_in_type_position() {
        let (module, diags) = parse("func f(b: Box[i64]) -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.params[0].ty.args.len(), 1);
    }

    #[test]
    fn parses_applied_type_with_multiple_arguments() {
        let (module, diags) = parse("func f(p: Pair[i64, str]) -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.params[0].ty.args.len(), 2);
    }

    #[test]
    fn parses_nested_applied_type() {
        let (module, diags) = parse("func f(b: Box[Maybe[i64]]) -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.params[0].ty.args.len(), 1);
        assert_eq!(f.params[0].ty.args[0].args.len(), 1);
    }

    #[test]
    fn a_trailing_comma_in_a_type_parameter_list_is_accepted() {
        let (module, diags) = parse("func pair[A, B,](left: A, right: B) -> A { return left }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.type_params.len(), 2);
    }

    #[test]
    fn a_trailing_comma_in_a_type_argument_list_is_accepted() {
        let (module, diags) = parse("func f(p: Pair[i64, str,]) -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert_eq!(f.params[0].ty.args.len(), 2);
    }

    #[test]
    fn an_empty_type_parameter_list_is_a_diagnostic_not_a_panic() {
        let (_, diags) =
            parse("func broken[]() -> i64 { return 0 } func main() -> i64 { return 0 }");
        assert!(
            !diags.is_empty(),
            "expected a diagnostic for `func broken[]`"
        );
    }

    #[test]
    fn a_duplicated_trailing_comma_type_parameter_list_still_recovers() {
        // `[T,]` (single trailing comma) is fine; `func broken[T,](...)`
        // rejecting outright would be *too* strict, but this still
        // exercises the same recovery path with a genuinely malformed
        // list (two consecutive commas) to prove it never panics.
        let (_, diags) = parse("func broken[T,,](x: T) -> i64 { return 0 }");
        assert!(!diags.is_empty(), "expected a diagnostic for `[T,,]`");
    }

    #[test]
    fn an_empty_type_argument_list_is_a_diagnostic_not_a_panic() {
        let (_, diags) = parse("func f(b: Box[]) -> i64 { return 0 }");
        assert!(!diags.is_empty(), "expected a diagnostic for `Box[]`");
    }

    #[test]
    fn an_unclosed_type_parameter_list_recovers_without_panicking() {
        let (_, diags) = parse("record Box[T { value: T }");
        assert!(
            !diags.is_empty(),
            "expected a diagnostic for `record Box[T`"
        );
    }

    #[test]
    fn an_unclosed_type_argument_list_recovers_without_panicking() {
        let (_, diags) = parse("func f(b: Box[i64) -> i64 { return 0 }");
        assert!(!diags.is_empty(), "expected a diagnostic for `Box[i64`");
    }

    #[test]
    fn a_type_argument_list_never_reinterprets_as_indexing_or_comparison() {
        // `Box[i64,]` (trailing comma) and a bare `identity[i64(42)`
        // (missing `]`) must never be silently reparsed as an indexing
        // expression or a `<`/`>` comparison chain -- both fail with a
        // structured diagnostic instead.
        let (_, diags) = parse("func f() -> i64 { return identity[i64(42) }");
        assert!(
            !diags.is_empty(),
            "expected a diagnostic for an unclosed type application"
        );
    }

    /// Built programmatically, never committed as a giant fixture: a
    /// chain of `Box[...]` applications nested exactly at
    /// `crate::limits::MAX_GENERIC_DEPTH`, which must still parse
    /// successfully -- the bound must reject strictly *more* than this,
    /// never this exact depth itself.
    #[test]
    fn a_type_application_exactly_at_the_depth_limit_still_parses() {
        let depth = crate::limits::MAX_GENERIC_DEPTH;
        let mut ty = "i64".to_string();
        for _ in 0..depth {
            ty = format!("Box[{ty}]");
        }
        let src = format!("func f(x: {ty}) -> i64 {{ return 0 }}");
        let (_, diags) = parse(&src);
        assert!(
            diags.is_empty(),
            "expected no diagnostics at exactly the depth limit, got {diags:?}"
        );
    }

    /// The same chain, one level past the limit: must fail with a
    /// structured diagnostic, never overflow the native call stack.
    #[test]
    fn a_type_application_past_the_depth_limit_is_a_diagnostic_not_a_panic() {
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let mut ty = "i64".to_string();
        for _ in 0..depth {
            ty = format!("Box[{ty}]");
        }
        let src = format!("func f(x: {ty}) -> i64 {{ return 0 }}");
        let (_, diags) = parse(&src);
        assert!(!diags.is_empty(), "expected a diagnostic, got none");
        assert!(
            diags.iter().any(|d| d.code == "P0001"),
            "expected a P0001 diagnostic, got {diags:?}"
        );
    }

    #[test]
    fn a_deeply_nested_type_application_in_expression_position_does_not_panic() {
        // The expression-position entry point (`identity[...]`) is a
        // separate call site into the same depth-guarded parsing --
        // must be independently protected, not just the type-position
        // one exercised above.
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let mut ty = "i64".to_string();
        for _ in 0..depth {
            ty = format!("Box[{ty}]");
        }
        let src = format!("func f() -> i64 {{ return identity[{ty}](0) }}");
        let (_, diags) = parse(&src);
        assert!(!diags.is_empty(), "expected a diagnostic, got none");
        assert!(
            diags.iter().any(|d| d.code == "P0001"),
            "expected a P0001 diagnostic, got {diags:?}"
        );
    }
}
