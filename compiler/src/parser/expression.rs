//! Pratt-style expression parsing.

use super::{Parser, recovery};
use crate::lexer::TokenKind;
use crate::syntax::ast::{
    AssignOp, BinaryOp, ElseBranch, Expr, FailurePattern, FieldInit, HandleArm, HandleExpr, IfExpr,
    MatchArm, MatchArmBody, MatchExpr, Pattern, UnaryOp,
};

impl<'a> Parser<'a> {
    pub(super) fn parse_expression(&mut self) -> Expr {
        self.parse_assignment()
    }

    /// Parses one expression with record-literal construction
    /// syntactically disabled at its top level (restored afterward),
    /// for the one position in the grammar (`if`/`while` condition,
    /// `match` scrutinee) where a bare `TypeName { ... }` would
    /// otherwise be ambiguous with the construct's own opening `{`. See
    /// `Parser::no_struct_literal`'s doc comment.
    pub(super) fn parse_expression_no_struct_literal(&mut self) -> Expr {
        let previous = self.no_struct_literal;
        self.no_struct_literal = true;
        let expr = self.parse_expression();
        self.no_struct_literal = previous;
        expr
    }

    fn parse_assignment(&mut self) -> Expr {
        let left = self.parse_range();
        if let Some(op) = assign_op(self.current()) {
            self.advance();
            let value = self.parse_assignment();
            let span = left.span().join(value.span());
            return Expr::Assign {
                target: Box::new(left),
                op,
                value: Box::new(value),
                span,
            };
        }
        left
    }

    fn parse_range(&mut self) -> Expr {
        let left = self.parse_binary(1);
        let op = match self.current() {
            TokenKind::DotDot => Some(BinaryOp::Range),
            TokenKind::DotDotEq => Some(BinaryOp::RangeInclusive),
            _ => None,
        };
        let Some(op) = op else { return left };
        self.advance();
        let right = self.parse_binary(1);
        let span = left.span().join(right.span());
        Expr::Binary {
            op,
            left: Box::new(left),
            right: Box::new(right),
            span,
        }
    }

    /// Precedence-climbing binary parser for levels 3-12 of
    /// `spec/0002`'s table (logical-or through multiplicative). Levels
    /// below `min_bp` stop the loop, and the recursive call for the
    /// right-hand side uses `bp + 1` so equal-precedence operators stay
    /// left-associative.
    fn parse_binary(&mut self, min_bp: u8) -> Expr {
        let mut left = self.parse_unary();
        while let Some((bp, op)) = infix_binding_power(self.current()) {
            if bp < min_bp {
                break;
            }
            self.advance();
            let right = self.parse_binary(bp + 1);
            let span = left.span().join(right.span());
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
                span,
            };
        }
        left
    }

    fn parse_unary(&mut self) -> Expr {
        let start = self.current_span();
        let op = match self.current() {
            TokenKind::Minus => Some(UnaryOp::Neg),
            TokenKind::Bang => Some(UnaryOp::Not),
            TokenKind::Tilde => Some(UnaryOp::BitNot),
            _ => None,
        };
        let Some(op) = op else {
            return self.parse_postfix();
        };
        self.advance();
        let operand = self.parse_unary();
        let span = start.join(operand.span());
        Expr::Unary {
            op,
            operand: Box::new(operand),
            span,
        }
    }

    fn parse_postfix(&mut self) -> Expr {
        let mut expr = self.parse_primary();
        loop {
            match self.current() {
                TokenKind::LParen => {
                    self.advance();
                    let args = self.parse_call_args();
                    let end_span = self
                        .expect(&TokenKind::RParen, "`)`")
                        .map(|t| t.span)
                        .unwrap_or(self.current_span());
                    let span = expr.span().join(end_span);
                    expr = Expr::Call {
                        callee: Box::new(expr),
                        args,
                        span,
                    };
                }
                TokenKind::Dot => {
                    self.advance();
                    let Some(name) = self.expect_ident("a field name") else {
                        break;
                    };
                    let span = expr.span().join(name.span);
                    expr = Expr::Field {
                        base: Box::new(expr),
                        name,
                        span,
                    };
                }
                TokenKind::As => {
                    self.advance();
                    let Some(ty) = self.parse_type() else { break };
                    let span = expr.span().join(ty.span());
                    expr = Expr::Cast {
                        expr: Box::new(expr),
                        ty,
                        span,
                    };
                }
                TokenKind::Question => {
                    let span = expr.span().join(self.current_span());
                    self.advance();
                    expr = Expr::Try {
                        expr: Box::new(expr),
                        span,
                    };
                }
                _ => break,
            }
        }
        expr
    }

    /// `TypeName { field: expr, ... }` (optionally `TypeName[Args] {
    /// ... }`, `rfcs/0008`), called once the leading identifier (and any
    /// `[Args]`) and the following `{` have already been recognized as a
    /// record literal (not a block).
    fn parse_record_literal(
        &mut self,
        type_name: crate::syntax::ast::Ident,
        type_args: Vec<crate::syntax::ast::Type>,
    ) -> Expr {
        let start = type_name.span;
        self.advance(); // '{'
        let mut fields = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let Some(name) = self.expect_ident("a field name") else {
                recovery::synchronize_to_stmt(self);
                break;
            };
            self.expect(&TokenKind::Colon, "`:`");
            let value = self.parse_expression();
            let fspan = name.span.join(value.span());
            fields.push(FieldInit {
                name,
                value,
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
        Expr::RecordLiteral {
            type_name,
            type_args,
            fields,
            span: start.join(end),
        }
    }

    fn parse_call_args(&mut self) -> Vec<Expr> {
        // Call arguments are already unambiguously delimited by `(...)`,
        // so an enclosing `if`/`while` condition or `match` scrutinee's
        // struct-literal restriction does not need to (and must not)
        // propagate into them: `if f(Foo { x: 1 }) { }` is unambiguous.
        let previous = self.no_struct_literal;
        self.no_struct_literal = false;
        let mut args = Vec::new();
        if self.check(&TokenKind::RParen) {
            self.no_struct_literal = previous;
            return args;
        }
        loop {
            args.push(self.parse_expression());
            if self.eat(&TokenKind::Comma) {
                if self.check(&TokenKind::RParen) {
                    break;
                }
                continue;
            }
            break;
        }
        self.no_struct_literal = previous;
        args
    }

    fn parse_primary(&mut self) -> Expr {
        let span = self.current_span();
        match self.current().clone() {
            TokenKind::Int { value, base } => {
                self.advance();
                Expr::Int { value, base, span }
            }
            TokenKind::Float(value) => {
                self.advance();
                Expr::Float { value, span }
            }
            TokenKind::Str(value) => {
                self.advance();
                Expr::Str { value, span }
            }
            TokenKind::Char(value) => {
                self.advance();
                Expr::Char { value, span }
            }
            TokenKind::True => {
                self.advance();
                Expr::Bool { value: true, span }
            }
            TokenKind::False => {
                self.advance();
                Expr::Bool { value: false, span }
            }
            TokenKind::Ident(symbol) => {
                self.advance();
                let ident = crate::syntax::ast::Ident { symbol, span };
                if self.check(&TokenKind::LBracket) {
                    // Type arguments bind tighter than the record-literal
                    // `{` or the postfix `.`/`(...)` that might follow --
                    // `Box[i64] { .. }`, `identity[i64](..)`, and
                    // `Maybe[i64].Some(..)` all resolve their `[..]`
                    // right here, before any of those (`rfcs/0008`).
                    let Some((args, bracket_span)) = self.parse_type_arg_list() else {
                        return Expr::Error { span };
                    };
                    if !self.no_struct_literal && self.check(&TokenKind::LBrace) {
                        self.parse_record_literal(ident, args)
                    } else {
                        Expr::TypeApply {
                            base: Box::new(Expr::Ident(ident)),
                            args,
                            span: span.join(bracket_span),
                        }
                    }
                } else if !self.no_struct_literal && self.check(&TokenKind::LBrace) {
                    self.parse_record_literal(ident, Vec::new())
                } else {
                    Expr::Ident(ident)
                }
            }
            TokenKind::LParen => {
                self.advance();
                // Parentheses fully delimit a nested expression, so the
                // struct-literal restriction from an enclosing `if`/
                // `while` condition or `match` scrutinee does not apply
                // inside them.
                let previous = self.no_struct_literal;
                self.no_struct_literal = false;
                let inner = self.parse_expression();
                self.no_struct_literal = previous;
                let end = self
                    .expect(&TokenKind::RParen, "`)`")
                    .map(|t| t.span)
                    .unwrap_or(inner.span());
                Expr::Paren {
                    inner: Box::new(inner),
                    span: span.join(end),
                }
            }
            TokenKind::If => Expr::If(Box::new(self.parse_if_expr())),
            TokenKind::Match => Expr::Match(Box::new(self.parse_match_expr())),
            TokenKind::LBrace => Expr::Block(Box::new(self.parse_block())),
            TokenKind::Return => self.parse_return_expr(),
            TokenKind::Break => self.parse_break_expr(),
            TokenKind::Continue => {
                self.advance();
                Expr::Continue { span }
            }
            TokenKind::Raise => self.parse_raise_expr(),
            TokenKind::Handle => Expr::Handle(Box::new(self.parse_handle_expr())),
            _ => {
                self.error_expected("an expression");
                Expr::Error { span }
            }
        }
    }

    /// `raise <expr>` (`rfcs/0010`) -- unlike `return`/`break`, the
    /// operand is mandatory: a bare `raise` names no value to raise.
    fn parse_raise_expr(&mut self) -> Expr {
        let start = self.current_span();
        self.advance(); // 'raise'
        let operand = self.parse_expression();
        let span = start.join(operand.span());
        Expr::Raise {
            operand: Box::new(operand),
            span,
        }
    }

    fn parse_handle_expr(&mut self) -> HandleExpr {
        let start = self.current_span();
        self.advance(); // 'handle'
        let operand = Box::new(self.parse_expression_no_struct_literal());
        self.expect(&TokenKind::LBrace, "`{`");
        let mut arms = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let before = self.pos;
            if let Some(arm) = self.parse_handle_arm() {
                arms.push(arm);
            }
            self.eat(&TokenKind::Comma);
            if self.pos == before {
                self.advance();
            }
        }
        let end = self
            .expect(&TokenKind::RBrace, "`}`")
            .map(|t| t.span)
            .unwrap_or(self.current_span());
        HandleExpr {
            operand,
            arms,
            span: start.join(end),
        }
    }

    fn parse_handle_arm(&mut self) -> Option<HandleArm> {
        match self.current() {
            TokenKind::Success => {
                let start = self.current_span();
                self.advance();
                let pattern = self.parse_pattern()?;
                self.expect(&TokenKind::FatArrow, "`=>`")?;
                let body = self.parse_arm_body();
                let span = start.join(Self::arm_body_span(&body));
                Some(HandleArm::Success {
                    pattern,
                    body,
                    span,
                })
            }
            TokenKind::Failure => {
                let start = self.current_span();
                self.advance();
                let pattern = self.parse_failure_pattern()?;
                self.expect(&TokenKind::FatArrow, "`=>`")?;
                let body = self.parse_arm_body();
                let span = start.join(Self::arm_body_span(&body));
                Some(HandleArm::Failure {
                    pattern,
                    body,
                    span,
                })
            }
            _ => {
                self.error_expected("`success` or `failure`");
                None
            }
        }
    }

    fn parse_arm_body(&mut self) -> MatchArmBody {
        if self.check(&TokenKind::LBrace) {
            MatchArmBody::Block(self.parse_block())
        } else {
            MatchArmBody::Expr(self.parse_expression())
        }
    }

    fn arm_body_span(body: &MatchArmBody) -> crate::source::Span {
        match body {
            MatchArmBody::Expr(e) => e.span(),
            MatchArmBody::Block(b) => b.span,
        }
    }

    /// `_` or `ErrorType.Case[(pattern, ...)]` (`rfcs/0010`). Payload
    /// patterns reuse `parse_pattern`, but are restricted to a bare bind
    /// or `_` later, in `hir::lower` -- this milestone has no nested
    /// refutable matching on a raised value's own payload.
    fn parse_failure_pattern(&mut self) -> Option<FailurePattern> {
        let span = self.current_span();
        if let TokenKind::Ident(symbol) = self.current().clone()
            && self.interner.resolve(symbol) == "_"
        {
            self.advance();
            return Some(FailurePattern::Wildcard { span });
        }
        let error_type = self.expect_ident("an error type name")?;
        self.expect(&TokenKind::Dot, "`.`")?;
        let case = self.expect_ident("a case name")?;
        let mut args = Vec::new();
        let mut end = case.span;
        if self.eat(&TokenKind::LParen) {
            if !self.check(&TokenKind::RParen) {
                loop {
                    args.push(self.parse_pattern()?);
                    if self.eat(&TokenKind::Comma) {
                        if self.check(&TokenKind::RParen) {
                            break;
                        }
                        continue;
                    }
                    break;
                }
            }
            end = self.expect(&TokenKind::RParen, "`)`")?.span;
        }
        Some(FailurePattern::Case {
            error_type,
            case,
            args,
            span: span.join(end),
        })
    }

    fn parse_return_expr(&mut self) -> Expr {
        let start = self.current_span();
        self.advance(); // 'return'
        let value = self.parse_optional_trailing_value();
        let end = value.as_ref().map(|v| v.span()).unwrap_or(start);
        Expr::Return {
            value: value.map(Box::new),
            span: start.join(end),
        }
    }

    fn parse_break_expr(&mut self) -> Expr {
        let start = self.current_span();
        self.advance(); // 'break'
        let value = self.parse_optional_trailing_value();
        let end = value.as_ref().map(|v| v.span()).unwrap_or(start);
        Expr::Break {
            value: value.map(Box::new),
            span: start.join(end),
        }
    }

    /// `return`/`break` may be followed by a value, or nothing at all if
    /// the next token can't start an expression (end of statement, block
    /// close, etc.) — this only checks for the tokens that would
    /// otherwise make parsing an expression here nonsensical.
    fn parse_optional_trailing_value(&mut self) -> Option<Expr> {
        match self.current() {
            TokenKind::Semi | TokenKind::RBrace | TokenKind::Comma | TokenKind::Eof => None,
            _ => Some(self.parse_expression()),
        }
    }

    pub(super) fn parse_if_expr(&mut self) -> IfExpr {
        let start = self.current_span();
        self.advance(); // 'if'
        let condition = Box::new(self.parse_expression_no_struct_literal());
        let then_branch = self.parse_block();
        let else_branch = if self.eat(&TokenKind::Else) {
            if self.check(&TokenKind::If) {
                Some(ElseBranch::If(Box::new(self.parse_if_expr())))
            } else {
                Some(ElseBranch::Block(self.parse_block()))
            }
        } else {
            None
        };
        let end = match &else_branch {
            Some(ElseBranch::Block(b)) => b.span,
            Some(ElseBranch::If(i)) => i.span,
            None => then_branch.span,
        };
        IfExpr {
            condition,
            then_branch,
            else_branch,
            span: start.join(end),
        }
    }

    fn parse_match_expr(&mut self) -> MatchExpr {
        let start = self.current_span();
        self.advance(); // 'match'
        let scrutinee = Box::new(self.parse_expression_no_struct_literal());
        self.expect(&TokenKind::LBrace, "`{`");
        let mut arms = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.at_eof() {
            let before = self.pos;
            if let Some(arm) = self.parse_match_arm() {
                arms.push(arm);
            }
            self.eat(&TokenKind::Comma);
            if self.pos == before {
                self.advance();
            }
        }
        let end = self
            .expect(&TokenKind::RBrace, "`}`")
            .map(|t| t.span)
            .unwrap_or(self.current_span());
        MatchExpr {
            scrutinee,
            arms,
            span: start.join(end),
        }
    }

    fn parse_match_arm(&mut self) -> Option<MatchArm> {
        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::FatArrow, "`=>`")?;
        if self.check(&TokenKind::LBrace) {
            let block = self.parse_block();
            let span = pattern.span().join(block.span);
            Some(MatchArm {
                pattern,
                body: MatchArmBody::Block(block),
                span,
            })
        } else {
            let expr = self.parse_expression();
            let span = pattern.span().join(expr.span());
            Some(MatchArm {
                pattern,
                body: MatchArmBody::Expr(expr),
                span,
            })
        }
    }

    fn parse_pattern(&mut self) -> Option<Pattern> {
        self.parse_pattern_at_depth(0)
    }

    /// `depth` counts `Variant(...)` sub-pattern nesting only -- the
    /// one recursive call this function makes, and so the one thing
    /// that grows this parser's own native call stack per level of
    /// source nesting. A malformed-looking but syntactically valid
    /// chain like `A(A(A(A(...))))` must fail with a diagnostic at
    /// `crate::limits::MAX_PATTERN_DEPTH`, never recurse past it --
    /// typeck's own bound only protects pattern *resolution*, which
    /// never even runs if parsing itself already overflowed the stack
    /// first.
    fn parse_pattern_at_depth(&mut self, depth: usize) -> Option<Pattern> {
        if depth > crate::limits::MAX_PATTERN_DEPTH {
            let span = self.current_span();
            self.error_pattern_too_deep(span);
            return None;
        }
        let span = self.current_span();
        match self.current().clone() {
            TokenKind::Ident(symbol) => {
                self.advance();
                if self.interner.resolve(symbol) == "_" {
                    return Some(Pattern::Wildcard { span });
                }
                let name = crate::syntax::ast::Ident { symbol, span };
                if self.eat(&TokenKind::LParen) {
                    let mut args = Vec::new();
                    if !self.check(&TokenKind::RParen) {
                        loop {
                            args.push(self.parse_pattern_at_depth(depth + 1)?);
                            if self.eat(&TokenKind::Comma) {
                                if self.check(&TokenKind::RParen) {
                                    break;
                                }
                                continue;
                            }
                            break;
                        }
                    }
                    let end = self.expect(&TokenKind::RParen, "`)`")?.span;
                    Some(Pattern::Variant {
                        name,
                        args,
                        span: span.join(end),
                    })
                } else {
                    Some(Pattern::Ident(name))
                }
            }
            TokenKind::Int { value, .. } => {
                self.advance();
                Some(Pattern::Int { value, span })
            }
            TokenKind::Str(value) => {
                self.advance();
                Some(Pattern::Str { value, span })
            }
            TokenKind::Char(value) => {
                self.advance();
                Some(Pattern::Char { value, span })
            }
            TokenKind::True => {
                self.advance();
                Some(Pattern::Bool { value: true, span })
            }
            TokenKind::False => {
                self.advance();
                Some(Pattern::Bool { value: false, span })
            }
            _ => {
                self.error_expected("a pattern");
                None
            }
        }
    }
}

fn infix_binding_power(kind: &TokenKind) -> Option<(u8, BinaryOp)> {
    Some(match kind {
        TokenKind::OrOr => (1, BinaryOp::Or),
        TokenKind::AndAnd => (2, BinaryOp::And),
        TokenKind::Pipe => (3, BinaryOp::BitOr),
        TokenKind::Caret => (4, BinaryOp::BitXor),
        TokenKind::Amp => (5, BinaryOp::BitAnd),
        TokenKind::EqEq => (6, BinaryOp::Eq),
        TokenKind::NotEq => (6, BinaryOp::Ne),
        TokenKind::Lt => (7, BinaryOp::Lt),
        TokenKind::LtEq => (7, BinaryOp::Le),
        TokenKind::Gt => (7, BinaryOp::Gt),
        TokenKind::GtEq => (7, BinaryOp::Ge),
        TokenKind::Shl => (8, BinaryOp::Shl),
        TokenKind::Shr => (8, BinaryOp::Shr),
        TokenKind::Plus => (9, BinaryOp::Add),
        TokenKind::Minus => (9, BinaryOp::Sub),
        TokenKind::Star => (10, BinaryOp::Mul),
        TokenKind::Slash => (10, BinaryOp::Div),
        TokenKind::Percent => (10, BinaryOp::Rem),
        _ => return None,
    })
}

fn assign_op(kind: &TokenKind) -> Option<AssignOp> {
    Some(match kind {
        TokenKind::Eq => AssignOp::Assign,
        TokenKind::PlusEq => AssignOp::Add,
        TokenKind::MinusEq => AssignOp::Sub,
        TokenKind::StarEq => AssignOp::Mul,
        TokenKind::SlashEq => AssignOp::Div,
        TokenKind::PercentEq => AssignOp::Rem,
        TokenKind::AmpEq => AssignOp::BitAnd,
        TokenKind::PipeEq => AssignOp::BitOr,
        TokenKind::CaretEq => AssignOp::BitXor,
        TokenKind::ShlEq => AssignOp::Shl,
        TokenKind::ShrEq => AssignOp::Shr,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::super::tests::parse;
    use crate::syntax::ast::{BinaryOp, Expr, FailurePattern, HandleArm, Item, Stmt};

    fn single_expr(text: &str) -> Expr {
        let src = format!("func f() -> i64 {{ {text} }}");
        let (module, diags) = parse(&src);
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert!(
            f.body.statements.is_empty(),
            "expected a tail expression, got statements"
        );
        (**f.body.tail.as_ref().expect("expected a tail expression")).clone()
    }

    #[test]
    fn arithmetic_precedence_multiplies_before_adding() {
        // 1 + 2 * 3 must parse as 1 + (2 * 3), not (1 + 2) * 3.
        let expr = single_expr("1 + 2 * 3");
        let Expr::Binary {
            op: BinaryOp::Add,
            right,
            ..
        } = expr
        else {
            panic!("expected add")
        };
        assert!(matches!(
            *right,
            Expr::Binary {
                op: BinaryOp::Mul,
                ..
            }
        ));
    }

    #[test]
    fn left_associative_subtraction() {
        // 10 - 3 - 2 must parse as (10 - 3) - 2 = 5, not 10 - (3 - 2) = 9.
        let expr = single_expr("10 - 3 - 2");
        let Expr::Binary {
            op: BinaryOp::Sub,
            left,
            ..
        } = expr
        else {
            panic!("expected sub")
        };
        assert!(matches!(
            *left,
            Expr::Binary {
                op: BinaryOp::Sub,
                ..
            }
        ));
    }

    #[test]
    fn comparison_binds_looser_than_arithmetic() {
        let expr = single_expr("1 + 2 == 3");
        assert!(matches!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                ..
            }
        ));
    }

    #[test]
    fn logical_and_binds_tighter_than_logical_or() {
        let expr = single_expr("true || false && false");
        let Expr::Binary {
            op: BinaryOp::Or,
            right,
            ..
        } = expr
        else {
            panic!("expected or")
        };
        assert!(matches!(
            *right,
            Expr::Binary {
                op: BinaryOp::And,
                ..
            }
        ));
    }

    #[test]
    fn parenthesized_expression_overrides_precedence() {
        let expr = single_expr("(1 + 2) * 3");
        assert!(matches!(
            expr,
            Expr::Binary {
                op: BinaryOp::Mul,
                ..
            }
        ));
    }

    #[test]
    fn unary_minus_binds_tighter_than_binary_minus() {
        let expr = single_expr("-1 - 2");
        let Expr::Binary {
            op: BinaryOp::Sub,
            left,
            ..
        } = expr
        else {
            panic!("expected sub")
        };
        assert!(matches!(*left, Expr::Unary { .. }));
    }

    #[test]
    fn assignment_is_right_associative() {
        let src = "func f() { mutable a = 0; mutable b = 0; a = b = 1; }";
        let (module, diags) = parse(src);
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        let Stmt::Expr(Expr::Assign { value, .. }) = &f.body.statements[2] else {
            panic!("expected assignment statement")
        };
        assert!(matches!(**value, Expr::Assign { .. }));
    }

    #[test]
    fn call_and_field_access_chain() {
        let expr = single_expr("a.b(1, 2).c");
        assert!(matches!(expr, Expr::Field { .. }));
    }

    #[test]
    fn cast_binds_as_postfix() {
        let expr = single_expr("1 as i64 + 2");
        // `as` binds tighter than `+`: (1 as i64) + 2.
        assert!(matches!(
            expr,
            Expr::Binary {
                op: BinaryOp::Add,
                ..
            }
        ));
    }

    #[test]
    fn try_operator_parses_as_postfix() {
        let expr = single_expr("f()?");
        assert!(matches!(expr, Expr::Try { .. }));
    }

    #[test]
    fn raise_expression_parses_its_mandatory_operand() {
        let expr = single_expr("raise FileError.Missing");
        let Expr::Raise { operand, .. } = expr else {
            panic!("expected raise, got {expr:?}")
        };
        assert!(matches!(*operand, Expr::Field { .. }));
    }

    #[test]
    fn handle_expression_parses_success_and_failure_arms() {
        let expr = single_expr("handle f() { success v => v, failure FileError.Missing => 0 }");
        let Expr::Handle(h) = expr else {
            panic!("expected handle, got {expr:?}")
        };
        assert_eq!(h.arms.len(), 2);
        assert!(matches!(h.arms[0], HandleArm::Success { .. }));
        assert!(matches!(h.arms[1], HandleArm::Failure { .. }));
    }

    #[test]
    fn handle_failure_arm_accepts_a_wildcard_catch_all() {
        let expr = single_expr("handle f() { success _ => 0, failure _ => 1 }");
        let Expr::Handle(h) = expr else {
            panic!("expected handle, got {expr:?}")
        };
        let HandleArm::Failure { pattern, .. } = &h.arms[1] else {
            panic!("expected a failure arm")
        };
        assert!(matches!(pattern, FailurePattern::Wildcard { .. }));
    }

    #[test]
    fn handle_failure_arm_parses_a_payload_carrying_case() {
        let expr =
            single_expr("handle f() { success v => v, failure NetworkError.Timeout(ms) => ms }");
        let Expr::Handle(h) = expr else {
            panic!("expected handle, got {expr:?}")
        };
        let HandleArm::Failure { pattern, .. } = &h.arms[1] else {
            panic!("expected a failure arm")
        };
        let FailurePattern::Case {
            error_type: _,
            case: _,
            args,
            ..
        } = pattern
        else {
            panic!("expected a case pattern")
        };
        assert_eq!(args.len(), 1);
    }

    // -- Fix 8: malformed `handle` parser recovery (`rfcs/0010`) --------

    /// A missing `=>` between a `handle` arm's pattern and its body is a
    /// diagnostic, not a panic or a hang -- the parser must still make
    /// progress and return control to its caller.
    #[test]
    fn handle_arm_missing_fat_arrow_is_a_diagnostic_not_a_hang() {
        let src = "func f() -> i64 { handle g() { success v 1 } }";
        let (_, diags) = super::super::tests::parse(src);
        assert!(!diags.is_empty(), "expected at least one diagnostic");
    }

    /// A `handle` expression missing its closing `}` is a diagnostic,
    /// not a panic or a hang.
    #[test]
    fn handle_missing_closing_brace_is_a_diagnostic_not_a_hang() {
        let src = "func f() -> i64 { handle g() { success v => v";
        let (_, diags) = super::super::tests::parse(src);
        assert!(!diags.is_empty(), "expected at least one diagnostic");
    }

    /// An unclosed failure-payload argument list is a diagnostic, not a
    /// panic or a hang.
    #[test]
    fn handle_failure_arm_unclosed_payload_list_is_a_diagnostic_not_a_hang() {
        let src = "func f() -> i64 { handle g() { success v => v, failure Err.Case(x => 1 } }";
        let (_, diags) = super::super::tests::parse(src);
        assert!(!diags.is_empty(), "expected at least one diagnostic");
    }

    /// A trailing comma followed by garbage inside a `handle`'s own
    /// brace-delimited arm list must not hang the parser -- it always
    /// makes forward progress (`parse_handle_expr`'s own `before`/`pos`
    /// guard), one token at a time if nothing else parses.
    #[test]
    fn handle_with_garbage_between_arms_terminates_with_diagnostics() {
        let src = "func f() -> i64 { handle g() { success v => v, 42, failure Err.Case => 1 } }";
        let (_, diags) = super::super::tests::parse(src);
        assert!(!diags.is_empty(), "expected at least one diagnostic");
    }

    #[test]
    fn if_else_expression_in_tail_position() {
        let expr = single_expr("if true { 1 } else { 2 }");
        assert!(matches!(expr, Expr::If(_)));
    }

    #[test]
    fn match_expression_with_literal_and_wildcard_arms() {
        let expr = single_expr("match 1 { 1 => 10, _ => 20 }");
        let Expr::Match(m) = expr else {
            panic!("expected match")
        };
        assert_eq!(m.arms.len(), 2);
    }

    #[test]
    fn match_variant_pattern_with_payload() {
        let expr = single_expr("match x { Some(v) => v, _ => 0 }");
        let Expr::Match(m) = expr else {
            panic!("expected match")
        };
        assert!(matches!(
            m.arms[0].pattern,
            crate::syntax::ast::Pattern::Variant { .. }
        ));
    }

    #[test]
    fn a_pattern_nested_past_the_depth_limit_fails_parsing_not_the_process() {
        // Built programmatically, never committed as a giant fixture:
        // a chain of `Wrap(...)` nested well past
        // `crate::limits::MAX_PATTERN_DEPTH`, which recurses once per
        // level on the parser's own native call stack. Must fail with
        // a deterministic diagnostic, never overflow the stack.
        let depth = crate::limits::MAX_PATTERN_DEPTH + 50;
        let mut pattern = "Leaf".to_string();
        for _ in 0..depth {
            pattern = format!("Wrap({pattern})");
        }
        let src = format!("func f() -> i64 {{ return match x {{ {pattern} => 1, _ => 0 }} }}");
        let (_, diags) = parse(&src);
        assert!(!diags.is_empty(), "expected a diagnostic, got none");
        assert!(
            diags.iter().any(|d| d.code == "P0001"),
            "expected a P0001 diagnostic, got {diags:?}"
        );
    }

    #[test]
    fn return_break_continue_are_expressions_without_trailing_semicolon() {
        let (module, diags) = parse("func f() -> i64 { return 1 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        assert!(matches!(f.body.tail.as_deref(), Some(Expr::Return { .. })));
    }

    #[test]
    fn malformed_expression_recovers_with_error_node() {
        let (_, diags) = parse("func f() -> i64 { value x = ; return 0 }");
        assert!(!diags.is_empty());
    }

    #[test]
    fn parses_record_construction_with_fields_in_any_order() {
        let expr = single_expr("User { id: 1, enabled: true }");
        let Expr::RecordLiteral {
            type_name, fields, ..
        } = expr
        else {
            panic!("expected a record literal")
        };
        assert_eq!(fields.len(), 2);
        assert_ne!(type_name.symbol, fields[0].name.symbol);
    }

    #[test]
    fn parses_empty_record_construction() {
        let expr = single_expr("User {}");
        assert!(matches!(expr, Expr::RecordLiteral { .. }));
    }

    #[test]
    fn bare_identifier_followed_by_block_is_not_a_record_literal() {
        // `if user { ... }` must parse `user` as the plain condition
        // expression, not `user { ... }` as a record literal followed by
        // an empty block -- the classic struct-literal-in-condition
        // ambiguity.
        let (module, diags) = parse("func f() { if user { } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        let Some(Expr::If(if_expr)) = f.body.tail.as_deref() else {
            panic!("expected an if expression")
        };
        assert!(matches!(*if_expr.condition, Expr::Ident(_)));
    }

    #[test]
    fn parenthesized_record_literal_is_allowed_in_a_condition() {
        let (module, diags) = parse("func f() { if (User { id: 1 }) { } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        let Some(Expr::If(if_expr)) = f.body.tail.as_deref() else {
            panic!("expected an if expression")
        };
        let Expr::Paren { inner, .. } = &*if_expr.condition else {
            panic!("expected a parenthesized condition")
        };
        assert!(matches!(**inner, Expr::RecordLiteral { .. }));
    }

    #[test]
    fn record_literal_is_allowed_inside_call_arguments_within_a_condition() {
        // Call arguments are already unambiguously delimited by `(...)`,
        // so the struct-literal restriction from the enclosing `if`
        // condition must not propagate into them.
        let (module, diags) = parse("func f() { if f(User { id: 1 }) { } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        let Some(Expr::If(if_expr)) = f.body.tail.as_deref() else {
            panic!("expected an if expression")
        };
        let Expr::Call { args, .. } = &*if_expr.condition else {
            panic!("expected a call")
        };
        assert!(matches!(args[0], Expr::RecordLiteral { .. }));
    }

    #[test]
    fn bare_identifier_followed_by_block_is_not_a_record_literal_in_match_scrutinee() {
        let (module, diags) = parse("func f() { match result { _ => 1 } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let Item::Function(f) = &module.items[0] else {
            panic!("expected function")
        };
        let Some(Expr::Match(m)) = f.body.tail.as_deref() else {
            panic!("expected a match expression")
        };
        assert!(matches!(*m.scrutinee, Expr::Ident(_)));
    }
}
