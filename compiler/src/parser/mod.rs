//! The hand-written recursive-descent parser.

pub mod declaration;
pub mod expression;
pub mod recovery;

use crate::diagnostics::Diagnostic;
use crate::lexer::{Token, TokenKind};
use crate::source::{SourceId, Span};
use crate::symbol::Interner;
use crate::syntax::ast::{Ident, Module};

const ERROR_CODE: &str = "P0001";

/// Parses a token stream (already produced by [`crate::lexer::tokenize`])
/// into a [`Module`], plus every diagnostic encountered along the way. A
/// syntax error never aborts parsing: the parser records a diagnostic,
/// recovers by synchronizing to the next safe point, and keeps going, so
/// one malformed item or statement doesn't hide every other error in the
/// file.
pub struct Parser<'a> {
    tokens: Vec<Token>,
    pos: usize,
    source: SourceId,
    interner: &'a mut Interner,
    diagnostics: Vec<Diagnostic>,
    /// When `true`, a bare identifier directly followed by `{` parses as
    /// an ordinary identifier expression, not a [`crate::syntax::ast::Expr::RecordLiteral`].
    /// Set while parsing the condition of `if`/`while` and the scrutinee
    /// of `match`, so `if user { ... }` can never be misread as
    /// `if (user { ... }) { ... }` — the same ambiguity every other
    /// brace-delimited language with struct literals resolves the same
    /// way. A parenthesized record literal (`if (user { ... }) { }`) is
    /// unaffected, since `(` starts a nested, independently-scoped
    /// expression.
    no_struct_literal: bool,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: Vec<Token>, source: SourceId, interner: &'a mut Interner) -> Self {
        assert!(
            !tokens.is_empty() && matches!(tokens.last().unwrap().kind, TokenKind::Eof),
            "token stream must end with exactly one Eof token"
        );
        Parser {
            tokens,
            pos: 0,
            source,
            interner,
            diagnostics: Vec::new(),
            no_struct_literal: false,
        }
    }

    pub fn parse_module(mut self) -> (Module, Vec<Diagnostic>) {
        let mut items = Vec::new();
        while !self.at_eof() {
            let before = self.pos;
            match self.parse_item() {
                Some(item) => items.push(item),
                None => recovery::synchronize_to_item(&mut self),
            }
            if self.pos == before {
                // Defensive: guarantee forward progress even if some
                // parse path above returned without consuming anything.
                self.advance();
            }
        }
        (Module { items }, self.diagnostics)
    }

    fn current(&self) -> &TokenKind {
        &self.tokens[self.pos].kind
    }

    fn current_span(&self) -> Span {
        self.tokens[self.pos].span
    }

    fn at_eof(&self) -> bool {
        matches!(self.current(), TokenKind::Eof)
    }

    fn check(&self, kind: &TokenKind) -> bool {
        self.current() == kind
    }

    fn advance(&mut self) -> Token {
        let tok = self.tokens[self.pos].clone();
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    fn eat(&mut self, kind: &TokenKind) -> bool {
        if self.check(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: &TokenKind, what: &str) -> Option<Token> {
        if self.check(kind) {
            Some(self.advance())
        } else {
            self.error_expected(what);
            None
        }
    }

    fn expect_ident(&mut self, what: &str) -> Option<Ident> {
        if let TokenKind::Ident(symbol) = self.current().clone() {
            let span = self.current_span();
            self.advance();
            Some(Ident { symbol, span })
        } else {
            self.error_expected(what);
            None
        }
    }

    fn error_expected(&mut self, what: &str) {
        // The lexer already reported a diagnostic for an Error token;
        // adding "expected X, found an invalid token" on top of it would
        // just be noise pointing at the same span.
        if matches!(self.current(), TokenKind::Error) {
            return;
        }
        let span = self.current_span();
        let found = describe(self.current());
        self.diagnostics.push(
            Diagnostic::error(
                ERROR_CODE,
                self.source,
                span,
                format!("expected {what}, found {found}"),
            )
            .with_primary_label("unexpected token"),
        );
    }
}

fn describe(kind: &TokenKind) -> String {
    match kind {
        TokenKind::Eof => "end of input".to_string(),
        TokenKind::Ident(_) => "an identifier".to_string(),
        TokenKind::Int { .. } => "an integer literal".to_string(),
        TokenKind::Float(_) => "a floating-point literal".to_string(),
        TokenKind::Str(_) => "a string literal".to_string(),
        TokenKind::Char(_) => "a character literal".to_string(),
        TokenKind::Error => "an invalid token".to_string(),
        TokenKind::LParen => "`(`".to_string(),
        TokenKind::RParen => "`)`".to_string(),
        TokenKind::LBrace => "`{`".to_string(),
        TokenKind::RBrace => "`}`".to_string(),
        TokenKind::LBracket => "`[`".to_string(),
        TokenKind::RBracket => "`]`".to_string(),
        TokenKind::Comma => "`,`".to_string(),
        TokenKind::Semi => "`;`".to_string(),
        TokenKind::Colon => "`:`".to_string(),
        TokenKind::Dot => "`.`".to_string(),
        TokenKind::Arrow => "`->`".to_string(),
        TokenKind::FatArrow => "`=>`".to_string(),
        TokenKind::Eq => "`=`".to_string(),
        TokenKind::Question => "`?`".to_string(),
        other => format!("`{other:?}`"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::tokenize;
    use crate::source::SourceMap;

    pub(super) fn parse(text: &str) -> (Module, Vec<Diagnostic>) {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, mut diags) = tokenize(map.get(id).content(), id, &mut interner);
        let parser = Parser::new(tokens, id, &mut interner);
        let (module, parse_diags) = parser.parse_module();
        diags.extend(parse_diags);
        (module, diags)
    }

    #[test]
    fn empty_module_has_no_items() {
        let (module, diags) = parse("");
        assert!(diags.is_empty());
        assert!(module.items.is_empty());
    }

    #[test]
    fn garbage_top_level_tokens_recover_to_the_next_item() {
        let (module, diags) = parse("@@@ func main() -> i64 { return 0 }");
        // Three unexpected characters, each already reported by the
        // lexer; the parser must not add redundant diagnostics for the
        // resulting Error tokens, and must still parse the function.
        assert_eq!(diags.len(), 3);
        assert_eq!(module.items.len(), 1);
    }
}
