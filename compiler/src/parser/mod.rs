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

/// Maximum expression *nesting* depth the parser will construct before
/// reporting `P0001` and refusing to nest any further.
///
/// Deliberately not in `crate::limits`, whose bounds are the ones every
/// stage re-enforces for itself because each is separately reachable
/// with hand-built input. This one is different: it bounds the shape of
/// the syntax tree *at the only place a syntax tree is ever built from
/// source*, so `hir::lower`, `typeck`, `resourceck::flow`, `nir::lower`
/// and Rust's own recursive `Drop` for the boxed tree are all bounded by
/// construction rather than by a guard each repeats. There is no second
/// way for a `.npt` file to reach them.
///
/// The bound counts *constructed* nesting, not parser recursion.
/// `1 + 1 + 1 + ...` and `f(a)(b)(c)` are folded by a loop rather than
/// by recursion, yet each iteration still wraps the accumulated tree in
/// one more node -- so counting only the recursive descents would leave
/// exactly those shapes unbounded, which is how a 400-term addition
/// chain exhausted the native stack while a 400-deep parenthesis nest
/// was caught.
///
/// Sized from measurement rather than taste. On the tightest platform
/// this compiler is built for (Windows, debug, the 1 MiB default
/// main-thread stack) the most expensive shape per nesting level is a
/// nested block -- parsing, HIR lowering, type checking, resource
/// checking and NIR lowering each descend once per level -- and it
/// exhausted the stack at roughly 115 levels. 32 keeps better than a 3x
/// margin under that while sitting far above anything hand-written
/// source plausibly reaches.
const MAX_EXPRESSION_DEPTH: usize = 32;

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
    /// How many expression nodes deep the tree currently being built
    /// already is ([`MAX_EXPRESSION_DEPTH`]). Maintained by
    /// [`Self::enter_expression`]/[`Self::leave_expression`] around
    /// every point that adds one more level of nesting — the recursive
    /// descents *and* the two loops that wrap an already-parsed operand
    /// in another node per iteration.
    expr_depth: usize,
    /// Whether this file has already been told its expressions nest too
    /// deeply.
    ///
    /// Latched for the rest of the parse, never reset. Once one
    /// expression has been refused, the parse of everything after it
    /// resumes mid-construct and every later "expected X" describes
    /// that truncation rather than anything the author wrote — and on a
    /// chain of tens of thousands of operators there is one such token
    /// per operator, each rendering the same (very long) source line.
    /// One honest diagnostic about the real problem is worth more than
    /// tens of thousands of consequences of it, and the file is rejected
    /// either way.
    reported_expression_too_deep: bool,
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
            expr_depth: 0,
            reported_expression_too_deep: false,
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

    /// Claims one more level of expression nesting, or refuses
    /// ([`MAX_EXPRESSION_DEPTH`]).
    ///
    /// `false` means the budget is spent: the caller must *not* recurse
    /// and must not wrap anything in another node. It reports `P0001`
    /// once, here, so every refusal site gets the same diagnostic
    /// without repeating it, and so a single pathological expression
    /// cannot emit one diagnostic per surplus level.
    ///
    /// Every `true` must be paired with exactly one
    /// [`Self::leave_expression`], including on the paths that bail out
    /// early -- an unbalanced pair would leak budget and start refusing
    /// perfectly ordinary later expressions.
    fn enter_expression(&mut self, span: Span) -> bool {
        if self.expr_depth >= MAX_EXPRESSION_DEPTH {
            self.error_expression_too_deep(span);
            return false;
        }
        self.expr_depth += 1;
        true
    }

    fn leave_expression(&mut self) {
        self.expr_depth = self.expr_depth.saturating_sub(1);
    }

    /// An expression nested past [`MAX_EXPRESSION_DEPTH`].
    ///
    /// Reported at most once per item. The refusal stops the tree from
    /// growing, and every enclosing level then unwinds with its own
    /// ordinary "expected `)`"-style recovery, refusing again as it
    /// goes; repeating this message for each of those would bury the one
    /// line that explains what actually happened. The item is rejected
    /// either way -- the surplus levels still produce their own ordinary
    /// syntax diagnostics.
    fn error_expression_too_deep(&mut self, span: Span) {
        if self.reported_expression_too_deep {
            return;
        }
        self.reported_expression_too_deep = true;
        self.diagnostics.push(
            Diagnostic::error(
                ERROR_CODE,
                self.source,
                span,
                "expression is nested too deeply to parse",
            )
            .with_primary_label("expression is too complex"),
        );
    }

    fn error_pattern_too_deep(&mut self, span: Span) {
        self.diagnostics.push(
            Diagnostic::error(
                ERROR_CODE,
                self.source,
                span,
                "pattern is nested too deeply to parse",
            )
            .with_primary_label("pattern is too complex"),
        );
    }

    /// A type application (`Box[Box[Box[...]]]`) nested past
    /// `crate::limits::MAX_GENERIC_DEPTH` -- the same shared bound
    /// `hir::lower`'s own type-application depth guard (R0019) and every
    /// other stage that walks a nested `Ty::Applied` enforces, so a
    /// pathological chain fails here, at the very first stage able to
    /// see it, rather than recursing further on the native call stack.
    fn error_type_too_deep(&mut self, span: Span) {
        self.diagnostics.push(
            Diagnostic::error(
                ERROR_CODE,
                self.source,
                span,
                "type application is nested too deeply to parse",
            )
            .with_primary_label("type is too complex"),
        );
    }

    fn error_expected(&mut self, what: &str) {
        // The lexer already reported a diagnostic for an Error token;
        // adding "expected X, found an invalid token" on top of it would
        // just be noise pointing at the same span.
        if matches!(self.current(), TokenKind::Error) {
            return;
        }
        // Same principle, one level up: once this item has been told its
        // expressions nest too deeply, the parse of it was truncated in
        // the middle of an expression on purpose, and every "expected X"
        // after that describes the truncation rather than anything the
        // author did. On a chain of tens of thousands of operators there
        // is one of those per surplus token, each rendering the same
        // (very long) source line -- which is how a file with exactly
        // one thing wrong with it produced enough output to look like a
        // hang. The item is still rejected: the depth diagnostic is an
        // error in its own right.
        if self.reported_expression_too_deep {
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
