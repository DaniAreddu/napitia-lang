//! Token kinds and the [`Token`] type.

use crate::source::Span;
use crate::symbol::Symbol;

/// The base an integer literal was written in. Kept on the token so
/// later stages (and tests) can distinguish `0x2A` from `42` even though
/// both parse to the same value.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum IntBase {
    Decimal,
    Binary,
    Octal,
    Hex,
}

/// One lexical token: its kind plus the byte span it came from. Every
/// token carries a span so diagnostics from later stages can always
/// point back at the exact source text that produced it.
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Token { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals.
    Int {
        value: u128,
        base: IntBase,
    },
    Float(f64),
    Str(String),
    Char(char),
    Ident(Symbol),

    // Keywords. See spec/0001-lexical-grammar.md for the provisional
    // vocabulary this table implements (rfcs/0004-language-independence.md).
    Func,
    Value,
    Mutable,
    Const,
    Return,
    If,
    Else,
    While,
    For,
    In,
    Loop,
    Break,
    Continue,
    True,
    False,
    Record,
    Variant,
    Match,
    Protocol,
    Extend,
    With,
    Import,
    Module,
    Public,
    Private,
    Uses,
    Raises,
    Raise,
    Handle,
    Success,
    Failure,
    As,
    Is,
    Unsafe,
    Async,
    Await,
    Region,
    Defer,

    // Operators and punctuation.
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    EqEq,
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    AndAnd,
    OrOr,
    Bang,
    Amp,
    Pipe,
    Caret,
    Tilde,
    Shl,
    Shr,
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    PercentEq,
    AmpEq,
    PipeEq,
    CaretEq,
    ShlEq,
    ShrEq,
    Dot,
    DotDot,
    DotDotEq,
    Arrow,
    FatArrow,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semi,
    Colon,
    Question,

    /// End of file. Emitted exactly once, as the last token, so the
    /// parser can treat "ran out of input" as an ordinary unexpected
    /// token case rather than an out-of-band signal.
    Eof,

    /// Placeholder for a lexical construct that failed to scan (an
    /// unterminated string, a malformed number, ...). A diagnostic has
    /// already been recorded for it; later stages should skip an `Error`
    /// token rather than treat it as a legitimate value.
    Error,
}

/// Maps a keyword's exact spelling to its token kind, or `None` if `text`
/// is an ordinary identifier.
pub fn keyword_kind(text: &str) -> Option<TokenKind> {
    Some(match text {
        "func" => TokenKind::Func,
        "value" => TokenKind::Value,
        "mutable" => TokenKind::Mutable,
        "const" => TokenKind::Const,
        "return" => TokenKind::Return,
        "if" => TokenKind::If,
        "else" => TokenKind::Else,
        "while" => TokenKind::While,
        "for" => TokenKind::For,
        "in" => TokenKind::In,
        "loop" => TokenKind::Loop,
        "break" => TokenKind::Break,
        "continue" => TokenKind::Continue,
        "true" => TokenKind::True,
        "false" => TokenKind::False,
        "record" => TokenKind::Record,
        "variant" => TokenKind::Variant,
        "match" => TokenKind::Match,
        "protocol" => TokenKind::Protocol,
        "extend" => TokenKind::Extend,
        "with" => TokenKind::With,
        "import" => TokenKind::Import,
        "module" => TokenKind::Module,
        "public" => TokenKind::Public,
        "private" => TokenKind::Private,
        "uses" => TokenKind::Uses,
        "raises" => TokenKind::Raises,
        "raise" => TokenKind::Raise,
        "handle" => TokenKind::Handle,
        "success" => TokenKind::Success,
        "failure" => TokenKind::Failure,
        "as" => TokenKind::As,
        "is" => TokenKind::Is,
        "unsafe" => TokenKind::Unsafe,
        "async" => TokenKind::Async,
        "await" => TokenKind::Await,
        "region" => TokenKind::Region,
        "defer" => TokenKind::Defer,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recognizes_every_reserved_keyword() {
        let keywords = [
            "func", "value", "mutable", "const", "return", "if", "else", "while", "for", "in",
            "loop", "break", "continue", "true", "false", "record", "variant", "match", "protocol",
            "extend", "with", "import", "module", "public", "private", "uses", "raises", "raise",
            "handle", "success", "failure", "as", "is", "unsafe", "async", "await", "region",
            "defer",
        ];
        for kw in keywords {
            assert!(keyword_kind(kw).is_some(), "{kw} should be a keyword");
        }
    }

    #[test]
    fn ordinary_identifiers_are_not_keywords() {
        for ident in ["value1", "myFunc", "Record", "func2"] {
            assert!(
                keyword_kind(ident).is_none(),
                "{ident} should not be a keyword"
            );
        }
    }

    #[test]
    fn move_is_no_longer_reserved() {
        // rfcs/0004-language-independence.md drops `move`: ownership
        // transfer is inferred, so there is no explicit move marker.
        assert!(keyword_kind("move").is_none());
    }
}
