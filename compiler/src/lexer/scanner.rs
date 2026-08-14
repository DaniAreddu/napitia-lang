//! The [`Scanner`]: turns source text into a stream of tokens.

use super::token::{IntBase, Token, TokenKind, keyword_kind};
use crate::diagnostics::Diagnostic;
use crate::source::{SourceId, Span};
use crate::symbol::Interner;

mod codes {
    pub const UNEXPECTED_CHARACTER: &str = "N0001";
    pub const MALFORMED_NUMBER: &str = "N0002";
    pub const INVALID_ESCAPE: &str = "N0003";
    pub const UNTERMINATED_STRING: &str = "N0004";
    pub const UNTERMINATED_CHAR: &str = "N0005";
    pub const INVALID_CHAR_LITERAL: &str = "N0006";
    pub const UNTERMINATED_COMMENT: &str = "N0007";
}

/// Tokenizes an entire source file, returning every token (always ending
/// in exactly one [`TokenKind::Eof`]) plus any diagnostics encountered.
/// A malformed token never stops tokenization: the scanner records a
/// diagnostic, emits a [`TokenKind::Error`] placeholder, and keeps going,
/// so one bad literal doesn't hide every other lexical error in the file.
pub fn tokenize(
    text: &str,
    source: SourceId,
    interner: &mut Interner,
) -> (Vec<Token>, Vec<Diagnostic>) {
    let mut scanner = Scanner::new(source, text);
    let mut tokens = Vec::new();

    loop {
        scanner.skip_trivia();
        let start = scanner.pos;
        let Some(ch) = scanner.peek() else {
            tokens.push(Token::new(TokenKind::Eof, Span::empty(start)));
            break;
        };
        let kind = scanner.scan_token(ch, interner);
        tokens.push(Token::new(kind, Span::new(start, scanner.pos)));
    }

    (tokens, scanner.diagnostics)
}

struct Scanner<'a> {
    source: SourceId,
    text: &'a str,
    pos: u32,
    diagnostics: Vec<Diagnostic>,
}

impl<'a> Scanner<'a> {
    fn new(source: SourceId, text: &'a str) -> Self {
        Scanner {
            source,
            text,
            pos: 0,
            diagnostics: Vec::new(),
        }
    }

    fn peek(&self) -> Option<char> {
        self.text[self.pos as usize..].chars().next()
    }

    fn peek_at(&self, n: usize) -> Option<char> {
        self.text[self.pos as usize..].chars().nth(n)
    }

    fn bump(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.pos += ch.len_utf8() as u32;
        Some(ch)
    }

    fn push_error(
        &mut self,
        span: Span,
        code: &'static str,
        message: impl Into<String>,
        label: impl Into<String>,
    ) {
        self.diagnostics
            .push(Diagnostic::error(code, self.source, span, message).with_primary_label(label));
    }

    fn skip_trivia(&mut self) {
        loop {
            match (self.peek(), self.peek_at(1)) {
                (Some(c), _) if c.is_whitespace() => {
                    self.bump();
                }
                (Some('/'), Some('/')) => {
                    while !matches!(self.peek(), Some('\n') | None) {
                        self.bump();
                    }
                }
                (Some('/'), Some('*')) => {
                    self.skip_block_comment();
                }
                _ => break,
            }
        }
    }

    fn skip_block_comment(&mut self) {
        let start = self.pos;
        self.bump();
        self.bump();
        let mut depth = 1u32;
        loop {
            match (self.peek(), self.peek_at(1)) {
                (Some('/'), Some('*')) => {
                    self.bump();
                    self.bump();
                    depth += 1;
                }
                (Some('*'), Some('/')) => {
                    self.bump();
                    self.bump();
                    depth -= 1;
                    if depth == 0 {
                        return;
                    }
                }
                (Some(_), _) => {
                    self.bump();
                }
                (None, _) => {
                    let span = Span::new(start, self.pos);
                    self.push_error(
                        span,
                        codes::UNTERMINATED_COMMENT,
                        "unterminated block comment",
                        "comment starts here",
                    );
                    return;
                }
            }
        }
    }

    fn scan_token(&mut self, ch: char, interner: &mut Interner) -> TokenKind {
        let start = self.pos;
        if ch.is_ascii_digit() {
            return self.scan_number(start);
        }
        if ch == 'r' && self.peek_at(1) == Some('"') {
            self.bump();
            return self.scan_raw_string(start);
        }
        if ch.is_ascii_alphabetic() || ch == '_' {
            return self.scan_ident(start, interner);
        }
        match ch {
            '"' => self.scan_string(start),
            '\'' => self.scan_char(start),
            _ => self.scan_operator(start),
        }
    }

    fn scan_ident(&mut self, start: u32, interner: &mut Interner) -> TokenKind {
        while self
            .peek()
            .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            self.bump();
        }
        let text = &self.text[start as usize..self.pos as usize];
        keyword_kind(text).unwrap_or_else(|| TokenKind::Ident(interner.intern(text)))
    }

    /// Scans a run of `is_digit(c) || c == '_'`, returning the raw slice
    /// and whether the underscore placement was valid (no leading,
    /// trailing, or doubled underscore).
    fn scan_digit_group(&mut self, is_digit: impl Fn(char) -> bool) -> (&'a str, bool) {
        let start = self.pos;
        while self.peek().is_some_and(|c| is_digit(c) || c == '_') {
            self.bump();
        }
        let text = &self.text[start as usize..self.pos as usize];
        let ok = !text.is_empty()
            && !text.starts_with('_')
            && !text.ends_with('_')
            && !text.contains("__");
        (text, ok)
    }

    fn scan_number(&mut self, start: u32) -> TokenKind {
        if self.peek() == Some('0') {
            match self.peek_at(1) {
                Some('b') => {
                    self.bump();
                    self.bump();
                    return self.scan_radix_int(start, 2, IntBase::Binary);
                }
                Some('o') => {
                    self.bump();
                    self.bump();
                    return self.scan_radix_int(start, 8, IntBase::Octal);
                }
                Some('x') => {
                    self.bump();
                    self.bump();
                    return self.scan_radix_int(start, 16, IntBase::Hex);
                }
                _ => {}
            }
        }

        let (_, mut ok) = self.scan_digit_group(|c| c.is_ascii_digit());
        let mut is_float = false;

        if self.peek() == Some('.') && self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) {
            is_float = true;
            self.bump();
            let (_, frac_ok) = self.scan_digit_group(|c| c.is_ascii_digit());
            ok &= frac_ok;
        }

        if matches!(self.peek(), Some('e') | Some('E')) {
            let mut lookahead = 1;
            if matches!(self.peek_at(lookahead), Some('+') | Some('-')) {
                lookahead += 1;
            }
            if self.peek_at(lookahead).is_some_and(|c| c.is_ascii_digit()) {
                is_float = true;
                self.bump();
                if matches!(self.peek(), Some('+') | Some('-')) {
                    self.bump();
                }
                let (_, exp_ok) = self.scan_digit_group(|c| c.is_ascii_digit());
                ok &= exp_ok;
            }
        }

        let span = Span::new(start, self.pos);
        let raw = &self.text[span.as_range()];
        let clean: String = raw.chars().filter(|c| *c != '_').collect();

        if !ok {
            self.push_error(
                span,
                codes::MALFORMED_NUMBER,
                "malformed numeric literal",
                "underscore separators must sit directly between digits",
            );
            return TokenKind::Error;
        }

        if is_float {
            match clean.parse::<f64>() {
                Ok(value) => TokenKind::Float(value),
                Err(_) => {
                    self.push_error(
                        span,
                        codes::MALFORMED_NUMBER,
                        "malformed floating-point literal",
                        "could not parse this literal",
                    );
                    TokenKind::Error
                }
            }
        } else {
            match clean.parse::<u128>() {
                Ok(value) => TokenKind::Int {
                    value,
                    base: IntBase::Decimal,
                },
                Err(_) => {
                    self.push_error(
                        span,
                        codes::MALFORMED_NUMBER,
                        "integer literal out of range",
                        "value does not fit in a 128-bit integer",
                    );
                    TokenKind::Error
                }
            }
        }
    }

    fn scan_radix_int(&mut self, start: u32, radix: u32, base: IntBase) -> TokenKind {
        let (text, ok) = self.scan_digit_group(move |c| c.is_digit(radix));
        let span = Span::new(start, self.pos);

        if !ok {
            self.push_error(
                span,
                codes::MALFORMED_NUMBER,
                "malformed integer literal",
                "expected digits after the base prefix, with underscores only between digits",
            );
            return TokenKind::Error;
        }

        let clean: String = text.chars().filter(|c| *c != '_').collect();
        match u128::from_str_radix(&clean, radix) {
            Ok(value) => TokenKind::Int { value, base },
            Err(_) => {
                self.push_error(
                    span,
                    codes::MALFORMED_NUMBER,
                    "integer literal out of range",
                    "value does not fit in a 128-bit integer",
                );
                TokenKind::Error
            }
        }
    }

    fn scan_escape(&mut self, string_start: u32) -> Result<char, ()> {
        let esc_start = self.pos;
        self.bump(); // consume the backslash
        match self.peek() {
            Some('n') => {
                self.bump();
                Ok('\n')
            }
            Some('t') => {
                self.bump();
                Ok('\t')
            }
            Some('r') => {
                self.bump();
                Ok('\r')
            }
            Some('\\') => {
                self.bump();
                Ok('\\')
            }
            Some('"') => {
                self.bump();
                Ok('"')
            }
            Some('\'') => {
                self.bump();
                Ok('\'')
            }
            Some('0') => {
                self.bump();
                Ok('\0')
            }
            Some(_) => {
                self.bump();
                let span = Span::new(esc_start, self.pos);
                self.push_error(
                    span,
                    codes::INVALID_ESCAPE,
                    "unknown escape sequence",
                    "not a recognized escape",
                );
                Err(())
            }
            None => {
                let span = Span::new(string_start, self.pos);
                self.push_error(
                    span,
                    codes::UNTERMINATED_STRING,
                    "unterminated string literal",
                    "string starts here",
                );
                Err(())
            }
        }
    }

    fn scan_string(&mut self, start: u32) -> TokenKind {
        self.bump(); // opening quote
        let mut value = String::new();
        loop {
            match self.peek() {
                None | Some('\n') => {
                    let span = Span::new(start, self.pos);
                    self.push_error(
                        span,
                        codes::UNTERMINATED_STRING,
                        "unterminated string literal",
                        "string starts here",
                    );
                    return TokenKind::Error;
                }
                Some('"') => {
                    self.bump();
                    return TokenKind::Str(value);
                }
                Some('\\') => match self.scan_escape(start) {
                    Ok(c) => value.push(c),
                    Err(()) => {
                        if self.peek().is_none() {
                            return TokenKind::Error;
                        }
                        // Unknown escape: keep scanning the rest of the
                        // string so later errors on the same line are
                        // still reported in this pass.
                    }
                },
                Some(c) => {
                    self.bump();
                    value.push(c);
                }
            }
        }
    }

    fn scan_raw_string(&mut self, start: u32) -> TokenKind {
        self.bump(); // opening quote
        let content_start = self.pos;
        loop {
            match self.peek() {
                None => {
                    let span = Span::new(start, self.pos);
                    self.push_error(
                        span,
                        codes::UNTERMINATED_STRING,
                        "unterminated raw string literal",
                        "raw string starts here",
                    );
                    return TokenKind::Error;
                }
                Some('"') => {
                    let value = self.text[content_start as usize..self.pos as usize].to_string();
                    self.bump();
                    return TokenKind::Str(value);
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
    }

    fn scan_char(&mut self, start: u32) -> TokenKind {
        self.bump(); // opening quote

        let value = match self.peek() {
            Some('\'') => {
                self.bump();
                self.push_error(
                    Span::new(start, self.pos),
                    codes::INVALID_CHAR_LITERAL,
                    "empty character literal",
                    "character literals must contain exactly one character",
                );
                return TokenKind::Error;
            }
            Some('\\') => match self.scan_escape(start) {
                Ok(c) => c,
                Err(()) => return TokenKind::Error,
            },
            Some(c) => {
                self.bump();
                c
            }
            None => {
                self.push_error(
                    Span::new(start, self.pos),
                    codes::UNTERMINATED_CHAR,
                    "unterminated character literal",
                    "character starts here",
                );
                return TokenKind::Error;
            }
        };

        match self.peek() {
            Some('\'') => {
                self.bump();
                TokenKind::Char(value)
            }
            _ => {
                while !matches!(self.peek(), Some('\'') | Some('\n') | None) {
                    self.bump();
                }
                if self.peek() == Some('\'') {
                    self.bump();
                }
                self.push_error(
                    Span::new(start, self.pos),
                    codes::INVALID_CHAR_LITERAL,
                    "character literal must contain exactly one character",
                    "too many characters in this literal",
                );
                TokenKind::Error
            }
        }
    }

    fn scan_operator(&mut self, start: u32) -> TokenKind {
        let c = self.bump().expect("scan_operator called at end of input");
        match c {
            '+' => self.one_or_eq(TokenKind::Plus, TokenKind::PlusEq),
            '*' => self.one_or_eq(TokenKind::Star, TokenKind::StarEq),
            '/' => self.one_or_eq(TokenKind::Slash, TokenKind::SlashEq),
            '%' => self.one_or_eq(TokenKind::Percent, TokenKind::PercentEq),
            '^' => self.one_or_eq(TokenKind::Caret, TokenKind::CaretEq),
            '~' => TokenKind::Tilde,
            '-' => {
                if self.peek() == Some('=') {
                    self.bump();
                    TokenKind::MinusEq
                } else if self.peek() == Some('>') {
                    self.bump();
                    TokenKind::Arrow
                } else {
                    TokenKind::Minus
                }
            }
            '=' => {
                if self.peek() == Some('=') {
                    self.bump();
                    TokenKind::EqEq
                } else if self.peek() == Some('>') {
                    self.bump();
                    TokenKind::FatArrow
                } else {
                    TokenKind::Eq
                }
            }
            '!' => self.one_or_eq(TokenKind::Bang, TokenKind::NotEq),
            '<' => {
                if self.peek() == Some('=') {
                    self.bump();
                    TokenKind::LtEq
                } else if self.peek() == Some('<') {
                    self.bump();
                    if self.peek() == Some('=') {
                        self.bump();
                        TokenKind::ShlEq
                    } else {
                        TokenKind::Shl
                    }
                } else {
                    TokenKind::Lt
                }
            }
            '>' => {
                if self.peek() == Some('=') {
                    self.bump();
                    TokenKind::GtEq
                } else if self.peek() == Some('>') {
                    self.bump();
                    if self.peek() == Some('=') {
                        self.bump();
                        TokenKind::ShrEq
                    } else {
                        TokenKind::Shr
                    }
                } else {
                    TokenKind::Gt
                }
            }
            '&' => {
                if self.peek() == Some('&') {
                    self.bump();
                    TokenKind::AndAnd
                } else if self.peek() == Some('=') {
                    self.bump();
                    TokenKind::AmpEq
                } else {
                    TokenKind::Amp
                }
            }
            '|' => {
                if self.peek() == Some('|') {
                    self.bump();
                    TokenKind::OrOr
                } else if self.peek() == Some('=') {
                    self.bump();
                    TokenKind::PipeEq
                } else {
                    TokenKind::Pipe
                }
            }
            '.' => {
                if self.peek() == Some('.') {
                    self.bump();
                    if self.peek() == Some('=') {
                        self.bump();
                        TokenKind::DotDotEq
                    } else {
                        TokenKind::DotDot
                    }
                } else {
                    TokenKind::Dot
                }
            }
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            ',' => TokenKind::Comma,
            ';' => TokenKind::Semi,
            ':' => TokenKind::Colon,
            '?' => TokenKind::Question,
            other => {
                let span = Span::new(start, self.pos);
                self.push_error(
                    span,
                    codes::UNEXPECTED_CHARACTER,
                    format!("unexpected character '{other}'"),
                    "not valid here",
                );
                TokenKind::Error
            }
        }
    }

    fn one_or_eq(&mut self, plain: TokenKind, with_eq: TokenKind) -> TokenKind {
        if self.peek() == Some('=') {
            self.bump();
            with_eq
        } else {
            plain
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::SourceMap;

    fn lex(text: &str) -> (Vec<Token>, Vec<Diagnostic>) {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        tokenize(map.get(id).content(), id, &mut interner)
    }

    fn kinds(text: &str) -> Vec<TokenKind> {
        lex(text).0.into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn empty_input_is_just_eof() {
        assert_eq!(kinds(""), vec![TokenKind::Eof]);
    }

    #[test]
    fn keywords_are_recognized() {
        assert_eq!(
            kinds("func value mutable"),
            vec![
                TokenKind::Func,
                TokenKind::Value,
                TokenKind::Mutable,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn identifiers_are_interned() {
        let (tokens, diags) = lex("answer answer other");
        assert!(diags.is_empty());
        let TokenKind::Ident(a1) = &tokens[0].kind else {
            panic!("expected ident")
        };
        let TokenKind::Ident(a2) = &tokens[1].kind else {
            panic!("expected ident")
        };
        let TokenKind::Ident(b) = &tokens[2].kind else {
            panic!("expected ident")
        };
        assert_eq!(a1, a2);
        assert_ne!(a1, b);
    }

    #[test]
    fn decimal_integer_literal() {
        assert_eq!(
            kinds("1_000_000"),
            vec![
                TokenKind::Int {
                    value: 1_000_000,
                    base: IntBase::Decimal
                },
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn binary_octal_hex_integer_literals() {
        assert_eq!(
            kinds("0b1010 0o17 0xFF"),
            vec![
                TokenKind::Int {
                    value: 10,
                    base: IntBase::Binary
                },
                TokenKind::Int {
                    value: 15,
                    base: IntBase::Octal
                },
                TokenKind::Int {
                    value: 255,
                    base: IntBase::Hex
                },
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn malformed_radix_literal_is_a_diagnostic() {
        let (tokens, diags) = lex("0b2");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "N0002");
        assert_eq!(tokens[0].kind, TokenKind::Error);
    }

    #[test]
    fn trailing_underscore_is_malformed() {
        let (_, diags) = lex("1_000_");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "N0002");
    }

    #[test]
    fn float_literal_with_fraction() {
        assert_eq!(kinds("3.5"), vec![TokenKind::Float(3.5), TokenKind::Eof]);
    }

    #[test]
    fn float_literal_with_exponent_only() {
        assert_eq!(kinds("1e10"), vec![TokenKind::Float(1e10), TokenKind::Eof]);
    }

    #[test]
    fn float_literal_with_negative_exponent() {
        assert_eq!(
            kinds("1.5e-3"),
            vec![TokenKind::Float(1.5e-3), TokenKind::Eof]
        );
    }

    #[test]
    fn dot_without_following_digit_is_not_part_of_a_float() {
        // "1.method" should lex as Int(1), Dot, Ident, not a float.
        let (tokens, diags) = lex("1.value");
        assert!(diags.is_empty());
        assert_eq!(
            tokens[0].kind,
            TokenKind::Int {
                value: 1,
                base: IntBase::Decimal
            }
        );
        assert_eq!(tokens[1].kind, TokenKind::Dot);
    }

    #[test]
    fn range_operators_are_not_confused_with_field_access() {
        assert_eq!(
            kinds("0..5"),
            vec![
                TokenKind::Int {
                    value: 0,
                    base: IntBase::Decimal
                },
                TokenKind::DotDot,
                TokenKind::Int {
                    value: 5,
                    base: IntBase::Decimal
                },
                TokenKind::Eof
            ]
        );
        assert_eq!(
            kinds("0..=5"),
            vec![
                TokenKind::Int {
                    value: 0,
                    base: IntBase::Decimal
                },
                TokenKind::DotDotEq,
                TokenKind::Int {
                    value: 5,
                    base: IntBase::Decimal
                },
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn string_literal_with_escapes() {
        let (tokens, diags) = lex(r#""line1\nline2\t\"quoted\"""#);
        assert!(diags.is_empty());
        assert_eq!(
            tokens[0].kind,
            TokenKind::Str("line1\nline2\t\"quoted\"".to_string())
        );
    }

    #[test]
    fn unterminated_string_literal_is_a_diagnostic() {
        let (tokens, diags) = lex("\"unterminated");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "N0004");
        assert_eq!(tokens[0].kind, TokenKind::Error);
    }

    #[test]
    fn unterminated_string_at_newline_is_a_diagnostic() {
        let (_, diags) = lex("\"oops\nnext line");
        assert_eq!(diags[0].code, "N0004");
    }

    #[test]
    fn invalid_escape_sequence_is_a_diagnostic() {
        let (tokens, diags) = lex(r#""bad \q escape""#);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "N0003");
        // Recovery continues scanning the rest of the string.
        assert!(matches!(tokens[0].kind, TokenKind::Str(_)));
    }

    #[test]
    fn raw_string_performs_no_escape_processing() {
        let (tokens, diags) = lex(r#"r"C:\no\escapes""#);
        assert!(diags.is_empty());
        assert_eq!(tokens[0].kind, TokenKind::Str(r"C:\no\escapes".to_string()));
    }

    #[test]
    fn character_literal() {
        assert_eq!(kinds("'a'"), vec![TokenKind::Char('a'), TokenKind::Eof]);
    }

    #[test]
    fn character_literal_with_escape() {
        assert_eq!(kinds(r"'\n'"), vec![TokenKind::Char('\n'), TokenKind::Eof]);
    }

    #[test]
    fn empty_character_literal_is_a_diagnostic() {
        let (_, diags) = lex("''");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "N0006");
    }

    #[test]
    fn overlong_character_literal_is_a_diagnostic() {
        let (_, diags) = lex("'ab'");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "N0006");
    }

    #[test]
    fn multi_byte_utf8_character_literal() {
        assert_eq!(kinds("'é'"), vec![TokenKind::Char('é'), TokenKind::Eof]);
    }

    #[test]
    fn line_comment_is_discarded() {
        assert_eq!(
            kinds("value x // trailing comment\n"),
            vec![
                TokenKind::Value,
                TokenKind::Ident(crate::symbol::Interner::new().intern("x")),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn nested_block_comments() {
        let (tokens, diags) = lex("/* outer /* inner */ still outer */ value");
        assert!(diags.is_empty());
        assert_eq!(tokens[0].kind, TokenKind::Value);
    }

    #[test]
    fn unterminated_block_comment_is_a_diagnostic() {
        let (_, diags) = lex("/* never closes");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "N0007");
    }

    #[test]
    fn all_operator_tokens() {
        assert_eq!(
            kinds("+ - * / % == != < <= > >= && || ! & | ^ ~ << >>"),
            vec![
                TokenKind::Plus,
                TokenKind::Minus,
                TokenKind::Star,
                TokenKind::Slash,
                TokenKind::Percent,
                TokenKind::EqEq,
                TokenKind::NotEq,
                TokenKind::Lt,
                TokenKind::LtEq,
                TokenKind::Gt,
                TokenKind::GtEq,
                TokenKind::AndAnd,
                TokenKind::OrOr,
                TokenKind::Bang,
                TokenKind::Amp,
                TokenKind::Pipe,
                TokenKind::Caret,
                TokenKind::Tilde,
                TokenKind::Shl,
                TokenKind::Shr,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn assignment_operators() {
        assert_eq!(
            kinds("= += -= *= /= %= &= |= ^= <<= >>="),
            vec![
                TokenKind::Eq,
                TokenKind::PlusEq,
                TokenKind::MinusEq,
                TokenKind::StarEq,
                TokenKind::SlashEq,
                TokenKind::PercentEq,
                TokenKind::AmpEq,
                TokenKind::PipeEq,
                TokenKind::CaretEq,
                TokenKind::ShlEq,
                TokenKind::ShrEq,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn arrows_and_question() {
        assert_eq!(
            kinds("-> => ?"),
            vec![
                TokenKind::Arrow,
                TokenKind::FatArrow,
                TokenKind::Question,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn unexpected_character_is_a_diagnostic() {
        let (tokens, diags) = lex("value x = 1 @ 2");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "N0001");
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Error));
    }

    #[test]
    fn multiple_errors_in_one_file_are_all_reported() {
        let (_, diags) = lex("value x = \"unterminated\nvalue y = 0b2");
        assert_eq!(diags.len(), 2);
        assert_eq!(diags[0].code, "N0004");
        assert_eq!(diags[1].code, "N0002");
    }

    #[test]
    fn every_token_has_a_span_matching_its_source_text() {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", "func add");
        let mut interner = Interner::new();
        let (tokens, _) = tokenize(map.get(id).content(), id, &mut interner);
        assert_eq!(map.get(id).slice(tokens[0].span), Some("func"));
        assert_eq!(map.get(id).slice(tokens[1].span), Some("add"));
    }
}
