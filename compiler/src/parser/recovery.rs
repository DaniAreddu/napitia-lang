//! Error-recovery synchronization points.

use super::Parser;
use crate::lexer::TokenKind;

/// Tokens that can begin a top-level [`crate::syntax::ast::Item`].
pub(super) fn is_item_start(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Func
            | TokenKind::Record
            | TokenKind::Variant
            | TokenKind::Protocol
            | TokenKind::Extend
            | TokenKind::Import
            | TokenKind::Public
    )
}

/// Tokens that can begin a [`crate::syntax::ast::Stmt`] (a superset of
/// item-start tokens, since an item cannot appear inside a block in this
/// milestone but a stray one is still a useful place to resume parsing).
pub(super) fn is_stmt_start(kind: &TokenKind) -> bool {
    is_item_start(kind)
        || matches!(
            kind,
            TokenKind::Value
                | TokenKind::Mutable
                | TokenKind::Defer
                | TokenKind::If
                | TokenKind::While
                | TokenKind::Loop
                | TokenKind::Match
                | TokenKind::Return
                | TokenKind::Break
                | TokenKind::Continue
        )
}

/// Advances past tokens until the next item-start keyword, or consumes a
/// `;` as a natural end-of-statement marker, or reaches end of input.
/// Called after a top-level item fails to parse.
pub(super) fn synchronize_to_item(p: &mut Parser) {
    loop {
        match p.current() {
            TokenKind::Eof => return,
            TokenKind::Semi => {
                p.advance();
                return;
            }
            kind if is_item_start(kind) => return,
            _ => {
                p.advance();
            }
        }
    }
}

/// Advances past tokens until the next statement-start keyword, a `;`
/// (consumed), or a block-closing `}` (left for the block parser to
/// consume). Called after a statement fails to parse inside a block.
pub(super) fn synchronize_to_stmt(p: &mut Parser) {
    loop {
        match p.current() {
            TokenKind::Eof | TokenKind::RBrace => return,
            TokenKind::Semi => {
                p.advance();
                return;
            }
            kind if is_stmt_start(kind) => return,
            _ => {
                p.advance();
            }
        }
    }
}

/// Advances past tokens until the next `func` keyword (a fresh member
/// attempt), a block-closing `}` (left for the caller), or end of input.
/// Called after a `protocol`/`extend` member fails to parse.
///
/// Deliberately never delegates to `synchronize_to_stmt`/`is_stmt_start`:
/// those consider a general statement-start token (`value`, `mutable`,
/// `if`, ...) itself a valid recovery point, correct inside an ordinary
/// block, where such a token really does start the next statement. A
/// `protocol`/`extend` body has no such statements -- it only ever
/// contains `func` declarations -- so a malformed member beginning with
/// one of those tokens is not a synchronization point at all here, and
/// `synchronize_to_stmt` would return without advancing, leaving the
/// caller's own "did this call make progress" check permanently false:
/// an infinite loop that keeps re-attempting the same non-`func` token
/// forever, its diagnostics list growing without bound.
pub(super) fn synchronize_to_member_start(p: &mut Parser) {
    loop {
        match p.current() {
            TokenKind::Eof | TokenKind::RBrace | TokenKind::Func => return,
            _ => {
                p.advance();
            }
        }
    }
}

/// Advances past tokens until the next `,` (consumed) or a closing `}`
/// (left for the caller). Called after one entry of a comma-separated,
/// brace-delimited list (a record's fields, a variant's cases, a
/// match's arms) fails to parse, so a single malformed entry doesn't
/// take the rest of the list down with it the way `synchronize_to_stmt`
/// would (that helper only recognizes statement/item boundaries, which
/// don't exist inside these lists).
pub(super) fn synchronize_to_list_item(p: &mut Parser) {
    loop {
        match p.current() {
            TokenKind::Eof | TokenKind::RBrace => return,
            TokenKind::Comma => {
                p.advance();
                return;
            }
            _ => {
                p.advance();
            }
        }
    }
}

/// Like [`synchronize_to_list_item`], but for a bracket-delimited list
/// (a generic parameter list `[T, U]` or a type-argument list
/// `[i64, str]`, `rfcs/0008`) rather than a brace-delimited one: stops at
/// the next `,` (consumed) or a closing `]` (left for the caller), never
/// mistaking a stray `}`/`)` elsewhere in the file for this list's own
/// end.
pub(super) fn synchronize_to_bracket_list_item(p: &mut Parser) {
    loop {
        match p.current() {
            TokenKind::Eof | TokenKind::RBracket => return,
            TokenKind::Comma => {
                p.advance();
                return;
            }
            _ => {
                p.advance();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn item_start_recognizes_every_item_keyword() {
        for kind in [
            TokenKind::Func,
            TokenKind::Record,
            TokenKind::Variant,
            TokenKind::Protocol,
            TokenKind::Extend,
            TokenKind::Import,
            TokenKind::Public,
        ] {
            assert!(is_item_start(&kind));
        }
        assert!(!is_item_start(&TokenKind::Plus));
    }

    #[test]
    fn stmt_start_includes_item_start() {
        assert!(is_stmt_start(&TokenKind::Func));
        assert!(is_stmt_start(&TokenKind::Value));
        assert!(is_stmt_start(&TokenKind::Return));
        assert!(!is_stmt_start(&TokenKind::Plus));
    }
}
