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
