//! The hand-written Napitia lexer.

pub mod scanner;
pub mod token;

pub use scanner::tokenize;
pub use token::{IntBase, Token, TokenKind};
