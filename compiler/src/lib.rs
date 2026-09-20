//! The Napitia reference compiler.
//!
//! This crate implements the compiler pipeline described in
//! `CONTRIBUTING.md`: source management, diagnostics, lexing, parsing,
//! name resolution, type checking, and lowering to the Napitia IR (NIR),
//! plus two consumers of verified NIR -- a small interpreter that
//! executes it directly and is the complete semantic execution path for
//! the language, and a native ahead-of-time backend ([`native`],
//! `rfcs/0014`) that compiles a deliberately small scalar subset of it
//! to an `x86_64-unknown-linux-gnu` executable.

pub mod cli;
pub mod diagnostics;
pub mod driver;
pub mod hir;
pub mod interpreter;
pub mod lexer;
pub(crate) mod limits;
pub mod native;
pub mod nir;
pub mod place;
pub mod project;
pub mod resolve;
pub mod resourceck;
pub mod source;
pub mod symbol;
pub mod syntax;
pub mod typeck;
pub mod types;

pub mod parser;
