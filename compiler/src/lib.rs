//! The Napitia reference compiler.
//!
//! This crate implements the compiler pipeline described in
//! `CONTRIBUTING.md`: source management, diagnostics, lexing, parsing,
//! name resolution, type checking, and lowering to the Napitia IR (NIR),
//! plus a small interpreter for executing NIR directly.

pub mod cli;
pub mod diagnostics;
pub mod driver;
pub mod hir;
pub mod interpreter;
pub mod lexer;
pub(crate) mod limits;
pub mod nir;
pub mod project;
pub mod resolve;
pub mod source;
pub mod symbol;
pub mod syntax;
pub mod typeck;
pub mod types;

pub mod parser;
