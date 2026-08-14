//! The Napitia IR (NIR): a typed control-flow graph.
//!
//! NIR is lower-level than HIR and is designed to be a reasonable input
//! to a future native backend (`spec/0006`). This milestone lowers HIR
//! to NIR (`lower.rs`), prints NIR as text for debugging (`printer.rs`),
//! and executes it directly with a tree-walking interpreter
//! (`crate::driver`'s `run` support, built on this module).

pub mod block;
pub mod instruction;
pub mod lower;
pub mod printer;

pub use block::{BasicBlock, BlockId, Terminator};
pub use instruction::{Const, FunctionRef, Instruction, ValueId, ValueKind};
pub use lower::lower_module;
pub use printer::print_module;

use crate::hir::ItemId;
use crate::symbol::Symbol;
use crate::types::Ty;

#[derive(Debug, Clone, Default)]
pub struct Module {
    pub functions: Vec<Function>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub id: ItemId,
    pub name: Symbol,
    pub params: Vec<Param>,
    pub return_type: Ty,
    pub blocks: Vec<BasicBlock>,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub value: ValueId,
    pub ty: Ty,
}
