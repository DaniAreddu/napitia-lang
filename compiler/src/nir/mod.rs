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
pub mod verify;

pub use block::{BasicBlock, BlockId, Terminator};
pub use instruction::{Const, FunctionRef, Instruction, ValueId, ValueKind};
pub use lower::lower_module;
pub use printer::print_module;
pub use verify::verify_module;

use crate::hir::{ItemId, TypeParamId};
use crate::symbol::Symbol;
use crate::types::Ty;

#[derive(Debug, Clone, Default)]
pub struct Module {
    pub functions: Vec<Function>,
    /// Every declared record's layout, in declaration order (never a
    /// bare `HashMap` iterated for output -- see `printer`/`verify`,
    /// which both need deterministic iteration).
    pub records: Vec<(ItemId, RecordLayout)>,
    /// Every declared variant's layout, in declaration order.
    pub variants: Vec<(ItemId, VariantLayout)>,
}

#[derive(Debug, Clone)]
pub struct RecordLayout {
    pub name: Symbol,
    /// This record's own generic parameters, in declaration order
    /// (`rfcs/0008`) -- empty for a non-generic record. `fields`' types
    /// may reference these via `Ty::Param`; one canonical layout schema
    /// is shared by every concrete use, never duplicated per
    /// instantiation.
    pub type_params: Vec<(TypeParamId, Symbol)>,
    /// `(field name, declared type)`, in declaration order -- the order
    /// `record.create`'s arguments are always given in.
    pub fields: Vec<(Symbol, Ty)>,
}

#[derive(Debug, Clone)]
pub struct VariantLayout {
    pub name: Symbol,
    /// See [`RecordLayout::type_params`].
    pub type_params: Vec<(TypeParamId, Symbol)>,
    /// One entry per case, in declaration order -- the order
    /// `Terminator::Switch`'s targets are always given in.
    pub cases: Vec<CaseLayout>,
}

#[derive(Debug, Clone)]
pub struct CaseLayout {
    pub name: Symbol,
    pub payload: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub id: ItemId,
    pub name: Symbol,
    /// This function's own generic parameters, in declaration order
    /// (`rfcs/0008`) -- empty for a non-generic function. `params`/
    /// `return_type` may reference these via `Ty::Param`; one parametric
    /// body is lowered per declaration, shared across every call
    /// (`ValueKind::Call` carries each call site's own concrete
    /// arguments instead of a cloned body).
    pub type_params: Vec<(TypeParamId, Symbol)>,
    pub params: Vec<Param>,
    pub return_type: Ty,
    pub blocks: Vec<BasicBlock>,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub value: ValueId,
    pub ty: Ty,
}
