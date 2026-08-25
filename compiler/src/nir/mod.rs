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

pub use block::{BasicBlock, BlockId, InvokeErrTarget, Terminator};
pub use instruction::{Const, FunctionRef, Instruction, ValueId, ValueKind};
pub use lower::{lower_module, lower_module_with_paths};
pub use printer::print_module;
pub use verify::verify_module;

use crate::hir::{ItemId, TypeParamId};
use crate::symbol::Symbol;
use crate::types::{CapabilityRequirement, Ty};

#[derive(Debug, Clone, Default)]
pub struct Module {
    pub functions: Vec<Function>,
    /// Every declared record's layout, in declaration order (never a
    /// bare `HashMap` iterated for output -- see `printer`/`verify`,
    /// which both need deterministic iteration).
    pub records: Vec<(ItemId, RecordLayout)>,
    /// Every declared variant's layout, in declaration order.
    pub variants: Vec<(ItemId, VariantLayout)>,
    /// Every declared protocol's layout, in declaration order
    /// (`rfcs/0009`).
    pub protocols: Vec<(ItemId, ProtocolLayout)>,
    /// Every accepted extend's layout, in declaration order (`rfcs/0009`)
    /// -- an extend that failed authority/overlap/completeness
    /// validation never reaches NIR at all.
    pub extends: Vec<(ItemId, ExtendLayout)>,
}

#[derive(Debug, Clone)]
pub struct ProtocolLayout {
    pub name: Symbol,
    /// This protocol's own type parameters, in declaration order -- at
    /// least one, always (`rfcs/0009`).
    pub type_params: Vec<(TypeParamId, Symbol)>,
    /// One entry per method, in declaration order -- a `protocol.call`'s
    /// own `method` index refers into this same order.
    pub methods: Vec<ProtocolMethodLayout>,
}

#[derive(Debug, Clone)]
pub struct ProtocolMethodLayout {
    pub name: Symbol,
    /// Still in terms of the protocol's own `type_params` -- substituted
    /// with a concrete requirement's own arguments wherever it is
    /// checked or displayed against one.
    pub params: Vec<Ty>,
    pub return_type: Ty,
}

#[derive(Debug, Clone)]
pub struct ExtendLayout {
    pub protocol: ItemId,
    /// This extend's own type parameters, in declaration order -- empty
    /// for a concrete extension (`extend Equal[i64]`).
    pub type_params: Vec<(TypeParamId, Symbol)>,
    /// `protocol`'s own type arguments at this extension's head, in
    /// terms of this extend's own `type_params`.
    pub protocol_arguments: Vec<Ty>,
    /// This extend's own `uses` requirements (`rfcs/0009`), in terms of
    /// its own `type_params`.
    pub requirements: Vec<CapabilityRequirement>,
    /// The underlying NIR function implementing each protocol method,
    /// indexed by that method's own declaration-order index within
    /// `protocol`'s own method list -- one entry per protocol method,
    /// always (an incomplete extend never reaches NIR).
    pub methods: Vec<ItemId>,
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
    /// Whether this was declared `resource` rather than `record`
    /// (`rfcs/0011`) -- see [`crate::hir::HirRecord::affine`]. Read back
    /// by `nir::lower`'s own cleanup-insertion bookkeeping and by
    /// `nir::verify`'s resource-state checks.
    pub affine: bool,
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
    /// This function's own `uses` capability requirements (`rfcs/0009`),
    /// in declared order -- empty for a function that declares none. A
    /// `Call` targeting this function carries exactly this many
    /// [`crate::types::Evidence`] entries, in this same order; a
    /// `protocol.call` inside this function's own body resolves through
    /// one of these via a compile-time-resolved
    /// [`crate::types::Evidence::Forwarded`] index into whatever
    /// evidence this function's own current call actually supplied.
    pub requirements: Vec<CapabilityRequirement>,
    pub params: Vec<Param>,
    pub return_type: Ty,
    /// This function's own declared raised-error set (`rfcs/0010`),
    /// canonical (deduplicated `ItemId`s) and in a fixed, deterministic
    /// order -- empty means this function is infallible, and may only
    /// ever be invoked through an ordinary `ValueKind::Call`, never a
    /// `Terminator::Invoke`.
    pub raises: Vec<ItemId>,
    pub blocks: Vec<BasicBlock>,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub value: ValueId,
    pub ty: Ty,
    /// Whether this parameter was declared `take` (`rfcs/0011`) --
    /// ownership-transferring rather than a call-scoped observation.
    /// Carried into NIR itself (not just `nir::lower`'s own internal
    /// bookkeeping) so a consumer independent of lowering -- the
    /// verifier, the interpreter -- can tell the two apart without
    /// re-deriving it from HIR.
    pub take: bool,
}
