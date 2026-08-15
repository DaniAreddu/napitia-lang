//! NIR instructions.

use crate::hir::ItemId;
use crate::types::Ty;

/// Identifies a value produced within one function: a parameter
/// (numbered first), an `alloc` (identifying the resulting storage slot
/// itself — there is no separate slot-ID space, matching `spec/0006`),
/// or any other instruction's result. Printed as `%N`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ValueId(pub(crate) u32);

/// A resolved reference to another function, for `call`. Reuses
/// [`ItemId`] rather than minting a parallel ID space, since NIR
/// functions are lowered 1:1 from HIR functions.
pub type FunctionRef = ItemId;

#[derive(Clone, Debug, PartialEq)]
pub enum Const {
    Int(u128),
    Float(f64),
    Bool(bool),
    Char(char),
    Str(String),
    Unit,
}

/// The operation a value-producing instruction performs.
#[derive(Clone, Debug, PartialEq)]
pub enum ValueKind {
    Alloc,
    Const(Const),
    Load(ValueId),
    Add(ValueId, ValueId),
    Sub(ValueId, ValueId),
    Mul(ValueId, ValueId),
    Div(ValueId, ValueId),
    Rem(ValueId, ValueId),
    Neg(ValueId),
    Not(ValueId),
    And(ValueId, ValueId),
    Or(ValueId, ValueId),
    Xor(ValueId, ValueId),
    Shl(ValueId, ValueId),
    Shr(ValueId, ValueId),
    Eq(ValueId, ValueId),
    Ne(ValueId, ValueId),
    Lt(ValueId, ValueId),
    Le(ValueId, ValueId),
    Gt(ValueId, ValueId),
    Ge(ValueId, ValueId),
    Call(FunctionRef, Vec<ValueId>),
}

/// One NIR instruction. `Value` produces a result (`%d = ...`); `Store`
/// does not (spec/0006's `store <local>, %s`).
#[derive(Clone, Debug, PartialEq)]
pub enum Instruction {
    Value {
        result: ValueId,
        ty: Ty,
        kind: ValueKind,
    },
    Store {
        slot: ValueId,
        value: ValueId,
    },
}
