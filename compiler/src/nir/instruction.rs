//! NIR instructions.

use crate::hir::ItemId;
use crate::types::{Evidence, Ty};

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
    /// `type_args` is this call's own concrete type arguments for the
    /// callee's generic parameters, in the callee's own declared order
    /// (`rfcs/0008`) -- empty for a non-generic call. The callee itself
    /// is looked up once by `FunctionRef` regardless: one parametric NIR
    /// function body is shared by every call, never cloned per
    /// instantiation. `evidence` is this call's own resolved capability
    /// evidence (`rfcs/0009`), one entry per requirement the callee
    /// itself declares (`Function::requirements`), in that same
    /// declared order -- empty when the callee declares none.
    Call(FunctionRef, Vec<Ty>, Vec<ValueId>, Vec<Evidence>),
    /// Constructs a record value. `fields` is already in **declaration
    /// order** (never construction-site/source order) -- reordering
    /// happens once, at the point of construction, so every later
    /// consumer (the verifier, the interpreter) can index into it
    /// positionally without re-deriving the order from a name.
    /// `type_args` is this construction's own concrete type arguments
    /// (`rfcs/0008`), empty for a non-generic record.
    RecordCreate(ItemId, Vec<Ty>, Vec<ValueId>),
    /// Projects one field (by declaration index) out of a record value.
    /// No separate `type_args` here: the verifier/interpreter recover
    /// the exact instantiation from `base`'s own already-recorded type
    /// (`Ty::Applied`, if generic) rather than duplicating it on this
    /// instruction too.
    RecordField {
        base: ValueId,
        record: ItemId,
        field: usize,
    },
    /// Constructs a variant value for the given case (by declaration
    /// index), with its payload values in declaration order. Empty
    /// `payload` for a unit case allocates no fabricated value.
    /// `type_args` is this construction's own concrete type arguments
    /// (`rfcs/0008`), empty for a non-generic variant.
    VariantCreate {
        variant: ItemId,
        case: usize,
        type_args: Vec<Ty>,
        payload: Vec<ValueId>,
    },
    /// Projects one payload position (by declaration index) out of a
    /// variant value already known to be the given case -- legal only
    /// on the control-flow edge reached through that case's
    /// `Terminator::Switch` target (`nir::verify` checks this).
    VariantPayload {
        base: ValueId,
        variant: ItemId,
        case: usize,
        index: usize,
    },
    /// An explicit protocol-call expression, `Protocol[Args].method(..)`
    /// (`rfcs/0009`), fully resolved at compile time: `protocol`/`method`
    /// are the canonical protocol identity and its method's
    /// declaration-order index (never re-derived from a name at run
    /// time), and `evidence` is exactly how this specific call answers
    /// that protocol's requirement -- a concrete extension
    /// (`Evidence::Extension`) or a forward to the current frame's own
    /// evidence (`Evidence::Forwarded`), resolved once by `typeck`'s
    /// capability solver. Dispatch is a pure lookup through `evidence`,
    /// never a name re-resolution.
    ProtocolCall {
        protocol: ItemId,
        /// `protocol`'s own type arguments at this specific call site
        /// (`Equal[i64]`'s `[i64]`), so the verifier can substitute them
        /// into the protocol's own declared method signature and check
        /// this instruction's operands/result against it, exactly like
        /// `Call`'s own `type_args` lets it check an ordinary call.
        arguments: Vec<Ty>,
        method: usize,
        evidence: Evidence,
        args: Vec<ValueId>,
    },
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
    /// Destroys a resource value (`rfcs/0011`): an explicit `drop`, or a
    /// scope's own implicit end-of-scope destruction of a still-owned
    /// resource local. `value` must be resource-typed and must not
    /// already have been the operand of another `Drop` on any path
    /// reaching this one (`nir::verify`'s own job, not lowering's).
    Drop {
        value: ValueId,
    },
}
