//! NIR instructions.

use crate::hir::ItemId;
use crate::place::Place;
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
    /// Explicitly transfers ownership of a resource value into a fresh
    /// one, with no intervening slot (`rfcs/0011`): a `take` argument, a
    /// `return`/`raise` operand, or a `value`/`mutable` binding rebound
    /// directly from another already-owned local. `source` is invalid
    /// immediately afterward; this instruction's own result is the
    /// resource's one current owner from this point on. `nir::verify`
    /// never infers this from syntax or use counts -- it is always an
    /// explicit instruction, emitted by `nir::lower` exactly where
    /// `resourceck`'s own checked `consume_sites` already decided a
    /// transfer (never an observation) occurs.
    Move {
        source: ValueId,
    },
    /// Transfers a `take`-flagged `defer` argument's ownership into a
    /// dedicated, hidden capture *at the `defer` statement's own
    /// lexical position* (`rfcs/0011`) -- not later, when the deferred
    /// call this capture eventually feeds actually replays. `source` is
    /// invalid immediately afterward; this instruction's own result is
    /// the resource's one current owner until whichever single
    /// reachable cleanup replay consumes it (an ordinary `Call`
    /// argument, exactly like any other `take` transfer).
    DeferCapture {
        source: ValueId,
    },
    /// Reads the affine value at `place` (`rfcs/0012`): `root` plus a
    /// possibly-empty chain of stable field projections, exactly the
    /// same shared [`Place`] representation `resourceck` and
    /// `nir::verify` also use, rooted here at a NIR [`ValueId`] instead
    /// of a HIR local. `mode: Observe` reads without disturbing
    /// `place`'s own current owner (repeatable, like any other read);
    /// `mode: Transfer` moves it out (`nir::verify`'s own job to check
    /// `place` was actually available, and that no sibling place, or the
    /// place's own strict ancestor, is affected). A structural drop of
    /// one field is expressed as a `Transfer` read of it immediately
    /// followed by an ordinary [`Instruction::Drop`] of this
    /// instruction's own result -- there is no separate `drop.place`
    /// instruction, since "get the value, then drop it" already
    /// composes the two primitives `rfcs/0012` itself only sketches
    /// conceptually.
    PlaceRead {
        place: Place<ValueId>,
        mode: OwnershipMode,
    },
}

/// Whether a `Store` (or, by extension, any other place a value flows
/// into another location) transfers ownership of its own operand, or
/// merely observes/copies it onward (`rfcs/0011`). Carried explicitly
/// on the instruction itself -- never re-derived by `nir::verify` from
/// how many times a value happens to be used elsewhere, a record of
/// `resourceck`'s own already-checked decision (`ConsumeInfo`) that
/// `nir::lower` threads through unchanged. Meaningless (but always
/// `Observe`) for a non-resource-typed value: ownership has nothing to
/// track there, and an ordinary value is always freely copyable.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum OwnershipMode {
    /// `value` remains independently valid after this instruction --
    /// its own underlying resource (if any) is not consumed here.
    Observe,
    /// `value`'s own underlying resource is consumed here: the
    /// destination becomes its one current owner, and `value`'s own
    /// prior identity is invalid immediately afterward.
    Transfer,
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
        mode: OwnershipMode,
    },
    /// Destroys a resource value (`rfcs/0011`): an explicit `drop`, or a
    /// scope's own implicit end-of-scope destruction of a still-owned
    /// resource local. `value` must be resource-typed and must not
    /// already have been the operand of another `Drop` on any path
    /// reaching this one (`nir::verify`'s own job, not lowering's).
    Drop { value: ValueId },
    /// Takes a variant apart into one specific case, transferring that
    /// case's own payload positions to the values that now own them
    /// (`rfcs/0012`).
    ///
    /// This is the one and only point a `match` arm's ownership of a
    /// payload begins. `ValueKind::VariantPayload` is deliberately just
    /// a *read*: the decision tree extracts every payload position of a
    /// case up front, in that case's own block, before it knows which
    /// arm will win -- and whether ownership moves depends entirely on
    /// that. A row that binds the payload, or ignores it with `_` and
    /// therefore has to destroy it, claims it; a row that bound the
    /// *whole* variant instead does not. One extraction is shared by
    /// every arm reachable through that case, so it cannot carry the
    /// answer; this instruction is emitted at the exact point the
    /// decision tree commits to an arm, on that arm's own path alone.
    ///
    /// `nir::verify` treats it as consuming `value`'s whole place and as
    /// the point each entry in `taken` becomes this frame's own
    /// obligation -- path-sensitively, like every other structural
    /// place. A whole-value `Drop` or transfer of the same variant on a
    /// *disjoint* path is therefore completely independent: neither can
    /// suppress or discharge the other, which is precisely what a
    /// function-global "was this consumed anywhere" test got wrong.
    ///
    /// `taken` lists `(payload index, owning value)` in declaration
    /// order. Every *affine* payload position of `case` must appear
    /// exactly once: a missing one would be a resource the shell no
    /// longer owns and nothing else does either, so the verifier
    /// requires completeness rather than trusting lowering.
    DecomposeVariant {
        value: ValueId,
        variant: ItemId,
        case: usize,
        taken: Vec<(usize, ValueId)>,
    },
    /// Reinitializes the affine place `place` with `value` (`rfcs/0012`):
    /// `session.input = open_file()`'s own structural counterpart to
    /// `Store`'s ordinary whole-slot assignment. Always a transfer of
    /// `value` into `place` -- there is no observing form, since
    /// reinitializing a place with a value it does not own would be
    /// meaningless. `nir::verify` requires `place` to be provably empty
    /// (never a live, un-moved field this would silently leak) on every
    /// reachable path reaching this instruction.
    StorePlace {
        place: Place<ValueId>,
        value: ValueId,
    },
}
