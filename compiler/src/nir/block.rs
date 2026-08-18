//! Basic blocks and terminators.

use super::instruction::{Instruction, ValueId};
use crate::hir::ItemId;
use crate::types::{Evidence, Ty};

/// Identifies a basic block within one function. Printed as `bbN`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BlockId(pub(crate) u32);

/// A straight-line sequence of instructions ending in exactly one
/// [`Terminator`]. NIR never falls through between blocks — every block
/// is independently meaningful (`spec/0006`).
#[derive(Clone, Debug, PartialEq)]
pub struct BasicBlock {
    pub id: BlockId,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Terminator {
    Return(Option<ValueId>),
    Branch(BlockId),
    CondBranch {
        condition: ValueId,
        then_block: BlockId,
        else_block: BlockId,
    },
    /// Dispatches on a variant value's active case. `cases` has exactly
    /// one target per case, index-aligned with the variant's own
    /// declaration order -- every case is covered, since exhaustiveness
    /// is already proven before this is ever built (a wildcard/binding
    /// pattern that covers several cases simply repeats the same target
    /// for each of them).
    Switch {
        scrutinee: ValueId,
        variant: ItemId,
        cases: Vec<BlockId>,
    },
    /// Calls a *fallible* function (one whose own `raises` is non-empty)
    /// (`rfcs/0010`). Never used for an infallible callee -- that stays
    /// an ordinary `ValueKind::Call`, a ordinary value-producing
    /// instruction, since it has only one possible continuation. `Invoke`
    /// is a terminator because it has two: on success, the returned
    /// value is stored into `ok_slot` and control continues at
    /// `ok_target`; on failure, the raised value (already a `Value` with
    /// its own dynamic variant/case identity, from the callee's own
    /// `Raise`) is stored into whichever `InvokeErrTarget` entry's own
    /// `variant` matches it, and control continues at that entry's own
    /// `target` -- exactly one entry per effect the callee's own
    /// `raises` declares, never more or fewer (the verifier's job to
    /// confirm).
    Invoke {
        callee: ItemId,
        type_args: Vec<Ty>,
        args: Vec<ValueId>,
        evidence: Vec<Evidence>,
        ok_slot: ValueId,
        ok_target: BlockId,
        err_targets: Vec<InvokeErrTarget>,
    },
    /// Ends the current function with a raised value instead of an
    /// ordinary return (`rfcs/0010`) -- resolved by whichever frame's own
    /// `Invoke` is waiting on this call, exactly like `Return` resolves
    /// to wherever that frame's own call site continues. `value`'s own
    /// declared type names the raised variant; there is no separate
    /// case/payload field here since `value` is already a complete,
    /// ordinary variant value (built by `ValueKind::VariantCreate` for a
    /// direct `raise`, or simply the value already loaded from an
    /// `Invoke`'s own `InvokeErrTarget` slot when `?` is forwarding one
    /// unchanged).
    Raise {
        value: ValueId,
    },
}

/// One possible failure destination of an [`Terminator::Invoke`] --
/// `variant` is one of the callee's own declared `raises` effects;
/// `slot` receives the raised value on that edge (`Ty::Named(variant,
/// ..)`, allocated by the same function this `Invoke` belongs to);
/// `target` is the block that consumes it.
#[derive(Clone, Debug, PartialEq)]
pub struct InvokeErrTarget {
    pub variant: ItemId,
    pub slot: ValueId,
    pub target: BlockId,
}
