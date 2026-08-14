//! Basic blocks and terminators.

use super::instruction::{Instruction, ValueId};

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
}
