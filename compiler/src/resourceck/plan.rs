//! The resource checker's own authoritative output (`rfcs/0011`): not
//! merely a `Vec<Diagnostic>`, but a structured plan `nir::lower`
//! consumes directly, so ownership is decided exactly once, by this
//! stage, rather than independently re-inferred a second time while
//! lowering.

use std::collections::BTreeMap;

use crate::diagnostics::Diagnostic;
use crate::hir::{ExprId, ItemId, LocalId};
use crate::place::Place;
use crate::types::Ty;

/// Whether one specific expression's own value, at the exact syntactic
/// position `resourceck::flow` checked it in, observes its underlying
/// resource for the duration of that use, or transfers ownership of it
/// away (`rfcs/0011`) -- `nir::lower` looks this up directly rather
/// than re-deriving it from the expression's own AST shape or a
/// callee's declared `take` flags a second time. Meaningless (and never
/// recorded) for a non-resource-typed expression: an ordinary value has
/// no ownership to speak of.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConsumeInfo {
    Observe,
    Transfer,
}

/// `resourceck`'s own checked plan for one `defer <expr>;` statement,
/// keyed by that exact call expression's own [`ExprId`] (`rfcs/0011`):
/// the resolved callee, each argument's own already-decided
/// [`ConsumeInfo`] and resolved type (in declaration order), the
/// callee's own resolved return type, and this exact `defer`'s own
/// registration order among every `defer` in its enclosing function
/// (lower numbers registered earlier -- LIFO replay processes
/// *decreasing* order). `nir::lower` consumes this directly when it
/// emits the deferred call's own capture/replay instructions, rather
/// than re-resolving the callee's `take` flags or signature a second
/// time from the module's own function signatures -- and independently
/// validates every field against what it resolves on its own, since a
/// plan this internally inconsistent is a bug in one stage or the
/// other, never something to silently paper over.
#[derive(Debug, Clone)]
pub struct CheckedDeferPlan {
    pub callee: ItemId,
    pub arg_modes: Vec<ConsumeInfo>,
    pub arg_types: Vec<Ty>,
    pub return_type: Ty,
    pub registration_order: u32,
}

/// One entry in a checked cleanup sequence, in the exact order
/// [`super::flow::FlowChecker`] already validated is sound: a resource
/// local's own implicit destruction, or a `defer`'s own registered call
/// running. Replayed in *reverse* by `nir::lower` at the exit edge it
/// belongs to -- last declared/registered, first destroyed/run -- which
/// is what makes resource drops and deferred calls interleave in the
/// declaration-reversed order `rfcs/0011` specifies.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum CleanupAction {
    /// Destroys this still-owned place -- a bare root (`Place::root`,
    /// zero projections) is exactly what a whole local's own destruction
    /// already was before Alpha 0.1.8; a projected place
    /// (`rfcs/0012`) destroys exactly one structural field, in the
    /// declaration-reversed order [`super::flow::FlowChecker::
    /// structural_drop_targets`] already expanded a single registered
    /// root obligation into. Never emitted for a place this exact exit
    /// has already proven `Moved`/`Dropped`/`Error` -- `nir::lower` does
    /// not re-derive that; it is baked into whether this variant appears
    /// here at all.
    Drop(Place<LocalId>),
    /// Runs a previously-registered `defer`'s own call, identified by
    /// its own callee expression's stable [`ExprId`] -- `nir::lower`
    /// looks up the concrete, already-lowered callee/arguments it
    /// recorded when it first walked that exact `defer` statement (a
    /// mechanical SSA-value fact, not an ownership decision) rather
    /// than re-lowering or re-deciding anything about it here.
    Defer(ExprId),
}

/// The resource checker's complete, authoritative analysis of one HIR
/// module (`rfcs/0011`). `nir::lower` treats `cleanup_edges` as the
/// single source of truth for every resource cleanup decision it makes:
/// it does not maintain its own independent notion of which locals are
/// currently moved, and does not re-derive one by walking sibling
/// branches or loop back-edges a second time.
#[derive(Debug, Default, Clone)]
pub struct ResourceCheckResult {
    pub diagnostics: Vec<Diagnostic>,
    /// Every reachable exit edge's own checked cleanup list, keyed by
    /// the stable [`ExprId`] of whatever HIR node *is* that exit --
    /// an explicit `return`/`raise`/`break`/`continue` expression's own
    /// id, or (for a normal, implicit fallthrough) the exiting block's
    /// own id. A key absent here means that exact exit is unreachable,
    /// or needs no cleanup at all (an empty list is recorded instead of
    /// omitted whenever the exit is reachable but genuinely has nothing
    /// to clean up, so an absent key always means "unreachable", never
    /// "nothing to do").
    pub cleanup_edges: BTreeMap<ExprId, Vec<CleanupAction>>,
    /// Every checked observe-vs-transfer decision this module's own
    /// resource check actually made, keyed by the exact expression's
    /// own [`ExprId`] (`rfcs/0011`): a `value`/`mutable` binding's own
    /// initializer, an assignment's own value, a call/`Invoke`
    /// argument, a `defer` argument, or a `return`/`raise` operand.
    /// `nir::lower` reads this back directly rather than re-deriving
    /// the same verdict from the expression's own HIR shape or a
    /// callee's declared `take` flags a second time -- a key absent
    /// here for an expression `nir::lower` expects one for is always a
    /// bug in one stage or the other, never silently treated as
    /// `Observe`.
    pub consume_sites: BTreeMap<ExprId, ConsumeInfo>,
    /// Every `defer <expr>;` statement's own checked plan, keyed by
    /// that exact call expression's own [`ExprId`] -- see
    /// [`CheckedDeferPlan`].
    pub defer_plans: BTreeMap<ExprId, CheckedDeferPlan>,
}
