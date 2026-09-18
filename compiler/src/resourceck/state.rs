//! The affine resource state machine (`rfcs/0011`, `rfcs/0013`).

use crate::hir::ObservationId;

/// One resource-typed local binding's own current ownership state,
/// tracked per [`crate::hir::LocalId`] by `super::flow`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceState {
    /// Owned, live: safe to read, move, drop, or observe.
    Available,
    /// Ownership transferred elsewhere (assignment, `return`, storage in
    /// another aggregate, a `take` argument). Using the old binding
    /// again is a compile-time diagnostic.
    Moved,
    /// Registered with a `defer` that has not yet run: still usable for
    /// ordinary reads, but may not be moved out from under the deferred
    /// action or explicitly dropped before it runs.
    DropScheduled,
    /// Destroyed, by an explicit `drop` or by implicit scope-exit
    /// destruction. Using or dropping it again is a compile-time
    /// diagnostic.
    Dropped,
    /// Checker-internal only, never user-visible: this binding's real
    /// state cannot be determined (an earlier diagnostic already fired
    /// against it, or two joined branches disagreed with no way to
    /// prove which one was taken). Suppresses further cascading
    /// diagnostics about the same root cause -- once a binding is
    /// `Error`, no further check against it fires.
    Error,
}

impl ResourceState {
    /// Combines this state with another reachable branch's own state for
    /// the same binding at a join point (`rfcs/0011`'s own "Joins"
    /// section). Identical states agree unambiguously; anything else
    /// becomes `Error`, since there is no single well-defined state left
    /// to check a later use against. `Error` is absorbing: once a branch
    /// already disagrees, more disagreement can't make it worse, and an
    /// already-diagnosed binding must never look "resolved" again purely
    /// because another branch happened to agree with one of the two
    /// conflicting readings.
    pub fn join(self, other: ResourceState) -> ResourceState {
        if self == other {
            self
        } else {
            ResourceState::Error
        }
    }
}

/// One structural place's own *complete* current status at a point in
/// the walk (`rfcs/0013`): [`ResourceState`]'s own recorded transition,
/// plus the two facts that are never recorded as a transition at all --
/// whether the place is partially moved (derived structurally from its
/// own descendants, `rfcs/0012`), and which observations are currently
/// holding it.
///
/// Deliberately a *query* result rather than a second state map:
/// `Observed` is not something a place is put into and later taken out
/// of, it is a fact about the lexically enclosing observation scopes at
/// this exact point, and `PartiallyMoved` is a fact about descendants.
/// Recording either as a stored `ResourceState` would make both
/// path-insensitive and would need a second, separately-fallible
/// "put it back" transition on every exit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlaceStatus {
    /// Owned, live, whole, and held by no observation: every ownership
    /// operation is available.
    Available,
    /// Owned and live, but one or more affine descendants have already
    /// been moved or dropped out of it (`rfcs/0012`). Usable for an
    /// unaffected sibling, a reinitialization, or structural cleanup --
    /// never as one whole value.
    PartiallyMoved,
    /// Ownership transferred elsewhere.
    Moved,
    /// Registered with a `defer` that has not yet run.
    DropScheduled,
    /// Destroyed.
    Dropped,
    /// Held by at least one currently-active observation whose own
    /// place overlaps this one (`rfcs/0013`) -- innermost last, in the
    /// exact order the scopes were opened, so a diagnostic naming "the
    /// observation holding this" always names the same one for the same
    /// program. Reading stays legal; every ownership operation does not,
    /// until every listed observation has ended.
    Observed(Vec<ObservationId>),
    /// See [`ResourceState::Error`].
    Error,
}
