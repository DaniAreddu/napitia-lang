//! The affine resource state machine (`rfcs/0011`).

/// One resource-typed local binding's own current ownership state,
/// tracked per [`crate::hir::LocalId`] by [`super::flow`].
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
