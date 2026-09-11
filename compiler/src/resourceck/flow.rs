//! Flow-sensitive affine ownership tracking over one function body
//! (`rfcs/0011`) -- a direct, deterministic recursive walk of the
//! already-typed HIR tree (not a separate CFG construction: the surface
//! language's own control constructs -- `if`/`match`/`handle`/`while`/
//! `loop` -- already give every join and every loop back-edge an
//! unambiguous lexical shape, so a structured walk threading one
//! `HashMap<LocalId, ResourceState>` forward is exactly as expressive
//! as a general worklist would be here, without needing to first lower
//! to a graph only to walk it again). Bounded by the same recursion the
//! rest of this compiler's own AST-shaped passes already rely on
//! (`typeck::Checker::check_expr` walks the identical tree the same
//! way) -- there is no separate depth limit to enforce here that
//! parsing didn't already enforce on the input that produced this tree.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::diagnostics::Diagnostic;
use crate::hir::{
    ExprId, HirBinding, HirBlock, HirElse, HirExpr, HirFailurePattern, HirFunction, HirHandleArm,
    HirHandleArmKind, HirMatchArm, HirMatchArmBody, HirPattern, HirStmt, ItemId, LocalId,
    TypeParamId,
};
use crate::place::{FieldId, Place, Projection};
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
use crate::types::Ty;

use super::AffineContext;
use super::plan::{CheckedDeferPlan, CleanupAction, ConsumeInfo};
use super::state::ResourceState;

/// One resource-typed (or transitively affine) local's own current
/// structural state, keyed by the exact [`Place`] the state describes
/// (`rfcs/0012`): the bare root (empty projections) is exactly what a
/// whole `resource` local already was in Alpha 0.1.7, and a projected
/// key (`session.input`) is that same tracking generalized one field
/// at a time. A key absent from this map is always `Available` --
/// its own initial, untouched state, whether that is because it was
/// never affine enough to need an entry at all, or because it simply
/// has not been touched yet -- *except* when some ancestor place (a
/// shorter prefix sharing the same root) is itself recorded as
/// anything other than `Available`, in which case that ancestor's own
/// state dominates: moving/dropping a whole aggregate consumes every
/// field reachable through it, whether or not each one individually
/// has its own entry here (see [`FlowChecker::place_state`]).
type PlaceStates = HashMap<Place<LocalId>, ResourceState>;

mod codes {
    /// A resource-typed binding is read, moved, or dropped after it was
    /// already moved elsewhere.
    pub const USE_AFTER_MOVE: &str = "U0001";
    /// A resource-typed binding is used after it was already dropped
    /// (explicitly or implicitly at an enclosing scope's own exit).
    pub const USE_AFTER_DROP: &str = "U0002";
    /// `drop`ping a binding that is not currently `Available` (already
    /// moved, already dropped, or protected by a still-pending `defer`).
    pub const DOUBLE_DROP: &str = "U0003";
    /// A value a still-pending `defer` will need is moved (or explicitly
    /// dropped) before that `defer` actually runs.
    pub const MOVE_AFTER_DEFER_CAPTURED: &str = "U0004";
    /// An ordinary (non-`take`) parameter's own call-scoped observation
    /// is used in a position that would let it escape the call (moved
    /// into a binding, returned, stored in a constructed aggregate, or
    /// passed to another call's own `take` parameter).
    pub const OBSERVATION_ESCAPES: &str = "U0005";
    /// Two reachable branches of an `if`/`match`/`handle` disagree about
    /// a resource binding's own state (one moves it, another does not);
    /// a later unconditional use has no single state to check against.
    /// Also reported when two reachable `break` exits of the same loop
    /// disagree the same way: whatever runs after the loop has no
    /// single state to check either of them against.
    pub const INCONSISTENT_BRANCH_STATE: &str = "U0006";
    /// A `while`/`loop` body's own end state for a resource binding
    /// declared outside the loop disagrees with its state on entry --
    /// a second iteration could not safely reuse it.
    pub const LOOP_CARRIED_INVALIDATION: &str = "U0007";
    /// A resource-typed `handle` (any consuming position), or a
    /// resource-typed `if`/`match` in a consuming position other than
    /// `return`/the function's own implicit tail, whose own value is
    /// directly moved, bound, assigned, passed to a `take` parameter,
    /// stored in a constructed aggregate, or raised. `nir::lower` can
    /// only push a `return`'s own per-branch/per-arm cleanup into a
    /// nested `if`/`match`/block's own branches/arms (`rfcs/0011`);
    /// every other compound origin shape (and `handle` even as a
    /// `return`'s own operand) has no sound lowering this milestone, so
    /// it is rejected here rather than silently mis-lowered into a
    /// double-drop or a leak.
    pub const UNSUPPORTED_COMPOUND_RESOURCE_ORIGIN: &str = "U0008";
    // U0009 ("resource field extraction") retired: Alpha 0.1.8
    // (`rfcs/0012`) lifts the blanket rejection this code used to
    // enforce -- a resource-typed field is now tracked structurally,
    // field by field, through `resolve_place`/`check_place_read`/
    // `apply_place_move` below, rather than rejected outright. Never
    // reused for a different diagnostic: a stale code in an old build's
    // cached output
    // must never silently start meaning something else.
    /// A `mutable` resource-typed binding is reassigned while it still
    /// owns an available (or `defer`-protected) value (Blocker 4) --
    /// overwriting it without first moving or dropping the old value
    /// would leak it, since nothing would ever destroy it again.
    /// Reassignment is only accepted once the path-sensitive state
    /// proves the slot is provably empty (`Moved`/`Dropped`) on every
    /// incoming path.
    pub const REASSIGNMENT_OF_LIVE_RESOURCE: &str = "U0010";
    /// A resource-typed *temporary* -- freshly constructed or returned
    /// from a call, never itself bound to an owned local -- appears
    /// somewhere its own value would just be discarded once evaluated
    /// (Blocker 3): a bare discarded statement-expression, the base of
    /// a field projection, or an argument to an ordinary (non-`take`)
    /// parameter. Only `nir::lower`'s own `cleanup_actions` list ever
    /// schedules a resource's destruction, and only a binding or a
    /// pattern ever registers an entry on it -- a temporary reaching
    /// any of these positions has no binding at all, so nothing would
    /// ever destroy it. `value`/`mutable`/`return`/`drop`/a `take`
    /// argument/a consuming `defer` are each their own already-correct
    /// sink, immediately capturing or transferring the temporary; this
    /// is every other position.
    pub const RESOURCE_TEMPORARY_LEAK: &str = "U0011";
    /// A `defer <call>;`'s own callee has a recorded per-parameter
    /// `take` flag count that does not match this exact call's own
    /// argument count (`rfcs/0011`) -- always unreachable for a program
    /// that actually passed `typeck`'s own arity check first (a direct
    /// caller feeding hand-built, never-type-checked HIR straight to
    /// this stage is the only way to reach it). Never silently treated
    /// as "every argument merely observes": a checked plan is not
    /// recorded for this exact `defer` at all when this fires, so
    /// `nir::lower` independently rejects it too, with its own
    /// missing-plan internal error.
    pub const MALFORMED_DEFER_CALLEE_SIGNATURE: &str = "U0012";
    /// An ordinary call's own callee resolves directly to a declared
    /// function/extend-method (`HirExpr::Function`), but this module's
    /// own `take_flags` table has no entry for it at all, or that
    /// entry's own length disagrees with this exact call's argument
    /// count (`rfcs/0011`) -- always unreachable for HIR that actually
    /// passed `hir::lower`'s own name resolution and `typeck`'s own
    /// arity check first; reachable only through hand-built HIR fed
    /// straight to this stage. Never silently treated as "every
    /// argument merely observes": no `consume_sites` entries are
    /// recorded for this call's own arguments at all when this fires.
    pub const MALFORMED_CALLEE_TAKE_FLAGS: &str = "U0013";
    /// A partially-moved aggregate (one or more of its own affine fields
    /// already moved out) is used as a whole value -- observed,
    /// returned, transferred, copied, or passed as a whole (`rfcs/0012`).
    /// Only accessing an unaffected field, reinserting into an empty
    /// one, or structurally dropping the remaining owned fields is still
    /// permitted on it.
    pub const PARTIAL_PARENT_USED_AS_WHOLE: &str = "U0014";
}

pub use codes::*;

/// What position an expression's own value is being checked in
/// (`rfcs/0011`, Blocker 2) -- threaded down through every recursive
/// [`FlowChecker`] walk so a resource-typed `if`/`match`/`handle`/block
/// nested arbitrarily deep still resolves the *same* underlying
/// question at its own terminal (usually a bare local) reference: is
/// this read, or consumed, and if consumed, by a position `nir::lower`
/// can actually represent a compound (branch-specific) origin for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConsumeKind {
    /// An ordinary, non-consuming observation -- the default for any
    /// subexpression that isn't itself a move/return/store/etc.
    Read,
    /// Consumed by `return`, or the function's own implicit tail
    /// return. `nir::lower` pushes this sink into each reachable
    /// branch/arm of a nested `if`/`match`/`handle`/block separately
    /// (Blocker 2), so a resource-typed compound origin is accepted
    /// here even when its branches/arms resolve to different underlying
    /// locals.
    Return,
    /// Consumed by anything else that transfers ownership: a `value`/
    /// `mutable` binding's own initializer, an assignment's own value,
    /// a `take` argument, a constructed aggregate's own field, or
    /// `raise`'s own operand. `nir::lower` has no per-branch sink for
    /// any of these yet, so a compound (`if`/`match`/`handle`) origin
    /// is rejected outright here; only an expression that bottoms out
    /// directly at a single resource-producing site (a bare local, or
    /// a fresh call/construction) is accepted.
    Other,
}

/// One `while`/`loop` statement's own accumulated exit states
/// (`rfcs/0011`, Blocker 2): every `break`'s own live state at the
/// point it executes (each contributes to the *after*-loop state), and
/// every `continue`'s own live state (each contributes to the loop's
/// own backedge, exactly like the body's ordinary fallthrough end
/// does) -- captured separately from the body's own sequential walk
/// since neither actually reaches "the textual end of the body," the
/// only point the previous, single-state implementation ever compared
/// against loop entry.
#[derive(Default)]
struct LoopFrame {
    break_states: Vec<PlaceStates>,
    continue_states: Vec<PlaceStates>,
    /// `pending_cleanup.len()` at the point this loop's own body began
    /// being checked -- every entry registered at or after this index
    /// is this exact iteration's own responsibility (the body's own
    /// top-level bindings/defers, or any nested scope's), so a
    /// `break`/`continue` reached inside it only ever needs to record
    /// `pending_cleanup[cleanup_marker..]`, mirroring `nir::lower`'s
    /// own `LoopCtx::cleanup_marker`.
    cleanup_marker: usize,
    /// `defer_scopes.len()` at the point this loop's own body began
    /// being checked -- every scope pushed at or after this index
    /// belongs to this exact iteration (the body's own top-level scope,
    /// or any block nested inside it), and is exited -- not merely
    /// truncated away later by its own `check_block_ctx_body`'s normal
    /// pop -- by a `break`/`continue` reached inside it. A `break`'s/
    /// `continue`'s own recorded exit state must reflect every one of
    /// those scopes' own observing-`defer` protections already released
    /// (see [`Self::released_snapshot`]) *before* it is stored, or code
    /// reachable after the loop (for `break`) or the next iteration
    /// (for `continue`) would wrongly still see a resource as
    /// `defer`-protected past the exact scope that protection was only
    /// ever supposed to outlive.
    defer_scope_marker: usize,
}

pub struct FlowChecker<'a> {
    local_types: &'a HashMap<LocalId, Ty>,
    expr_types: &'a HashMap<crate::hir::ExprId, Ty>,
    affine_items: &'a HashSet<ItemId>,
    /// Every declared variant's own `ItemId` (`rfcs/0012`) -- a
    /// variant's own payload is never individually addressable outside a
    /// pattern match (there is no `.field` syntax for it, unlike a
    /// record), so which case is actually live at a given point is not
    /// something static analysis can know in general. An affine
    /// variant-typed place is therefore always tracked, and structurally
    /// dropped, as one opaque whole-value unit -- see [`Self::
    /// structural_drop_targets`]/[`Self::place_is_wholly_available`],
    /// which consult this set specifically so neither ever treats
    /// [`AffineContext::aggregate_field_types`]'s own *flattened,
    /// cross-case* payload list for a variant as if it were one record's
    /// own named field vector.
    variant_items: &'a HashSet<ItemId>,
    /// Every known function/extend-method's own per-parameter `take`
    /// flags, by `ItemId`, in declared order -- read back to decide
    /// whether a `Call` argument transfers ownership or merely observes
    /// (`rfcs/0011`). A callee absent here (an unresolved name, a
    /// variant case constructor, a protocol method whose concrete
    /// implementation isn't known syntactically) is treated as having
    /// no `take` parameters at all, matching this milestone's own
    /// observation-by-default rule.
    take_flags: &'a HashMap<ItemId, Vec<bool>>,
    /// `typeck`'s own transitive-affinity metadata (`rfcs/0012`),
    /// bundled -- see [`AffineContext`]'s own doc comment for what each
    /// field is and why this stage never re-derives it. Read through
    /// [`Self::aggregate_field_types`]/[`Self::declared_resources`]/
    /// [`Self::item_type_params`]/[`Self::field_projections`] accessors
    /// below rather than `self.affine.<field>` directly, purely so every
    /// call site keeps reading the same as it did before this was
    /// bundled.
    affine: &'a AffineContext<'a>,
    source: SourceId,
    interner: &'a Interner,
    diagnostics: &'a mut Vec<Diagnostic>,
    /// Every resource-typed (or transitively affine) *owned* place's
    /// own current structural state -- take parameters and `value`/
    /// `mutable` bindings' own root place, and every affine field
    /// reached through one that has actually been touched (moved,
    /// dropped, or reinitialized) at least once. A key absent here is
    /// either not affine at all, or still in its own initial,
    /// untouched `Available` state (see [`Self::place_state`], which
    /// also accounts for a shorter ancestor place dominating a key that
    /// is technically present but whose own root/ancestor has already
    /// been consumed as a whole).
    states: PlaceStates,
    /// Every resource-typed *ordinary* (non-`take`) parameter -- never
    /// entered into `states` at all, since the callee never owns it;
    /// tracked separately purely to reject an attempt to move, return,
    /// store, or otherwise let it escape the call.
    observing: HashSet<LocalId>,
    /// One [`LoopFrame`] per lexically-enclosing `while`/`loop`, innermost
    /// last (Blocker 2) -- `break`/`continue` always targets the
    /// innermost one, exactly like `nir::lower`'s own loop-exit lowering
    /// already does; a nested loop's own frame is pushed/popped around
    /// only its own body walk, so an inner `break` never contributes to
    /// an outer loop's own accumulated exits.
    loop_stack: Vec<LoopFrame>,
    /// One entry per lexically-enclosing block, innermost last (Blocker
    /// 9): every resource local a `defer` directly inside *that* block
    /// promoted from `Available` to `DropScheduled` purely by observing
    /// it (never one a *consuming* defer already moved -- that local
    /// never re-enters `Available` at all, so releasing it here would be
    /// a no-op, see [`Self::check_defer`]). Released back to `Available`
    /// the moment that exact block's own [`Self::check_block_ctx`]
    /// finishes, on every exit from it -- an observing defer's own
    /// protection only ever lasts until the deferred call itself would
    /// actually run.
    defer_scopes: Vec<HashSet<Place<LocalId>>>,
    /// Every bare `loop`'s own body block id (Blocker: infinite-loop
    /// reachability) for which [`Self::finish_loop`] found no reachable
    /// `break` at all -- a `loop` with no exit of its own genuinely never
    /// falls through, exactly like `return`/`raise`, so [`Self::
    /// stmt_diverges`] must treat it the same way: nothing lexically
    /// after it in the same block is reachable either. A `while` is
    /// never a member (its own condition-false edge always reaches
    /// after it, regardless of `break`), and a nested loop's own body id
    /// never collides with an enclosing one's.
    diverging_loops: HashSet<ExprId>,
    /// Every resource local's own implicit destruction, and every
    /// `defer`'s own registration, in the exact order this walk
    /// encountered them -- the sole, authoritative source `nir::lower`
    /// builds every cleanup instruction it emits from (`rfcs/0011`; see
    /// `resourceck::plan::CleanupAction`). A single flat, function-wide
    /// list: a nested scope's own entries are appended onto the same
    /// list as its enclosing scopes', and truncated back off again once
    /// that exact scope's own snapshot has been recorded (see
    /// [`Self::record_exit`]), so an enclosing scope's later snapshot
    /// never includes (and never re-records) them.
    pending_cleanup: Vec<CleanupAction>,
    /// Every reachable exit's own checked, ordered cleanup list, keyed
    /// by the stable id of whatever HIR node *is* that exit (an
    /// explicit `return`/`raise`/`break`/`continue` expression's own
    /// id, a plain block's own id for its normal fallthrough, or a
    /// `match`/`handle` arm's own body id for that arm's own normal
    /// completion). This is `ResourceCheckResult::cleanup_edges` in
    /// progress -- exported once this function's own check finishes
    /// (see [`Self::into_cleanup_edges`]).
    cleanup_edges: BTreeMap<ExprId, Vec<CleanupAction>>,
    /// Every checked observe-vs-transfer decision this function's own
    /// check actually made, keyed by the exact expression's own
    /// `ExprId` -- see [`super::plan::ResourceCheckResult::
    /// consume_sites`].
    consume_sites: BTreeMap<ExprId, ConsumeInfo>,
    /// Every `defer` statement's own checked plan -- see
    /// [`super::plan::ResourceCheckResult::defer_plans`].
    defer_plans: BTreeMap<ExprId, CheckedDeferPlan>,
    /// The next `CheckedDeferPlan::registration_order` value to hand
    /// out, incremented once per `defer` actually recorded -- this
    /// function's own `defer`s are numbered in the exact order this
    /// walk encounters them, matching `pending_cleanup`'s own append
    /// order (`rfcs/0011`).
    next_defer_registration: u32,
}

impl<'a> FlowChecker<'a> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        local_types: &'a HashMap<LocalId, Ty>,
        expr_types: &'a HashMap<crate::hir::ExprId, Ty>,
        affine_items: &'a HashSet<ItemId>,
        variant_items: &'a HashSet<ItemId>,
        take_flags: &'a HashMap<ItemId, Vec<bool>>,
        affine: &'a AffineContext<'a>,
        source: SourceId,
        interner: &'a Interner,
        diagnostics: &'a mut Vec<Diagnostic>,
    ) -> Self {
        Self {
            local_types,
            expr_types,
            affine_items,
            variant_items,
            take_flags,
            affine,
            source,
            interner,
            diagnostics,
            states: HashMap::new(),
            observing: HashSet::new(),
            loop_stack: Vec::new(),
            defer_scopes: Vec::new(),
            diverging_loops: HashSet::new(),
            pending_cleanup: Vec::new(),
            cleanup_edges: BTreeMap::new(),
            consume_sites: BTreeMap::new(),
            defer_plans: BTreeMap::new(),
            next_defer_registration: 0,
        }
    }

    /// Records `id`'s own checked observe-vs-transfer decision
    /// (`rfcs/0011`) -- only ever called for a resource-typed
    /// expression; `nir::lower` never needs (and this never records)
    /// anything for an ordinary value, which is always freely copyable
    /// regardless of context.
    fn record_consume(&mut self, id: ExprId, info: ConsumeInfo) {
        self.consume_sites.insert(id, info);
    }

    /// Consumes this checker, handing its own checked plan to
    /// [`super::check_module`] for merging into the module-wide
    /// [`super::ResourceCheckResult`]. Called once this checker's own
    /// function/extend-method has been fully checked.
    #[allow(clippy::type_complexity)]
    pub fn into_plan(
        self,
    ) -> (
        BTreeMap<ExprId, Vec<CleanupAction>>,
        BTreeMap<ExprId, ConsumeInfo>,
        BTreeMap<ExprId, CheckedDeferPlan>,
    ) {
        (self.cleanup_edges, self.consume_sites, self.defer_plans)
    }

    pub fn check_function(&mut self, f: &HirFunction) {
        for param in &f.params {
            if !self.is_resource_local(param.local) {
                continue;
            }
            if param.take {
                let place = Place::root(param.local);
                self.states.insert(place.clone(), ResourceState::Available);
                self.pending_cleanup.push(CleanupAction::Drop(place));
            } else {
                self.observing.insert(param.local);
            }
        }
        // The function's own top-level scope is *always* a marker-0
        // exit (`rfcs/0011`): every `take` parameter's own implicit
        // destruction above must be visible to this exact snapshot,
        // exactly like `nir::lower`'s own `emit_cleanup` (as opposed to
        // `emit_cleanup_since`) always replays the *whole* flat list
        // from the very start, not just whatever this one block's own
        // marker would otherwise cover.
        self.check_block_ctx_body(&f.body, ConsumeKind::Return);
        if !self.diverges(f.body.id) {
            self.record_exit(f.body.id, 0);
        }
    }

    /// Expands `self.pending_cleanup[marker..]` down to what is still
    /// actually owed at this exact point -- reversed, since cleanup
    /// replays last registered first. A `Drop(root)` entry (registered
    /// once, when the local itself became owned) expands here, fresh,
    /// into every place `structural_drop_targets` proves is still
    /// actually live under it right now -- an aggregate registered as a
    /// single whole-value obligation may need zero, one, or several
    /// concrete destroy actions by the time this exact exit is reached,
    /// depending what has been moved out of it since. A `Defer` entry
    /// is always kept: its own presence here already means its scope
    /// has not released it yet.
    fn snapshot_cleanup(&self, marker: usize) -> Vec<CleanupAction> {
        self.pending_cleanup[marker..]
            .iter()
            .rev()
            .flat_map(|action| match action {
                CleanupAction::Drop(place) => self
                    .structural_drop_targets(place)
                    .into_iter()
                    .map(CleanupAction::Drop)
                    .collect::<Vec<_>>(),
                CleanupAction::Defer(id) => vec![CleanupAction::Defer(*id)],
            })
            .collect()
    }

    /// Records `id`'s own checked cleanup list (`rfcs/0011`) -- an
    /// empty list is recorded just the same as a non-empty one, so a
    /// reachable exit with nothing to clean up is still distinguishable
    /// from one that is simply unreachable (absent from the map
    /// entirely).
    fn record_exit(&mut self, id: ExprId, marker: usize) {
        let actions = self.snapshot_cleanup(marker);
        self.cleanup_edges.insert(id, actions);
    }

    /// A copy of `self.states` with every scope in
    /// `self.defer_scopes[from_scope..]`'s own observing-`defer`
    /// protection already released -- exactly the reset
    /// `check_block_ctx_body`'s own normal pop would apply to each of
    /// those scopes in turn, applied here instead to a `break`'s/
    /// `continue`'s own *recorded exit state*, since neither actually
    /// waits for those scopes to pop normally: both exit them early,
    /// right here, before `check_block_ctx_body` ever gets a chance to
    /// (`rfcs/0011`). Never mutates `self.defer_scopes`/`self.states`
    /// themselves -- those still belong to whatever scope keeps walking
    /// after this exact point (a sibling statement in an enclosing,
    /// *not*-exited block; dead code after an unconditional break/
    /// continue is never walked at all, see `stmt_diverges`), which
    /// must still see its own protection exactly as it was.
    fn released_snapshot(&self, from_scope: usize) -> PlaceStates {
        let mut states = self.states.clone();
        for scope in &self.defer_scopes[from_scope.min(self.defer_scopes.len())..] {
            for place in scope {
                if let Some(ResourceState::DropScheduled) = states.get(place) {
                    states.insert(place.clone(), ResourceState::Available);
                }
            }
        }
        states
    }

    fn is_resource_local(&self, local: LocalId) -> bool {
        self.local_types
            .get(&local)
            .is_some_and(|ty| self.is_affine(ty))
    }

    /// `true` iff `ty` is transitively affine (`rfcs/0012`): `self.
    /// affine_items` already *is* the transitive set for a plain,
    /// non-generic `Ty::Named` (computed once by `super::check_module`,
    /// mirroring `typeck::Checker::is_affine`'s own declaration-time
    /// query); a `Ty::Applied` instead substitutes its own concrete
    /// arguments into the declaration's field types fresh, the same way
    /// `typeck`'s own equivalent does, since the same generic
    /// declaration can be affine for one instantiation and not another.
    /// Place *decomposition* (`resolve_place`/`structural_drop_targets`)
    /// is intentionally narrower than this: a generic instantiation is
    /// tracked as a single whole-value place only, exactly like Alpha
    /// 0.1.7's own resources always were, never decomposed field by
    /// field -- this query alone still needs to answer soundly for one,
    /// so `take`/observation/whole-move accounting stays correct even
    /// though per-field tracking does not extend into it.
    fn is_affine(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Named(item, _) => self.affine_items.contains(item),
            Ty::Applied(item, args) => {
                if self.affine.declared_resources.contains(item) {
                    return true;
                }
                // Missing or arity-disagreeing generic metadata is never
                // an *empty* substitution (`rfcs/0008`): an
                // unsubstituted `Ty::Param` answers `false`, which
                // would let a genuinely affine instantiation be treated
                // as a freely-copyable value with no ownership to
                // track. Fail closed -- treat it as affine, so every
                // ownership obligation is still demanded.
                let type_params = self.affine.item_type_params.get(item);
                let Some(type_params) = type_params.filter(|p| p.len() == args.len()) else {
                    return true;
                };
                let subst: HashMap<TypeParamId, Ty> = type_params
                    .iter()
                    .copied()
                    .zip(args.iter().cloned())
                    .collect();
                self.affine
                    .aggregate_field_types
                    .get(item)
                    .into_iter()
                    .flatten()
                    .any(|fty| self.is_affine(&crate::types::substitute(fty, &subst)))
            }
            _ => false,
        }
    }

    /// This place's own current structural state (`rfcs/0012`): the
    /// exact key's own recorded state if present, but dominated by the
    /// *shortest* ancestor prefix (sharing the same root) that is
    /// itself recorded as anything other than `Available` -- moving or
    /// dropping a whole aggregate consumes every field reachable
    /// through it, whether or not each one individually ever got its
    /// own map entry. A key with no recorded ancestor or exact entry at
    /// all is simply still in its own initial, untouched `Available`
    /// state.
    fn place_state(&self, place: &Place<LocalId>) -> ResourceState {
        for len in 0..=place.projections.len() {
            let prefix = Place {
                root: place.root,
                projections: place.projections[..len].to_vec(),
            };
            if let Some(state) = self.states.get(&prefix)
                && *state != ResourceState::Available
            {
                return *state;
            }
        }
        ResourceState::Available
    }

    /// `true` iff every place reachable through `place` (`place` itself,
    /// and every affine descendant field `structural_drop_targets` could
    /// ever reach) is currently `Available` -- what a *whole-value* use
    /// (observed, returned, transferred, copied, passed as a whole)
    /// requires, but a mere child access, a reinsertion into one empty
    /// child, or a structural drop of the remaining owned fields does
    /// not (`rfcs/0012`). `ty` is `place`'s own current type -- the
    /// caller already has it (from `local_types`/`aggregate_field_types`)
    /// and re-resolving it here a second time would risk disagreeing
    /// with the caller's own idea of what `place` even refers to.
    fn place_is_wholly_available(&self, place: &Place<LocalId>, ty: &Ty) -> bool {
        if self.place_state(place) != ResourceState::Available {
            return false;
        }
        // A variant (whose live case is only a runtime fact), or an
        // item with malformed generic metadata, is not decomposed at
        // all -- `place_state` above already answered the whole
        // question for it. A generic *record* instantiation now is
        // decomposed, through its own substituted field types.
        let Some((item, fields)) = self.decomposable_fields(ty) else {
            return true;
        };
        fields
            .iter()
            .enumerate()
            .filter(|(_, fty)| self.is_affine(fty))
            .all(|(index, fty)| {
                self.place_is_wholly_available(&place.field(item, FieldId(index as u32)), fty)
            })
    }

    /// Sets `place`'s own leaf state, first clearing every strictly
    /// deeper entry it now supersedes -- moving or dropping `place` as
    /// a whole consumes everything reachable through it, so a stale,
    /// finer-grained entry for one of its own descendants (recorded
    /// before this exact move/drop) must never again be consulted; the
    /// new state at `place` itself now dominates all of them via
    /// [`Self::place_state`]'s own prefix walk regardless, but removing
    /// them too keeps the map's own size bounded by how many places are
    /// *actually* still individually tracked, not how many ever were.
    fn set_place_state(&mut self, place: &Place<LocalId>, state: ResourceState) {
        self.states
            .retain(|key, _| key.root != place.root || !place.is_ancestor_of(key) || key == place);
        self.states.insert(place.clone(), state);
    }

    /// Resolves `expr` to the stable [`Place`] it names, if it names one
    /// at all (`rfcs/0012`): a bare local, or a `Field` access chain
    /// rooted in one, through nothing but further `Field` accesses --
    /// never through a call, a construction, or any other expression
    /// that produces a fresh, not-yet-owned value with no place of its
    /// own. `None` for anything else (a temporary): extracting an
    /// affine field out of one would leak its own siblings, since
    /// nothing owns the temporary itself to structurally clean the rest
    /// of it up -- the caller falls back to `reject_leaked_temporary`
    /// for that case, exactly as Alpha 0.1.7 already does for reading a
    /// non-affine field off one.
    fn resolve_place(&self, expr: &HirExpr) -> Option<Place<LocalId>> {
        match expr {
            HirExpr::Local { local, .. } => Some(Place::root(*local)),
            HirExpr::Field { id, base, .. } => {
                let base_place = self.resolve_place(base)?;
                let (owner, field) = self.affine.field_projections.get(id).copied()?;
                Some(base_place.field(owner, FieldId(field as u32)))
            }
            _ => None,
        }
    }

    /// `place`'s own current type, resolved the same way a place is
    /// built: `local_types` for the root, then one `aggregate_field_types`
    /// lookup per projection. `None` only for malformed metadata (an
    /// owner/field this stage's own checked `field_projections` should
    /// never actually disagree with `aggregate_field_types` about, since
    /// both ultimately come from the same `typeck` pass).
    fn place_ty(&self, place: &Place<LocalId>) -> Option<Ty> {
        let mut ty = self.local_types.get(&place.root)?.clone();
        for projection in &place.projections {
            let Projection::Field { owner, field } = projection else {
                return None;
            };
            // The owner's own type arguments come from this place's
            // *current* type at this exact step, and are substituted
            // into the selected field's declared type before the walk
            // continues from it (`rfcs/0008`, `rfcs/0012`) -- otherwise
            // `Box[File]`'s own `item` field would resolve to a bare,
            // never-affine `Ty::Param`.
            let args: Vec<Ty> = match &ty {
                Ty::Named(item, _) if item == owner => Vec::new(),
                Ty::Applied(item, args) if item == owner => args.clone(),
                _ => return None,
            };
            let field_ty = self
                .affine
                .aggregate_field_types
                .get(owner)?
                .get(field.0 as usize)?
                .clone();
            ty = self.substitute_field(*owner, &args, &field_ty)?;
        }
        Some(ty)
    }

    /// `field_ty` with `owner`'s own declared type parameters replaced
    /// by `args` (`rfcs/0008`). `None` -- never a partial or empty
    /// substitution -- when `owner` has no recorded type-parameter list
    /// at all (an item `typeck` never registered; every real
    /// record/variant always gets one, empty for a non-generic
    /// declaration) or when its arity disagrees with `args`: an
    /// unsubstituted `Ty::Param` escaping here would answer "not
    /// affine" for a genuinely affine field.
    fn substitute_field(&self, owner: ItemId, args: &[Ty], field_ty: &Ty) -> Option<Ty> {
        let params = self.affine.item_type_params.get(&owner)?;
        if params.len() != args.len() {
            return None;
        }
        let subst: HashMap<TypeParamId, Ty> =
            params.iter().copied().zip(args.iter().cloned()).collect();
        Some(crate::types::substitute(field_ty, &subst))
    }

    /// `place`'s own declared aggregate item, its concrete type
    /// arguments, and its already-substituted field types -- the shared
    /// shape both [`Self::place_is_wholly_available`] and
    /// [`Self::structural_drop_targets`] decompose an affine aggregate
    /// through, generic or not. `None` for anything that is not a
    /// decomposable record/resource: a primitive, a variant (whose live
    /// case is a runtime fact -- see `variant_items`), or an item with
    /// malformed generic metadata.
    fn decomposable_fields(&self, ty: &Ty) -> Option<(ItemId, Vec<Ty>)> {
        let (item, args): (ItemId, Vec<Ty>) = match ty {
            Ty::Named(item, _) => (*item, Vec::new()),
            Ty::Applied(item, args) => (*item, args.clone()),
            _ => return None,
        };
        if self.variant_items.contains(&item) {
            return None;
        }
        let declared = self.affine.aggregate_field_types.get(&item)?;
        let substituted = declared
            .iter()
            .map(|fty| self.substitute_field(item, &args, fty))
            .collect::<Option<Vec<Ty>>>()?;
        Some((item, substituted))
    }

    /// Every place `place` structurally owns that is currently still
    /// `Available` -- what a structural `drop`/scope-exit destruction of
    /// `place` must actually destroy, in the exact deterministic order
    /// `rfcs/0012` specifies: an aggregate's own affine fields, in
    /// *reverse* declaration order, each recursively expanded the same
    /// way first, followed by `place` itself *only* if `place`'s own
    /// type is a declared `resource` (an ordinary, non-`resource`
    /// aggregate has no separate runtime identity of its own to destroy
    /// beyond its fields). A place already `Moved`/`Dropped`/`Error`
    /// contributes nothing at all -- already someone else's
    /// responsibility, or already diagnosed. A generic (`Ty::Applied`)
    /// place is never decomposed (see `is_affine`'s own doc comment):
    /// it contributes itself alone, exactly like Alpha 0.1.7's own
    /// whole-value resources always did.
    fn structural_drop_targets(&self, place: &Place<LocalId>) -> Vec<Place<LocalId>> {
        // `DropScheduled` still needs destroying here exactly like
        // `Available` does -- it means only that an observing `defer`
        // has *already run* by the time this exact exit replays cleanup
        // (`check_defer` promotes straight back to `Available` once its
        // own protecting scope ends, so a place already reaching a real
        // exit while still `DropScheduled` is one whose defer is part
        // of *this same* cleanup replay, ordered before it): the
        // resource is still owned and must still be destroyed, just not
        // moved or dropped *early*, out from under a pending defer that
        // still needs it -- `apply_place_move`/`check_consume` already
        // separately reject that.
        if !matches!(
            self.place_state(place),
            ResourceState::Available | ResourceState::DropScheduled
        ) {
            return Vec::new();
        }
        let Some(ty) = self.place_ty(place) else {
            return Vec::new();
        };
        // A variant's own live payload can only be identified at
        // runtime (whichever case is actually active) -- never
        // decomposed into `aggregate_field_types`'s own flattened,
        // cross-case payload list as if it were one record's own named
        // fields (see `variant_items`'s own doc comment). Contributed
        // as a single opaque target regardless of `declared_resources`
        // (a variant is never itself declared `resource`, but still
        // needs exactly one "destroy whatever is actually live inside"
        // action of its own): `nir::lower` reads this back as a place
        // to move-then-drop as a whole, and the interpreter recursively
        // destroys only the active case's own affine payload fields
        // when that drop actually runs. Same single-target treatment
        // for an item with malformed generic metadata, which is never
        // decomposed on a substitution nobody could build.
        let Some((item, fields)) = self.decomposable_fields(&ty) else {
            return vec![place.clone()];
        };
        let mut targets = Vec::new();
        for (index, field_ty) in fields.iter().enumerate().rev() {
            if self.is_affine(field_ty) {
                targets.extend(
                    self.structural_drop_targets(&place.field(item, FieldId(index as u32))),
                );
            }
        }
        if self.affine.declared_resources.contains(&item) {
            targets.push(place.clone());
        }
        targets
    }

    /// The field name/span this diagnostic is reported against --
    /// `expr` is always the exact `HirExpr::Field` [`Self::resolve_place`]
    /// just resolved `place` from.
    fn field_name_and_span(expr: &HirExpr) -> (Symbol, Span) {
        match expr {
            HirExpr::Field { name, span, .. } => (*name, *span),
            _ => unreachable!("only ever called with the `HirExpr::Field` `resolve_place` saw"),
        }
    }

    /// Validates an *observing* use of `place` (`rfcs/0012`): still
    /// usable for ordinary reads and further projection while
    /// `Available`/`DropScheduled`, but a use-after-move or
    /// use-after-drop is reported the same way a whole local's would
    /// be, since it is exactly the same underlying violation, now at a
    /// finer grain. Never transitions `place`'s own state -- observing
    /// never consumes.
    fn check_place_read(&mut self, place: &Place<LocalId>, expr: &HirExpr) {
        let (name, span) = Self::field_name_and_span(expr);
        match self.place_state(place) {
            ResourceState::Available | ResourceState::DropScheduled | ResourceState::Error => {}
            ResourceState::Moved => {
                self.diagnose(
                    USE_AFTER_MOVE,
                    span,
                    format!(
                        "`{}` was already moved and cannot be used",
                        self.interner.resolve(name)
                    ),
                    "use after move",
                );
                self.set_place_state(place, ResourceState::Error);
            }
            ResourceState::Dropped => {
                self.diagnose(
                    USE_AFTER_DROP,
                    span,
                    format!(
                        "`{}` was already dropped and cannot be used",
                        self.interner.resolve(name)
                    ),
                    "use after drop",
                );
                self.set_place_state(place, ResourceState::Error);
            }
        }
    }

    /// Transfers ownership of `place` (`rfcs/0012`): the structural
    /// generalization of [`Self::check_consume`], for an individual
    /// affine field rather than a whole local. Moving a child updates
    /// only that child's own entry -- a sibling field, and the parent's
    /// own ability to be structurally dropped later, are both
    /// completely unaffected (the parent's own *whole-value* use is
    /// separately gated by [`Self::reject_partial_whole_use`]).
    fn apply_place_move(&mut self, place: &Place<LocalId>, expr: &HirExpr) {
        let (name, span) = Self::field_name_and_span(expr);
        match self.place_state(place) {
            ResourceState::Available => {
                self.set_place_state(place, ResourceState::Moved);
            }
            ResourceState::Error => {}
            ResourceState::Moved => {
                self.diagnose(
                    USE_AFTER_MOVE,
                    span,
                    format!(
                        "`{}` was already moved and cannot be moved again",
                        self.interner.resolve(name)
                    ),
                    "use after move",
                );
                self.set_place_state(place, ResourceState::Error);
            }
            ResourceState::Dropped => {
                self.diagnose(
                    USE_AFTER_DROP,
                    span,
                    format!(
                        "`{}` was already dropped and cannot be moved",
                        self.interner.resolve(name)
                    ),
                    "use after drop",
                );
                self.set_place_state(place, ResourceState::Error);
            }
            ResourceState::DropScheduled => {
                self.diagnose(
                    MOVE_AFTER_DEFER_CAPTURED,
                    span,
                    format!(
                        "`{}` is still needed by a pending `defer` and cannot be moved away",
                        self.interner.resolve(name)
                    ),
                    "moved before its defer ran",
                );
                self.set_place_state(place, ResourceState::Error);
            }
        }
    }

    fn diverges(&self, id: crate::hir::ExprId) -> bool {
        matches!(self.expr_types.get(&id), Some(Ty::Never))
    }

    fn diagnose(&mut self, code: &'static str, span: Span, message: String, label: &'static str) {
        self.diagnostics
            .push(Diagnostic::error(code, self.source, span, message).with_primary_label(label));
    }

    fn local_name(&self, local: LocalId, fallback: crate::symbol::Symbol) -> String {
        let _ = local;
        self.interner.resolve(fallback).to_string()
    }

    // -- Statements ----------------------------------------------------

    /// Checks `block`'s own statements (always `ConsumeKind::Read`
    /// contexts on their own -- a statement's value, if any, is always
    /// discarded), then its own tail expression, if any, in `kind`'s
    /// own context -- a block is transparent to whatever consumes its
    /// own value (Blocker 2): `{ ...; tail }` used as a `return`'s own
    /// operand consumes `tail` exactly like a bare `return tail`
    /// would, not merely reads it.
    ///
    /// Also `block`'s own defer scope (Blocker 9): every `defer` this
    /// exact block directly registers (not one nested inside a further
    /// block/if/loop of its own, which already released its own defers
    /// by the time control returns here) stops protecting whatever it
    /// only *observes* the moment this block's own walk ends, on every
    /// exit from it -- normal fallthrough, or an early return through
    /// [`stmt_diverges`]'s own truncation -- exactly like the deferred
    /// call itself would actually run at real scope exit.
    fn check_block_ctx(&mut self, block: &HirBlock, kind: ConsumeKind) {
        let marker = self.pending_cleanup.len();
        self.check_block_ctx_body(block, kind);
        // Recorded only when this block's own normal end is genuinely
        // reachable (Blocker 11): a block that itself diverges (every
        // path through it ends in `return`/`raise`/`break`/`continue`)
        // has no real fallthrough for anything to replay here at all --
        // whatever exit it actually took already recorded its own
        // cleanup list separately.
        if !self.diverges(block.id) {
            self.record_exit(block.id, marker);
        }
        self.pending_cleanup.truncate(marker);
    }

    /// Like [`Self::check_block_ctx`], but manages neither
    /// `pending_cleanup`'s own marker nor its own recorded exit --
    /// only this block's own defer-scope release. Used by a caller that
    /// already owns a wider marker of its own spanning more than just
    /// this one block (a `match`/`handle` arm's own pattern binding
    /// plus its block body, recorded together as that arm's own single
    /// combined exit -- see [`Self::check_match_arms`]/[`Self::
    /// check_handle_arms`]), and by [`Self::check_function`] (the
    /// function's own top-level scope is always a marker-0 exit, never
    /// a fresh one of its own).
    fn check_block_ctx_body(&mut self, block: &HirBlock, kind: ConsumeKind) {
        self.defer_scopes.push(HashSet::new());
        self.check_block_ctx_inner(block, kind);
        let scope = self.defer_scopes.pop().expect("pushed immediately above");
        for place in scope {
            if let Some(ResourceState::DropScheduled) = self.states.get(&place) {
                self.states.insert(place, ResourceState::Available);
            }
        }
    }

    fn check_block_ctx_inner(&mut self, block: &HirBlock, kind: ConsumeKind) {
        for stmt in &block.statements {
            self.check_stmt(stmt);
            // Blocker 11: a statement that itself unconditionally
            // diverges (`return`/`break`/`continue`/`raise`, or a
            // binding whose own initializer does) makes every later
            // statement -- and this block's own tail, if it somehow
            // still has one -- unreachable. Not walking them at all
            // (rather than walking them but suppressing what they'd
            // report) is what actually matters: a mutation to
            // `self.states` from dead code must never contaminate the
            // reachable state that follows this block, the same
            // "unreachable code must not mutate reachable ownership
            // state" property `nir::verify` already independently
            // upholds at the NIR layer.
            if self.stmt_diverges(stmt) {
                return;
            }
        }
        if let Some(tail) = &block.tail {
            self.check_expr_ctx(tail, kind);
            // A compound `return`'s own per-branch cleanup (Blocker 2):
            // `kind == Return` here means this exact tail's own value
            // *is* the enclosing `return`'s operand, one leaf of
            // (possibly) a nested `if`, each of whose branches disagree
            // about which underlying resource is even being returned --
            // `self.states` right here, before any join with a sibling
            // branch runs, is this one leaf's own unambiguous truth.
            // `nir::lower`'s own `lower_into_return_sink` looks this up
            // by this exact tail's own id at the matching leaf, rather
            // than by the outer `return`'s id (which only a *direct*,
            // non-compound return value would ever be looked up by).
            if kind == ConsumeKind::Return && !self.diverges(tail.id()) {
                self.record_exit(tail.id(), 0);
            }
        }
    }

    fn stmt_diverges(&self, stmt: &HirStmt) -> bool {
        match stmt {
            HirStmt::Expr(e) => self.diverges(e.id()),
            HirStmt::Binding(b) => self.diverges(b.value.id()),
            HirStmt::Drop { .. } | HirStmt::Defer { .. } | HirStmt::While { .. } => false,
            HirStmt::Loop { body, .. } => self.diverging_loops.contains(&body.id),
        }
    }

    fn check_block(&mut self, block: &HirBlock) {
        self.check_block_ctx(block, ConsumeKind::Read);
    }

    fn check_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::Binding(b) => self.check_binding(b),
            HirStmt::Expr(e) => {
                self.check_expr(e);
                // Blocker 3: a bare statement-expression's own value is
                // always discarded (see `check_block_ctx`'s own doc
                // comment) -- if it is itself a fresh resource temporary
                // rather than a local reference, nothing will ever
                // destroy it.
                self.reject_leaked_temporary(e);
            }
            HirStmt::Defer { expr, span } => self.check_defer(expr, *span),
            HirStmt::Drop { expr, span } => self.check_drop(expr, *span),
            HirStmt::While {
                condition, body, ..
            } => self.check_while_loop(condition, body),
            HirStmt::Loop { body, .. } => self.check_loop_body(body),
        }
    }

    fn check_binding(&mut self, b: &HirBinding) {
        // A binding's own initializer always transfers ownership into
        // the fresh local it names (`rfcs/0011`) -- there is no
        // "observing" binding.
        if self.is_affine_expr(b.value.id()) {
            self.record_consume(b.value.id(), ConsumeInfo::Transfer);
        }
        self.check_expr_ctx(&b.value, ConsumeKind::Other);
        if self.is_resource_local(b.local) {
            let place = Place::root(b.local);
            self.states.insert(place.clone(), ResourceState::Available);
            self.pending_cleanup.push(CleanupAction::Drop(place));
        }
    }

    /// `defer <expr>;` (`rfcs/0011`). `expr` is an ordinary call
    /// expression, checked exactly like any other statement-expression
    /// (an argument passed to a `take` parameter is moved *now*, at
    /// registration time -- `defer` never delays argument evaluation,
    /// only the call's own side effect). Every resource-typed local
    /// this expression merely *observes* (an ordinary-parameter
    /// argument, or a receiver read within it) that is still `Available`
    /// afterward is promoted to `DropScheduled`: the enclosing scope
    /// still owns it and will still drop it at scope exit, but may no
    /// longer move it away or drop it early out from under the deferred
    /// call that still needs to observe it.
    fn check_defer(&mut self, expr: &HirExpr, span: Span) {
        self.check_expr(expr);
        // `nir::lower`'s own `lower_defer_call` independently re-checks
        // that `expr` is structurally a direct call to a plain function
        // reference (a well-formedness concern outside this stage's own
        // ownership-decision scope, exactly like an unsupported generic/
        // fallible/resource-returning defer already is) -- a plan is
        // only ever recorded here when it already is, so a shape that
        // fails that structural check simply never gets one, and
        // `nir::lower` reports its own diagnostic for it as today.
        if let HirExpr::Call { callee, args, .. } = expr
            && let HirExpr::Function { item, .. } = callee.as_ref()
            && let Some(take_flags) = self.take_flags_for_callee(callee)
        {
            // The callee's own recorded `take` flags must match this
            // exact call's own argument count -- always true for a
            // program that actually passed `typeck`'s own arity check
            // first; reachable only through hand-built, never-type-
            // checked HIR fed straight to this stage. Diagnosed
            // explicitly here (`MALFORMED_DEFER_CALLEE_SIGNATURE`)
            // rather than silently recording every argument as a mere
            // observation -- no plan is recorded for this `defer` at
            // all when this fires, so `nir::lower` independently
            // rejects it too, with its own missing-plan internal error.
            if take_flags.len() != args.len() {
                self.diagnose(
                    MALFORMED_DEFER_CALLEE_SIGNATURE,
                    span,
                    format!(
                        "this `defer`'s own callee declares {} parameter(s) but is called with {} argument(s)",
                        take_flags.len(),
                        args.len()
                    ),
                    "argument count disagrees with the callee's own declared parameters",
                );
            } else if let Some(return_type) = self.expr_types.get(&expr.id()).cloned()
                && let Some(arg_types) = args
                    .iter()
                    .map(|a| self.expr_types.get(&a.id()).cloned())
                    .collect::<Option<Vec<Ty>>>()
            {
                // Every other field this plan needs is actually
                // resolvable: this exact call expression's own resolved
                // return type, and every argument's own resolved type.
                // Either missing means `expr` was never actually type-
                // checked by a real `typeck` pass at all (the same
                // hand-built-HIR scenario as above) -- `nir::lower`'s
                // own "no checked plan recorded" internal error already
                // exists precisely to catch a `defer` reaching it with
                // no plan here, so this never falls back to fabricating
                // one from incomplete information either.
                let arg_modes = take_flags
                    .iter()
                    .map(|&takes| {
                        if takes {
                            ConsumeInfo::Transfer
                        } else {
                            ConsumeInfo::Observe
                        }
                    })
                    .collect();
                // Each argument's own exact place (`rfcs/0012`), in
                // declaration order -- see `CheckedDeferPlan::
                // arg_places`.
                let arg_places: Vec<Option<Place<LocalId>>> = args
                    .iter()
                    .map(|a| {
                        if self.is_affine_expr(a.id()) {
                            self.resolve_place(a)
                        } else {
                            None
                        }
                    })
                    .collect();
                let registration_order = self.next_defer_registration;
                self.next_defer_registration += 1;
                self.defer_plans.insert(
                    expr.id(),
                    CheckedDeferPlan {
                        callee: *item,
                        arg_modes,
                        arg_types,
                        arg_places,
                        return_type,
                        registration_order,
                    },
                );
            }
        }
        // Registered by this exact call's own callee-expression id
        // (`rfcs/0011`): `nir::lower` looks its own already-lowered
        // callee/arguments back up by this same id when it later
        // replays this cleanup action, rather than this stage trying
        // to describe a NIR-level call itself.
        self.pending_cleanup.push(CleanupAction::Defer(expr.id()));
        // The *exact* places this `defer` observes (`rfcs/0012`), not
        // merely the roots they are reached through: `defer
        // inspect(session.input)` protects `session.input` alone, so an
        // unaffected sibling (`session.output`) stays freely movable
        // while the parent as a whole does not (see
        // `reject_partial_whole_use`, which reports a defer-protected
        // descendant as its own violation rather than a partial move).
        let observed = self.observed_places(expr);
        for place in observed {
            if self.place_state(&place) == ResourceState::Available {
                self.states
                    .insert(place.clone(), ResourceState::DropScheduled);
                // Blocker 9: remembered against *this* defer's own
                // enclosing block so `check_block_ctx` can release this
                // exact protection once that block's own walk ends,
                // rather than leaving it protected indefinitely.
                if let Some(scope) = self.defer_scopes.last_mut() {
                    scope.insert(place);
                }
            }
        }
    }

    /// Every exact place this `defer` argument expression observes
    /// (`rfcs/0012`). A field access chain that resolves to a stable
    /// affine place contributes that whole place; anything else
    /// contributes whatever roots it reaches through, exactly as
    /// before. Collected through this stage's own `resolve_place`, so a
    /// place recorded here is the identical key `apply_place_move`/
    /// `check_place_read` already compare against -- never a
    /// second, parallel notion of "the same field".
    fn observed_places(&self, expr: &HirExpr) -> Vec<Place<LocalId>> {
        let mut out = Vec::new();
        collect_observed_places(self, expr, &mut out);
        out
    }

    /// `true` iff some place strictly *under* `root` is currently held
    /// by a pending observing `defer` (`rfcs/0012`) -- what makes an
    /// otherwise-complete parent unusable as a whole value: moving or
    /// dropping it would destroy the very descendant that `defer` still
    /// needs to observe when it runs. A boolean `any`, so `self.states`'
    /// own iteration order cannot affect the answer.
    fn has_defer_protected_descendant(&self, root: &Place<LocalId>) -> bool {
        self.states.iter().any(|(key, state)| {
            key != root && root.is_ancestor_of(key) && *state == ResourceState::DropScheduled
        })
    }

    fn check_drop(&mut self, expr: &HirExpr, span: Span) {
        // Deliberately does *not* run `expr` through the generic
        // `check_expr`/`check_read` path first: `drop`'s own target is
        // being consumed here, not read, and the match below already
        // gives every state (including `Moved`/`Dropped`) its own more
        // precise diagnostic (`double drop`, not the generic `use after
        // drop` a plain read would report for the same case).
        let HirExpr::Local { local, name, .. } = expr else {
            // A non-local drop target (already rejected by typeck's own
            // static-type check if it isn't even a resource) has no
            // owned binding here to transition; still walked with
            // `ConsumeKind::Other` for whatever nested reads/moves it
            // does contain -- a compound `if`/`match`/`handle` origin
            // here hits the same `nir::lower` limitation as any other
            // non-`return` consuming position (Blocker 2).
            self.check_expr_ctx(expr, ConsumeKind::Other);
            return;
        };
        if self.observing.contains(local) {
            self.diagnose(
                OBSERVATION_ESCAPES,
                span,
                format!(
                    "`{}` is an ordinary parameter's own call-scoped observation and cannot be dropped",
                    self.local_name(*local, *name)
                ),
                "dropping a non-owned observation",
            );
            return;
        }
        let root = Place::root(*local);
        let Some(state) = self.states.get(&root).copied() else {
            return;
        };
        match state {
            // A partially-moved aggregate's own *root* state is still
            // `Available` (only its children's own entries changed) --
            // structurally destroying it here means destroying exactly
            // its still-live descendants (`structural_drop_targets`),
            // never re-deriving "the whole thing" blindly: a field
            // already moved out is never touched again, and the outer
            // identity itself (if this is a declared `resource`) is
            // included by that same walk, last.
            ResourceState::Available => {
                // A descendant an observing `defer` is still holding
                // makes this whole-value destruction illegal
                // (`rfcs/0012`): LIFO replay runs that defer *after*
                // this drop, so it would observe a field this very
                // statement destroyed. Rejected here rather than left
                // for the runtime to discover.
                if self.has_defer_protected_descendant(&root) {
                    self.diagnose(
                        MOVE_AFTER_DEFER_CAPTURED,
                        span,
                        format!(
                            "`{}` has a field a pending `defer` still needs and cannot be dropped \
                             yet",
                            self.local_name(*local, *name)
                        ),
                        "a field is still needed by a pending defer",
                    );
                    self.set_place_state(&root, ResourceState::Error);
                    return;
                }
                // Structurally destroys exactly `root`'s own still-live
                // descendants (`rfcs/0012`) -- computed *before*
                // transitioning `root` itself, so it still reflects
                // whatever has already been moved out of it -- recorded
                // directly under this exact drop expression's own
                // `ExprId`, reusing `cleanup_edges`'s own existing shape
                // (an explicit `drop` is its own one-off exit, not a
                // scope-exit snapshot, so `pending_cleanup`'s marker
                // mechanism does not apply here at all): `nir::lower`
                // looks this up by this same id instead of naively
                // dropping `root`'s own bare whole value, which would
                // silently leak every one of its own remaining owned
                // fields.
                let targets = self.structural_drop_targets(&root);
                self.cleanup_edges.insert(
                    expr.id(),
                    targets.into_iter().map(CleanupAction::Drop).collect(),
                );
                self.set_place_state(&root, ResourceState::Dropped);
            }
            ResourceState::Error => {}
            ResourceState::Moved => {
                self.diagnose(
                    USE_AFTER_MOVE,
                    span,
                    format!(
                        "`{}` was already moved and cannot be dropped",
                        self.local_name(*local, *name)
                    ),
                    "drop after move",
                );
                self.set_place_state(&root, ResourceState::Error);
            }
            ResourceState::Dropped => {
                self.diagnose(
                    DOUBLE_DROP,
                    span,
                    format!("`{}` was already dropped", self.local_name(*local, *name)),
                    "double drop",
                );
                self.set_place_state(&root, ResourceState::Error);
            }
            ResourceState::DropScheduled => {
                self.diagnose(
                    MOVE_AFTER_DEFER_CAPTURED,
                    span,
                    format!(
                        "`{}` is still needed by a pending `defer` and cannot be dropped early",
                        self.local_name(*local, *name)
                    ),
                    "dropped before its defer ran",
                );
                self.set_place_state(&root, ResourceState::Error);
            }
        }
    }

    /// A bare `loop` body is checked once, from a clone of the current
    /// entry state (Blocker 2) -- `loop` has no condition, and therefore
    /// no zero-iteration exit at all: the state *after* the loop is
    /// formed purely from `break`'s own reachable states (`entry` itself
    /// if there are none reachable, which is correct exactly because
    /// nothing after an always-looping `loop` is itself reachable
    /// either). See [`Self::finish_loop`] for the shared backedge
    /// invariant this shares with [`Self::check_while_loop`].
    fn check_loop_body(&mut self, body: &HirBlock) {
        let entry = self.states.clone();
        self.loop_stack.push(LoopFrame {
            cleanup_marker: self.pending_cleanup.len(),
            defer_scope_marker: self.defer_scopes.len(),
            ..LoopFrame::default()
        });
        self.check_block(body);
        let fallthrough_reachable = !self.diverges(body.id);
        let fallthrough_state = std::mem::replace(&mut self.states, entry.clone());
        let frame = self
            .loop_stack
            .pop()
            .expect("this exact push is right above");
        if frame.break_states.is_empty() {
            self.diverging_loops.insert(body.id);
        }
        self.states = self.finish_loop(
            entry,
            None,
            frame,
            fallthrough_reachable,
            fallthrough_state,
            body.span,
        );
    }

    /// A `while` loop's own condition is evaluated fresh on *every*
    /// visit to the loop header -- the very first one, and again after
    /// every `continue`/fallthrough backedge -- so it cannot be checked
    /// only once, from `entry`, and then forgotten (Blocker: loop
    /// condition re-evaluation). Folded into the exact same repeating
    /// region the body itself already is: `entry` is the state each
    /// fresh evaluation of `condition` actually starts from, so a
    /// backedge that leaves a resource in a state a *second* evaluation
    /// of `condition` could not safely reuse (moving it, say) is exactly
    /// as much a loop-carried invalidation as the body doing the same
    /// thing would be, and is caught by the identical
    /// [`Self::finish_loop`] check. The state *after* the loop is
    /// `condition`'s own state immediately once evaluated (its own
    /// side effects/consumption already happened whether it returned
    /// `true` or `false`), joined with every reachable `break`.
    fn check_while_loop(&mut self, condition: &HirExpr, body: &HirBlock) {
        let entry = self.states.clone();
        self.loop_stack.push(LoopFrame {
            cleanup_marker: self.pending_cleanup.len(),
            defer_scope_marker: self.defer_scopes.len(),
            ..LoopFrame::default()
        });
        self.check_expr(condition);
        let after_condition = self.states.clone();
        self.check_block(body);
        let fallthrough_reachable = !self.diverges(body.id);
        let fallthrough_state = std::mem::replace(&mut self.states, entry.clone());
        let frame = self
            .loop_stack
            .pop()
            .expect("this exact push is right above");
        self.states = self.finish_loop(
            entry,
            Some(after_condition),
            frame,
            fallthrough_reachable,
            fallthrough_state,
            body.span,
        );
    }

    /// Shared backedge-invariant check and after-loop state computation
    /// for both loop forms (Blocker 2 / loop condition re-evaluation).
    /// Three distinct edges can carry a resource local's own state back
    /// into the *next* visit to the loop header: the body's own ordinary
    /// fallthrough end, and every `continue` reached anywhere inside it
    /// -- each must agree with `entry` for every resource local declared
    /// outside the loop, since the header (a `while`'s own condition, or
    /// a bare `loop`'s own body start) reuses that exact entry state
    /// regardless of which edge produced it. `break` is different: it
    /// never re-enters the loop at all, so its own live state instead
    /// joins directly into the state *after* the loop, alongside
    /// `after_base` -- `None` for a bare `loop` (it has no
    /// zero-iteration exit at all: if nothing inside it ever reaches a
    /// reachable `break`, the code after it is itself unreachable, and
    /// `entry` is returned as an unobserved placeholder), or `Some` of a
    /// `while`'s own state immediately after evaluating `condition`
    /// (which always finishes evaluating, and so always has whatever
    /// side effect it has, regardless of which way it comes out) -- a
    /// genuinely reachable edge into "after the loop" in its own right,
    /// competing with every `break`'s own state exactly the way two
    /// sibling `if` branches compete in [`join_branch_states`]. Two
    /// reachable exits disagreeing is reported once, the same
    /// [`INCONSISTENT_BRANCH_STATE`] an `if`/`match`/`handle` join
    /// already reports, rather than silently becoming
    /// [`ResourceState::Error`] and suppressing every later check
    /// against it. A resource local the loop body itself *declares* is
    /// scoped to one iteration and never compared this way (comparing
    /// against entry, where it never existed, would be meaningless) --
    /// excluded by only ever producing a state for a key already
    /// present on `entry`, the same discipline [`join_branch_states`]
    /// already follows.
    fn finish_loop(
        &mut self,
        entry: PlaceStates,
        after_base: Option<PlaceStates>,
        frame: LoopFrame,
        fallthrough_reachable: bool,
        fallthrough_state: PlaceStates,
        span: Span,
    ) -> PlaceStates {
        let mut backedges: Vec<&PlaceStates> = frame.continue_states.iter().collect();
        if fallthrough_reachable {
            backedges.push(&fallthrough_state);
        }

        // Every place already tracked before the loop, plus every place
        // a backedge newly introduced for a root *already* tracked
        // before the loop (a field touched for the first time during
        // one iteration, of an aggregate declared outside the loop) --
        // never a place whose own root is itself declared inside the
        // loop body (out of scope for this comparison entirely,
        // exactly as before: comparing against `entry`, where it never
        // existed, would be meaningless).
        let tracked_roots: HashSet<LocalId> = entry.keys().map(|p| p.root).collect();
        let mut compare_keys: BTreeSet<Place<LocalId>> = entry.keys().cloned().collect();
        for backedge in &backedges {
            for key in backedge.keys() {
                if tracked_roots.contains(&key.root) {
                    compare_keys.insert(key.clone());
                }
            }
        }
        let default_for = |states: &PlaceStates, key: &Place<LocalId>| -> ResourceState {
            states
                .get(key)
                .copied()
                .unwrap_or_else(|| entry.get(key).copied().unwrap_or(ResourceState::Available))
        };

        let mut poisoned: HashSet<Place<LocalId>> = HashSet::new();
        for key in &compare_keys {
            let entry_state = default_for(&entry, key);
            if entry_state == ResourceState::Error {
                continue;
            }
            let disagrees = backedges.iter().any(|backedge| {
                let backedge_state = default_for(backedge, key);
                backedge_state != entry_state && backedge_state != ResourceState::Error
            });
            if disagrees {
                poisoned.insert(key.clone());
            }
        }
        for _ in &poisoned {
            self.diagnose(
                LOOP_CARRIED_INVALIDATION,
                span,
                "a resource's own state reaching the top of this loop again (through the \
                 body's own fallthrough, a `continue`, or a `while` condition evaluated again) \
                 disagrees with its state on entry; a later iteration could not safely reuse it"
                    .to_string(),
                "loop-carried resource invalidation",
            );
        }

        let mut edges: Vec<&PlaceStates> = frame.break_states.iter().collect();
        if let Some(base) = &after_base {
            edges.push(base);
        }
        let Some((first, rest)) = edges.split_first() else {
            // No `break` reaches here, and a bare `loop` has no other
            // exit either -- "after the loop" is itself unreachable.
            return entry;
        };
        let mut after_keys = compare_keys;
        for key in first.keys() {
            if tracked_roots.contains(&key.root) {
                after_keys.insert(key.clone());
            }
        }
        for edge in rest {
            for key in edge.keys() {
                if tracked_roots.contains(&key.root) {
                    after_keys.insert(key.clone());
                }
            }
        }
        let mut after: PlaceStates = after_keys
            .iter()
            .map(|key| (key.clone(), default_for(first, key)))
            .collect();
        for key in &poisoned {
            after.insert(key.clone(), ResourceState::Error);
        }
        let mut disagreements: HashSet<Place<LocalId>> = HashSet::new();
        for other in rest {
            for (key, current) in after.iter_mut() {
                if poisoned.contains(key) {
                    continue;
                }
                let other_state = default_for(other, key);
                let joined = current.join(other_state);
                if joined == ResourceState::Error && *current != ResourceState::Error {
                    disagreements.insert(key.clone());
                }
                *current = joined;
            }
        }
        for _ in &disagreements {
            self.diagnose(
                INCONSISTENT_BRANCH_STATE,
                span,
                "two reachable exits of this loop (a `break`, or a `while` condition's own \
                 false edge) disagree about a resource's own state; whatever runs after the \
                 loop has no single state to check it against"
                    .to_string(),
                "inconsistent resource state across loop exits",
            );
        }
        after
    }

    // -- Expressions -----------------------------------------------------

    fn check_expr(&mut self, expr: &HirExpr) {
        self.check_expr_ctx(expr, ConsumeKind::Read);
    }

    /// Checks `expr` in `kind`'s own context (`rfcs/0011`, Blocker 2),
    /// then -- if `expr` is itself a direct (non-compound) leaf a
    /// `return` consumes -- records its own whole-function cleanup
    /// snapshot under its own id, exactly like [`Self::
    /// check_block_ctx_inner`]'s identical tail special-case already
    /// does for a block's own tail, and [`Self::check_match_arms`]/
    /// [`Self::check_handle_arms`] already do for a bare arm body: a
    /// direct `return`'s own leaf value (a bare local, a fresh call, a
    /// literal construction -- anything that is not itself one of the
    /// handful of forms already handled below) is exactly the id
    /// `nir::lower`'s own `lower_into_return_sink`'s catch-all looks
    /// this exact snapshot up by. Without this, a function returning a
    /// direct (non-compound) resource value leaked every *other*
    /// resource it still owned at that exact exit (an unrelated `take`
    /// parameter, say) -- nothing ever recorded that they needed
    /// cleaning up there at all.
    fn check_expr_ctx(&mut self, expr: &HirExpr, kind: ConsumeKind) {
        self.check_expr_ctx_inner(expr, kind);
        if kind == ConsumeKind::Return
            && !matches!(
                expr,
                HirExpr::Block(_)
                    | HirExpr::If { .. }
                    | HirExpr::Match { .. }
                    | HirExpr::Handle { .. }
                    | HirExpr::Return { .. }
                    | HirExpr::Raise { .. }
                    | HirExpr::Try { .. }
                    | HirExpr::Break { .. }
                    | HirExpr::Continue { .. }
            )
            && !self.diverges(expr.id())
        {
            self.record_exit(expr.id(), 0);
        }
    }

    /// `kind` is only ever actually consulted at a leaf: a bare
    /// `Local` (transitions its own state when consumed, merely
    /// validates it when read) or a resource-typed `match`/`handle`/
    /// non-`return` `if` (rejected outright when `kind` isn't `Read`,
    /// see [`ConsumeKind`]). Every other node either always uses
    /// `Read` for its own subexpressions (an operand, a call's own
    /// callee, a condition -- none of these are the value actually
    /// flowing onward) or is one of the handful of forms that are
    /// *transparent* to their own outer context (`block`/`if`/`match`/
    /// `handle`, which propagate `kind` into their own tail/arm
    /// bodies) or that unconditionally force their own sub-value into
    /// a specific kind regardless of the outer one (`return`'s own
    /// operand, a binding/assignment's own value, a `take` argument, a
    /// constructed field, `raise`'s own operand -- always at least
    /// `ConsumeKind::Other`, since each of these really does transfer
    /// ownership no matter what encloses it).
    fn check_expr_ctx_inner(&mut self, expr: &HirExpr, kind: ConsumeKind) {
        match expr {
            HirExpr::Int { .. }
            | HirExpr::Float { .. }
            | HirExpr::Str { .. }
            | HirExpr::Char { .. }
            | HirExpr::Bool { .. }
            | HirExpr::Function { .. }
            | HirExpr::CaseRef { .. }
            | HirExpr::ProtocolMethodRef { .. }
            | HirExpr::Error { .. } => {}
            HirExpr::Continue { id, .. } => {
                if let Some(marker) = self.loop_stack.last().map(|f| f.cleanup_marker) {
                    self.record_exit(*id, marker);
                }
                if let Some(frame) = self.loop_stack.last() {
                    // This iteration's own scopes (the loop body's own
                    // top-level scope, and any block nested inside it
                    // this `continue` sits within) are exited right
                    // here, back to the loop's own condition/backedge --
                    // any observing `defer` they registered must be
                    // released in this exact recorded state, or the
                    // next iteration's own fresh `check_defer` call
                    // would wrongly find it still protected instead of
                    // `Available` again (`rfcs/0011`).
                    let state = self.released_snapshot(frame.defer_scope_marker);
                    self.loop_stack
                        .last_mut()
                        .expect("checked Some immediately above")
                        .continue_states
                        .push(state);
                }
            }
            HirExpr::Local {
                local, name, span, ..
            } => self.check_local_use(*local, *name, *span, kind),
            HirExpr::Unary { operand, .. } => self.check_expr(operand),
            HirExpr::Binary { left, right, .. } => {
                self.check_expr(left);
                self.check_expr(right);
            }
            HirExpr::Assign { target, value, .. } => {
                // A plain reassignment's own value always transfers,
                // exactly like a binding's own initializer (`rfcs/
                // 0011`) -- `nir::lower` only actually applies this for
                // `AssignOp::Assign` (a compound assignment is always
                // numeric/bitwise, never affine, so `is_affine_expr`
                // already excludes it here).
                if self.is_affine_expr(value.id()) {
                    self.record_consume(value.id(), ConsumeInfo::Transfer);
                }
                self.check_expr_ctx(value, ConsumeKind::Other);
                match target.as_ref() {
                    HirExpr::Local {
                        local, name, span, ..
                    } if self.is_resource_local(*local) => {
                        self.check_reassignment(&Place::root(*local), *name, *span);
                    }
                    HirExpr::Field {
                        name, span, base, ..
                    } if self.is_affine_expr(target.id()) => {
                        match self.resolve_place(target) {
                            Some(place) => self.check_reassignment(&place, *name, *span),
                            None => {
                                // The base isn't a stable place at all
                                // (a temporary) -- there is no place
                                // here to reinitialize into in the
                                // first place; fall back to the
                                // ordinary read-and-leak-check path.
                                self.check_expr(base);
                                self.reject_leaked_temporary(base);
                            }
                        }
                    }
                    _ => self.check_expr(target),
                }
            }
            HirExpr::Call {
                callee, args, span, ..
            } => {
                self.check_expr(callee);
                // A callee that resolves directly to a declared function
                // (`HirExpr::Function`) must have a real, correctly-sized
                // `take_flags` entry -- always true for HIR that actually
                // passed `hir::lower`'s own name resolution and
                // `typeck`'s own arity check first. A callee that is
                // *not* a direct function reference at all (a variant
                // case constructor, a protocol method) legitimately has
                // none: `take_flags_for_callee` already returns `None`
                // for exactly that shape, never for a resolved one
                // that's merely missing.
                if let HirExpr::Function { item, .. } = callee.as_ref() {
                    match self.take_flags.get(item) {
                        Some(flags) if flags.len() == args.len() => {}
                        Some(flags) => {
                            self.diagnose(
                                MALFORMED_CALLEE_TAKE_FLAGS,
                                *span,
                                format!(
                                    "this call's own callee declares {} parameter(s) but is called with {} argument(s)",
                                    flags.len(),
                                    args.len()
                                ),
                                "argument count disagrees with the callee's own declared parameters",
                            );
                            return;
                        }
                        None => {
                            self.diagnose(
                                MALFORMED_CALLEE_TAKE_FLAGS,
                                *span,
                                "this call's own callee has no take-flag metadata recorded for it"
                                    .to_string(),
                                "unresolved callee signature",
                            );
                            return;
                        }
                    }
                }
                let take_flags = self.take_flags_for_callee(callee);
                // A variant case constructor (`FileResult.Found(file)`)
                // always transfers every one of its own payload
                // arguments (`rfcs/0012`) -- exactly like `RecordLiteral`
                // fields already do, and completely unlike an ordinary
                // call's own non-`take` parameter, which only ever
                // observes: constructing a variant case is itself the
                // one and only place its own payload becomes owned by
                // something, so there is no "observing" shape of it to
                // fall back to. `take_flags_for_callee` correctly has no
                // entry at all for this callee shape (a case constructor
                // is not a declared function), which is exactly why this
                // needs its own explicit check here rather than falling
                // through to the ordinary `unwrap_or(false)` default
                // below.
                let is_variant_construct = matches!(callee.as_ref(), HirExpr::CaseRef { .. });
                for (index, arg) in args.iter().enumerate() {
                    // `false` here only ever means "this callee is not a
                    // direct function reference at all" (a variant case
                    // constructor, a protocol method -- `take_flags_for_
                    // callee` itself returns `None` for exactly that
                    // shape, correctly, since neither has a `take`
                    // parameter to speak of); for a resolved
                    // `HirExpr::Function` callee specifically, the guard
                    // above already proved a same-length entry exists,
                    // so `flags.get(index)` can never actually miss here.
                    let takes = is_variant_construct
                        || take_flags
                            .and_then(|flags| flags.get(index))
                            .copied()
                            .unwrap_or(false);
                    if self.is_affine_expr(arg.id()) {
                        self.record_consume(
                            arg.id(),
                            if takes {
                                ConsumeInfo::Transfer
                            } else {
                                ConsumeInfo::Observe
                            },
                        );
                    }
                    self.check_expr_ctx(
                        arg,
                        if takes {
                            ConsumeKind::Other
                        } else {
                            ConsumeKind::Read
                        },
                    );
                    // Blocker 3: an ordinary (non-`take`) parameter only
                    // ever observes for the duration of this call --
                    // nothing keeps whatever a fresh resource temporary
                    // argument named alive afterward, so nothing would
                    // ever destroy it.
                    if !takes {
                        self.reject_leaked_temporary(arg);
                    }
                }
            }
            // A well-typed field projection *can* now be affine-typed
            // itself (`rfcs/0012`, lifting Alpha 0.1.7's blanket
            // rejection of a resource-typed field in any aggregate): if
            // it is, and `base` resolves to a stable place (a bare
            // local, or a further field chain rooted in one), the field
            // itself is the place actually being read/consumed here,
            // not `base` as a whole -- `base`'s own remaining fields are
            // completely unaffected (`rfcs/0012`'s "unaffected sibling
            // field" rule). `base` is walked through `resolve_place`
            // itself (never `check_expr(base)` first): an intermediate
            // `Field` in the chain must not be treated as a *whole-value
            // read* of its own base, which would wrongly reject reading
            // through an already-partially-moved intermediate aggregate
            // (`session.output` after `session.input` was moved is
            // still valid). A non-affine field, or a field whose own
            // `base` is not a stable place at all (a temporary), keeps
            // exactly Alpha 0.1.7's original behavior.
            HirExpr::Field { base, .. } => {
                if kind == ConsumeKind::Read && self.is_affine_expr(expr.id()) {
                    match self.resolve_place(expr) {
                        Some(place) => self.check_place_read(&place, expr),
                        None => {
                            self.check_expr(base);
                            self.reject_leaked_temporary(base);
                        }
                    }
                } else if kind != ConsumeKind::Read && self.is_affine_expr(expr.id()) {
                    match self.resolve_place(expr) {
                        Some(place) => {
                            self.apply_place_move(&place, expr);
                            self.record_consume(expr.id(), ConsumeInfo::Transfer);
                        }
                        None => {
                            self.check_expr(base);
                            self.reject_leaked_temporary(base);
                        }
                    }
                } else {
                    self.check_expr(base);
                    self.reject_leaked_temporary(base);
                }
            }
            HirExpr::Cast { expr, .. } => self.check_expr(expr),
            HirExpr::Try { expr, id, .. } => {
                self.check_expr(expr);
                // Postfix `?` unwinds this whole function on its own
                // implicit failure edge, exactly like an explicit
                // `raise` (`rfcs/0010`) -- recorded here, at marker 0,
                // so `nir::lower`'s own `lower_try` can look this exact
                // propagation's own checked cleanup up by this same
                // `Try` expression's id, the same way `lower_raise`
                // looks an explicit `raise` up by its own.
                self.record_exit(*id, 0);
            }
            HirExpr::If {
                condition,
                then_branch,
                else_branch,
                id,
                span,
                ..
            } => {
                self.check_expr(condition);
                let kind = self.check_compound_origin(*id, *span, kind, "if");
                self.check_if(*id, *span, then_branch, else_branch.as_ref(), kind);
            }
            HirExpr::Match {
                scrutinee,
                arms,
                id,
                span,
                ..
            } => {
                // An affine scrutinee is *decomposed* by matching it,
                // never merely observed (`rfcs/0012`): whichever case
                // is actually active hands its own payload to that
                // arm's own pattern -- see `check_pattern` -- so the
                // scrutinee's own place (if it names one at all, e.g. a
                // bare local) must itself become `Moved` here, or its
                // own later implicit end-of-scope cleanup would try to
                // structurally destroy the very same payload a pattern
                // binding already took ownership of, double-dropping
                // it. A non-affine scrutinee keeps its own original,
                // purely observing read.
                if self.is_affine_expr(scrutinee.id()) {
                    self.check_expr_ctx(scrutinee, ConsumeKind::Other);
                } else {
                    self.check_expr(scrutinee);
                }
                let kind = self.check_compound_origin(*id, *span, kind, "match");
                self.check_match_arms(*id, *span, arms, kind);
            }
            HirExpr::Block(block) => self.check_block_ctx(block, kind),
            HirExpr::Return { value, id, .. } => {
                if let Some(value) = value {
                    self.check_expr_ctx(value, ConsumeKind::Return);
                }
                // A `return` always unwinds the *whole* function, from
                // the very start (`rfcs/0011`) -- marker 0, mirroring
                // `nir::lower`'s own `emit_cleanup` (as opposed to
                // `emit_cleanup_since`).
                self.record_exit(*id, 0);
            }
            HirExpr::Break { value, id, .. } => {
                if let Some(value) = value {
                    self.check_expr_ctx(value, ConsumeKind::Other);
                }
                if let Some(marker) = self.loop_stack.last().map(|f| f.cleanup_marker) {
                    self.record_exit(*id, marker);
                }
                // This loop's own body scope (and any block nested
                // inside it this `break` sits within) is exited right
                // here, straight past the loop entirely -- any
                // observing `defer` one of those scopes registered must
                // be released in this exact recorded state, or code
                // reachable after the loop would wrongly still find it
                // `defer`-protected past the exact scope that
                // protection was only ever supposed to outlive
                // (`rfcs/0011`).
                let state = self
                    .loop_stack
                    .last()
                    .map(|frame| self.released_snapshot(frame.defer_scope_marker))
                    .unwrap_or_else(|| self.states.clone());
                if let Some(frame) = self.loop_stack.last_mut() {
                    frame.break_states.push(state);
                }
            }
            HirExpr::RecordLiteral { fields, .. } => {
                for field in fields {
                    self.check_expr_ctx(&field.value, ConsumeKind::Other);
                }
            }
            HirExpr::Raise { operand, id, .. } => {
                self.check_expr_ctx(operand, ConsumeKind::Other);
                self.record_exit(*id, 0);
            }
            HirExpr::Handle {
                operand,
                arms,
                id,
                span,
                ..
            } => {
                self.check_expr(operand);
                let kind = self.check_compound_origin(*id, *span, kind, "handle");
                self.check_handle_arms(*id, *span, arms, kind);
            }
        }
    }

    /// Rejects a resource-typed `handle`, or a resource-typed `if`/
    /// `match` used in a consuming position other than `return`, with
    /// [`UNSUPPORTED_COMPOUND_RESOURCE_ORIGIN`] (Blocker 2:
    /// `nir::lower` cannot yet represent a compound origin there --
    /// see [`ConsumeKind`]) -- returning `ConsumeKind::Read` in that
    /// case so the rest of this walk still validates ordinary use/move
    /// correctness inside every branch/arm, just without pretending
    /// the construct's own overall value is soundly consumed. Returns
    /// `kind` unchanged whenever no rejection is needed (a `Read`
    /// context, a non-affine type, or -- for `if`/`match` specifically
    /// -- a `Return` context).
    fn check_compound_origin(
        &mut self,
        id: crate::hir::ExprId,
        span: Span,
        kind: ConsumeKind,
        construct: &'static str,
    ) -> ConsumeKind {
        let supported = match kind {
            ConsumeKind::Read => true,
            ConsumeKind::Return => matches!(construct, "if" | "match" | "handle"),
            ConsumeKind::Other => false,
        };
        if supported || !self.is_affine_expr(id) {
            return kind;
        }
        self.diagnose(
            UNSUPPORTED_COMPOUND_RESOURCE_ORIGIN,
            span,
            format!(
                "a resource-typed `{construct}` cannot be directly moved, bound, assigned, \
                 passed to a `take` parameter, stored, or raised this milestone; consume each \
                 branch/arm's own resource individually instead (e.g. `return` it from inside \
                 that branch/arm)"
            ),
            "unsupported compound resource origin",
        );
        ConsumeKind::Read
    }

    fn is_affine_expr(&self, id: crate::hir::ExprId) -> bool {
        self.expr_types
            .get(&id)
            .is_some_and(|ty| self.is_affine(ty))
    }

    /// Rejects `expr` with [`RESOURCE_TEMPORARY_LEAK`] (Blocker 3) if
    /// evaluating it can produce a fresh, affine-typed value with no
    /// owner at all yet -- a call, or a record/resource literal, at
    /// `expr` itself or (recursing through every construct transparent
    /// to its own resulting value) at some reachable leaf of a nested
    /// `if`/`match`/`handle`/block wrapping one. Deliberately narrower
    /// than "any affine expression that is not a bare local reference":
    /// a compound expression every one of whose reachable leaves merely
    /// *re-observes* an existing binding (`if cond { file } else { file
    /// }`, still valid input to an observing `defer`) never brings a
    /// new, otherwise-unreachable resource into existence the way a
    /// call or a literal construction does, so it is not this check's
    /// concern -- only a leaf that actually constructs one is.
    fn reject_leaked_temporary(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::Call { .. } | HirExpr::RecordLiteral { .. } => {
                if !self.is_affine_expr(expr.id()) {
                    return;
                }
                self.diagnose(
                    RESOURCE_TEMPORARY_LEAK,
                    expr.span(),
                    "a resource-typed temporary here is never bound, returned, dropped, or \
                     transferred to a `take` parameter, so nothing would ever destroy it; bind \
                     it to a `value` first, or pass/return/drop it directly"
                        .to_string(),
                    "resource temporary would leak",
                );
            }
            // Transparent to their own resulting value: a fresh
            // resource any *reachable* leaf of one of these directly
            // constructs is exactly as much this position's own concern
            // as if it were written here directly -- a diverging leaf
            // (`self.diverges`) never actually produces a value here at
            // all, so it is not recursed into.
            HirExpr::Block(block) => {
                if let Some(tail) = &block.tail
                    && !self.diverges(tail.id())
                {
                    self.reject_leaked_temporary(tail);
                }
            }
            HirExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                if let Some(tail) = &then_branch.tail
                    && !self.diverges(tail.id())
                {
                    self.reject_leaked_temporary(tail);
                }
                match else_branch {
                    Some(HirElse::Block(block)) => {
                        if let Some(tail) = &block.tail
                            && !self.diverges(tail.id())
                        {
                            self.reject_leaked_temporary(tail);
                        }
                    }
                    Some(HirElse::If(inner)) if !self.diverges(inner.id()) => {
                        self.reject_leaked_temporary(inner);
                    }
                    Some(HirElse::If(_)) | None => {}
                }
            }
            HirExpr::Match { arms, .. } => {
                for arm in arms {
                    self.reject_leaked_temporary_in_arm_body(&arm.body);
                }
            }
            HirExpr::Handle { arms, .. } => {
                for arm in arms {
                    self.reject_leaked_temporary_in_arm_body(&arm.body);
                }
            }
            _ => {}
        }
    }

    /// One `match`/`handle` arm's own share of [`Self::
    /// reject_leaked_temporary`]'s recursion.
    fn reject_leaked_temporary_in_arm_body(&mut self, body: &HirMatchArmBody) {
        match body {
            HirMatchArmBody::Expr(e) => {
                if !self.diverges(e.id()) {
                    self.reject_leaked_temporary(e);
                }
            }
            HirMatchArmBody::Block(block) => {
                if let Some(tail) = &block.tail
                    && !self.diverges(tail.id())
                {
                    self.reject_leaked_temporary(tail);
                }
            }
        }
    }

    fn check_local_use(
        &mut self,
        local: LocalId,
        name: crate::symbol::Symbol,
        span: Span,
        kind: ConsumeKind,
    ) {
        if kind == ConsumeKind::Read {
            self.check_read(local, name, span);
        } else {
            self.check_consume(local, name, span);
        }
    }

    fn check_read(&mut self, local: LocalId, name: crate::symbol::Symbol, span: Span) {
        if self.observing.contains(&local) {
            return;
        }
        let root = Place::root(local);
        let Some(state) = self.states.get(&root).copied() else {
            return;
        };
        if state == ResourceState::Available
            && self.reject_partial_whole_use(&root, local, name, span)
        {
            return;
        }
        match state {
            ResourceState::Available | ResourceState::DropScheduled => {}
            ResourceState::Error => {}
            ResourceState::Moved => {
                self.diagnose(
                    USE_AFTER_MOVE,
                    span,
                    format!(
                        "`{}` was already moved and cannot be used",
                        self.local_name(local, name)
                    ),
                    "use after move",
                );
                self.set_place_state(&root, ResourceState::Error);
            }
            ResourceState::Dropped => {
                self.diagnose(
                    USE_AFTER_DROP,
                    span,
                    format!(
                        "`{}` was already dropped and cannot be used",
                        self.local_name(local, name)
                    ),
                    "use after drop",
                );
                self.set_place_state(&root, ResourceState::Error);
            }
        }
    }

    /// `true` (having already diagnosed [`PARTIAL_PARENT_USED_AS_WHOLE`])
    /// iff `root`'s own type is an aggregate currently missing at least
    /// one of its own affine fields (`rfcs/0012`): a partially-moved
    /// aggregate may only be used for accessing an unaffected child
    /// place, reinserting into an empty child, or structural cleanup --
    /// never observed, returned, transferred, copied, or passed as a
    /// whole. Only ever called once `root`'s own recorded state is
    /// already known to be `Available` (a `Moved`/`Dropped`/`Error`
    /// whole-value use is a different, already-existing diagnostic).
    fn reject_partial_whole_use(
        &mut self,
        root: &Place<LocalId>,
        local: LocalId,
        name: crate::symbol::Symbol,
        span: Span,
    ) -> bool {
        let Some(ty) = self.place_ty(root) else {
            return false;
        };
        if self.place_is_wholly_available(root, &ty) {
            return false;
        }
        // A descendant an observing `defer` is still holding is not a
        // *partially moved* parent (`rfcs/0012`): the field is entirely
        // intact, and this parent becomes usable as a whole again the
        // moment that defer's own scope ends. Reported as its own
        // violation so the diagnostic names the real reason.
        if self.has_defer_protected_descendant(root) {
            self.diagnose(
                MOVE_AFTER_DEFER_CAPTURED,
                span,
                format!(
                    "`{}` has a field a pending `defer` still needs and cannot be moved or \
                     dropped as a whole yet",
                    self.local_name(local, name)
                ),
                "a field is still needed by a pending defer",
            );
            return true;
        }
        self.diagnose(
            PARTIAL_PARENT_USED_AS_WHOLE,
            span,
            format!(
                "`{}` has had one or more of its own fields moved out and cannot be used as a \
                 whole value -- access an unaffected field, reinsert into an empty one, or drop \
                 it to clean up what remains",
                self.local_name(local, name)
            ),
            "partially moved value used as a whole",
        );
        true
    }

    /// Transitions `local`'s own state to `Moved` -- the only shape an
    /// existing owned *whole* binding can be consumed *from* is a bare
    /// local reference naming one; consuming an individual affine field
    /// out of one goes through [`Self::apply_place_move`] instead
    /// (`rfcs/0012`).
    fn check_consume(&mut self, local: LocalId, name: crate::symbol::Symbol, span: Span) {
        if self.observing.contains(&local) {
            self.diagnose(
                OBSERVATION_ESCAPES,
                span,
                format!(
                    "`{}` is an ordinary parameter's own call-scoped observation and cannot be moved, returned, or stored",
                    self.local_name(local, name)
                ),
                "observation escapes its call",
            );
            return;
        }
        let root = Place::root(local);
        let Some(state) = self.states.get(&root).copied() else {
            return;
        };
        if state == ResourceState::Available
            && self.reject_partial_whole_use(&root, local, name, span)
        {
            return;
        }
        match state {
            ResourceState::Available => {
                self.set_place_state(&root, ResourceState::Moved);
            }
            ResourceState::Error => {}
            ResourceState::Moved => {
                self.diagnose(
                    USE_AFTER_MOVE,
                    span,
                    format!(
                        "`{}` was already moved and cannot be moved again",
                        self.local_name(local, name)
                    ),
                    "use after move",
                );
                self.set_place_state(&root, ResourceState::Error);
            }
            ResourceState::Dropped => {
                self.diagnose(
                    USE_AFTER_DROP,
                    span,
                    format!(
                        "`{}` was already dropped and cannot be moved",
                        self.local_name(local, name)
                    ),
                    "use after drop",
                );
                self.set_place_state(&root, ResourceState::Error);
            }
            ResourceState::DropScheduled => {
                self.diagnose(
                    MOVE_AFTER_DEFER_CAPTURED,
                    span,
                    format!(
                        "`{}` is still needed by a pending `defer` and cannot be moved away",
                        self.local_name(local, name)
                    ),
                    "moved before its defer ran",
                );
                self.set_place_state(&root, ResourceState::Error);
            }
        }
    }

    /// Reassigning a `mutable` resource-typed binding, or reinitializing
    /// an individual empty affine field (`session.input = open_file();`,
    /// `rfcs/0012`): accepted -- and transitions `place` back to
    /// `Available`, exactly like a fresh binding -- only when the
    /// path-sensitive state already proves that exact place holds
    /// nothing needing destruction (`Moved`/`Dropped`) on every incoming
    /// path; an `Available` or `DropScheduled` old value would otherwise
    /// be silently overwritten and leaked, since nothing would ever
    /// destroy it again. A place absent from `self.states` with no
    /// affine type at all (an ordinary, non-resource-typed target the
    /// caller already filtered out) has nothing here to protect.
    fn check_reassignment(
        &mut self,
        place: &Place<LocalId>,
        name: crate::symbol::Symbol,
        span: Span,
    ) {
        match self.place_state(place) {
            ResourceState::Moved | ResourceState::Dropped => {
                self.set_place_state(place, ResourceState::Available);
            }
            ResourceState::Error => {}
            ResourceState::Available | ResourceState::DropScheduled => {
                self.diagnose(
                    REASSIGNMENT_OF_LIVE_RESOURCE,
                    span,
                    format!(
                        "`{}` still owns a resource that was never moved or dropped; \
                         reassigning it would leak the old value",
                        self.interner.resolve(name)
                    ),
                    "reassigning a live resource",
                );
                self.set_place_state(place, ResourceState::Error);
            }
        }
    }

    // -- Joins -----------------------------------------------------------

    fn check_if(
        &mut self,
        if_id: crate::hir::ExprId,
        span: Span,
        then_branch: &HirBlock,
        else_branch: Option<&HirElse>,
        kind: ConsumeKind,
    ) {
        let entry = self.states.clone();
        self.check_block_ctx(then_branch, kind);
        let then_diverges = self.diverges(then_branch.id);
        let then_exit = std::mem::replace(&mut self.states, entry.clone());

        let (else_exit, else_diverges) = match else_branch {
            Some(HirElse::Block(block)) => {
                self.check_block_ctx(block, kind);
                let diverges = self.diverges(block.id);
                (std::mem::replace(&mut self.states, entry.clone()), diverges)
            }
            Some(HirElse::If(inner)) => {
                self.check_expr_ctx(inner, kind);
                let diverges = self.diverges(inner.id());
                (self.states.clone(), diverges)
            }
            None => (entry.clone(), false),
        };

        self.states = join_branch_states(
            &entry,
            &[(then_exit, then_diverges), (else_exit, else_diverges)],
        );
        // In a `ConsumeKind::Return` context, this `if`'s own value is
        // being consumed by an enclosing `return` right here, at this
        // exact point (Blocker 2) -- `nir::lower` pushes that
        // `return`'s own cleanup+terminate into each branch separately
        // (`Lowering::lower_into_return_sink`), so a branch moving
        // exactly the local that *is* its own tail while a sibling
        // branch leaves that same local untouched is the expected
        // shape of a compound return, not a real ambiguity: nothing
        // ever reads `self.states` again on either path, since both
        // already end the function right here. Only a *different*
        // kind of disagreement (anything other than a clean
        // entry-`Available`-to-branch-`Moved`/`Available` split) still
        // indicates a real bug and is still reported.
        if kind != ConsumeKind::Return
            && self.states.values().any(|s| *s == ResourceState::Error)
            && entry.values().all(|s| *s != ResourceState::Error)
        {
            self.diagnose_inconsistent_join(if_id, span);
        }
    }

    fn check_match_arms(
        &mut self,
        match_id: crate::hir::ExprId,
        span: Span,
        arms: &[HirMatchArm],
        kind: ConsumeKind,
    ) {
        let entry = self.states.clone();
        let mut branches = Vec::with_capacity(arms.len());
        for arm in arms {
            self.states = entry.clone();
            // One marker spans the pattern's own binding(s) *and* the
            // body (Blocker 4): recorded together, under the body's own
            // id, as this arm's one combined normal-completion exit --
            // reverse replay drains the body's own nested scope first
            // (already truncated away by its own `check_block_ctx`, if
            // it is a block) and the pattern's own binding(s) after,
            // exactly matching declaration order reversed.
            let marker = self.pending_cleanup.len();
            self.check_pattern(&arm.pattern);
            let (body_id, diverges, return_leaf_recorded) = match &arm.body {
                HirMatchArmBody::Expr(e) => {
                    self.check_expr_ctx(e, kind);
                    let diverges = self.diverges(e.id());
                    // A compound `return`'s own per-branch cleanup
                    // (Blocker 2), mirroring `check_block_ctx_inner`'s
                    // identical tail special-case: in a `Return`
                    // context this exact bare arm body *is* the leaf
                    // `nir::lower`'s own `lower_into_return_sink`
                    // replays cleanup for, so it needs its own
                    // whole-function (marker-0) snapshot -- taken here,
                    // before this arm's own state joins any sibling.
                    // Recorded *instead of* (not in addition to) the
                    // arm-local-marker version below, which shares this
                    // exact same id (an Expr body's own id) for a bare
                    // arm -- recording both would let whichever ran
                    // second silently overwrite the other's entry. Only
                    // when this whole `match` is itself the resource
                    // actually being return-sunk (`is_affine_expr`):
                    // `kind` alone is not enough to tell apart "this
                    // exact leaf is a compound-return-sink leaf" from "a
                    // `match` producing some unrelated, non-affine value
                    // merely sits inside a `return`'s own operand, and
                    // `kind` propagates through it for some *other*,
                    // unrelated resource nested inside one of its arms"
                    // -- the latter must never let this override the
                    // arm-local entry `nir::lower`'s own ordinary
                    // (non-sink) `lower_arm_body` still depends on.
                    let return_leaf_recorded =
                        kind == ConsumeKind::Return && self.is_affine_expr(match_id);
                    if return_leaf_recorded && !diverges {
                        self.record_exit(e.id(), 0);
                    }
                    (e.id(), diverges, return_leaf_recorded)
                }
                HirMatchArmBody::Block(block) => {
                    // `check_block_ctx_body`, not `check_block_ctx`:
                    // this block's own scope is not recorded/truncated
                    // separately under its own id -- this arm's own
                    // wider marker (opened above, before the pattern)
                    // already spans it, so it is recorded once, below,
                    // combined with the pattern's own binding(s). A
                    // `Return` context's own whole-function snapshot is
                    // already handled independently, keyed by this
                    // block's own *tail expression*'s id (never
                    // `block.id` itself), by `check_block_ctx_inner`,
                    // so there is no id collision here to guard against.
                    self.check_block_ctx_body(block, kind);
                    (block.id, self.diverges(block.id), false)
                }
            };
            if !diverges && !return_leaf_recorded {
                self.record_exit(body_id, marker);
            }
            self.pending_cleanup.truncate(marker);
            let mut locals = Vec::new();
            Self::pattern_locals(&arm.pattern, &mut locals);
            for local in locals {
                self.states.remove(&Place::root(local));
            }
            branches.push((self.states.clone(), diverges));
        }
        self.states = join_branch_states(&entry, &branches);
        // See `check_if`'s identical guard: in a `Return` context, two
        // arms disagreeing about exactly which underlying resource
        // their own shared tail moved is the expected shape of a
        // compound return (`nir::lower` already gives each arm its own
        // independent per-branch cleanup+terminate), not a real
        // ambiguity -- nothing ever reads `self.states` again on either
        // path, since both already end the function right here.
        if kind != ConsumeKind::Return
            && self.states.values().any(|s| *s == ResourceState::Error)
            && entry.values().all(|s| *s != ResourceState::Error)
        {
            self.diagnose_inconsistent_join(match_id, span);
        }
    }

    fn check_handle_arms(
        &mut self,
        handle_id: crate::hir::ExprId,
        span: Span,
        arms: &[HirHandleArm],
        kind: ConsumeKind,
    ) {
        let entry = self.states.clone();
        let mut branches = Vec::with_capacity(arms.len());
        for arm in arms {
            self.states = entry.clone();
            // See `check_match_arms`'s own equivalent comment: one
            // marker spans every pattern this arm binds *and* its own
            // body, recorded together as this arm's one combined
            // normal-completion exit.
            let marker = self.pending_cleanup.len();
            let mut locals = Vec::new();
            if let HirHandleArmKind::Success(pattern) = &arm.kind {
                self.check_pattern(pattern);
                Self::pattern_locals(pattern, &mut locals);
            } else if let HirHandleArmKind::Failure(HirFailurePattern::Case { args, .. }) =
                &arm.kind
            {
                for pattern in args {
                    self.check_pattern(pattern);
                    Self::pattern_locals(pattern, &mut locals);
                }
            }
            let (body_id, diverges, return_leaf_recorded) = match &arm.body {
                HirMatchArmBody::Expr(e) => {
                    self.check_expr_ctx(e, kind);
                    let diverges = self.diverges(e.id());
                    // See `check_match_arms`'s own identical handling
                    // (including the `is_affine_expr` guard: `kind`
                    // alone does not tell apart this whole `handle`
                    // itself being return-sunk from it merely sitting,
                    // non-affine, inside a `return`'s own operand while
                    // some *other* resource nested in one of its arms is
                    // what `kind` actually still needs to reach).
                    let return_leaf_recorded =
                        kind == ConsumeKind::Return && self.is_affine_expr(handle_id);
                    if return_leaf_recorded && !diverges {
                        self.record_exit(e.id(), 0);
                    }
                    (e.id(), diverges, return_leaf_recorded)
                }
                HirMatchArmBody::Block(block) => {
                    self.check_block_ctx_body(block, kind);
                    (block.id, self.diverges(block.id), false)
                }
            };
            if !diverges && !return_leaf_recorded {
                self.record_exit(body_id, marker);
            }
            self.pending_cleanup.truncate(marker);
            for local in locals {
                self.states.remove(&Place::root(local));
            }
            branches.push((self.states.clone(), diverges));
        }
        self.states = join_branch_states(&entry, &branches);
        // See `check_if`'s identical guard.
        if kind != ConsumeKind::Return
            && self.states.values().any(|s| *s == ResourceState::Error)
            && entry.values().all(|s| *s != ResourceState::Error)
        {
            self.diagnose_inconsistent_join(handle_id, span);
        }
    }

    /// `Some(flags)` when `callee` is a resolved reference to a
    /// function/extend-method this module's own `take_flags` table has
    /// an entry for; `None` otherwise (an unresolved name, a variant
    /// case constructor, a protocol method), treated as "no `take`
    /// parameters at all" by every caller.
    fn take_flags_for_callee(&self, callee: &HirExpr) -> Option<&'a Vec<bool>> {
        match callee {
            HirExpr::Function { item, .. } => self.take_flags.get(item),
            _ => None,
        }
    }

    /// Registers every resource-typed local `pattern` binds as a fresh
    /// owned value, `Available` from this exact point in this arm's own
    /// scope onward (`rfcs/0011`, Blocker 4) -- in practice only ever a
    /// `handle` `success` pattern (a `match`/ordinary `handle` failure
    /// pattern's own bound locals come from a variant's payload, which
    /// `RESOURCE_FIELD_IN_ORDINARY_AGGREGATE` already forbids from ever
    /// being affine), but walked structurally rather than special-cased
    /// to `success` specifically, so nothing here depends on that
    /// invariant holding forever to stay sound.
    fn check_pattern(&mut self, pattern: &HirPattern) {
        match pattern {
            HirPattern::Bind { local, .. } => {
                if self.is_resource_local(*local) {
                    self.states
                        .insert(Place::root(*local), ResourceState::Available);
                    self.pending_cleanup
                        .push(CleanupAction::Drop(Place::root(*local)));
                }
            }
            HirPattern::Variant { args, .. } => {
                for arg in args {
                    self.check_pattern(arg);
                }
            }
            HirPattern::Wildcard { .. }
            | HirPattern::Int { .. }
            | HirPattern::Str { .. }
            | HirPattern::Char { .. }
            | HirPattern::Bool { .. } => {}
        }
    }

    /// Every `LocalId` `pattern` itself directly binds (Blocker 4) --
    /// used to strip an arm-scoped pattern binding back out of that
    /// arm's own final state snapshot before it is joined with its
    /// siblings, exactly like a `while`/`loop` body's own internally
    /// declared resource is never compared against loop entry: a local
    /// that does not exist outside this one arm must never leak into
    /// the state joined for code that runs after every arm, whichever
    /// one actually ran.
    fn pattern_locals(pattern: &HirPattern, out: &mut Vec<LocalId>) {
        match pattern {
            HirPattern::Bind { local, .. } => out.push(*local),
            HirPattern::Variant { args, .. } => {
                for arg in args {
                    Self::pattern_locals(arg, out);
                }
            }
            HirPattern::Wildcard { .. }
            | HirPattern::Int { .. }
            | HirPattern::Str { .. }
            | HirPattern::Char { .. }
            | HirPattern::Bool { .. } => {}
        }
    }

    fn diagnose_inconsistent_join(&mut self, id: crate::hir::ExprId, span: Span) {
        let _ = id;
        self.diagnose(
            INCONSISTENT_BRANCH_STATE,
            span,
            "reachable branches disagree about a resource's own state; a later use has no \
             single state to check against"
                .to_string(),
            "inconsistent resource state across branches",
        );
    }
}

/// Joins `entry` with every *reachable* (non-diverging) branch's own
/// exit state (`rfcs/0011`'s own "Joins" section) -- a diverging branch
/// contributes nothing at all, exactly like `Ty::Never` never
/// contributing to an ordinary type join. If every branch diverges, the
/// join itself is unreachable code; `entry` is returned unchanged (there
/// is no reachable use past this point for it to matter).
/// Only ever produces a state for a place whose own *root* is already
/// present in `entry` (Blocker 11): a local one specific branch/arm
/// declares fresh -- an ordinary binding local to its own block, or a
/// `handle` pattern's own binding -- does not exist outside that
/// branch/arm at all, and must never leak into the state checked for
/// whichever one actually ran. A *field* of an aggregate whose own root
/// *is* already tracked in `entry` is still compared even if this is
/// the first branch to ever touch that exact field (`rfcs/0012`): its
/// implicit default on every other branch is simply its own state in
/// `entry` (typically `Available`, its untouched default) -- skipping
/// it just because no branch had touched it *yet* would silently miss
/// exactly the "moved on only one branch" case this join exists to
/// catch.
fn join_branch_states(entry: &PlaceStates, branches: &[(PlaceStates, bool)]) -> PlaceStates {
    let reachable: Vec<&PlaceStates> = branches
        .iter()
        .filter(|(_, diverges)| !*diverges)
        .map(|(states, _)| states)
        .collect();
    let Some((first, rest)) = reachable.split_first() else {
        return entry.clone();
    };
    let tracked_roots: HashSet<LocalId> = entry.keys().map(|p| p.root).collect();
    let mut keys: BTreeSet<Place<LocalId>> = entry.keys().cloned().collect();
    for branch in &reachable {
        for key in branch.keys() {
            if tracked_roots.contains(&key.root) {
                keys.insert(key.clone());
            }
        }
    }
    let default_for = |key: &Place<LocalId>| -> ResourceState {
        entry.get(key).copied().unwrap_or(ResourceState::Available)
    };
    let mut joined: PlaceStates = keys
        .iter()
        .map(|key| {
            let state = first.get(key).copied().unwrap_or_else(|| default_for(key));
            (key.clone(), state)
        })
        .collect();
    for other in rest {
        for (key, state) in joined.iter_mut() {
            let other_state = other.get(key).copied().unwrap_or_else(|| default_for(key));
            *state = state.join(other_state);
        }
    }
    joined
}

/// Every resource-typed local a defer's own expression reads (bare
/// `Local` occurrences anywhere within it, including inside a nested
/// `if`/`match`/`handle`/block/record-literal argument), used to
/// promote each one still `Available` to `DropScheduled`. Deliberately
/// a plain, direct collection (not `check_expr`'s own move-aware walk):
/// a `defer`'s argument evaluation already ran through `check_expr` for
/// its own diagnostics; this second, narrow pass only needs *which*
/// locals it touched, not to re-validate them. Exhaustive over every
/// `HirExpr`/`HirStmt` shape (no wildcard arm) on purpose: an
/// incomplete recursion here would under-protect a value a pending
/// `defer` still needs whenever it is observed through anything other
/// than a bare call argument, letting a later `drop`/move of it slip
/// past this stage's own `U0004` check undetected.
/// Appends `place` unless it is already recorded -- a `Vec` rather than
/// a `HashSet` specifically so the protected places stay in a
/// deterministic, source-order sequence no `HashMap`/`HashSet`
/// iteration order can perturb.
fn push_place(out: &mut Vec<Place<LocalId>>, place: Place<LocalId>) {
    if !out.contains(&place) {
        out.push(place);
    }
}

fn collect_observed_places(checker: &FlowChecker, expr: &HirExpr, out: &mut Vec<Place<LocalId>>) {
    match expr {
        HirExpr::Int { .. }
        | HirExpr::Float { .. }
        | HirExpr::Str { .. }
        | HirExpr::Char { .. }
        | HirExpr::Bool { .. }
        | HirExpr::Function { .. }
        | HirExpr::CaseRef { .. }
        | HirExpr::ProtocolMethodRef { .. }
        | HirExpr::Continue { .. }
        | HirExpr::Error { .. } => {}
        HirExpr::Local { local, .. } => push_place(out, Place::root(*local)),
        HirExpr::Unary { operand, .. }
        | HirExpr::Cast { expr: operand, .. }
        | HirExpr::Try { expr: operand, .. } => collect_observed_places(checker, operand, out),
        HirExpr::Binary { left, right, .. } => {
            collect_observed_places(checker, left, out);
            collect_observed_places(checker, right, out);
        }
        HirExpr::Assign { target, value, .. } => {
            collect_observed_places(checker, target, out);
            collect_observed_places(checker, value, out);
        }
        HirExpr::Call { callee, args, .. } => {
            collect_observed_places(checker, callee, out);
            for arg in args {
                collect_observed_places(checker, arg, out);
            }
        }
        // The exact place, when this access resolves to a stable affine
        // one (`rfcs/0012`): `defer inspect(session.input)` protects
        // `session.input` itself, never the whole `session` root it is
        // reached through -- an unaffected sibling (`session.output`)
        // must stay freely movable while the defer is pending. Anything
        // else (a non-affine field, or a chain rooted in a temporary)
        // keeps the original root-granularity behavior.
        HirExpr::Field { base, .. } => {
            if checker.is_affine_expr(expr.id())
                && let Some(place) = checker.resolve_place(expr)
            {
                push_place(out, place);
            } else {
                collect_observed_places(checker, base, out);
            }
        }
        HirExpr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            collect_observed_places(checker, condition, out);
            collect_observed_places_block(checker, then_branch, out);
            match else_branch {
                Some(HirElse::Block(block)) => collect_observed_places_block(checker, block, out),
                Some(HirElse::If(inner)) => collect_observed_places(checker, inner, out),
                None => {}
            }
        }
        HirExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_observed_places(checker, scrutinee, out);
            for arm in arms {
                collect_observed_places_arm_body(checker, &arm.body, out);
            }
        }
        HirExpr::Block(block) => collect_observed_places_block(checker, block, out),
        HirExpr::Return { value, .. } | HirExpr::Break { value, .. } => {
            if let Some(value) = value {
                collect_observed_places(checker, value, out);
            }
        }
        HirExpr::RecordLiteral { fields, .. } => {
            for field in fields {
                collect_observed_places(checker, &field.value, out);
            }
        }
        HirExpr::Raise { operand, .. } => collect_observed_places(checker, operand, out),
        HirExpr::Handle { operand, arms, .. } => {
            collect_observed_places(checker, operand, out);
            for arm in arms {
                collect_observed_places_arm_body(checker, &arm.body, out);
            }
        }
    }
}

fn collect_observed_places_arm_body(
    checker: &FlowChecker,
    body: &HirMatchArmBody,
    out: &mut Vec<Place<LocalId>>,
) {
    match body {
        HirMatchArmBody::Expr(e) => collect_observed_places(checker, e, out),
        HirMatchArmBody::Block(block) => collect_observed_places_block(checker, block, out),
    }
}

fn collect_observed_places_block(
    checker: &FlowChecker,
    block: &HirBlock,
    out: &mut Vec<Place<LocalId>>,
) {
    for stmt in &block.statements {
        match stmt {
            HirStmt::Binding(b) => collect_observed_places(checker, &b.value, out),
            HirStmt::Expr(e) => collect_observed_places(checker, e, out),
            HirStmt::Defer { expr, .. } | HirStmt::Drop { expr, .. } => {
                collect_observed_places(checker, expr, out)
            }
            HirStmt::While {
                condition, body, ..
            } => {
                collect_observed_places(checker, condition, out);
                collect_observed_places_block(checker, body, out);
            }
            HirStmt::Loop { body, .. } => collect_observed_places_block(checker, body, out),
        }
    }
    if let Some(tail) = &block.tail {
        collect_observed_places(checker, tail, out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_branch_local_key_absent_from_every_other_branch_is_dropped_from_the_join() {
        // Blocker 11: a local one specific branch declares fresh (an
        // ordinary block-scoped binding, or a `handle` pattern's own
        // binding after `check_handle_arms`'s own explicit strip) must
        // never survive into the state checked for code after every
        // branch, regardless of which branch actually ran.
        let entry: PlaceStates =
            HashMap::from([(Place::root(LocalId(0)), ResourceState::Available)]);
        let first: PlaceStates = HashMap::from([
            (Place::root(LocalId(0)), ResourceState::Moved),
            (Place::root(LocalId(1)), ResourceState::Available), // branch-local, absent from entry
        ]);
        let second: PlaceStates = HashMap::from([(Place::root(LocalId(0)), ResourceState::Moved)]);
        let joined = join_branch_states(&entry, &[(first, false), (second, false)]);
        assert_eq!(
            joined,
            HashMap::from([(Place::root(LocalId(0)), ResourceState::Moved)]),
            "a branch-local key must not appear in the joined state at all"
        );
    }

    #[test]
    fn every_reachable_branchs_own_state_for_an_entry_local_still_agrees_or_joins_to_error() {
        let entry: PlaceStates =
            HashMap::from([(Place::root(LocalId(0)), ResourceState::Available)]);
        let agreeing: PlaceStates =
            HashMap::from([(Place::root(LocalId(0)), ResourceState::Moved)]);
        let disagreeing: PlaceStates =
            HashMap::from([(Place::root(LocalId(0)), ResourceState::Available)]);
        let joined = join_branch_states(&entry, &[(agreeing, false), (disagreeing, false)]);
        assert_eq!(
            joined.get(&Place::root(LocalId(0))),
            Some(&ResourceState::Error)
        );
    }

    /// A call whose own callee resolves directly to a declared function
    /// (`HirExpr::Function`), but this checker's own `take_flags` table
    /// has no entry for it at all -- always unreachable for HIR that
    /// actually passed `hir::lower`'s own name resolution first (every
    /// declared function gets an entry); reachable only through
    /// hand-built HIR fed straight to this stage, exactly as
    /// constructed here. Must be diagnosed (`MALFORMED_CALLEE_TAKE_
    /// FLAGS`), never silently treated as "every argument observes".
    #[test]
    fn a_resolved_callee_missing_from_take_flags_is_diagnosed_not_silently_observed() {
        let local_types: HashMap<LocalId, Ty> = HashMap::new();
        let expr_types: HashMap<crate::hir::ExprId, Ty> = HashMap::new();
        let affine_items: HashSet<ItemId> = HashSet::new();
        let variant_items: HashSet<ItemId> = HashSet::new();
        let take_flags: HashMap<ItemId, Vec<bool>> = HashMap::new();
        let aggregate_field_types: HashMap<ItemId, Vec<Ty>> = HashMap::new();
        let declared_resources: HashSet<ItemId> = HashSet::new();
        let item_type_params: HashMap<ItemId, Vec<TypeParamId>> = HashMap::new();
        let field_projections: HashMap<ExprId, (ItemId, usize)> = HashMap::new();
        let affine = AffineContext {
            aggregate_field_types: &aggregate_field_types,
            declared_resources: &declared_resources,
            item_type_params: &item_type_params,
            field_projections: &field_projections,
        };
        let mut map = crate::source::SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let g_name = interner.intern("g");
        let mut diagnostics = Vec::new();
        let mut checker = FlowChecker::new(
            &local_types,
            &expr_types,
            &affine_items,
            &variant_items,
            &take_flags,
            &affine,
            source,
            &interner,
            &mut diagnostics,
        );
        let callee = HirExpr::Function {
            id: crate::hir::ExprId(0),
            item: ItemId(0),
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        let call_expr = HirExpr::Call {
            id: crate::hir::ExprId(1),
            callee: Box::new(callee),
            args: Vec::new(),
            span: Span::dummy(),
        };
        checker.check_expr_ctx(&call_expr, ConsumeKind::Read);
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code == MALFORMED_CALLEE_TAKE_FLAGS),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    /// Same shape as above, but the callee *does* have a `take_flags`
    /// entry -- just the wrong length for this exact call's own
    /// argument count.
    #[test]
    fn a_take_flags_length_disagreeing_with_the_call_arity_is_diagnosed() {
        let local_types: HashMap<LocalId, Ty> = HashMap::new();
        let expr_types: HashMap<crate::hir::ExprId, Ty> = HashMap::new();
        let affine_items: HashSet<ItemId> = HashSet::new();
        let variant_items: HashSet<ItemId> = HashSet::new();
        let mut take_flags: HashMap<ItemId, Vec<bool>> = HashMap::new();
        take_flags.insert(ItemId(0), vec![false, false]);
        let aggregate_field_types: HashMap<ItemId, Vec<Ty>> = HashMap::new();
        let declared_resources: HashSet<ItemId> = HashSet::new();
        let item_type_params: HashMap<ItemId, Vec<TypeParamId>> = HashMap::new();
        let field_projections: HashMap<ExprId, (ItemId, usize)> = HashMap::new();
        let affine = AffineContext {
            aggregate_field_types: &aggregate_field_types,
            declared_resources: &declared_resources,
            item_type_params: &item_type_params,
            field_projections: &field_projections,
        };
        let mut map = crate::source::SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let g_name = interner.intern("g");
        let mut diagnostics = Vec::new();
        let mut checker = FlowChecker::new(
            &local_types,
            &expr_types,
            &affine_items,
            &variant_items,
            &take_flags,
            &affine,
            source,
            &interner,
            &mut diagnostics,
        );
        let callee = HirExpr::Function {
            id: crate::hir::ExprId(0),
            item: ItemId(0),
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        // Only one argument, but `take_flags` above declares two.
        let call_expr = HirExpr::Call {
            id: crate::hir::ExprId(1),
            callee: Box::new(callee),
            args: vec![HirExpr::Bool {
                id: crate::hir::ExprId(2),
                value: true,
                span: Span::dummy(),
            }],
            span: Span::dummy(),
        };
        checker.check_expr_ctx(&call_expr, ConsumeKind::Read);
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code == MALFORMED_CALLEE_TAKE_FLAGS),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }
}
