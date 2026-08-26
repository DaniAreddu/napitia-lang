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

use std::collections::{HashMap, HashSet};

use crate::diagnostics::Diagnostic;
use crate::hir::{
    HirBinding, HirBlock, HirElse, HirExpr, HirFailurePattern, HirFunction, HirHandleArm,
    HirHandleArmKind, HirMatchArm, HirMatchArmBody, HirPattern, HirStmt, ItemId, LocalId,
};
use crate::source::{SourceId, Span};
use crate::symbol::Interner;
use crate::types::Ty;

use super::state::ResourceState;

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
    pub const INCONSISTENT_BRANCH_STATE: &str = "U0006";
    /// A `while`/`loop` body's own end state for a resource binding
    /// declared outside the loop disagrees with its state on entry --
    /// a second iteration could not safely reuse it.
    pub const LOOP_CARRIED_INVALIDATION: &str = "U0007";
    /// A resource-typed `match`/`handle` (any consuming position), or a
    /// resource-typed `if` in a consuming position other than `return`/
    /// the function's own implicit tail, whose own value is directly
    /// moved, bound, assigned, passed to a `take` parameter, stored in
    /// a constructed aggregate, or raised. `nir::lower` can only push a
    /// `return`'s own per-branch cleanup into a nested `if`/block's own
    /// branches (`rfcs/0011`); every other compound origin shape (and
    /// `match`/`handle` even as a `return`'s own operand) has no sound
    /// lowering this milestone, so it is rejected here rather than
    /// silently mis-lowered into a double-drop or a leak.
    pub const UNSUPPORTED_COMPOUND_RESOURCE_ORIGIN: &str = "U0008";
    /// A resource-typed field projected out of its containing resource
    /// (`box.file`) is moved, bound, assigned, passed to a `take`
    /// parameter, stored, raised, or scheduled through `defer`
    /// (Blocker 3). Only a *whole* resource binding may ever be moved
    /// this milestone -- a partial/field-level move is not tracked at
    /// all, so allowing one here would silently let `box`'s own
    /// `file` field be read again later as if it were still owned,
    /// double-destroying it (once through whatever the field's own
    /// extracted value fed into, once through `box`'s own eventual
    /// destruction).
    pub const RESOURCE_FIELD_EXTRACTION: &str = "U0009";
    /// A `mutable` resource-typed binding is reassigned while it still
    /// owns an available (or `defer`-protected) value (Blocker 4) --
    /// overwriting it without first moving or dropping the old value
    /// would leak it, since nothing would ever destroy it again.
    /// Reassignment is only accepted once the path-sensitive state
    /// proves the slot is provably empty (`Moved`/`Dropped`) on every
    /// incoming path.
    pub const REASSIGNMENT_OF_LIVE_RESOURCE: &str = "U0010";
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
    /// branch of a nested `if`/block separately (Blocker 2), so a
    /// resource-typed `if` is accepted here even when its two branches
    /// resolve to different underlying locals; `match`/`handle` are
    /// still not supported even in this position.
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
    break_states: Vec<HashMap<LocalId, ResourceState>>,
    continue_states: Vec<HashMap<LocalId, ResourceState>>,
}

pub struct FlowChecker<'a> {
    local_types: &'a HashMap<LocalId, Ty>,
    expr_types: &'a HashMap<crate::hir::ExprId, Ty>,
    affine_items: &'a HashSet<ItemId>,
    /// Every known function/extend-method's own per-parameter `take`
    /// flags, by `ItemId`, in declared order -- read back to decide
    /// whether a `Call` argument transfers ownership or merely observes
    /// (`rfcs/0011`). A callee absent here (an unresolved name, a
    /// variant case constructor, a protocol method whose concrete
    /// implementation isn't known syntactically) is treated as having
    /// no `take` parameters at all, matching this milestone's own
    /// observation-by-default rule.
    take_flags: &'a HashMap<ItemId, Vec<bool>>,
    source: SourceId,
    interner: &'a Interner,
    diagnostics: &'a mut Vec<Diagnostic>,
    /// Every resource-typed *owned* local's own current state -- take
    /// parameters and `value`/`mutable` bindings. A local absent here is
    /// either not a resource type at all, or an ordinary (observing)
    /// parameter (see `observing` below).
    states: HashMap<LocalId, ResourceState>,
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
    defer_scopes: Vec<HashSet<LocalId>>,
}

impl<'a> FlowChecker<'a> {
    pub fn new(
        local_types: &'a HashMap<LocalId, Ty>,
        expr_types: &'a HashMap<crate::hir::ExprId, Ty>,
        affine_items: &'a HashSet<ItemId>,
        take_flags: &'a HashMap<ItemId, Vec<bool>>,
        source: SourceId,
        interner: &'a Interner,
        diagnostics: &'a mut Vec<Diagnostic>,
    ) -> Self {
        Self {
            local_types,
            expr_types,
            affine_items,
            take_flags,
            source,
            interner,
            diagnostics,
            states: HashMap::new(),
            observing: HashSet::new(),
            loop_stack: Vec::new(),
            defer_scopes: Vec::new(),
        }
    }

    pub fn check_function(&mut self, f: &HirFunction) {
        for param in &f.params {
            if !self.is_resource_local(param.local) {
                continue;
            }
            if param.take {
                self.states.insert(param.local, ResourceState::Available);
            } else {
                self.observing.insert(param.local);
            }
        }
        self.check_block_ctx(&f.body, ConsumeKind::Return);
    }

    fn is_resource_local(&self, local: LocalId) -> bool {
        self.local_types
            .get(&local)
            .is_some_and(|ty| self.is_affine(ty))
    }

    fn is_affine(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Named(item, _) if self.affine_items.contains(item))
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
        self.defer_scopes.push(HashSet::new());
        self.check_block_ctx_inner(block, kind);
        let scope = self.defer_scopes.pop().expect("pushed immediately above");
        for local in scope {
            if let Some(ResourceState::DropScheduled) = self.states.get(&local) {
                self.states.insert(local, ResourceState::Available);
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
        }
    }

    fn stmt_diverges(&self, stmt: &HirStmt) -> bool {
        match stmt {
            HirStmt::Expr(e) => self.diverges(e.id()),
            HirStmt::Binding(b) => self.diverges(b.value.id()),
            HirStmt::Drop { .. }
            | HirStmt::Defer { .. }
            | HirStmt::While { .. }
            | HirStmt::Loop { .. } => false,
        }
    }

    fn check_block(&mut self, block: &HirBlock) {
        self.check_block_ctx(block, ConsumeKind::Read);
    }

    fn check_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::Binding(b) => self.check_binding(b),
            HirStmt::Expr(e) => self.check_expr(e),
            HirStmt::Defer { expr, span } => self.check_defer(expr, *span),
            HirStmt::Drop { expr, span } => self.check_drop(expr, *span),
            HirStmt::While {
                condition, body, ..
            } => {
                self.check_expr(condition);
                self.check_loop_body(body);
            }
            HirStmt::Loop { body, .. } => self.check_loop_body(body),
        }
    }

    fn check_binding(&mut self, b: &HirBinding) {
        self.check_expr_ctx(&b.value, ConsumeKind::Other);
        if self.is_resource_local(b.local) {
            self.states.insert(b.local, ResourceState::Available);
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
    fn check_defer(&mut self, expr: &HirExpr, _span: Span) {
        self.check_expr(expr);
        let mut observed = HashSet::new();
        collect_observed_locals(expr, &mut observed);
        for local in observed {
            if let Some(ResourceState::Available) = self.states.get(&local) {
                self.states.insert(local, ResourceState::DropScheduled);
                // Blocker 9: remembered against *this* defer's own
                // enclosing block so `check_block_ctx` can release this
                // exact protection once that block's own walk ends,
                // rather than leaving it protected indefinitely.
                if let Some(scope) = self.defer_scopes.last_mut() {
                    scope.insert(local);
                }
            }
        }
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
        let Some(state) = self.states.get(local).copied() else {
            return;
        };
        match state {
            ResourceState::Available => {
                self.states.insert(*local, ResourceState::Dropped);
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
                self.states.insert(*local, ResourceState::Error);
            }
            ResourceState::Dropped => {
                self.diagnose(
                    DOUBLE_DROP,
                    span,
                    format!("`{}` was already dropped", self.local_name(*local, *name)),
                    "double drop",
                );
                self.states.insert(*local, ResourceState::Error);
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
                self.states.insert(*local, ResourceState::Error);
            }
        }
    }

    /// A `while`/`loop` body is checked once, from a clone of the
    /// current entry state (Blocker 2). Three distinct edges can carry a
    /// resource local's own state back into the *next* iteration's own
    /// entry: the body's own ordinary fallthrough end, and every
    /// `continue` reached anywhere inside it -- each must agree with
    /// `entry` for every resource local declared outside the loop, since
    /// a second iteration reuses that exact entry state regardless of
    /// which of these edges actually produced it. `break` is different:
    /// it never re-enters the loop at all, so its own live state instead
    /// contributes directly to the state *after* the loop statement,
    /// alongside a `while`'s own condition-false exit -- which, once the
    /// backedge invariant above is proven, is just `entry` again (an
    /// untaken loop, or one that already proved every iteration restores
    /// exactly `entry`). A resource local the loop body itself
    /// *declares* is scoped to one iteration and never compared this way
    /// (comparing against entry, where it never existed, would be
    /// meaningless) -- excluded by only comparing keys already present
    /// on entry.
    fn check_loop_body(&mut self, body: &HirBlock) {
        let entry = self.states.clone();
        self.loop_stack.push(LoopFrame::default());
        self.check_block(body);
        let fallthrough_reachable = !self.diverges(body.id);
        let fallthrough_state = std::mem::replace(&mut self.states, entry.clone());
        let frame = self
            .loop_stack
            .pop()
            .expect("this exact push is right above");

        let mut backedges: Vec<&HashMap<LocalId, ResourceState>> =
            frame.continue_states.iter().collect();
        if fallthrough_reachable {
            backedges.push(&fallthrough_state);
        }

        let mut poisoned: HashSet<LocalId> = HashSet::new();
        for (local, entry_state) in &entry {
            if *entry_state == ResourceState::Error {
                continue;
            }
            let disagrees = backedges.iter().any(|backedge| {
                let backedge_state = backedge.get(local).copied().unwrap_or(*entry_state);
                backedge_state != *entry_state && backedge_state != ResourceState::Error
            });
            if disagrees {
                poisoned.insert(*local);
            }
        }
        for _ in &poisoned {
            self.diagnose(
                LOOP_CARRIED_INVALIDATION,
                body.span,
                "a resource's own state reaching the top of this loop again (through the body's \
                 own fallthrough or a `continue`) disagrees with its state on entry; a later \
                 iteration could not safely reuse it"
                    .to_string(),
                "loop-carried resource invalidation",
            );
        }

        let mut after = entry;
        for local in &poisoned {
            after.insert(*local, ResourceState::Error);
        }
        for break_state in &frame.break_states {
            for (local, current) in after.iter_mut() {
                if poisoned.contains(local) {
                    continue;
                }
                let state = break_state.get(local).copied().unwrap_or(*current);
                *current = current.join(state);
            }
        }
        self.states = after;
    }

    // -- Expressions -----------------------------------------------------

    fn check_expr(&mut self, expr: &HirExpr) {
        self.check_expr_ctx(expr, ConsumeKind::Read);
    }

    /// Checks `expr` in `kind`'s own context (`rfcs/0011`, Blocker 2).
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
    fn check_expr_ctx(&mut self, expr: &HirExpr, kind: ConsumeKind) {
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
            HirExpr::Continue { .. } => {
                let state = self.states.clone();
                if let Some(frame) = self.loop_stack.last_mut() {
                    frame.continue_states.push(state);
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
                self.check_expr_ctx(value, ConsumeKind::Other);
                if let HirExpr::Local {
                    local, name, span, ..
                } = target.as_ref()
                    && self.is_resource_local(*local)
                {
                    self.check_reassignment(*local, *name, *span);
                } else {
                    self.check_expr(target);
                }
            }
            HirExpr::Call { callee, args, .. } => {
                self.check_expr(callee);
                let take_flags = self.take_flags_for_callee(callee);
                for (index, arg) in args.iter().enumerate() {
                    let takes = take_flags
                        .and_then(|flags| flags.get(index))
                        .copied()
                        .unwrap_or(false);
                    self.check_expr_ctx(
                        arg,
                        if takes {
                            ConsumeKind::Other
                        } else {
                            ConsumeKind::Read
                        },
                    );
                }
            }
            HirExpr::Field { base, id, span, .. } => {
                self.check_expr(base);
                if kind != ConsumeKind::Read && self.is_affine_expr(*id) {
                    self.diagnose(
                        RESOURCE_FIELD_EXTRACTION,
                        *span,
                        "a resource-typed field cannot be moved, bound, assigned, passed to a \
                         `take` parameter, stored, raised, or scheduled through `defer` this \
                         milestone; only a whole resource binding may ever be moved, never a \
                         field projected out of one"
                            .to_string(),
                        "resource field extraction",
                    );
                }
            }
            HirExpr::Cast { expr, .. } => self.check_expr(expr),
            HirExpr::Try { expr, .. } => self.check_expr(expr),
            HirExpr::If {
                condition,
                then_branch,
                else_branch,
                id,
                ..
            } => {
                self.check_expr(condition);
                let kind = self.check_compound_origin(*id, kind, "if");
                self.check_if(*id, then_branch, else_branch.as_ref(), kind);
            }
            HirExpr::Match {
                scrutinee,
                arms,
                id,
                ..
            } => {
                self.check_expr(scrutinee);
                let kind = self.check_compound_origin(*id, kind, "match");
                self.check_match_arms(*id, arms, kind);
            }
            HirExpr::Block(block) => self.check_block_ctx(block, kind),
            HirExpr::Return { value, .. } => {
                if let Some(value) = value {
                    self.check_expr_ctx(value, ConsumeKind::Return);
                }
            }
            HirExpr::Break { value, .. } => {
                if let Some(value) = value {
                    self.check_expr_ctx(value, ConsumeKind::Other);
                }
                let state = self.states.clone();
                if let Some(frame) = self.loop_stack.last_mut() {
                    frame.break_states.push(state);
                }
            }
            HirExpr::RecordLiteral { fields, .. } => {
                for field in fields {
                    self.check_expr_ctx(&field.value, ConsumeKind::Other);
                }
            }
            HirExpr::Raise { operand, .. } => {
                self.check_expr_ctx(operand, ConsumeKind::Other);
            }
            HirExpr::Handle {
                operand, arms, id, ..
            } => {
                self.check_expr(operand);
                let kind = self.check_compound_origin(*id, kind, "handle");
                self.check_handle_arms(*id, arms, kind);
            }
        }
    }

    /// Rejects a resource-typed `match`/`handle`, or a resource-typed
    /// `if` used in a consuming position other than `return`, with
    /// [`UNSUPPORTED_COMPOUND_RESOURCE_ORIGIN`] (Blocker 2:
    /// `nir::lower` cannot yet represent a compound origin there --
    /// see [`ConsumeKind`]) -- returning `ConsumeKind::Read` in that
    /// case so the rest of this walk still validates ordinary use/move
    /// correctness inside every branch/arm, just without pretending
    /// the construct's own overall value is soundly consumed. Returns
    /// `kind` unchanged whenever no rejection is needed (a `Read`
    /// context, a non-affine type, or -- for `if` specifically -- a
    /// `Return` context).
    fn check_compound_origin(
        &mut self,
        id: crate::hir::ExprId,
        kind: ConsumeKind,
        construct: &'static str,
    ) -> ConsumeKind {
        let supported = match kind {
            ConsumeKind::Read => true,
            ConsumeKind::Return => construct == "if",
            ConsumeKind::Other => false,
        };
        if supported || !self.is_affine_expr(id) {
            return kind;
        }
        self.diagnose(
            UNSUPPORTED_COMPOUND_RESOURCE_ORIGIN,
            Span::dummy(),
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
        let Some(state) = self.states.get(&local).copied() else {
            return;
        };
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
                self.states.insert(local, ResourceState::Error);
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
                self.states.insert(local, ResourceState::Error);
            }
        }
    }

    /// Transitions `local`'s own state to `Moved` -- the only shape an
    /// existing owned binding can be consumed *from* is a bare local
    /// reference naming one. Moving a resource-typed value *out of* a
    /// field (`take other.file`) is not supported this milestone --
    /// only a whole binding may ever be moved.
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
        let Some(state) = self.states.get(&local).copied() else {
            return;
        };
        match state {
            ResourceState::Available => {
                self.states.insert(local, ResourceState::Moved);
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
                self.states.insert(local, ResourceState::Error);
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
                self.states.insert(local, ResourceState::Error);
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
                self.states.insert(local, ResourceState::Error);
            }
        }
    }

    /// Reassigning a `mutable` resource-typed binding (Blocker 4):
    /// accepted -- and transitions `local` to `Available`, exactly
    /// like a fresh binding -- only when the path-sensitive state
    /// already proves the slot holds nothing needing destruction
    /// (`Moved`/`Dropped`) on every incoming path; an `Available` or
    /// `DropScheduled` old value would otherwise be silently
    /// overwritten and leaked, since nothing would ever destroy it
    /// again. A local absent from `self.states` (an ordinary, non-
    /// resource-typed target the caller already filtered out, or one
    /// this checker never saw declared) has nothing here to protect.
    fn check_reassignment(&mut self, local: LocalId, name: crate::symbol::Symbol, span: Span) {
        let Some(state) = self.states.get(&local).copied() else {
            return;
        };
        match state {
            ResourceState::Moved | ResourceState::Dropped => {
                self.states.insert(local, ResourceState::Available);
            }
            ResourceState::Error => {}
            ResourceState::Available | ResourceState::DropScheduled => {
                self.diagnose(
                    REASSIGNMENT_OF_LIVE_RESOURCE,
                    span,
                    format!(
                        "`{}` still owns a resource that was never moved or dropped; \
                         reassigning it would leak the old value",
                        self.local_name(local, name)
                    ),
                    "reassigning a live resource",
                );
                self.states.insert(local, ResourceState::Error);
            }
        }
    }

    // -- Joins -----------------------------------------------------------

    fn check_if(
        &mut self,
        if_id: crate::hir::ExprId,
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
            self.diagnose_inconsistent_join(if_id);
        }
    }

    fn check_match_arms(
        &mut self,
        match_id: crate::hir::ExprId,
        arms: &[HirMatchArm],
        kind: ConsumeKind,
    ) {
        let entry = self.states.clone();
        let mut branches = Vec::with_capacity(arms.len());
        for arm in arms {
            self.states = entry.clone();
            self.check_pattern(&arm.pattern);
            let diverges = match &arm.body {
                HirMatchArmBody::Expr(e) => {
                    self.check_expr_ctx(e, kind);
                    self.diverges(e.id())
                }
                HirMatchArmBody::Block(block) => {
                    self.check_block_ctx(block, kind);
                    self.diverges(block.id)
                }
            };
            branches.push((self.states.clone(), diverges));
        }
        self.states = join_branch_states(&entry, &branches);
        if self.states.values().any(|s| *s == ResourceState::Error)
            && entry.values().all(|s| *s != ResourceState::Error)
        {
            self.diagnose_inconsistent_join(match_id);
        }
    }

    fn check_handle_arms(
        &mut self,
        handle_id: crate::hir::ExprId,
        arms: &[HirHandleArm],
        kind: ConsumeKind,
    ) {
        let entry = self.states.clone();
        let mut branches = Vec::with_capacity(arms.len());
        for arm in arms {
            self.states = entry.clone();
            if let HirHandleArmKind::Success(pattern) = &arm.kind {
                self.check_pattern(pattern);
            } else if let HirHandleArmKind::Failure(HirFailurePattern::Case { args, .. }) =
                &arm.kind
            {
                for pattern in args {
                    self.check_pattern(pattern);
                }
            }
            let diverges = match &arm.body {
                HirMatchArmBody::Expr(e) => {
                    self.check_expr_ctx(e, kind);
                    self.diverges(e.id())
                }
                HirMatchArmBody::Block(block) => {
                    self.check_block_ctx(block, kind);
                    self.diverges(block.id)
                }
            };
            branches.push((self.states.clone(), diverges));
        }
        self.states = join_branch_states(&entry, &branches);
        if self.states.values().any(|s| *s == ResourceState::Error)
            && entry.values().all(|s| *s != ResourceState::Error)
        {
            self.diagnose_inconsistent_join(handle_id);
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

    fn check_pattern(&mut self, _pattern: &HirPattern) {
        // Pattern-bound locals are never resource-typed constructions in
        // this milestone's own surface (a `match`/`handle` scrutinee is
        // never itself a bare resource move target here): nothing to
        // track. Kept as an explicit no-op call site, not an omission,
        // so a future pattern-level resource binding has an obvious
        // place to extend.
    }

    fn diagnose_inconsistent_join(&mut self, id: crate::hir::ExprId) {
        let _ = id;
        self.diagnose(
            INCONSISTENT_BRANCH_STATE,
            Span::dummy(),
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
fn join_branch_states(
    entry: &HashMap<LocalId, ResourceState>,
    branches: &[(HashMap<LocalId, ResourceState>, bool)],
) -> HashMap<LocalId, ResourceState> {
    let reachable: Vec<&HashMap<LocalId, ResourceState>> = branches
        .iter()
        .filter(|(_, diverges)| !*diverges)
        .map(|(states, _)| states)
        .collect();
    let Some((first, rest)) = reachable.split_first() else {
        return entry.clone();
    };
    let mut joined = (*first).clone();
    for other in rest {
        for (local, state) in joined.iter_mut() {
            let other_state = other.get(local).copied().unwrap_or(*state);
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
fn collect_observed_locals(expr: &HirExpr, out: &mut HashSet<LocalId>) {
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
        HirExpr::Local { local, .. } => {
            out.insert(*local);
        }
        HirExpr::Unary { operand, .. }
        | HirExpr::Cast { expr: operand, .. }
        | HirExpr::Try { expr: operand, .. } => collect_observed_locals(operand, out),
        HirExpr::Binary { left, right, .. } => {
            collect_observed_locals(left, out);
            collect_observed_locals(right, out);
        }
        HirExpr::Assign { target, value, .. } => {
            collect_observed_locals(target, out);
            collect_observed_locals(value, out);
        }
        HirExpr::Call { callee, args, .. } => {
            collect_observed_locals(callee, out);
            for arg in args {
                collect_observed_locals(arg, out);
            }
        }
        HirExpr::Field { base, .. } => collect_observed_locals(base, out),
        HirExpr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            collect_observed_locals(condition, out);
            collect_observed_locals_block(then_branch, out);
            match else_branch {
                Some(HirElse::Block(block)) => collect_observed_locals_block(block, out),
                Some(HirElse::If(inner)) => collect_observed_locals(inner, out),
                None => {}
            }
        }
        HirExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_observed_locals(scrutinee, out);
            for arm in arms {
                collect_observed_locals_arm_body(&arm.body, out);
            }
        }
        HirExpr::Block(block) => collect_observed_locals_block(block, out),
        HirExpr::Return { value, .. } | HirExpr::Break { value, .. } => {
            if let Some(value) = value {
                collect_observed_locals(value, out);
            }
        }
        HirExpr::RecordLiteral { fields, .. } => {
            for field in fields {
                collect_observed_locals(&field.value, out);
            }
        }
        HirExpr::Raise { operand, .. } => collect_observed_locals(operand, out),
        HirExpr::Handle { operand, arms, .. } => {
            collect_observed_locals(operand, out);
            for arm in arms {
                collect_observed_locals_arm_body(&arm.body, out);
            }
        }
    }
}

fn collect_observed_locals_arm_body(body: &HirMatchArmBody, out: &mut HashSet<LocalId>) {
    match body {
        HirMatchArmBody::Expr(e) => collect_observed_locals(e, out),
        HirMatchArmBody::Block(block) => collect_observed_locals_block(block, out),
    }
}

fn collect_observed_locals_block(block: &HirBlock, out: &mut HashSet<LocalId>) {
    for stmt in &block.statements {
        match stmt {
            HirStmt::Binding(b) => collect_observed_locals(&b.value, out),
            HirStmt::Expr(e) => collect_observed_locals(e, out),
            HirStmt::Defer { expr, .. } | HirStmt::Drop { expr, .. } => {
                collect_observed_locals(expr, out)
            }
            HirStmt::While {
                condition, body, ..
            } => {
                collect_observed_locals(condition, out);
                collect_observed_locals_block(body, out);
            }
            HirStmt::Loop { body, .. } => collect_observed_locals_block(body, out),
        }
    }
    if let Some(tail) = &block.tail {
        collect_observed_locals(tail, out);
    }
}
