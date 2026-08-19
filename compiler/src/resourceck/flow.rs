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
}

pub use codes::*;

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
        self.check_block(&f.body);
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

    fn check_block(&mut self, block: &HirBlock) {
        for stmt in &block.statements {
            self.check_stmt(stmt);
        }
        if let Some(tail) = &block.tail {
            self.check_expr(tail);
        }
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
        self.check_expr(&b.value);
        self.check_consume(&b.value);
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
            // owned binding here to transition; still walked generically
            // for whatever nested reads it does contain.
            self.check_expr(expr);
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
    /// current entry state; if the state it produces at the body's own
    /// end disagrees with entry for any resource local declared outside
    /// the loop, a second iteration could not safely reuse that local,
    /// so this is reported once, at the loop, rather than silently
    /// picking either state. A resource local the loop body itself
    /// *declares* is scoped to one iteration and never compared this
    /// way (comparing against entry, where it never existed, would be
    /// meaningless) -- excluded by only comparing keys already present
    /// on entry.
    fn check_loop_body(&mut self, body: &HirBlock) {
        let entry = self.states.clone();
        self.check_block(body);
        for (local, entry_state) in &entry {
            let exit_state = self.states.get(local).copied().unwrap_or(*entry_state);
            if exit_state != *entry_state
                && *entry_state != ResourceState::Error
                && exit_state != ResourceState::Error
            {
                self.diagnose(
                    LOOP_CARRIED_INVALIDATION,
                    body.span,
                    "a resource's own state at the end of this loop body disagrees with its \
                     state on entry; a later iteration could not safely reuse it"
                        .to_string(),
                    "loop-carried resource invalidation",
                );
                self.states.insert(*local, ResourceState::Error);
            }
        }
    }

    // -- Expressions -----------------------------------------------------

    fn check_expr(&mut self, expr: &HirExpr) {
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
            HirExpr::Local {
                local, name, span, ..
            } => self.check_read(*local, *name, *span),
            HirExpr::Unary { operand, .. } => self.check_expr(operand),
            HirExpr::Binary { left, right, .. } => {
                self.check_expr(left);
                self.check_expr(right);
            }
            HirExpr::Assign { target, value, .. } => {
                self.check_expr(value);
                self.check_consume(value);
                if let HirExpr::Local { local, .. } = target.as_ref()
                    && self.is_resource_local(*local)
                {
                    self.states.insert(*local, ResourceState::Available);
                } else {
                    self.check_expr(target);
                }
            }
            HirExpr::Call { callee, args, .. } => {
                self.check_expr(callee);
                let take_flags = self.take_flags_for_callee(callee);
                for (index, arg) in args.iter().enumerate() {
                    self.check_expr(arg);
                    let takes = take_flags
                        .and_then(|flags| flags.get(index))
                        .copied()
                        .unwrap_or(false);
                    if takes {
                        self.check_consume(arg);
                    }
                }
            }
            HirExpr::Field { base, .. } => self.check_expr(base),
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
                self.check_if(*id, then_branch, else_branch.as_ref());
            }
            HirExpr::Match {
                scrutinee,
                arms,
                id,
                ..
            } => {
                self.check_expr(scrutinee);
                self.check_match_arms(*id, arms);
            }
            HirExpr::Block(block) => self.check_block(block),
            HirExpr::Return { value, .. } | HirExpr::Break { value, .. } => {
                if let Some(value) = value {
                    self.check_expr(value);
                    self.check_consume(value);
                }
            }
            HirExpr::RecordLiteral { fields, .. } => {
                for field in fields {
                    self.check_expr(&field.value);
                    self.check_consume(&field.value);
                }
            }
            HirExpr::Raise { operand, .. } => {
                self.check_expr(operand);
                self.check_consume(operand);
            }
            HirExpr::Handle {
                operand, arms, id, ..
            } => {
                self.check_expr(operand);
                self.check_handle_arms(*id, arms);
            }
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

    /// Transitions `expr`'s own source binding to `Moved`, if `expr` is
    /// a bare local reference naming one -- the only shape an existing
    /// owned binding can be consumed *from*. Any other expression shape
    /// (a fresh call/construction result, a literal, a field read) has
    /// no existing owned binding to transition at all: it simply
    /// produces a new value for whatever consumed it to own from here
    /// on. Moving a resource-typed value *out of* a field
    /// (`take other.file`) is not supported this milestone -- only a
    /// whole binding may ever be moved.
    fn check_consume(&mut self, expr: &HirExpr) {
        let HirExpr::Local {
            local, name, span, ..
        } = expr
        else {
            return;
        };
        if self.observing.contains(local) {
            self.diagnose(
                OBSERVATION_ESCAPES,
                *span,
                format!(
                    "`{}` is an ordinary parameter's own call-scoped observation and cannot be moved, returned, or stored",
                    self.local_name(*local, *name)
                ),
                "observation escapes its call",
            );
            return;
        }
        let Some(state) = self.states.get(local).copied() else {
            return;
        };
        match state {
            ResourceState::Available => {
                self.states.insert(*local, ResourceState::Moved);
            }
            ResourceState::Error => {}
            ResourceState::Moved => {
                self.diagnose(
                    USE_AFTER_MOVE,
                    *span,
                    format!(
                        "`{}` was already moved and cannot be moved again",
                        self.local_name(*local, *name)
                    ),
                    "use after move",
                );
                self.states.insert(*local, ResourceState::Error);
            }
            ResourceState::Dropped => {
                self.diagnose(
                    USE_AFTER_DROP,
                    *span,
                    format!(
                        "`{}` was already dropped and cannot be moved",
                        self.local_name(*local, *name)
                    ),
                    "use after drop",
                );
                self.states.insert(*local, ResourceState::Error);
            }
            ResourceState::DropScheduled => {
                self.diagnose(
                    MOVE_AFTER_DEFER_CAPTURED,
                    *span,
                    format!(
                        "`{}` is still needed by a pending `defer` and cannot be moved away",
                        self.local_name(*local, *name)
                    ),
                    "moved before its defer ran",
                );
                self.states.insert(*local, ResourceState::Error);
            }
        }
    }

    // -- Joins -----------------------------------------------------------

    fn check_if(
        &mut self,
        if_id: crate::hir::ExprId,
        then_branch: &HirBlock,
        else_branch: Option<&HirElse>,
    ) {
        let entry = self.states.clone();
        self.check_block(then_branch);
        let then_diverges = self.diverges(then_branch.id);
        let then_exit = std::mem::replace(&mut self.states, entry.clone());

        let (else_exit, else_diverges) = match else_branch {
            Some(HirElse::Block(block)) => {
                self.check_block(block);
                let diverges = self.diverges(block.id);
                (std::mem::replace(&mut self.states, entry.clone()), diverges)
            }
            Some(HirElse::If(inner)) => {
                self.check_expr(inner);
                let diverges = self.diverges(inner.id());
                (self.states.clone(), diverges)
            }
            None => (entry.clone(), false),
        };

        self.states = join_branch_states(
            &entry,
            &[(then_exit, then_diverges), (else_exit, else_diverges)],
        );
        if self.states.values().any(|s| *s == ResourceState::Error)
            && entry.values().all(|s| *s != ResourceState::Error)
        {
            self.diagnose_inconsistent_join(if_id);
        }
    }

    fn check_match_arms(&mut self, match_id: crate::hir::ExprId, arms: &[HirMatchArm]) {
        let entry = self.states.clone();
        let mut branches = Vec::with_capacity(arms.len());
        for arm in arms {
            self.states = entry.clone();
            self.check_pattern(&arm.pattern);
            let diverges = match &arm.body {
                HirMatchArmBody::Expr(e) => {
                    self.check_expr(e);
                    self.diverges(e.id())
                }
                HirMatchArmBody::Block(block) => {
                    self.check_block(block);
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

    fn check_handle_arms(&mut self, handle_id: crate::hir::ExprId, arms: &[HirHandleArm]) {
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
                    self.check_expr(e);
                    self.diverges(e.id())
                }
                HirMatchArmBody::Block(block) => {
                    self.check_block(block);
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
