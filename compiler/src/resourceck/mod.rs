//! Resource checker (`rfcs/0011`): a dedicated compiler stage between
//! `typeck` and `nir::lower` that tracks each owned, affine `resource`
//! value's own ownership state through a function body -- use-after-
//! move, use-after-drop, double-drop, moving a value a pending `defer`
//! still needs, an ordinary parameter's own observation escaping its
//! call, and inconsistent state across a join or loop back-edge.
//!
//! `nir::lower` never re-derives ownership from spans or names: it is
//! only ever invoked (via `driver::check`) once this stage's own
//! diagnostics are empty, at which point it performs its own,
//! independent, deliberately simpler bookkeeping (see `nir::lower`'s
//! own `ResourceScope`) to decide where to insert `Drop`/deferred-call
//! instructions -- trusting that a program this stage accepted can
//! never make that bookkeeping ambiguous, without needing this stage to
//! export a full cross-referenced ownership map of its own.
//!
//! Known, honest scope limits for this milestone: only a *whole*
//! binding may ever be moved (moving a resource-typed value out of a
//! record/resource field, `take other.file`, is not tracked -- field
//! reads are always treated as a non-consuming observation); a
//! `mutable` resource-typed binding's own old value is not specially
//! validated for disposal when reassigned.

mod flow;
mod state;

pub use state::ResourceState;

use std::collections::{HashMap, HashSet};

use crate::diagnostics::Diagnostic;
use crate::hir::{HirModule, ItemId, LocalId};
use crate::symbol::Interner;
use crate::types::Ty;

/// Checks every function and extend-method body in `hir` for affine
/// ownership violations (`rfcs/0011`). `local_types`/`expr_types` are
/// `typeck`'s own already-computed results -- this stage never re-infers
/// a type, only reads one back, exactly like `nir::lower` already does.
pub fn check_module(
    hir: &HirModule,
    local_types: &HashMap<LocalId, Ty>,
    expr_types: &HashMap<crate::hir::ExprId, Ty>,
    interner: &Interner,
) -> Vec<Diagnostic> {
    let affine_items: HashSet<ItemId> = hir
        .records
        .iter()
        .filter(|r| r.affine)
        .map(|r| r.id)
        .collect();
    let mut take_flags: HashMap<ItemId, Vec<bool>> = HashMap::new();
    for f in &hir.functions {
        take_flags.insert(f.id, f.params.iter().map(|p| p.take).collect());
    }
    for e in &hir.extends {
        for m in &e.methods {
            take_flags.insert(m.id, m.params.iter().map(|p| p.take).collect());
        }
    }

    let mut diagnostics = Vec::new();
    for f in &hir.functions {
        let mut checker = flow::FlowChecker::new(
            local_types,
            expr_types,
            &affine_items,
            &take_flags,
            f.source,
            interner,
            &mut diagnostics,
        );
        checker.check_function(f);
    }
    for e in &hir.extends {
        for m in &e.methods {
            let mut checker = flow::FlowChecker::new(
                local_types,
                expr_types,
                &affine_items,
                &take_flags,
                m.source,
                interner,
                &mut diagnostics,
            );
            checker.check_function(m);
        }
    }
    diagnostics
}
