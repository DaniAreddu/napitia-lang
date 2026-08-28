//! Resource checker (`rfcs/0011`): a dedicated compiler stage between
//! `typeck` and `nir::lower` that tracks each owned, affine `resource`
//! value's own ownership state through a function body -- use-after-
//! move, use-after-drop, double-drop, moving a value a pending `defer`
//! still needs, an ordinary parameter's own observation escaping its
//! call, inconsistent state across a join, a compound `if`/`match`/
//! `handle`/block origin whose own underlying resource differs by
//! branch, a resource-typed value bound by a `handle` `success`
//! pattern, and a resource-typed temporary reaching a position nothing
//! would ever destroy it from.
//!
//! Loop ownership (`while`/`loop`) is edge-sensitive, not a single
//! "body's own textual end" check: `break` and `continue` are tracked
//! separately (`FlowChecker::loop_stack`) since only `continue` and the
//! body's own reachable fallthrough feed the loop's own backedge (which
//! must agree with entry, or a second iteration could not safely reuse
//! it); `break`'s own live state instead joins directly into the state
//! after the loop, alongside a `while`'s own condition-false exit.
//!
//! `nir::lower` never re-derives ownership from spans or names, and
//! never re-infers *whether* a resource is still live at a given exit:
//! it is only ever invoked (via `driver::check`/`project::
//! compile_project`) once this stage's own diagnostics are empty, and
//! it consumes this stage's own [`ResourceCheckResult::cleanup_edges`]
//! directly as the authoritative plan for every `Drop`/deferred-call
//! instruction it places -- a checked, per-exit, already-ordered
//! cleanup list keyed by the stable [`crate::hir::ExprId`] of whatever
//! HIR node *is* that exit, rather than lowering independently
//! re-walking branches/loop back-edges to guess the same answer a
//! second time. A resource-typed `return`/tail value that is itself a
//! compound `if`/block is the one shape `nir::lower` handles by pushing
//! that `return`'s own cleanup into each branch separately
//! (`Lowering::lower_into_return_sink`), each branch's own leaf looked
//! up by its own `ExprId` in `cleanup_edges`.
//!
//! Known, honest scope limits for this milestone: only a *whole*
//! binding may ever be moved -- moving a resource-typed value out of a
//! field is not a concern this stage tracks at all, since `typeck`'s
//! own `RESOURCE_FIELD_IN_ORDINARY_AGGREGATE` (T0064) already rejects a
//! resource-typed field in any aggregate -- record, variant, or another
//! resource -- at that aggregate's own declaration; a resource-typed
//! `handle`, or a resource-typed `if`/`match` in any consuming position
//! other than `return`/the function's own implicit tail, is rejected
//! outright (`U0008`), since `nir::lower` has no per-branch/per-arm
//! sink for those yet; a resource-typed temporary reaching a compound
//! `if`/`match`/`handle` that itself constructs a genuinely fresh
//! resource on some branch is not caught by the temporary check
//! (`U0011`), only a direct call or literal construction is.

mod flow;
mod plan;
mod state;

pub use plan::{CleanupAction, ResourceCheckResult};
pub use state::ResourceState;

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::hir::{ExprId, HirModule, ItemId, LocalId};
use crate::symbol::Interner;
use crate::types::Ty;

/// Checks every function and extend-method body in `hir` for affine
/// ownership violations (`rfcs/0011`), returning the authoritative,
/// structured [`ResourceCheckResult`] -- not merely a `Vec<Diagnostic>`
/// -- so `nir::lower` can consume its own checked `cleanup_edges` as the
/// single source of truth for resource cleanup, rather than
/// independently re-inferring which locals are still live at a given
/// exit by re-walking the HIR a second time. `local_types`/`expr_types`
/// are `typeck`'s own already-computed results -- this stage never
/// re-infers a type, only reads one back, exactly like `nir::lower`
/// already does.
pub fn check_module(
    hir: &HirModule,
    local_types: &HashMap<LocalId, Ty>,
    expr_types: &HashMap<ExprId, Ty>,
    interner: &Interner,
) -> ResourceCheckResult {
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
    let mut cleanup_edges: BTreeMap<ExprId, Vec<CleanupAction>> = BTreeMap::new();
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
        cleanup_edges.extend(checker.into_cleanup_edges());
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
            cleanup_edges.extend(checker.into_cleanup_edges());
        }
    }
    ResourceCheckResult {
        diagnostics,
        cleanup_edges,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostics::Diagnostic;
    use crate::hir::lower_module;
    use crate::lexer::tokenize;
    use crate::parser::Parser;
    use crate::source::SourceMap;
    use crate::typeck;

    fn check(text: &str) -> Vec<Diagnostic> {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, lex_diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(
            lex_diags.is_empty(),
            "unexpected lexer diagnostics: {lex_diags:?}"
        );
        let (module, parse_diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(
            parse_diags.is_empty(),
            "unexpected parser diagnostics: {parse_diags:?}"
        );
        let (hir, resolve_diags) = lower_module(&module, id, &interner);
        assert!(
            resolve_diags.is_empty(),
            "unexpected resolve diagnostics: {resolve_diags:?}"
        );
        let typeck_result = typeck::check_module(&hir, id, &interner, typeck::EntryMain::ByName);
        assert!(
            typeck_result.diagnostics.is_empty(),
            "unexpected typeck diagnostics: {:?}",
            typeck_result.diagnostics
        );
        check_module(
            &hir,
            &typeck_result.local_types,
            &typeck_result.expr_types,
            &interner,
        )
        .diagnostics
    }

    fn codes_of(diagnostics: &[Diagnostic]) -> Vec<&str> {
        diagnostics.iter().map(|d| d.code).collect()
    }

    #[test]
    fn a_freshly_constructed_resource_is_available() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func f() { value file = File { descriptor: 3 }; drop file; }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn using_a_resource_after_it_was_moved_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f() { \
                 value file = File { descriptor: 3 }; \
                 value moved = file; \
                 consume(moved); \
                 drop file; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0001"], "unexpected: {diags:?}");
    }

    #[test]
    fn double_drop_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func f() { value file = File { descriptor: 3 }; drop file; drop file; }",
        );
        assert_eq!(codes_of(&diags), vec!["U0003"], "unexpected: {diags:?}");
    }

    #[test]
    fn using_a_resource_after_it_was_dropped_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f() -> i64 { \
                 value file = File { descriptor: 3 }; \
                 drop file; \
                 return inspect(file); \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0002"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_take_parameter_moves_the_argument() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f() { \
                 value file = File { descriptor: 3 }; \
                 consume(file); \
                 consume(file); \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0001"], "unexpected: {diags:?}");
    }

    #[test]
    fn an_ordinary_parameter_observes_without_consuming() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f() -> i64 { \
                 value file = File { descriptor: 3 }; \
                 value first = inspect(file); \
                 value second = inspect(file); \
                 drop file; \
                 return first + second; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn an_ordinary_parameters_own_observation_cannot_escape_by_return() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func identity(file: File) -> File { return file }",
        );
        assert_eq!(codes_of(&diags), vec!["U0005"], "unexpected: {diags:?}");
    }

    #[test]
    fn moving_a_value_a_pending_defer_still_needs_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func consume(take file: File) -> unit {} \
             func f() { \
                 value file = File { descriptor: 3 }; \
                 defer inspect(file); \
                 consume(file); \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0004"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_value_observed_only_inside_a_nested_if_within_a_defer_call_is_still_protected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f(cond: bool) { \
                 value file = File { descriptor: 3 }; \
                 defer inspect(if cond { file } else { file }); \
                 drop file; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0004"], "unexpected: {diags:?}");
    }

    #[test]
    fn inconsistent_branch_state_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f(cond: bool) { \
                 value file = File { descriptor: 3 }; \
                 if cond { \
                     consume(file); \
                 } else { \
                 } \
                 drop file; \
             }",
        );
        // The join itself reports U0006; the subsequent `drop file`
        // fires nothing further -- once a binding is checker-internal
        // `Error`, later checks against it are suppressed, matching this
        // stage's own "one diagnostic per root violation" discipline.
        assert_eq!(codes_of(&diags), vec!["U0006"], "unexpected: {diags:?}");
    }

    #[test]
    fn inconsistent_branch_state_points_at_the_if_not_a_dummy_span() {
        let text = "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f(cond: bool) { \
                 value file = File { descriptor: 3 }; \
                 if cond { \
                     consume(file); \
                 } else { \
                 } \
                 drop file; \
             }";
        let diags = check(text);
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        let span = diags[0].primary_span;
        assert!(
            span.end > span.start,
            "expected a real, non-empty span, got {span:?}"
        );
        assert_eq!(
            &text[span.start as usize..span.end as usize],
            "if cond { consume(file); } else { }",
            "expected the diagnostic to span the `if` itself, not a dummy span"
        );
    }

    #[test]
    fn unsupported_compound_resource_origin_points_at_the_construct_not_a_dummy_span() {
        let text = "resource File { descriptor: i64 } \
             func choose(cond: bool, take left: File, take right: File) -> i64 { \
                 value picked = if cond { left } else { right }; \
                 return 1; \
             }";
        let diags = check(text);
        assert_eq!(codes_of(&diags), vec!["U0008"], "unexpected: {diags:?}");
        let span = diags[0].primary_span;
        assert!(
            span.end > span.start,
            "expected a real, non-empty span, got {span:?}"
        );
        assert_eq!(
            &text[span.start as usize..span.end as usize],
            "if cond { left } else { right }",
            "expected the diagnostic to span the `if` itself, not a dummy span"
        );
    }

    #[test]
    fn a_branch_that_diverges_never_poisons_the_join() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f(cond: bool) { \
                 value file = File { descriptor: 3 }; \
                 if cond { \
                     consume(file); \
                     return; \
                 } \
                 drop file; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_join_with_every_arm_diverging_contributes_nothing_and_leaves_no_after_state() {
        // Both arms of this `if` return, disagreeing with each other
        // about `file`'s own state (one moves it, one drops it) -- that
        // must never be reported as an inconsistent join, since a join
        // with no reachable contributing branch at all carries nothing
        // forward for anything after it to disagree about (matching
        // typeck's own `Ty::Never` handling of a fully-diverging `if`).
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 3 }; \
                 if cond { \
                     consume(file); \
                     return 1; \
                 } else { \
                     drop file; \
                     return 2; \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn loop_carried_resource_invalidation_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f(cond: bool) { \
                 value file = File { descriptor: 3 }; \
                 while cond { \
                     consume(file); \
                 } \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0007"], "unexpected: {diags:?}");
    }

    #[test]
    fn returning_an_owned_resource_moves_it_out_without_a_double_drop() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func make() -> File { return File { descriptor: 3 } } \
             func f() -> File { value file = make(); return file; }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    // Resource-typed field extraction (formerly U0009) is no longer
    // reachable here at all (Blocker 8): `typeck`'s own
    // RESOURCE_FIELD_IN_ORDINARY_AGGREGATE (T0064) now rejects a
    // resource-typed field in any aggregate -- record, variant, or
    // another resource -- at that aggregate's own declaration, so no
    // well-typed HIR naming `box.file` where `file` is resource-typed
    // can ever reach this stage. That coverage (a plain record, and a
    // resource, each with a resource-typed field, each rejected at
    // typeck) now lives in `typeck::tests` instead, next to
    // `RESOURCE_FIELD_IN_ORDINARY_AGGREGATE`'s own implementation.

    #[test]
    fn a_compound_return_choosing_between_two_taken_resources_has_no_diagnostics() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func choose(cond: bool, take left: File, take right: File) -> File { \
                 return if cond { left } else { right }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn an_implicit_compound_tail_return_choosing_between_two_taken_resources_has_no_diagnostics() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func choose(cond: bool, take left: File, take right: File) -> File { \
                 if cond { left } else { right } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_nested_if_inside_a_compound_return_has_no_diagnostics() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func choose(a: bool, b: bool, take x: File, take y: File, take z: File) -> File { \
                 return if a { x } else if b { y } else { z }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_compound_return_with_one_diverging_arm_has_no_diagnostics() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func fail() -> i64 { return 0 } \
             func choose(cond: bool, take left: File) -> File { \
                 return if cond { left } else { return left; }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_resource_typed_match_directly_returned_has_no_diagnostics() {
        let diags = check(
            "variant Choice { A, B } \
             resource File { descriptor: i64 } \
             func choose(c: Choice, take left: File, take right: File) -> File { \
                 return match c { A => left, B => right }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_resource_typed_match_bound_to_a_value_is_still_rejected() {
        let diags = check(
            "variant Choice { A, B } \
             resource File { descriptor: i64 } \
             func choose(c: Choice, take left: File, take right: File) -> File { \
                 value picked = match c { A => left, B => right }; \
                 return picked; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0008"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_resource_typed_handle_directly_returned_is_still_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func open() -> File raises OpenError { return File { descriptor: 1 } } \
             func choose(take fallback: File) -> File { \
                 return handle open() { \
                     success file => file, \
                     failure OpenError.Invalid => fallback, \
                 }; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0008"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_resource_typed_if_bound_to_a_value_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func choose(cond: bool, take left: File, take right: File) -> File { \
                 value picked = if cond { left } else { right }; \
                 return picked; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0008"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_resource_typed_if_passed_to_a_take_parameter_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> i64 { return 1 } \
             func choose(cond: bool, take left: File, take right: File) -> i64 { \
                 return sink(if cond { left } else { right }); \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0008"], "unexpected: {diags:?}");
    }

    #[test]
    fn reassigning_a_mutable_resource_that_still_owns_a_value_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func open_first() -> File { return File { descriptor: 1 } } \
             func open_second() -> File { return File { descriptor: 2 } } \
             func f() { \
                 mutable file = open_first(); \
                 file = open_second(); \
                 drop file; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0010"], "unexpected: {diags:?}");
    }

    #[test]
    fn reassigning_a_mutable_resource_after_an_explicit_drop_is_accepted() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func open_first() -> File { return File { descriptor: 1 } } \
             func open_second() -> File { return File { descriptor: 2 } } \
             func f() { \
                 mutable file = open_first(); \
                 drop file; \
                 file = open_second(); \
                 drop file; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn reassigning_a_mutable_resource_after_it_was_moved_is_accepted() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func open_first() -> File { return File { descriptor: 1 } } \
             func open_second() -> File { return File { descriptor: 2 } } \
             func f() { \
                 mutable file = open_first(); \
                 consume(file); \
                 file = open_second(); \
                 drop file; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn reassigning_a_mutable_resource_consumed_on_only_one_branch_is_rejected() {
        // The old value is consumed on only one branch, so the two
        // branches disagree about the slot's own state; reassignment
        // must not be accepted regardless of which branch actually ran.
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func open_second() -> File { return File { descriptor: 2 } } \
             func f(cond: bool) { \
                 mutable file = open_second(); \
                 if cond { \
                     consume(file); \
                 } \
                 file = open_second(); \
                 drop file; \
             }",
        );
        assert!(!diags.is_empty(), "expected a diagnostic: {diags:?}");
    }

    #[test]
    fn reassigning_a_mutable_resource_consumed_on_every_branch_is_accepted() {
        // Both branches agree the slot is empty on entry to the
        // reassignment, even though it was consumed through two
        // different call sites -- this is not the same local moved
        // twice, so no disagreement.
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func open_second() -> File { return File { descriptor: 2 } } \
             func f(cond: bool) { \
                 mutable file = open_second(); \
                 if cond { \
                     consume(file); \
                 } else { \
                     consume(file); \
                 } \
                 file = open_second(); \
                 drop file; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    // -- Loop ownership edges (Blocker 2) -------------------------------

    #[test]
    fn a_direct_break_after_a_move_has_no_diagnostics() {
        // The only reachable after-loop state has `file` moved: an
        // unconditional `break` never re-enters the loop, so there is
        // no second iteration to disagree with entry.
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f() -> i64 { \
                 value file = File { descriptor: 3 }; \
                 loop { \
                     consume(file); \
                     break; \
                 } \
                 return 0; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_conditional_break_after_a_move_has_no_diagnostics() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 3 }; \
                 loop { \
                     if cond { \
                         consume(file); \
                         break; \
                     } \
                 } \
                 return 0; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_direct_continue_carrying_a_moved_resource_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f(cond: bool) { \
                 value file = File { descriptor: 3 }; \
                 while cond { \
                     consume(file); \
                     continue; \
                 } \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0007"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_conditional_continue_carrying_a_moved_resource_is_rejected() {
        // The `other` branch moves `file` and jumps straight back to the
        // top of the loop through `continue`, skipping `inspect` on that
        // path; the fallthrough path instead reaches `inspect` with
        // `file` still available. Both paths feed the same backedge, so
        // they must agree -- they don't, and a second iteration taking
        // the `continue` path again would use-after-move.
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f(cond: bool, other: bool) { \
                 value file = File { descriptor: 3 }; \
                 while cond { \
                     if other { \
                         consume(file); \
                         continue; \
                     } \
                     inspect(file); \
                 } \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0007"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_while_conditions_own_false_edge_leaves_the_resource_available_after_the_loop() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f(cond: bool) { \
                 value file = File { descriptor: 3 }; \
                 while cond { \
                     inspect(file); \
                 } \
                 drop file; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn nested_loops_keep_independent_break_and_continue_targets() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f(outer: bool, inner: bool) -> i64 { \
                 value file = File { descriptor: 3 }; \
                 while outer { \
                     while inner { \
                         if inner { \
                             break; \
                         } \
                     } \
                 } \
                 drop file; \
                 return 0; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn an_inner_loops_break_does_not_move_an_outer_loops_own_resource() {
        // The inner `break` only ever exits the inner loop; it must
        // never be mistaken for exiting the outer one, which still
        // legitimately owns `file` after the inner loop finishes.
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f(outer: bool, inner: bool) { \
                 value file = File { descriptor: 3 }; \
                 while outer { \
                     while inner { \
                         break; \
                     } \
                     consume(file); \
                 } \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0007"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_resource_declared_inside_a_nested_loop_body_is_not_compared_to_loop_entry() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func f(outer: bool, inner: bool) { \
                 while outer { \
                     while inner { \
                         value file = File { descriptor: 3 }; \
                         drop file; \
                     } \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_defer_registered_before_a_conditional_break_still_protects_its_resource() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f(cond: bool) { \
                 value file = File { descriptor: 3 }; \
                 defer inspect(file); \
                 loop { \
                     if cond { \
                         break; \
                     } \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn code_after_an_unconditional_break_in_the_same_block_is_not_checked() {
        // `consume(file)` after the unconditional `break` never runs;
        // walking it anyway would wrongly report a use-after-move for
        // the still-available `file` reaching that dead statement, since
        // nothing before it in this same iteration ever moved it.
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f() -> i64 { \
                 value file = File { descriptor: 3 }; \
                 loop { \
                     break; \
                     consume(file); \
                     consume(file); \
                 } \
                 drop file; \
                 return 0; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn reversed_branch_order_in_a_conditional_continue_produces_the_identical_diagnostic() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f(cond: bool, other: bool) { \
                 value file = File { descriptor: 3 }; \
                 while cond { \
                     if other { \
                         inspect(file); \
                     } else { \
                         consume(file); \
                         continue; \
                     } \
                 } \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0007"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_while_condition_that_consumes_a_resource_is_rejected() {
        // The condition runs again on every iteration; a take-consuming
        // condition call would use-after-move the second time it runs.
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume_as_bool(take file: File) -> bool { \
                 drop file; \
                 return true; \
             } \
             func f() { \
                 value file = File { descriptor: 1 }; \
                 while consume_as_bool(file) { \
                 } \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0007"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_conditional_break_after_a_move_followed_by_a_later_use_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> unit { drop file; } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 loop { \
                     if cond { \
                         sink(file); \
                         break; \
                     } \
                 } \
                 return inspect(file); \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0001"], "unexpected: {diags:?}");
    }

    #[test]
    fn two_break_states_disagreeing_about_a_resource_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> unit { drop file; } \
             func f(a: bool, b: bool) { \
                 value file = File { descriptor: 1 }; \
                 loop { \
                     if a { \
                         sink(file); \
                         break; \
                     } \
                     if b { \
                         break; \
                     } \
                 } \
                 drop file; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0006"], "unexpected: {diags:?}");
    }

    #[test]
    fn two_break_states_agreeing_about_a_resource_has_no_diagnostics() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> unit { drop file; } \
             func f(a: bool, b: bool) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 loop { \
                     if a { \
                         sink(file); \
                         break; \
                     } \
                     if b { \
                         sink(file); \
                         break; \
                     } \
                 } \
                 return 0; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_while_condition_false_edge_disagreeing_with_a_break_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> unit { drop file; } \
             func f(cond: bool, inner: bool) { \
                 value file = File { descriptor: 1 }; \
                 while cond { \
                     if inner { \
                         sink(file); \
                         break; \
                     } \
                 } \
                 drop file; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0006"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_loop_with_no_reachable_break_produces_an_unreachable_after_state() {
        // `loop {}` with no break never falls through -- `finish_loop`
        // must fall back to its own harmless "unreachable" placeholder
        // (returning `entry` unchanged) rather than panicking or
        // fabricating a state, even though nothing can actually observe
        // it here.
        let diags = check(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> unit { drop file; } \
             func f() { \
                 value file = File { descriptor: 1 }; \
                 sink(file); \
                 loop { \
                 } \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn code_after_a_loop_with_no_reachable_break_is_not_checked() {
        // A bare `loop` with no reachable `break` anywhere inside it
        // genuinely never falls through, exactly like `return`/`raise` --
        // `sink(file)` below is unreachable dead code, and must not be
        // checked as if it were live: it would otherwise wrongly report a
        // use-after-move for a resource this same statement already moved
        // before the loop.
        let diags = check(
            "resource File { descriptor: i64 } \
             func sink(take file: File) -> unit { drop file; } \
             func f() { \
                 value file = File { descriptor: 1 }; \
                 sink(file); \
                 loop { \
                 } \
                 sink(file); \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    // -- Reachability and lexical state (Blocker 11) --------------------

    #[test]
    fn code_after_return_in_the_same_block_is_not_checked() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f() { \
                 value file = File { descriptor: 3 }; \
                 consume(file); \
                 return; \
                 inspect(file); \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn code_after_a_diverging_bindings_initializer_is_not_checked() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f() -> i64 { \
                 value file = File { descriptor: 3 }; \
                 consume(file); \
                 value unreachable = return 0; \
                 consume(file); \
                 return 1; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    // -- Defer scope and capture semantics (Blocker 9) ------------------

    #[test]
    fn an_observing_defer_stops_protecting_its_resource_once_its_own_scope_exits() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func consume(take file: File) -> unit {} \
             func f() { \
                 value file = File { descriptor: 3 }; \
                 { \
                     defer inspect(file); \
                 } \
                 consume(file); \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn breaking_out_of_a_loop_releases_that_iterations_own_observing_defer() {
        // The break exits the loop body's own scope, where `defer
        // inspect(file)` was registered -- its own observing
        // protection must release right there, exactly like reaching
        // the end of that same scope normally would, so `consume(file)`
        // after the loop is accepted.
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func consume(take file: File) -> i64 { drop file; return 1 } \
             func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 loop { \
                     defer inspect(file); \
                     if cond { \
                         break; \
                     } \
                 } \
                 return consume(file); \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn continuing_a_loop_releases_that_iterations_own_observing_defer() {
        // `continue` exits the current iteration's own scope back to
        // the loop's own backedge -- the next iteration's fresh `defer`
        // must find the resource `Available` again, not still
        // protected by the iteration that just ended.
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func consume(take file: File) -> i64 { drop file; return 1 } \
             func f(start: i64) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 mutable n = start; \
                 loop { \
                     defer inspect(file); \
                     n = n - 1; \
                     if n > 0 { \
                         continue; \
                     } \
                     break; \
                 } \
                 return consume(file); \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn an_observing_defer_still_protects_its_resource_before_its_own_scope_exits() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func consume(take file: File) -> unit {} \
             func f() { \
                 value file = File { descriptor: 3 }; \
                 { \
                     defer inspect(file); \
                     consume(file); \
                 } \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0004"], "unexpected: {diags:?}");
    }

    #[test]
    fn an_outer_defers_protection_outlives_a_nested_scope_it_did_not_register_in() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func consume(take file: File) -> unit {} \
             func f() { \
                 value file = File { descriptor: 3 }; \
                 defer inspect(file); \
                 { \
                     inspect(file); \
                 } \
                 consume(file); \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0004"], "unexpected: {diags:?}");
    }

    #[test]
    fn using_a_resource_after_registering_a_consuming_defer_is_use_after_move() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func consume(take file: File) -> unit {} \
             func f() -> i64 { \
                 value file = File { descriptor: 3 }; \
                 defer consume(file); \
                 return inspect(file); \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0001"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_consuming_defer_never_used_again_has_no_diagnostics() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f() { \
                 value file = File { descriptor: 3 }; \
                 defer consume(file); \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    // -- Resource ownership from patterns (Blocker 4) --------------------

    #[test]
    fn a_handle_success_bindings_resource_is_observed_without_consuming_it() {
        let diags = check(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func open() -> File raises OpenError { return File { descriptor: 1 } } \
             func f() -> i64 { \
                 return handle open() { \
                     success file => file.descriptor, \
                     failure OpenError.Invalid => 0, \
                 }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_handle_success_bindings_resource_can_be_passed_to_a_take_parameter() {
        let diags = check(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func open() -> File raises OpenError { return File { descriptor: 1 } } \
             func consume(take file: File) -> i64 { return 1 } \
             func f() -> i64 { \
                 return handle open() { \
                     success file => consume(file), \
                     failure OpenError.Invalid => 0, \
                 }; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn using_a_handle_success_bindings_resource_after_a_take_call_is_use_after_move() {
        let diags = check(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func open() -> File raises OpenError { return File { descriptor: 1 } } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func consume(take file: File) -> i64 { return 1 } \
             func f() -> i64 { \
                 return handle open() { \
                     success file => { \
                         consume(file); \
                         return inspect(file); \
                     }, \
                     failure OpenError.Invalid => 0, \
                 }; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0001"], "unexpected: {diags:?}");
    }

    #[test]
    fn dropping_a_handle_success_bindings_resource_twice_is_a_double_drop() {
        let diags = check(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func open() -> File raises OpenError { return File { descriptor: 1 } } \
             func f() -> i64 { \
                 return handle open() { \
                     success file => { \
                         drop file; \
                         drop file; \
                         return 0; \
                     }, \
                     failure OpenError.Invalid => 0, \
                 }; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0003"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_handle_success_bindings_local_id_does_not_leak_past_the_handle() {
        // A resource local elsewhere in the function, unrelated to the
        // handle's own success pattern, must be checked exactly as if
        // the handle weren't there at all -- the pattern-scoped local's
        // own final state must never contaminate the join.
        let diags = check(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func open() -> File raises OpenError { return File { descriptor: 1 } } \
             func f() -> i64 { \
                 value outer = File { descriptor: 9 }; \
                 value r = handle open() { \
                     success file => { drop file; 1 }, \
                     failure OpenError.Invalid => 0, \
                 }; \
                 drop outer; \
                 return r; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    // -- Resource-valued temporaries (Blocker 3) -------------------------

    #[test]
    fn a_discarded_call_returning_a_resource_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func make_file() -> File { return File { descriptor: 1 } } \
             func f() { make_file(); }",
        );
        assert_eq!(codes_of(&diags), vec!["U0011"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_discarded_resource_literal_is_rejected() {
        let diags = check("resource File { descriptor: i64 } func f() { File { descriptor: 1 }; }");
        assert_eq!(codes_of(&diags), vec!["U0011"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_resource_temporary_passed_to_an_ordinary_parameter_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func make_file() -> File { return File { descriptor: 1 } } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f() -> i64 { return inspect(make_file()); }",
        );
        assert_eq!(codes_of(&diags), vec!["U0011"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_resource_temporary_observed_by_a_defer_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func make_file() -> File { return File { descriptor: 1 } } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f() { defer inspect(make_file()); }",
        );
        assert_eq!(codes_of(&diags), vec!["U0011"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_resource_temporarys_field_read_and_discarded_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func make_file() -> File { return File { descriptor: 1 } } \
             func f() -> i64 { return make_file().descriptor; }",
        );
        assert_eq!(codes_of(&diags), vec!["U0011"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_resource_temporary_bound_to_a_value_remains_valid() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func make_file() -> File { return File { descriptor: 1 } } \
             func f() { value file = make_file(); drop file; }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_resource_temporary_explicitly_dropped_remains_valid() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func make_file() -> File { return File { descriptor: 1 } } \
             func f() { drop make_file(); }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_resource_temporary_returned_remains_valid() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func make_file() -> File { return File { descriptor: 1 } } \
             func f() -> File { return make_file(); }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_resource_temporary_passed_to_a_take_parameter_remains_valid() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func make_file() -> File { return File { descriptor: 1 } } \
             func consume(take file: File) -> i64 { return 1 } \
             func f() -> i64 { return consume(make_file()); }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_resource_temporary_captured_by_a_consuming_defer_remains_valid() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func make_file() -> File { return File { descriptor: 1 } } \
             func consume(take file: File) -> i64 { return 1 } \
             func f() { defer consume(make_file()); }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_compound_if_wrapping_only_already_owned_locals_remains_valid() {
        // Not itself a fresh temporary on either branch -- both arms
        // just re-observe an already-owned local, exactly as valid here
        // as passing that same local directly would be.
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 value r = inspect(if cond { file } else { file }); \
                 drop file; \
                 return r; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }
}
