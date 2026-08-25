//! Resource checker (`rfcs/0011`): a dedicated compiler stage between
//! `typeck` and `nir::lower` that tracks each owned, affine `resource`
//! value's own ownership state through a function body -- use-after-
//! move, use-after-drop, double-drop, moving a value a pending `defer`
//! still needs, an ordinary parameter's own observation escaping its
//! call, inconsistent state across a join or loop back-edge, and (as
//! of Blocker 2) a compound `if`/`match`/`handle`/block origin whose
//! own underlying resource differs by branch.
//!
//! `nir::lower` never re-derives ownership from spans or names: it is
//! only ever invoked (via `driver::check`) once this stage's own
//! diagnostics are empty, at which point it performs its own,
//! independent bookkeeping (`nir::lower`'s own `FnBuilder::
//! cleanup_actions`/`moved_out`, isolated per branch through
//! `FnBuilder::move_join_stack`) to decide where to insert `Drop`/
//! deferred-call instructions -- trusting that a program this stage
//! accepted can never make that bookkeeping ambiguous, without needing
//! this stage to export a full cross-referenced ownership map of its
//! own. A resource-typed `return`/tail value that is itself a compound
//! `if`/block is the one shape `nir::lower` handles by pushing that
//! `return`'s own cleanup into each branch separately
//! (`Lowering::lower_into_return_sink`), rather than by this
//! bookkeeping alone.
//!
//! Known, honest scope limits for this milestone: only a *whole*
//! binding may ever be moved -- moving a resource-typed value out of a
//! record/resource field (`take other.file`) is rejected outright
//! (`U0009`), not silently mis-tracked as a non-consuming observation;
//! a resource-typed `match`/`handle`, or a resource-typed `if` in any
//! consuming position other than `return`/the function's own implicit
//! tail, is rejected outright too (`U0008`), since `nir::lower` has no
//! per-branch sink for those yet; a `mutable` resource-typed binding's
//! own old value is not specially validated for disposal when
//! reassigned; a `break`/`continue` loop exit does not run any
//! enclosing scope's pending cleanup (`nir::lower`'s own limitation,
//! not checked/rejected here either).

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

#[cfg(test)]
mod tests {
    use super::*;
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

    #[test]
    fn storing_a_resource_in_another_resources_field_moves_it() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Wrapper { file: File } \
             func f() { \
                 value file = File { descriptor: 3 }; \
                 value wrapped = Wrapper { file: file }; \
                 drop file; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0001"], "unexpected: {diags:?}");
    }

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
    fn a_resource_typed_match_directly_returned_is_rejected() {
        let diags = check(
            "variant Choice { A, B } \
             resource File { descriptor: i64 } \
             func choose(c: Choice, take left: File, take right: File) -> File { \
                 return match c { A => left, B => right }; \
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
    fn returning_a_resource_typed_field_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Box { file: File } \
             func steal(box: Box) -> File { return box.file; }",
        );
        assert_eq!(codes_of(&diags), vec!["U0009"], "unexpected: {diags:?}");
    }

    #[test]
    fn binding_a_resource_typed_field_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Box { file: File } \
             func steal(box: Box) { value file = box.file; drop file; }",
        );
        assert_eq!(codes_of(&diags), vec!["U0009"], "unexpected: {diags:?}");
    }

    #[test]
    fn passing_a_resource_typed_field_to_a_take_parameter_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Box { file: File } \
             func consume(take file: File) -> unit {} \
             func steal(box: Box) { consume(box.file); }",
        );
        assert_eq!(codes_of(&diags), vec!["U0009"], "unexpected: {diags:?}");
    }

    #[test]
    fn assigning_a_resource_typed_field_into_a_mutable_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Box { file: File } \
             func f() -> File { return File { descriptor: 1 } } \
             func steal(box: Box) { \
                 mutable file = f(); \
                 drop file; \
                 file = box.file; \
                 drop file; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0009"], "unexpected: {diags:?}");
    }

    #[test]
    fn storing_a_resource_typed_field_into_another_resources_field_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Box { file: File } \
             resource Wrapper { file: File } \
             func steal(box: Box) -> Wrapper { return Wrapper { file: box.file }; }",
        );
        assert_eq!(codes_of(&diags), vec!["U0009"], "unexpected: {diags:?}");
    }

    #[test]
    fn scheduling_a_resource_typed_field_through_defer_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Box { file: File } \
             func consume(take file: File) -> unit {} \
             func steal(box: Box) { defer consume(box.file); }",
        );
        assert_eq!(codes_of(&diags), vec!["U0009"], "unexpected: {diags:?}");
    }

    #[test]
    fn observing_a_primitive_field_through_a_resource_field_remains_valid() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Box { file: File } \
             func peek(box: Box) -> i64 { return box.file.descriptor; }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn passing_a_resource_typed_field_to_an_ordinary_parameter_remains_valid() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Box { file: File } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func peek(box: Box) -> i64 { return inspect(box.file); }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
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
}
