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
}
