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
//! compound `if`/`match`/`handle`/block is handled by pushing that
//! `return`'s own cleanup into each branch/arm separately
//! (`Lowering::lower_into_return_sink`), each branch/arm's own leaf
//! looked up by its own `ExprId` in `cleanup_edges`.
//!
//! Known, honest scope limits for this milestone: only a *whole*
//! binding may ever be moved -- moving a resource-typed value out of a
//! field is not a concern this stage tracks at all, since `typeck`'s
//! own `RESOURCE_FIELD_IN_ORDINARY_AGGREGATE` (T0064) already rejects a
//! resource-typed field in any aggregate -- record, variant, or another
//! resource -- at that aggregate's own declaration; a resource-typed
//! `if`/`match`/`handle` in any consuming position other than
//! `return`/the function's own implicit tail is rejected outright
//! (`U0008`), since `nir::lower` has no per-branch/per-arm sink for
//! those yet.

mod flow;
mod plan;
mod state;

pub use plan::{
    CheckedDeferPlan, CheckedObservation, CleanupAction, ConsumeInfo, ObservationExit,
    ResourceCheckResult,
};
pub use state::{PlaceStatus, ResourceState};

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::hir::{ExprId, HirModule, ItemId, LocalId, TypeParamId};
use crate::symbol::Interner;
use crate::types::Ty;

/// `typeck`'s own transitive-affinity metadata (`rfcs/0012`), bundled
/// into one reference so [`check_module`]/`flow::FlowChecker::new`
/// don't each need four more separate parameters for it. Every field
/// mirrors the identically-named [`crate::typeck::TypeckResult`] field
/// it is built from directly -- see each one's own doc comment there.
pub struct AffineContext<'a> {
    pub aggregate_field_types: &'a HashMap<ItemId, Vec<Ty>>,
    pub declared_resources: &'a HashSet<ItemId>,
    pub item_type_params: &'a HashMap<ItemId, Vec<TypeParamId>>,
    pub field_projections: &'a HashMap<ExprId, (ItemId, usize)>,
}

/// `true` iff `item` (a record, resource, or variant) is transitively
/// affine (`rfcs/0012`): a declared `resource` itself, or reachably
/// containing one -- the same query `typeck::Checker::is_affine` already
/// computes at declaration time, recomputed here directly from
/// [`AffineContext`]'s own exported structural data rather than
/// threading `typeck`'s own boolean answer through as a third
/// representation of the same fact. Memoized, and guarded against a
/// genuinely cyclic declaration (already independently rejected as an
/// infinite-size layout by `typeck::cycles`) the same way: a cycle
/// back-edge contributes `false` to *that one* occurrence's own
/// disjunction without ever being cached as the type's own final answer.
fn is_affine_item(
    item: ItemId,
    affine: &AffineContext<'_>,
    visiting: &mut HashSet<ItemId>,
    memo: &mut HashMap<ItemId, bool>,
) -> bool {
    if let Some(&cached) = memo.get(&item) {
        return cached;
    }
    if affine.declared_resources.contains(&item) {
        memo.insert(item, true);
        return true;
    }
    if !visiting.insert(item) {
        return false;
    }
    let result = affine
        .aggregate_field_types
        .get(&item)
        .into_iter()
        .flatten()
        .any(|ty| is_affine_ty(ty, affine, visiting, memo));
    visiting.remove(&item);
    memo.insert(item, result);
    result
}

fn is_affine_ty(
    ty: &Ty,
    affine: &AffineContext<'_>,
    visiting: &mut HashSet<ItemId>,
    memo: &mut HashMap<ItemId, bool>,
) -> bool {
    match ty {
        Ty::Named(item, _) => is_affine_item(*item, affine, visiting, memo),
        Ty::Applied(item, args) => {
            if affine.declared_resources.contains(item) {
                return true;
            }
            if !visiting.insert(*item) {
                return false;
            }
            // Missing or arity-disagreeing generic metadata is never an
            // *empty* substitution (`rfcs/0008`): an unsubstituted
            // `Ty::Param` answers `false` below, which would let a
            // genuinely affine instantiation be treated as an ordinary,
            // freely-copyable value with no ownership to track at all.
            // Fail closed -- answer *affine*, so every ownership
            // obligation is still demanded -- exactly as
            // `flow::FlowChecker::is_affine` and `nir::lower`'s own copy
            // of this query do.
            let type_params = affine.item_type_params.get(item);
            let Some(type_params) = type_params.filter(|p| p.len() == args.len()) else {
                visiting.remove(item);
                return true;
            };
            let subst: HashMap<TypeParamId, Ty> = type_params
                .iter()
                .copied()
                .zip(args.iter().cloned())
                .collect();
            let result = affine
                .aggregate_field_types
                .get(item)
                .into_iter()
                .flatten()
                .any(|fty| {
                    is_affine_ty(
                        &crate::types::substitute(fty, &subst),
                        affine,
                        visiting,
                        memo,
                    )
                });
            visiting.remove(item);
            result
        }
        _ => false,
    }
}

/// The full transitive-affinity set (`rfcs/0012`) over every record and
/// variant [`AffineContext::aggregate_field_types`] knows about --
/// mirrors `typeck::Checker`'s own identical declaration-time query
/// exactly, so `resourceck` never disagrees with `typeck` about which
/// plain (non-generic) `Ty::Named` is affine. `flow::FlowChecker::
/// is_affine`'s own fast path for `Ty::Named` trusts this set completely
/// rather than recomputing it per function.
fn compute_affine_items(affine: &AffineContext<'_>) -> HashSet<ItemId> {
    let mut memo = HashMap::new();
    affine
        .aggregate_field_types
        .keys()
        .copied()
        .filter(|&item| is_affine_item(item, affine, &mut HashSet::new(), &mut memo))
        .collect()
}

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
    affine: &AffineContext<'_>,
) -> ResourceCheckResult {
    let affine_items = compute_affine_items(affine);
    // Every declared variant's own `ItemId` (`rfcs/0012`) -- a variant's
    // own payload is never individually addressable outside a pattern
    // match (there is no `.field` syntax for it, unlike a record), so an
    // affine variant-typed place is always tracked as one opaque
    // whole-value unit rather than decomposed field-by-field the way a
    // record's own declared fields are: which case is actually live is
    // not knowable statically, so `FlowChecker::structural_drop_targets`
    // must never treat `aggregate_field_types`'s own flattened per-case
    // payload list as if it were one case's own named field vector.
    let variant_items: HashSet<ItemId> = hir.variants.iter().map(|v| v.id).collect();
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
    let mut consume_sites: BTreeMap<ExprId, ConsumeInfo> = BTreeMap::new();
    let mut defer_plans: BTreeMap<ExprId, CheckedDeferPlan> = BTreeMap::new();
    let mut observations: BTreeMap<crate::hir::ObservationId, CheckedObservation> = BTreeMap::new();
    let mut observation_exits: BTreeMap<ExprId, Vec<ObservationExit>> = BTreeMap::new();
    for f in &hir.functions {
        let mut checker = flow::FlowChecker::new(
            local_types,
            expr_types,
            &affine_items,
            &variant_items,
            &take_flags,
            affine,
            f.source,
            interner,
            &mut diagnostics,
        );
        checker.check_function(f);
        let plan = checker.into_plan();
        cleanup_edges.extend(plan.cleanup_edges);
        consume_sites.extend(plan.consume_sites);
        defer_plans.extend(plan.defer_plans);
        observations.extend(plan.observations);
        observation_exits.extend(plan.observation_exits);
    }
    for e in &hir.extends {
        for m in &e.methods {
            let mut checker = flow::FlowChecker::new(
                local_types,
                expr_types,
                &affine_items,
                &variant_items,
                &take_flags,
                affine,
                m.source,
                interner,
                &mut diagnostics,
            );
            checker.check_function(m);
            let plan = checker.into_plan();
            cleanup_edges.extend(plan.cleanup_edges);
            consume_sites.extend(plan.consume_sites);
            defer_plans.extend(plan.defer_plans);
            observations.extend(plan.observations);
            observation_exits.extend(plan.observation_exits);
        }
    }
    ResourceCheckResult {
        diagnostics,
        cleanup_edges,
        consume_sites,
        defer_plans,
        observations,
        observation_exits,
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
            &AffineContext {
                aggregate_field_types: &typeck_result.aggregate_field_types,
                declared_resources: &typeck_result.declared_resources,
                item_type_params: &typeck_result.item_type_params,
                field_projections: &typeck_result.field_projections,
            },
        )
        .diagnostics
    }

    fn codes_of(diagnostics: &[Diagnostic]) -> Vec<&str> {
        diagnostics.iter().map(|d| d.code).collect()
    }

    /// `rfcs/0013` -- lexically scoped observations, at the grain the
    /// resource checker actually decides them: which places are frozen,
    /// which are untouched, where every scope ends, and what an alias
    /// may never be used for.
    mod observations {
        use super::{check, check_result, check_result_rejecting};

        const PRELUDE: &str = "\
            resource File { descriptor: i64 }\n\
            resource Session { left: File, right: File }\n\
            record Holder { item: File, count: i64 }\n\
            variant Maybe { Some(File), None }\n\
            func inspect(file: File) -> i64 { return file.descriptor; }\n\
            func peek(session: Session) -> i64 { return inspect(session.left); }\n\
            func sink(take file: File) -> i64 { drop file; return 1; }\n\
            func swallow(take session: Session) -> i64 { drop session; return 1; }\n\
            func hold(take holder: Holder) -> i64 { drop holder; return 1; }\n";

        fn codes(text: &str) -> Vec<String> {
            check(&format!("{PRELUDE}{text}"))
                .iter()
                .map(|d| d.code.to_string())
                .collect()
        }

        fn accepted(text: &str) {
            let codes = codes(text);
            assert!(codes.is_empty(), "unexpected diagnostics: {codes:?}");
        }

        fn rejected_with(text: &str, code: &str) {
            let codes = codes(text);
            assert_eq!(codes, vec![code], "unexpected diagnostics: {codes:?}");
        }

        // -- straight line, nesting, repetition -----------------------

        #[test]
        fn a_straight_line_scope_releases_its_owner() {
            accepted(
                "func f(take file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   observe file as view { n = inspect(view); }\n\
                   return n + sink(file);\n\
                 }",
            );
        }

        #[test]
        fn nested_scopes_release_from_the_inside_out() {
            accepted(
                "func f(take file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   observe file as outer { observe outer as inner { n = inspect(inner); } }\n\
                   return n + sink(file);\n\
                 }",
            );
        }

        #[test]
        fn repeated_sequential_observations_of_one_place_are_legal() {
            accepted(
                "func f(take file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   observe file as a { n = inspect(a); }\n\
                   observe file as b { n = n + inspect(b); }\n\
                   return n + sink(file);\n\
                 }",
            );
        }

        #[test]
        fn overlapping_observations_are_all_legal_because_all_are_read_only() {
            accepted(
                "func f(take session: Session) -> i64 {\n\
                   mutable n = 0;\n\
                   observe session as whole {\n\
                     observe session.left as part { n = inspect(part) + peek(whole); }\n\
                   }\n\
                   return n + swallow(session);\n\
                 }",
            );
        }

        // -- overlap ---------------------------------------------------

        #[test]
        fn a_disjoint_sibling_field_stays_movable() {
            accepted(
                "func f(take session: Session) -> i64 {\n\
                   mutable n = 0;\n\
                   observe session.left as view {\n\
                     n = inspect(view) + sink(session.right);\n\
                   }\n\
                   drop session.left;\n\
                   return n;\n\
                 }",
            );
        }

        #[test]
        fn a_disjoint_sibling_may_itself_be_observed() {
            accepted(
                "func f(take session: Session) -> i64 {\n\
                   mutable n = 0;\n\
                   observe session.left as a {\n\
                     observe session.right as b { n = inspect(a) + inspect(b); }\n\
                   }\n\
                   return n + swallow(session);\n\
                 }",
            );
        }

        #[test]
        fn moving_the_exact_observed_place_is_rejected() {
            rejected_with(
                "func f(take session: Session) -> i64 {\n\
                   mutable n = 0;\n\
                   observe session.left as view { n = sink(session.left); }\n\
                   return n;\n\
                 }",
                "U0017",
            );
        }

        #[test]
        fn moving_an_ancestor_of_the_observed_place_is_rejected() {
            rejected_with(
                "func f(take session: Session) -> i64 {\n\
                   mutable n = 0;\n\
                   observe session.left as view { n = swallow(session); }\n\
                   return n;\n\
                 }",
                "U0017",
            );
        }

        #[test]
        fn dropping_an_ancestor_of_the_observed_place_is_rejected() {
            rejected_with(
                "func f(take session: Session) -> i64 {\n\
                   observe session.left as view { drop session; }\n\
                   return 0;\n\
                 }",
                "U0017",
            );
        }

        #[test]
        fn moving_a_descendant_of_the_observed_place_is_rejected() {
            rejected_with(
                "func f(take holder: Holder) -> i64 {\n\
                   mutable n = 0;\n\
                   observe holder as view { n = sink(holder.item); }\n\
                   return n;\n\
                 }",
                "U0017",
            );
        }

        #[test]
        fn overwriting_an_observed_place_is_rejected() {
            rejected_with(
                "func f(take session: Session, take other: File) -> i64 {\n\
                   observe session.left as view { session.left = other; }\n\
                   return 0;\n\
                 }",
                "U0017",
            );
        }

        #[test]
        fn decomposing_an_observed_variant_is_rejected() {
            rejected_with(
                "func f(take maybe: Maybe) -> i64 {\n\
                   mutable n = 0;\n\
                   observe maybe as view {\n\
                     n = match maybe { Some(file) => sink(file), None => 0 };\n\
                   }\n\
                   return n;\n\
                 }",
                "U0017",
            );
        }

        #[test]
        fn one_conflicting_operation_reports_exactly_one_diagnostic() {
            // A nested aggregate has several affine descendants; the
            // rejection must name the operation once, not once per
            // field reachable through it.
            let codes = codes(
                "func f(take session: Session) -> i64 {\n\
                   mutable n = 0;\n\
                   observe session as view { n = swallow(session); }\n\
                   return n;\n\
                 }",
            );
            assert_eq!(codes, vec!["U0017"]);
        }

        #[test]
        fn a_non_affine_field_of_an_observed_aggregate_is_still_readable() {
            accepted(
                "func f(take holder: Holder) -> i64 {\n\
                   mutable n = 0;\n\
                   observe holder as view { n = holder.count + inspect(view.item); }\n\
                   return n + hold(holder);\n\
                 }",
            );
        }

        // -- the alias -------------------------------------------------

        #[test]
        fn passing_the_alias_to_an_ordinary_parameter_is_legal() {
            accepted(
                "func f(take file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   observe file as view { n = inspect(view); }\n\
                   return n + sink(file);\n\
                 }",
            );
        }

        #[test]
        fn passing_the_alias_to_a_take_parameter_is_rejected() {
            rejected_with(
                "func f(take file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   observe file as view { n = sink(view); }\n\
                   return n;\n\
                 }",
                "U0016",
            );
        }

        #[test]
        fn dropping_the_alias_is_rejected() {
            rejected_with(
                "func f(take file: File) -> i64 {\n\
                   observe file as view { drop view; }\n\
                   return sink(file);\n\
                 }",
                "U0016",
            );
        }

        #[test]
        fn returning_the_alias_is_rejected() {
            rejected_with(
                "func f(take file: File) -> File {\n\
                   observe file as view { return view; }\n\
                 }",
                "U0016",
            );
        }

        #[test]
        fn a_field_reached_through_the_alias_is_equally_unownable() {
            rejected_with(
                "func f(take session: Session) -> i64 {\n\
                   mutable n = 0;\n\
                   observe session as view { n = sink(view.left); }\n\
                   return n;\n\
                 }",
                "U0016",
            );
        }

        #[test]
        fn storing_the_alias_into_an_aggregate_is_rejected() {
            rejected_with(
                "func f(take file: File) -> i64 {\n\
                   observe file as view {\n\
                     value boxed = Holder { item: view, count: 1 };\n\
                     drop boxed;\n\
                   }\n\
                   return sink(file);\n\
                 }",
                "U0016",
            );
        }

        #[test]
        fn a_defer_capturing_the_alias_is_rejected() {
            rejected_with(
                "func f(take file: File) -> i64 {\n\
                   observe file as view { defer inspect(view); }\n\
                   return sink(file);\n\
                 }",
                "U0016",
            );
        }

        #[test]
        fn a_defer_capturing_the_alias_through_a_field_is_rejected() {
            rejected_with(
                "func f(take session: Session) -> i64 {\n\
                   observe session as view { defer inspect(view.left); }\n\
                   return swallow(session);\n\
                 }",
                "U0016",
            );
        }

        #[test]
        fn a_defer_that_does_not_mention_the_alias_stays_legal() {
            accepted(
                "func f(take file: File, other: File) -> i64 {\n\
                   observe file as view {\n\
                     defer inspect(other);\n\
                     value n = inspect(view);\n\
                   }\n\
                   return sink(file);\n\
                 }",
            );
        }

        // -- exits ------------------------------------------------------

        #[test]
        fn a_return_inside_the_scope_ends_it_exactly_once() {
            let result = check_result(&format!(
                "{PRELUDE}func f(take file: File) -> i64 {{\n\
                   observe file as view {{ return inspect(view); }}\n\
                 }}"
            ));
            assert!(result.diagnostics.is_empty());
            assert_eq!(result.observations.len(), 1);
            let ends: usize = result.observation_exits.values().map(|v| v.len()).sum();
            assert_eq!(ends, 1, "exactly one recorded end edge for one `return`");
        }

        #[test]
        fn break_ends_only_the_observations_opened_inside_the_loop() {
            let result = check_result(&format!(
                "{PRELUDE}func f(take file: File) -> i64 {{\n\
                   mutable n = 0;\n\
                   observe file as outer {{\n\
                     loop {{\n\
                       observe outer as inner {{ n = inspect(inner); break; }}\n\
                     }}\n\
                   }}\n\
                   return n + sink(file);\n\
                 }}"
            ));
            assert!(
                result.diagnostics.is_empty(),
                "unexpected diagnostics: {:?}",
                result.diagnostics
            );
            // The `break` leaves only the inner scope: the outer one is
            // still active after the loop and must not be ended here.
            let ends: Vec<usize> = result
                .observation_exits
                .values()
                .map(|entry| entry.len())
                .collect();
            assert_eq!(ends, vec![1]);
        }

        #[test]
        fn a_continue_inside_the_scope_ends_it() {
            accepted(
                "func f(take file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   while n < 3 {\n\
                     observe file as view { n = n + inspect(view); continue; }\n\
                   }\n\
                   return n + sink(file);\n\
                 }",
            );
        }

        #[test]
        fn an_observation_in_one_branch_does_not_leak_into_its_sibling() {
            // The `then` branch opens a scope over `file`; the `else`
            // branch moves `file` away. If the observation leaked past
            // its own branch, the sibling's move would be rejected --
            // and if it leaked past the join, the drop after it would
            // be too.
            accepted(
                "func f(take file: File, flag: bool) -> i64 {\n\
                   mutable n = 0;\n\
                   if flag {\n\
                     observe file as view { n = inspect(view); }\n\
                     n = n + sink(file);\n\
                   } else {\n\
                     n = sink(file);\n\
                   }\n\
                   return n;\n\
                 }",
            );
        }

        #[test]
        fn an_observation_in_one_branch_does_not_freeze_the_join() {
            accepted(
                "func f(take file: File, flag: bool) -> i64 {\n\
                   mutable n = 0;\n\
                   if flag {\n\
                     observe file as view { n = inspect(view); }\n\
                   } else {\n\
                     n = 1;\n\
                   }\n\
                   return n + sink(file);\n\
                 }",
            );
        }

        #[test]
        fn the_owner_is_usable_again_after_the_scope_ends() {
            accepted(
                "func f(take file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   observe file as view { n = inspect(view); }\n\
                   drop file;\n\
                   return n;\n\
                 }",
            );
        }

        #[test]
        fn a_loop_carried_observation_is_opened_and_closed_each_iteration() {
            accepted(
                "func f(take file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   while n < 3 { observe file as view { n = n + inspect(view); } }\n\
                   return n + sink(file);\n\
                 }",
            );
        }

        // -- sources ----------------------------------------------------

        #[test]
        fn observing_an_already_moved_place_reports_the_move_not_the_observation() {
            let codes = codes(
                "func f(take file: File) -> i64 {\n\
                   value n = sink(file);\n\
                   observe file as view { }\n\
                   return n;\n\
                 }",
            );
            assert_eq!(codes, vec!["U0001"]);
        }

        #[test]
        fn observing_a_dropped_owner_names_the_owner() {
            let diagnostics = check(&format!(
                "{PRELUDE}func f(take file: File) -> i64 {{\n\
                   drop file;\n\
                   observe file as view {{ }}\n\
                   return 0;\n\
                 }}"
            ));
            assert_eq!(diagnostics.len(), 1, "unexpected: {diagnostics:?}");
            assert_eq!(diagnostics[0].code, "U0002");
            assert!(
                diagnostics[0].message.contains("`file`"),
                "a bare local source must be named, not called \"this field\": {}",
                diagnostics[0].message
            );
        }

        #[test]
        fn returning_the_owner_while_observed_is_rejected() {
            rejected_with(
                "func f(take file: File) -> File {\n\
                   observe file as view {\n\
                     value n = inspect(view);\n\
                     return file;\n\
                   }\n\
                 }",
                "U0017",
            );
        }

        #[test]
        fn raising_the_owner_while_observed_is_rejected() {
            rejected_with(
                "variant Wrap { W(File) }\n\
                 func f(take file: File) -> i64 raises Wrap {\n\
                   observe file as view { raise Wrap.W(file); }\n\
                 }",
                "U0017",
            );
        }

        #[test]
        fn observing_a_partially_moved_aggregate_as_a_whole_is_rejected() {
            let codes = codes(
                "func f(take session: Session) -> i64 {\n\
                   value n = sink(session.left);\n\
                   observe session as view { }\n\
                   drop session;\n\
                   return n;\n\
                 }",
            );
            assert_eq!(codes, vec!["U0014"]);
        }

        #[test]
        fn observing_an_ordinary_parameters_own_observation_is_legal() {
            accepted(
                "func f(file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   observe file as view { n = inspect(view); }\n\
                   return n;\n\
                 }",
            );
        }

        #[test]
        fn an_observation_of_an_observation_still_cannot_be_owned() {
            rejected_with(
                "func f(file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   observe file as view { n = sink(view); }\n\
                   return n;\n\
                 }",
                "U0016",
            );
        }

        #[test]
        fn one_diverging_arm_does_not_leave_a_scope_open_for_the_other() {
            accepted(
                "func f(take file: File, flag: bool) -> i64 {\n\
                   mutable n = 0;\n\
                   if flag {\n\
                     observe file as view { return inspect(view); }\n\
                   } else {\n\
                     observe file as view { n = inspect(view); }\n\
                   }\n\
                   return n + sink(file);\n\
                 }",
            );
        }

        #[test]
        fn every_arm_diverging_through_its_own_scope_is_accepted() {
            accepted(
                "func f(take file: File, flag: bool) -> i64 {\n\
                   if flag {\n\
                     observe file as view { return inspect(view); }\n\
                   } else {\n\
                     observe file as view { return inspect(view) + 1; }\n\
                   }\n\
                 }",
            );
        }

        #[test]
        fn a_handle_success_arm_may_open_and_close_its_own_scope() {
            accepted(
                "variant Failed { Bad }\n\
                 func fallible() -> i64 raises Failed { return 1; }\n\
                 func f(take file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   n = handle fallible() {\n\
                     success v => { observe file as view { n = inspect(view); } n + v },\n\
                     failure _ => { observe file as view { n = inspect(view); } n },\n\
                   };\n\
                   return n + sink(file);\n\
                 }",
            );
        }

        #[test]
        fn a_generic_aggregates_affine_field_is_observable() {
            accepted(
                "record Cell[T] { slot: T }\n\
                 func f(take boxed: Cell[File]) -> i64 {\n\
                   mutable n = 0;\n\
                   observe boxed.slot as view { n = inspect(view); }\n\
                   drop boxed;\n\
                   return n;\n\
                 }",
            );
        }

        #[test]
        fn moving_a_generic_aggregates_observed_field_is_rejected() {
            rejected_with(
                "record Cell[T] { slot: T }\n\
                 func f(take boxed: Cell[File]) -> i64 {\n\
                   mutable n = 0;\n\
                   observe boxed.slot as view { n = sink(boxed.slot); }\n\
                   return n;\n\
                 }",
                "U0017",
            );
        }

        #[test]
        fn an_alias_escaping_through_a_variant_payload_is_rejected() {
            rejected_with(
                "func f(take file: File) -> i64 {\n\
                   observe file as view {\n\
                     value held = Maybe.Some(view);\n\
                     drop held;\n\
                   }\n\
                   return sink(file);\n\
                 }",
                "U0016",
            );
        }

        #[test]
        fn an_alias_escaping_through_a_compound_expression_is_rejected() {
            // A `return` whose operand is a compound `if` is the one
            // shape lowering *can* push a sink into per branch, so the
            // alias really is reached here as a transfer rather than
            // being stopped earlier by the unsupported-compound-origin
            // rule -- which is exactly what makes this a test of the
            // escape check rather than of that one.
            // One diagnostic per branch leaf, because each really is
            // its own distinct use of the alias -- not a cascade from
            // one.
            let codes = codes(
                "func f(take file: File, flag: bool) -> File {\n\
                   observe file as view {\n\
                     return if flag { view } else { view };\n\
                   }\n\
                 }",
            );
            assert_eq!(codes, vec!["U0016", "U0016"]);
        }

        #[test]
        fn a_compound_consuming_position_the_lowering_cannot_sink_is_still_rejected() {
            // The same alias in a compound origin lowering has no
            // per-branch sink for is refused by that pre-existing rule
            // (`U0008`) before the escape is even reached -- rejected
            // either way, never accepted.
            let codes = codes(
                "func f(take file: File, flag: bool) -> i64 {\n\
                   mutable n = 0;\n\
                   observe file as view {\n\
                     n = sink(if flag { view } else { view });\n\
                   }\n\
                   return n;\n\
                 }",
            );
            assert_eq!(codes, vec!["U0008"]);
        }

        #[test]
        fn a_scope_opened_inside_a_loop_is_closed_before_its_own_back_edge() {
            // If the scope survived the back edge, the second iteration
            // would find the same observation already active.
            accepted(
                "func f(take file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   while n < 3 {\n\
                     observe file as view { n = n + inspect(view); }\n\
                   }\n\
                   return n + sink(file);\n\
                 }",
            );
        }

        #[test]
        fn a_loop_nested_inside_a_scope_keeps_it_open_across_continue() {
            accepted(
                "func f(take file: File) -> i64 {\n\
                   mutable n = 0;\n\
                   observe file as view {\n\
                     while n < 2 {\n\
                       n = n + inspect(view);\n\
                       continue;\n\
                     }\n\
                   }\n\
                   return n + sink(file);\n\
                 }",
            );
        }

        #[test]
        fn a_resource_temporary_discarded_by_the_body_is_rejected_here() {
            // The body's own tail value is discarded, exactly like a
            // bare statement-expression's is -- so a freshly
            // constructed resource there is never bound, returned,
            // dropped or transferred, and nothing would ever destroy
            // it. Caught at `check`, not left for the verifier to
            // report as a leak with no source to point at.
            rejected_with(
                "func make() -> File { return File { descriptor: 1 }; }\n\
                 func f(take file: File) -> i64 {\n\
                   observe file as view { make() }\n\
                   return sink(file);\n\
                 }",
                "U0011",
            );
        }

        #[test]
        fn an_ordinary_value_tail_in_the_body_is_still_fine() {
            accepted(
                "func f(take file: File) -> i64 {\n\
                   observe file as view { inspect(view) }\n\
                   return sink(file);\n\
                 }",
            );
        }

        #[test]
        fn a_reversed_declaration_order_checks_identically() {
            // The place's identity is structural, not positional: the
            // same program with its two resource fields declared the
            // other way round must be accepted on exactly the same
            // terms.
            let forward = check(&format!(
                "{PRELUDE}func f(take session: Session) -> i64 {{\n\
                   mutable n = 0;\n\
                   observe session.right as view {{ n = inspect(view) + sink(session.left); }}\n\
                   drop session.right;\n\
                   return n;\n\
                 }}"
            ));
            assert!(forward.is_empty(), "unexpected diagnostics: {forward:?}");
        }

        #[test]
        fn a_checked_observation_records_its_exact_place_and_scope() {
            let result = check_result(&format!(
                "{PRELUDE}func f(take session: Session) -> i64 {{\n\
                   mutable n = 0;\n\
                   observe session.left as view {{ n = inspect(view); }}\n\
                   return n + swallow(session);\n\
                 }}"
            ));
            assert!(result.diagnostics.is_empty());
            assert_eq!(result.observations.len(), 1);
            let observation = result.observations.values().next().expect("one recorded");
            assert_eq!(
                observation.source.projections.len(),
                1,
                "the recorded place must be the field itself, never its root"
            );
        }

        #[test]
        fn a_rejected_observation_records_no_checked_metadata_at_all() {
            let result = check_result_rejecting(&format!(
                "{PRELUDE}func f(take session: Session) -> i64 {{\n\
                   value n = sink(session.left);\n\
                   observe session as view {{ }}\n\
                   drop session;\n\
                   return n;\n\
                 }}"
            ));
            assert!(!result.diagnostics.is_empty());
            assert!(
                result.observations.is_empty(),
                "a rejected observation must not reach lowering as if it had been accepted"
            );
        }
    }

    /// Like [`check`], but returns the whole [`ResourceCheckResult`]
    /// rather than only its diagnostics -- for tests that need to
    /// directly inspect `consume_sites`/`defer_plans` themselves,
    /// rather than only the source-level diagnostics they helped
    /// produce.
    fn check_result(text: &str) -> ResourceCheckResult {
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
        let result = check_module(
            &hir,
            &typeck_result.local_types,
            &typeck_result.expr_types,
            &interner,
            &AffineContext {
                aggregate_field_types: &typeck_result.aggregate_field_types,
                declared_resources: &typeck_result.declared_resources,
                item_type_params: &typeck_result.item_type_params,
                field_projections: &typeck_result.field_projections,
            },
        );
        assert!(
            result.diagnostics.is_empty(),
            "unexpected resource diagnostics: {:?}",
            result.diagnostics
        );
        result
    }

    /// Like [`check_result`], but for a program this stage is *expected*
    /// to reject -- so a test can assert what a rejected program leaves
    /// behind (which must be nothing a later stage could mistake for an
    /// accepted decision).
    fn check_result_rejecting(text: &str) -> ResourceCheckResult {
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
            &AffineContext {
                aggregate_field_types: &typeck_result.aggregate_field_types,
                declared_resources: &typeck_result.declared_resources,
                item_type_params: &typeck_result.item_type_params,
                field_projections: &typeck_result.field_projections,
            },
        )
    }

    #[test]
    fn a_take_argument_is_recorded_as_a_checked_transfer() {
        let result = check_result(
            "resource File { descriptor: i64 } \
             func consume(take file: File) -> unit {} \
             func f() { value file = File { descriptor: 3 }; consume(file); }",
        );
        let transfers = result
            .consume_sites
            .values()
            .filter(|c| matches!(c, ConsumeInfo::Transfer))
            .count();
        // One for `file`'s own binding initializer, one for the `consume`
        // call argument -- both genuinely checked transfers.
        assert_eq!(
            transfers, 2,
            "unexpected consume_sites: {:?}",
            result.consume_sites
        );
        assert!(
            result
                .consume_sites
                .values()
                .all(|c| matches!(c, ConsumeInfo::Transfer)),
            "unexpected consume_sites: {:?}",
            result.consume_sites
        );
    }

    #[test]
    fn an_ordinary_argument_is_recorded_as_a_checked_observation() {
        let result = check_result(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> unit {} \
             func f() { value file = File { descriptor: 3 }; inspect(file); drop file; }",
        );
        // `file`'s own binding initializer is a checked transfer; the
        // `inspect` call argument -- an ordinary, non-`take` parameter
        // -- is a checked observation, not a transfer.
        let observes = result
            .consume_sites
            .values()
            .filter(|c| matches!(c, ConsumeInfo::Observe))
            .count();
        assert_eq!(
            observes, 1,
            "unexpected consume_sites: {:?}",
            result.consume_sites
        );
    }

    #[test]
    fn a_consuming_defer_argument_is_recorded_in_its_own_checked_plan() {
        let result = check_result(
            "resource File { descriptor: i64 } \
             func close(take file: File) -> unit {} \
             func f() { value file = File { descriptor: 3 }; defer close(file); }",
        );
        assert_eq!(
            result.defer_plans.len(),
            1,
            "unexpected defer_plans: {:?}",
            result.defer_plans
        );
        let plan = result.defer_plans.values().next().unwrap();
        assert_eq!(plan.arg_modes, vec![ConsumeInfo::Transfer]);
    }

    #[test]
    fn an_observing_defer_argument_is_recorded_in_its_own_checked_plan() {
        let result = check_result(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> unit {} \
             func f() { value file = File { descriptor: 3 }; defer inspect(file); }",
        );
        assert_eq!(
            result.defer_plans.len(),
            1,
            "unexpected defer_plans: {:?}",
            result.defer_plans
        );
        let plan = result.defer_plans.values().next().unwrap();
        assert_eq!(plan.arg_modes, vec![ConsumeInfo::Observe]);
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
    fn a_non_affine_match_returned_alongside_an_unrelated_resource_has_no_diagnostics() {
        // The `match` itself produces `i64`, not a resource -- `kind`
        // still propagates `Return` through it (for whatever it might
        // contain), but that must never be mistaken for `file` itself
        // being the thing under compound return-sink treatment: each
        // bare arm's own leaf here is not a resource-return-sink leaf
        // at all, so it must not claim `file`'s own whole-function
        // cleanup for itself, wrongly excluding it from the arm-local
        // entry `nir::lower`'s own ordinary (non-sink) merge path still
        // depends on.
        let diags = check(
            "variant Choice { A, B } \
             resource File { descriptor: i64 } \
             func f(c: Choice, take file: File) -> i64 { \
                 return match c { A => 1, B => 2 }; \
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
    fn a_resource_typed_handle_directly_returned_has_no_diagnostics() {
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
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_resource_typed_handle_bound_to_a_value_is_still_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             variant OpenError { Invalid } \
             func open() -> File raises OpenError { return File { descriptor: 1 } } \
             func choose(take fallback: File) -> File { \
                 value picked = handle open() { \
                     success file => file, \
                     failure OpenError.Invalid => fallback, \
                 }; \
                 return picked; \
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
    fn a_fresh_temporary_on_one_arm_of_an_if_passed_to_an_ordinary_parameter_is_rejected() {
        // `cond`-false leaks nothing (`existing` is an already-owned
        // binding, merely observed), but `cond`-true constructs a
        // genuinely fresh resource with no owner at all -- caught by
        // recursing into the `if`'s own reachable leaves, not just at
        // `inspect`'s own call-argument position directly.
        let diags = check(
            "resource File { descriptor: i64 } \
             func make_file(n: i64) -> File { return File { descriptor: n } } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f(cond: bool) -> i64 { \
                 value existing = File { descriptor: 1 }; \
                 value result = inspect(if cond { make_file(9) } else { existing }); \
                 drop existing; \
                 return result; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0011"], "unexpected: {diags:?}");
    }

    #[test]
    fn a_fresh_temporary_in_one_match_arm_passed_to_an_ordinary_parameter_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             variant Choice { A, B } \
             func make_file(n: i64) -> File { return File { descriptor: n } } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f(c: Choice) -> i64 { \
                 value existing = File { descriptor: 1 }; \
                 value result = inspect(match c { A => make_file(9), B => existing }); \
                 drop existing; \
                 return result; \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0011"], "unexpected: {diags:?}");
    }

    #[test]
    fn every_arm_re_observing_an_already_owned_local_through_an_if_remains_valid() {
        // Neither branch constructs anything fresh -- both merely
        // re-observe already-owned bindings -- so this is exactly the
        // still-valid shape `RESOURCE_TEMPORARY_LEAK`'s own doc comment
        // describes, not a leak.
        let diags = check(
            "resource File { descriptor: i64 } \
             func inspect(file: File) -> i64 { return file.descriptor } \
             func f(cond: bool) -> i64 { \
                 value a = File { descriptor: 1 }; \
                 value b = File { descriptor: 2 }; \
                 value result = inspect(if cond { a } else { b }); \
                 drop a; \
                 drop b; \
                 return result; \
             }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
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

    // -- compound arguments carry the places they forward --------------
    //
    // An `if`/`match`/block argument produces one of its branches'
    // values, so the places it may name are the union of theirs.
    // Answering "no place" for it -- which is what a bare
    // `resolve_place` does -- reads as "aliases nothing", and that let
    // the same resource reach an observing and a `take` parameter with
    // nothing noticing.

    const COMPOUND_PRELUDE: &str = "resource File { descriptor: i64 } \
         resource Session { input: File, output: File } \
         variant Choice { Left(i64), Right(i64) } \
         func mixed(file: File, take owner: File) -> i64 { \
             drop owner; \
             return file.descriptor; \
         } \
         func mixed_rev(take owner: File, file: File) -> i64 { \
             value d = file.descriptor; \
             drop owner; \
             return d; \
         } \
         func obs2(a: File, b: File) -> i64 { return a.descriptor + b.descriptor } ";

    fn check_compound(body: &str) -> Vec<crate::diagnostics::Diagnostic> {
        check(&format!("{COMPOUND_PRELUDE}{body}"))
    }

    #[test]
    fn an_if_argument_forwarding_a_taken_resource_is_rejected() {
        let diags = check_compound(
            "func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 42 }; \
                 return mixed(if cond { file } else { file }, file); \
             }",
        );
        assert!(
            codes_of(&diags).contains(&"U0015"),
            "an `if` forwards its branches' places: {diags:?}"
        );
    }

    /// The same call with the parameters swapped. Both spellings must
    /// name the same fault rather than one tripping a move rule.
    #[test]
    fn an_if_argument_is_rejected_in_either_parameter_order() {
        let diags = check_compound(
            "func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 42 }; \
                 return mixed_rev(file, if cond { file } else { file }); \
             }",
        );
        assert!(
            codes_of(&diags).contains(&"U0015"),
            "argument order must not decide the answer: {diags:?}"
        );
    }

    #[test]
    fn a_match_argument_forwarding_a_taken_resource_is_rejected() {
        let diags = check_compound(
            "func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 42 }; \
                 value c = if cond { Choice.Left(1) } else { Choice.Right(2) }; \
                 return mixed(match c { Left(n) => { file } Right(n) => { file } }, file); \
             }",
        );
        assert!(
            codes_of(&diags).contains(&"U0015"),
            "every arm's value is a place this argument may name: {diags:?}"
        );
    }

    #[test]
    fn a_block_argument_forwarding_a_taken_resource_is_rejected() {
        let diags = check_compound(
            "func f() -> i64 { \
                 value file = File { descriptor: 42 }; \
                 return mixed({ file }, file); \
             }",
        );
        assert!(
            codes_of(&diags).contains(&"U0015"),
            "a block's value is its tail's value: {diags:?}"
        );
    }

    /// Only *one* branch overlaps. The union is what catches it -- an
    /// analysis that took a single representative branch would accept
    /// this half the time depending which it picked.
    #[test]
    fn an_if_argument_overlapping_on_only_one_branch_is_rejected() {
        let diags = check_compound(
            "func f(cond: bool) -> i64 { \
                 mutable s = Session { \
                     input: File { descriptor: 1 }, \
                     output: File { descriptor: 2 }, \
                 }; \
                 return mixed(if cond { s.input } else { s.output }, s.input); \
             }",
        );
        assert!(
            codes_of(&diags).contains(&"U0015"),
            "one overlapping branch is enough: {diags:?}"
        );
    }

    #[test]
    fn an_if_argument_naming_a_disjoint_sibling_is_accepted() {
        let diags = check_compound(
            "func f(cond: bool) -> i64 { \
                 mutable s = Session { \
                     input: File { descriptor: 1 }, \
                     output: File { descriptor: 2 }, \
                 }; \
                 value n = mixed(if cond { s.output } else { s.output }, s.input); \
                 value rest = s.output; \
                 drop rest; \
                 return n; \
             }",
        );
        assert!(
            !codes_of(&diags).contains(&"U0015"),
            "disjoint sibling fields never alias: {diags:?}"
        );
    }

    #[test]
    fn two_compound_observations_of_one_resource_are_accepted() {
        let diags = check_compound(
            "func f(cond: bool) -> i64 { \
                 value file = File { descriptor: 1 }; \
                 value n = obs2(if cond { file } else { file }, file); \
                 drop file; \
                 return n; \
             }",
        );
        assert!(
            !codes_of(&diags).contains(&"U0015"),
            "neither observation can end the resource: {diags:?}"
        );
    }

    #[test]
    fn a_compound_argument_naming_a_distinct_resource_is_accepted() {
        let diags = check_compound(
            "func f(cond: bool) -> i64 { \
                 value kept = File { descriptor: 1 }; \
                 value given = File { descriptor: 2 }; \
                 value n = mixed(if cond { kept } else { kept }, given); \
                 drop kept; \
                 return n; \
             }",
        );
        assert!(
            !codes_of(&diags).contains(&"U0015"),
            "distinct resources never alias: {diags:?}"
        );
    }
    // -- one resource may not be observed and taken by one call --------
    //
    // The `take` parameter owns what it was given for the whole call
    // and may destroy it at any point in the body, while the observing
    // parameter stays readable for exactly as long. Nothing orders
    // those, and no signature the caller can see says which the callee
    // does -- so the pairing is refused at the call, not reasoned about
    // per body.

    #[test]
    fn observing_and_taking_one_resource_in_one_call_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(file: File, take owner: File) -> i64 { \
                 drop owner; \
                 return file.descriptor; \
             } \
             func f() -> i64 { \
                 value file = File { descriptor: 42 }; \
                 return consume(file, file); \
             }",
        );
        assert_eq!(codes_of(&diags), vec!["U0015"], "unexpected: {diags:?}");
    }

    /// The same call with the parameters swapped. This order used to
    /// trip `U0001` on the later read purely because the transfer
    /// happened to come first; the fault is the pairing, so both orders
    /// must name the same one.
    #[test]
    fn taking_and_observing_one_resource_in_one_call_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func consume(take owner: File, file: File) -> i64 { \
                 value d = file.descriptor; \
                 drop owner; \
                 return d; \
             } \
             func f() -> i64 { \
                 value file = File { descriptor: 42 }; \
                 return consume(file, file); \
             }",
        );
        assert!(
            codes_of(&diags).contains(&"U0015"),
            "both argument orders must report the alias: {diags:?}"
        );
    }

    #[test]
    fn observing_a_parent_while_taking_its_field_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Session { input: File, output: File } \
             func mixed(observed: Session, take owner: File) -> i64 { \
                 drop owner; \
                 return observed.output.descriptor; \
             } \
             func f() -> i64 { \
                 mutable s = Session { \
                     input: File { descriptor: 1 }, \
                     output: File { descriptor: 2 }, \
                 }; \
                 return mixed(s, s.input); \
             }",
        );
        assert!(
            codes_of(&diags).contains(&"U0015"),
            "taking a field of an observed parent is the same alias: {diags:?}"
        );
    }

    #[test]
    fn taking_a_parent_while_observing_its_field_is_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Session { input: File, output: File } \
             func mixed(observed: File, take owner: Session) -> i64 { \
                 value d = observed.descriptor; \
                 drop owner; \
                 return d; \
             } \
             func f() -> i64 { \
                 mutable s = Session { \
                     input: File { descriptor: 1 }, \
                     output: File { descriptor: 2 }, \
                 }; \
                 return mixed(s.input, s); \
             }",
        );
        assert!(
            codes_of(&diags).contains(&"U0015"),
            "containment in the other direction is the same alias: {diags:?}"
        );
    }

    #[test]
    fn observing_one_resource_twice_in_one_call_is_accepted() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func both(a: File, b: File) -> i64 { return a.descriptor + b.descriptor } \
             func f() -> i64 { \
                 value file = File { descriptor: 1 }; \
                 value n = both(file, file); \
                 drop file; \
                 return n; \
             }",
        );
        assert!(
            diags.is_empty(),
            "neither observation can end the resource: {diags:?}"
        );
    }

    #[test]
    fn observing_one_resource_while_taking_a_different_one_is_accepted() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func mixed(a: File, take b: File) -> i64 { \
                 value d = a.descriptor; \
                 drop b; \
                 return d; \
             } \
             func f() -> i64 { \
                 value kept = File { descriptor: 1 }; \
                 value given = File { descriptor: 2 }; \
                 value n = mixed(kept, given); \
                 drop kept; \
                 return n; \
             }",
        );
        assert!(
            diags.is_empty(),
            "distinct resources never alias: {diags:?}"
        );
    }

    #[test]
    fn observing_one_sibling_field_while_taking_another_is_accepted() {
        let diags = check(
            "resource File { descriptor: i64 } \
             resource Session { input: File, output: File } \
             func mixed(a: File, take b: File) -> i64 { \
                 value d = a.descriptor; \
                 drop b; \
                 return d; \
             } \
             func f() -> i64 { \
                 mutable s = Session { \
                     input: File { descriptor: 1 }, \
                     output: File { descriptor: 2 }, \
                 }; \
                 value n = mixed(s.output, s.input); \
                 value rest = s.output; \
                 drop rest; \
                 return n; \
             }",
        );
        assert!(
            !codes_of(&diags).contains(&"U0015"),
            "disjoint sibling fields are not an alias: {diags:?}"
        );
    }

    /// Two `take` arguments reaching one identity were already rejected
    /// by the move rules; adding the observe/take check must not have
    /// replaced that answer with its own.
    #[test]
    fn taking_one_resource_twice_in_one_call_is_still_rejected() {
        let diags = check(
            "resource File { descriptor: i64 } \
             func both(take a: File, take b: File) -> unit { drop a; drop b; } \
             func f() { \
                 value file = File { descriptor: 1 }; \
                 both(file, file); \
             }",
        );
        assert!(
            !diags.is_empty(),
            "one identity may not be transferred twice: {diags:?}"
        );
        assert!(
            !codes_of(&diags).contains(&"U0015"),
            "two transfers are not an observe/take alias: {diags:?}"
        );
    }
}

/// Missing-metadata fail-closed behavior (`rfcs/0008`, `rfcs/0012`):
/// this stage's own affinity query must never answer "not affine" just
/// because a generic declaration's own type-parameter list is absent or
/// disagrees with the arguments a use supplies. Answering `false` there
/// would let a genuinely affine instantiation be treated as an
/// ordinary, freely-copyable value with no ownership tracked at all --
/// the one direction that leaks rather than over-demands.
#[cfg(test)]
mod missing_metadata {
    use super::*;

    const BOXY: ItemId = ItemId(70);
    const FILE: ItemId = ItemId(71);

    /// The four owned tables an [`AffineContext`] borrows, kept alive
    /// by the caller for exactly as long as the borrow it hands out.
    struct Tables {
        fields: HashMap<ItemId, Vec<Ty>>,
        resources: HashSet<ItemId>,
        params: HashMap<ItemId, Vec<TypeParamId>>,
        projections: HashMap<ExprId, (ItemId, usize)>,
    }

    fn context(type_params: Option<Vec<TypeParamId>>) -> Tables {
        let param = TypeParamId(0);
        let name = crate::symbol::Symbol(0);
        let mut fields = HashMap::new();
        fields.insert(BOXY, vec![Ty::Param(param, name)]);
        fields.insert(FILE, vec![Ty::I64]);
        let mut resources = HashSet::new();
        resources.insert(FILE);
        let mut params = HashMap::new();
        if let Some(declared) = type_params {
            params.insert(BOXY, declared);
        }
        params.insert(FILE, Vec::new());
        Tables {
            fields,
            resources,
            params,
            projections: HashMap::new(),
        }
    }

    fn affine_with(type_params: Option<Vec<TypeParamId>>, args: Vec<Ty>) -> bool {
        let tables = context(type_params);
        let affine = AffineContext {
            aggregate_field_types: &tables.fields,
            declared_resources: &tables.resources,
            item_type_params: &tables.params,
            field_projections: &tables.projections,
        };
        is_affine_ty(
            &Ty::Applied(BOXY, args),
            &affine,
            &mut HashSet::new(),
            &mut HashMap::new(),
        )
    }

    #[test]
    fn a_well_formed_generic_instantiation_answers_from_its_substituted_field() {
        let file = Ty::Named(FILE, crate::symbol::Symbol(0));
        assert!(
            affine_with(Some(vec![TypeParamId(0)]), vec![file]),
            "`Box[File]` must be affine"
        );
        assert!(
            !affine_with(Some(vec![TypeParamId(0)]), vec![Ty::I64]),
            "`Box[i64]` must not be affine"
        );
    }

    #[test]
    fn a_missing_type_parameter_list_fails_closed_to_affine() {
        assert!(
            affine_with(None, vec![Ty::I64]),
            "missing generic metadata must never be answered as an empty substitution"
        );
    }

    #[test]
    fn an_arity_disagreement_fails_closed_to_affine() {
        assert!(
            affine_with(Some(vec![TypeParamId(0)]), vec![Ty::I64, Ty::I64]),
            "an arity disagreement must never be answered as a partial substitution"
        );
    }
}
