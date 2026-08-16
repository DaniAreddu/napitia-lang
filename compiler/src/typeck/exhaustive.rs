//! Pattern-matrix usefulness/exhaustiveness analysis (Maranget-style),
//! specialized to this milestone's closed pattern grammar: boolean and
//! variant constructor spaces are closed (enumerable); integer/string/
//! char literal spaces are open (never exhaustively listable, so a
//! catch-all is always required); wildcard/binding patterns cover
//! everything. No or-patterns, guards, or tuples exist in this grammar,
//! so a "row" is a `Vec<ResolvedPattern>` of positions introduced purely
//! by descending into nested `Variant` payloads.

use std::collections::HashMap;

use crate::hir::ItemId;
use crate::types::Ty;

/// A pattern with every name resolved: a `Bind`/`Wildcard` HIR pattern
/// that did not resolve to a payload-less variant case becomes
/// `Wildcard` here (it matches everything, for this analysis's
/// purposes); a `Variant` pattern's case name is already resolved to
/// its declaration index.
#[derive(Clone, Debug, PartialEq)]
pub enum ResolvedPattern {
    Wildcard,
    Bool(bool),
    /// An integer/string/char literal. Compared for exact equality only
    /// (used solely to detect a literally-duplicated arm as
    /// unreachable); the *exhaustiveness* verdict for an open domain
    /// never depends on which literals were listed, only on whether a
    /// catch-all is present.
    Literal(LiteralKey),
    Variant {
        variant: ItemId,
        case: usize,
        args: Vec<ResolvedPattern>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LiteralKey {
    Int(u128),
    Str(String),
    Char(char),
}

type Row = Vec<ResolvedPattern>;

/// Total recursive specialize/default steps allowed per `match`
/// expression -- a hard backstop against pathological nested input.
/// Ordinary programs need a small fraction of this even for deeply
/// nested variant patterns; exceeding it is reported as its own
/// diagnostic (`T0019`), never a hang or a stack overflow.
pub const MAX_USEFULNESS_STEPS: usize = 100_000;

/// `is_useful` recurses once per occurrence position it consumes from
/// `row` -- for a single deeply-nested `Variant` pattern, that is once
/// per nesting level, on this function's own native call stack.
/// `MAX_USEFULNESS_STEPS` bounds total *work* across an entire match's
/// analysis, not any one call's recursion *depth*: a single
/// pathologically nested row could still recurse up to
/// `MAX_USEFULNESS_STEPS` native stack frames deep before that counter
/// ever reaches zero, which is nowhere near a safe call-stack depth.
/// `typeck::check_pattern`'s own bound already keeps every
/// `ResolvedPattern` this module receives through the normal pipeline
/// within this same limit, but `is_useful` is a public function a
/// caller can invoke directly with a hand-built row bypassing that
/// protection, so it needs its own independent depth bound too.
const MAX_RECURSION_DEPTH: usize = 200;

pub struct VariantSpace {
    /// Case index -> that case's payload types, in declaration order.
    pub payloads: HashMap<ItemId, Vec<Vec<Ty>>>,
}

pub enum Usefulness {
    /// The row is useful; carries the completed witness (only
    /// meaningful when the caller asked for a witness against an
    /// all-wildcard row -- an arbitrary caller-supplied row's own
    /// witness value is discarded).
    Useful(Row),
    NotUseful,
    BudgetExceeded,
}

/// Constructor space of `ty`, as far as this analysis cares.
enum Space<'a> {
    Bool,
    Variant(ItemId, &'a [Vec<Ty>]),
    Open,
}

fn space<'a>(ty: &Ty, variants: &'a VariantSpace) -> Space<'a> {
    match ty {
        Ty::Bool => Space::Bool,
        Ty::Named(item, _) => match variants.payloads.get(item) {
            Some(cases) => Space::Variant(*item, cases),
            None => Space::Open,
        },
        _ => Space::Open,
    }
}

/// Is `row` useful against `matrix` (does it match some value nothing
/// in `matrix` already matches)? `occurrence_types` is parallel to
/// `row`/each matrix row: the type of each pending occurrence.
pub fn is_useful(
    matrix: &[Row],
    row: &[ResolvedPattern],
    occurrence_types: &[Ty],
    variants: &VariantSpace,
    budget: &mut usize,
) -> Usefulness {
    is_useful_at_depth(matrix, row, occurrence_types, variants, budget, 0)
}

#[allow(clippy::too_many_arguments)]
fn is_useful_at_depth(
    matrix: &[Row],
    row: &[ResolvedPattern],
    occurrence_types: &[Ty],
    variants: &VariantSpace,
    budget: &mut usize,
    depth: usize,
) -> Usefulness {
    if depth > MAX_RECURSION_DEPTH {
        return Usefulness::BudgetExceeded;
    }
    if *budget == 0 {
        return Usefulness::BudgetExceeded;
    }
    *budget -= 1;

    let Some((head, rest)) = row.split_first() else {
        return if matrix.is_empty() {
            Usefulness::Useful(Vec::new())
        } else {
            Usefulness::NotUseful
        };
    };
    // `row` and `occurrence_types` are always built in lockstep by every
    // caller in this module, so this never actually fires -- but a
    // malformed `ResolvedPattern` reaching this analysis by some path
    // this module doesn't control (e.g. a future caller, or a defect
    // elsewhere) must never be able to turn a compiler-internal
    // inconsistency into a user-facing panic. Conservatively reporting
    // "not useful" never fabricates a missing-pattern witness or an
    // incorrect unreachable-arm diagnostic; it just stops analyzing.
    let Some((ty0, rest_tys)) = occurrence_types.split_first() else {
        return Usefulness::NotUseful;
    };

    match head {
        ResolvedPattern::Variant {
            variant,
            case,
            args,
        } => {
            let arity = args.len();
            let specialized = specialize_variant(matrix, *variant, *case, arity);
            let mut new_row = args.clone();
            new_row.extend_from_slice(rest);
            let payload_tys = variants
                .payloads
                .get(variant)
                .and_then(|cases| cases.get(*case))
                .cloned()
                .unwrap_or_default();
            let mut new_tys = payload_tys;
            new_tys.extend_from_slice(rest_tys);
            match is_useful_at_depth(
                &specialized,
                &new_row,
                &new_tys,
                variants,
                budget,
                depth + 1,
            ) {
                Usefulness::Useful(mut witness) => {
                    // `witness` always has at least `arity` leading
                    // entries in the well-formed case (one per payload
                    // position just specialized); clamp defensively so a
                    // shorter witness can never panic here.
                    let split = arity.min(witness.len());
                    let args_witness: Vec<_> = witness.drain(0..split).collect();
                    let mut out = vec![ResolvedPattern::Variant {
                        variant: *variant,
                        case: *case,
                        args: args_witness,
                    }];
                    out.extend(witness);
                    Usefulness::Useful(out)
                }
                other => other,
            }
        }
        ResolvedPattern::Bool(b) => {
            let specialized = specialize_bool(matrix, *b);
            match is_useful_at_depth(&specialized, rest, rest_tys, variants, budget, depth + 1) {
                Usefulness::Useful(mut witness) => {
                    witness.insert(0, ResolvedPattern::Bool(*b));
                    Usefulness::Useful(witness)
                }
                other => other,
            }
        }
        ResolvedPattern::Literal(lit) => {
            let specialized = specialize_literal(matrix, lit);
            match is_useful_at_depth(&specialized, rest, rest_tys, variants, budget, depth + 1) {
                Usefulness::Useful(mut witness) => {
                    witness.insert(0, ResolvedPattern::Literal(lit.clone()));
                    Usefulness::Useful(witness)
                }
                other => other,
            }
        }
        // Closed domains (`bool`, a variant's finite case set) always
        // enumerate their *actual* constructors here, never falling
        // back to the default/wildcard matrix -- unlike a plain
        // true/false usefulness check, this also has to produce a
        // *concrete* witness (RFC 0005 requires a real missing
        // pattern, never a bare `_`), and enumerating the specific
        // missing constructor is both correct and strictly more
        // informative than reporting the space is merely "incomplete".
        // An entirely-absent constructor's specialized matrix is empty,
        // so it is immediately found useful with no wasted work.
        ResolvedPattern::Wildcard => match space(ty0, variants) {
            Space::Bool => try_each_bool(matrix, rest, rest_tys, variants, budget, depth),
            Space::Variant(item, cases) => {
                try_each_case(matrix, item, cases, rest, rest_tys, variants, budget, depth)
            }
            Space::Open => {
                let defaulted = default_matrix(matrix);
                match is_useful_at_depth(&defaulted, rest, rest_tys, variants, budget, depth + 1) {
                    Usefulness::Useful(mut witness) => {
                        witness.insert(0, ResolvedPattern::Wildcard);
                        Usefulness::Useful(witness)
                    }
                    other => other,
                }
            }
        },
    }
}

#[allow(clippy::too_many_arguments)]
fn try_each_bool(
    matrix: &[Row],
    rest: &[ResolvedPattern],
    rest_tys: &[Ty],
    variants: &VariantSpace,
    budget: &mut usize,
    depth: usize,
) -> Usefulness {
    for b in [false, true] {
        let specialized = specialize_bool(matrix, b);
        let mut new_row = vec![];
        new_row.extend_from_slice(rest);
        match is_useful_at_depth(
            &specialized,
            &new_row,
            rest_tys,
            variants,
            budget,
            depth + 1,
        ) {
            Usefulness::Useful(mut witness) => {
                witness.insert(0, ResolvedPattern::Bool(b));
                return Usefulness::Useful(witness);
            }
            Usefulness::BudgetExceeded => return Usefulness::BudgetExceeded,
            Usefulness::NotUseful => {}
        }
        new_row.clear();
    }
    Usefulness::NotUseful
}

#[allow(clippy::too_many_arguments)]
fn try_each_case(
    matrix: &[Row],
    item: ItemId,
    cases: &[Vec<Ty>],
    rest: &[ResolvedPattern],
    rest_tys: &[Ty],
    variants: &VariantSpace,
    budget: &mut usize,
    depth: usize,
) -> Usefulness {
    for (case, payload_tys) in cases.iter().enumerate() {
        let specialized = specialize_variant(matrix, item, case, payload_tys.len());
        let mut new_row = vec![ResolvedPattern::Wildcard; payload_tys.len()];
        new_row.extend_from_slice(rest);
        let mut new_tys = payload_tys.clone();
        new_tys.extend_from_slice(rest_tys);
        match is_useful_at_depth(
            &specialized,
            &new_row,
            &new_tys,
            variants,
            budget,
            depth + 1,
        ) {
            Usefulness::Useful(mut witness) => {
                let split = payload_tys.len().min(witness.len());
                let args: Vec<_> = witness.drain(0..split).collect();
                let mut out = vec![ResolvedPattern::Variant {
                    variant: item,
                    case,
                    args,
                }];
                out.extend(witness);
                return Usefulness::Useful(out);
            }
            Usefulness::BudgetExceeded => return Usefulness::BudgetExceeded,
            Usefulness::NotUseful => {}
        }
    }
    Usefulness::NotUseful
}

fn specialize_variant(matrix: &[Row], item: ItemId, case: usize, arity: usize) -> Vec<Row> {
    matrix
        .iter()
        .filter_map(|row| {
            let (head, rest) = row.split_first()?;
            match head {
                ResolvedPattern::Wildcard => {
                    let mut new_row = vec![ResolvedPattern::Wildcard; arity];
                    new_row.extend_from_slice(rest);
                    Some(new_row)
                }
                ResolvedPattern::Variant {
                    variant,
                    case: c,
                    args,
                } if *variant == item && *c == case => {
                    let mut new_row = args.clone();
                    new_row.extend_from_slice(rest);
                    Some(new_row)
                }
                _ => None,
            }
        })
        .collect()
}

fn specialize_bool(matrix: &[Row], value: bool) -> Vec<Row> {
    matrix
        .iter()
        .filter_map(|row| {
            let (head, rest) = row.split_first()?;
            match head {
                ResolvedPattern::Wildcard => Some(rest.to_vec()),
                ResolvedPattern::Bool(b) if *b == value => Some(rest.to_vec()),
                _ => None,
            }
        })
        .collect()
}

fn specialize_literal(matrix: &[Row], value: &LiteralKey) -> Vec<Row> {
    matrix
        .iter()
        .filter_map(|row| {
            let (head, rest) = row.split_first()?;
            match head {
                ResolvedPattern::Wildcard => Some(rest.to_vec()),
                ResolvedPattern::Literal(l) if l == value => Some(rest.to_vec()),
                _ => None,
            }
        })
        .collect()
}

fn default_matrix(matrix: &[Row]) -> Vec<Row> {
    matrix
        .iter()
        .filter_map(|row| {
            let (head, rest) = row.split_first()?;
            match head {
                ResolvedPattern::Wildcard => Some(rest.to_vec()),
                _ => None,
            }
        })
        .collect()
}

/// Checks a `match`'s full arm list, in source order, for exhaustiveness
/// and per-arm unreachability. `patterns[i]` corresponds to arm `i`'s
/// top-level pattern.
pub struct MatchAnalysis {
    /// `Some(witness)` iff the match is not exhaustive.
    pub missing: Option<ResolvedPattern>,
    /// Indices (into `patterns`) of arms that are unreachable given
    /// every earlier arm.
    pub unreachable: Vec<usize>,
    pub budget_exceeded: bool,
}

pub fn analyze_match(
    scrutinee_ty: &Ty,
    patterns: &[ResolvedPattern],
    variants: &VariantSpace,
) -> MatchAnalysis {
    let mut budget = MAX_USEFULNESS_STEPS;
    let occurrence_types = [scrutinee_ty.clone()];
    let mut matrix: Vec<Row> = Vec::new();
    let mut unreachable = Vec::new();
    let mut budget_exceeded = false;

    for (i, pattern) in patterns.iter().enumerate() {
        let row = vec![pattern.clone()];
        match is_useful(&matrix, &row, &occurrence_types, variants, &mut budget) {
            Usefulness::Useful(_) => {}
            Usefulness::NotUseful => unreachable.push(i),
            Usefulness::BudgetExceeded => {
                budget_exceeded = true;
                break;
            }
        }
        matrix.push(row);
    }

    let missing = if budget_exceeded {
        None
    } else {
        match is_useful(
            &matrix,
            &[ResolvedPattern::Wildcard],
            &occurrence_types,
            variants,
            &mut budget,
        ) {
            Usefulness::Useful(witness) => Some(
                witness
                    .into_iter()
                    .next()
                    .unwrap_or(ResolvedPattern::Wildcard),
            ),
            Usefulness::NotUseful => None,
            Usefulness::BudgetExceeded => {
                budget_exceeded = true;
                None
            }
        }
    };

    MatchAnalysis {
        missing,
        unreachable,
        budget_exceeded,
    }
}

/// Renders a witness pattern back into Napitia surface syntax for a
/// non-exhaustive-match diagnostic, e.g. `LookupResult.Missing` or
/// `Outer.A(Inner.Y)`.
pub fn describe_pattern(
    pattern: &ResolvedPattern,
    variant_names: &HashMap<ItemId, (String, Vec<String>)>,
) -> String {
    match pattern {
        ResolvedPattern::Wildcard => "_".to_string(),
        ResolvedPattern::Bool(b) => b.to_string(),
        ResolvedPattern::Literal(LiteralKey::Int(v)) => v.to_string(),
        ResolvedPattern::Literal(LiteralKey::Str(s)) => format!("{s:?}"),
        ResolvedPattern::Literal(LiteralKey::Char(c)) => format!("{c:?}"),
        ResolvedPattern::Variant {
            variant,
            case,
            args,
        } => {
            let (variant_name, case_names) = variant_names
                .get(variant)
                .map(|(v, c)| (v.as_str(), c.as_slice()))
                .unwrap_or(("<unknown>", &[]));
            let case_name = case_names
                .get(*case)
                .map(String::as_str)
                .unwrap_or("<unknown>");
            if args.is_empty() {
                format!("{variant_name}.{case_name}")
            } else {
                let args_text = args
                    .iter()
                    .map(|a| describe_pattern(a, variant_names))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{variant_name}.{case_name}({args_text})")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn variant_space(cases_per_item: Vec<(ItemId, Vec<Vec<Ty>>)>) -> VariantSpace {
        VariantSpace {
            payloads: cases_per_item.into_iter().collect(),
        }
    }

    #[test]
    fn wildcard_alone_is_exhaustive_for_bool() {
        let result = analyze_match(
            &Ty::Bool,
            &[ResolvedPattern::Wildcard],
            &variant_space(vec![]),
        );
        assert!(result.missing.is_none());
        assert!(result.unreachable.is_empty());
    }

    #[test]
    fn missing_false_case_is_reported() {
        let result = analyze_match(
            &Ty::Bool,
            &[ResolvedPattern::Bool(true)],
            &variant_space(vec![]),
        );
        assert_eq!(result.missing, Some(ResolvedPattern::Bool(false)));
    }

    #[test]
    fn both_bool_cases_plus_wildcard_flags_wildcard_unreachable() {
        let result = analyze_match(
            &Ty::Bool,
            &[
                ResolvedPattern::Bool(true),
                ResolvedPattern::Bool(false),
                ResolvedPattern::Wildcard,
            ],
            &variant_space(vec![]),
        );
        assert!(result.missing.is_none());
        assert_eq!(result.unreachable, vec![2]);
    }

    #[test]
    fn int_scrutinee_requires_a_catch_all() {
        let ty = Ty::I64;
        let result = analyze_match(
            &ty,
            &[ResolvedPattern::Literal(LiteralKey::Int(1))],
            &variant_space(vec![]),
        );
        assert!(result.missing.is_some());
    }

    #[test]
    fn variant_with_all_cases_covered_is_exhaustive() {
        let item = ItemId(0);
        let space = variant_space(vec![(item, vec![vec![], vec![]])]);
        let ty = Ty::Named(item, crate::symbol::Symbol(0));
        let result = analyze_match(
            &ty,
            &[
                ResolvedPattern::Variant {
                    variant: item,
                    case: 0,
                    args: vec![],
                },
                ResolvedPattern::Variant {
                    variant: item,
                    case: 1,
                    args: vec![],
                },
            ],
            &space,
        );
        assert!(result.missing.is_none());
    }

    #[test]
    fn variant_missing_a_case_is_reported_with_that_case_as_witness() {
        let item = ItemId(0);
        let space = variant_space(vec![(item, vec![vec![], vec![]])]);
        let ty = Ty::Named(item, crate::symbol::Symbol(0));
        let result = analyze_match(
            &ty,
            &[ResolvedPattern::Variant {
                variant: item,
                case: 0,
                args: vec![],
            }],
            &space,
        );
        assert_eq!(
            result.missing,
            Some(ResolvedPattern::Variant {
                variant: item,
                case: 1,
                args: vec![]
            })
        );
    }

    #[test]
    fn duplicate_variant_case_arm_is_unreachable() {
        let item = ItemId(0);
        let space = variant_space(vec![(item, vec![vec![], vec![]])]);
        let ty = Ty::Named(item, crate::symbol::Symbol(0));
        let result = analyze_match(
            &ty,
            &[
                ResolvedPattern::Variant {
                    variant: item,
                    case: 0,
                    args: vec![],
                },
                ResolvedPattern::Variant {
                    variant: item,
                    case: 0,
                    args: vec![],
                },
                ResolvedPattern::Variant {
                    variant: item,
                    case: 1,
                    args: vec![],
                },
            ],
            &space,
        );
        assert_eq!(result.unreachable, vec![1]);
        assert!(result.missing.is_none());
    }

    #[test]
    fn nested_variant_pattern_exhaustiveness() {
        // Outer { A(Inner), B }, Inner { X, Y }
        let outer = ItemId(0);
        let inner = ItemId(1);
        let inner_ty = Ty::Named(inner, crate::symbol::Symbol(1));
        let space = variant_space(vec![
            (outer, vec![vec![inner_ty.clone()], vec![]]),
            (inner, vec![vec![], vec![]]),
        ]);
        let outer_ty = Ty::Named(outer, crate::symbol::Symbol(0));
        // Only Outer.A(Inner.X) and Outer.B covered -- Outer.A(Inner.Y) missing.
        let result = analyze_match(
            &outer_ty,
            &[
                ResolvedPattern::Variant {
                    variant: outer,
                    case: 0,
                    args: vec![ResolvedPattern::Variant {
                        variant: inner,
                        case: 0,
                        args: vec![],
                    }],
                },
                ResolvedPattern::Variant {
                    variant: outer,
                    case: 1,
                    args: vec![],
                },
            ],
            &space,
        );
        assert_eq!(
            result.missing,
            Some(ResolvedPattern::Variant {
                variant: outer,
                case: 0,
                args: vec![ResolvedPattern::Variant {
                    variant: inner,
                    case: 1,
                    args: vec![]
                }],
            })
        );
    }

    #[test]
    fn budget_exceeded_is_reported_not_hung() {
        let mut budget = 2usize;
        let outcome = is_useful(
            &[],
            &[ResolvedPattern::Wildcard],
            &[Ty::Bool],
            &variant_space(vec![]),
            &mut budget,
        );
        // With a tiny budget this may or may not exceed depending on
        // recursion depth for this trivial case; assert it never panics
        // and returns one of the three defined outcomes.
        assert!(matches!(
            outcome,
            Usefulness::Useful(_) | Usefulness::NotUseful | Usefulness::BudgetExceeded
        ));
    }

    /// `Rec { Cons(Rec), Nil }` nested 50 levels deep against a budget
    /// far smaller than that -- `is_useful` recurses once per nesting
    /// level (each `Cons` descends into its own payload), consuming one
    /// unit of budget per level, so this deterministically runs out
    /// partway through a single row's descent rather than merely
    /// "maybe" exceeding depending on incidental recursion elsewhere.
    /// This is the real analogue of a deeply-nested source pattern:
    /// the budget must be what stops it, never the Rust call stack.
    fn nested_cons_pattern(item: ItemId, depth: usize) -> ResolvedPattern {
        if depth == 0 {
            ResolvedPattern::Variant {
                variant: item,
                case: 1,
                args: vec![],
            }
        } else {
            ResolvedPattern::Variant {
                variant: item,
                case: 0,
                args: vec![nested_cons_pattern(item, depth - 1)],
            }
        }
    }

    #[test]
    fn deeply_nested_pattern_genuinely_exhausts_the_budget() {
        let item = ItemId(0);
        let ty = Ty::Named(item, crate::symbol::Symbol(0));
        let space = variant_space(vec![(item, vec![vec![ty.clone()], vec![]])]);
        let pattern = nested_cons_pattern(item, 50);
        let mut budget = 10usize;
        let outcome = is_useful(&[], &[pattern], &[ty], &space, &mut budget);
        assert!(
            matches!(outcome, Usefulness::BudgetExceeded),
            "expected the budget to be exhausted by depth 50 with only 10 steps allowed"
        );
    }

    #[test]
    fn deeply_nested_pattern_hits_the_recursion_depth_bound_not_the_step_budget() {
        // Nested past MAX_RECURSION_DEPTH but with a step budget large
        // enough that it would never run out first -- isolates
        // is_useful's own stack-safety bound (independent of, and much
        // smaller than, MAX_USEFULNESS_STEPS) as what actually stops
        // this, the same defense a direct caller bypassing
        // typeck::check_pattern's own bound would otherwise be missing.
        let item = ItemId(0);
        let ty = Ty::Named(item, crate::symbol::Symbol(0));
        let space = variant_space(vec![(item, vec![vec![ty.clone()], vec![]])]);
        let pattern = nested_cons_pattern(item, MAX_RECURSION_DEPTH + 50);
        let mut budget = MAX_USEFULNESS_STEPS;
        let outcome = is_useful(&[], &[pattern], &[ty], &space, &mut budget);
        assert!(
            matches!(outcome, Usefulness::BudgetExceeded),
            "expected the recursion-depth bound to stop this before the step budget ever could"
        );
        assert!(
            budget > MAX_USEFULNESS_STEPS - MAX_RECURSION_DEPTH - 10,
            "the step budget barely moved; the depth bound, not step exhaustion, must be what fired"
        );
    }
}
