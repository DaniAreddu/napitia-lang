//! Type unification.
//!
//! This is constraint-based, monomorphic local inference over literal
//! type variables — not full Hindley-Milner (there is no let-generalization
//! or polymorphism: every variable is solved to one concrete type per
//! function, never generalized over multiple call sites). "Unification"
//! here means solving a small set of `Integer`/`Float`-kinded variables
//! introduced by literals, plus the union-find-style merging below for
//! when two such variables are unified with each other before either is
//! known concretely.

use super::context::{TypeContext, VarKind};
use crate::limits::MAX_GENERIC_DEPTH;
use crate::types::{Ty, TyVar, is_integer};

/// Unifies `a` and `b`, binding type variables in `ctx` as needed.
/// `Error` and `Never` unify with anything (an unchecked/malformed
/// expression, or one that never produces a value, should not cause
/// unrelated cascading diagnostics). A kinded variable (`VarKind`) only
/// unifies with a concrete type consistent with its kind — e.g. an
/// integer-literal's variable refuses to unify with `bool` — so a
/// literal's pending default can't be silently overwritten by something
/// it was never actually compatible with.
///
/// Unifying two *variables* with each other is handled as a small
/// union-find merge: whichever kind constraint either side already
/// carries must survive on the merged root, or a later default (e.g.
/// binding the merged variable to `f64` because a `1.0` was unified with
/// it) could silently violate a constraint the other variable required
/// (e.g. that same merged variable also being unified with an
/// `Integer`-kinded literal). Merging two variables whose kinds
/// genuinely conflict (`Integer` vs `Float`) is itself a unification
/// failure, not a silent pick of one side.
///
/// On failure, returns both sides fully resolved, for the caller to
/// report. Resolution always terminates: a variable is only ever bound
/// to the *other* side's already-fully-resolved form, so the
/// substitution graph is always a forest (no cycles can form).
///
/// A `Ty::Applied` unifies structurally with another one iff they name
/// the exact same declaration (nominal, matching `Ty::Applied`'s own
/// identity contract -- `sales.Box[i64]` never unifies with
/// `admin.Box[i64]` even if both spell `Box`, and an alias never affects
/// this since the declaration is always the canonical `ItemId`) and have
/// the same arity, in which case corresponding type arguments unify
/// pairwise, recursively (`rfcs/0008`) -- this is what lets a generic
/// parameter's fresh inference variable be discovered *inside* an
/// applied argument (`unify(Box[Var(T)], Box[i64])` binds `T` to `i64`),
/// not just at the top level. A mismatched declaration or arity is a
/// deterministic, immediate failure, never a partial/best-effort bind.
pub fn unify(ctx: &mut TypeContext, a: &Ty, b: &Ty) -> Result<(), (Ty, Ty)> {
    unify_at_depth(ctx, a, b, 0)
}

fn unify_at_depth(ctx: &mut TypeContext, a: &Ty, b: &Ty, depth: usize) -> Result<(), (Ty, Ty)> {
    let a = ctx.resolve(a);
    let b = ctx.resolve(b);

    if a == b {
        return Ok(());
    }

    match (&a, &b) {
        (Ty::Error, _) | (_, Ty::Error) => Ok(()),
        (Ty::Never, _) | (_, Ty::Never) => Ok(()),
        (Ty::Var(va), Ty::Var(vb)) => merge_vars(ctx, *va, *vb, &a, &b),
        (Ty::Var(v), _) => {
            if kind_allows(ctx, *v, &b) {
                ctx.bind(*v, b);
                Ok(())
            } else {
                Err((a, b))
            }
        }
        (_, Ty::Var(v)) => {
            if kind_allows(ctx, *v, &a) {
                ctx.bind(*v, a);
                Ok(())
            } else {
                Err((a, b))
            }
        }
        (Ty::Applied(a_item, a_args), Ty::Applied(b_item, b_args)) => {
            if a_item != b_item || a_args.len() != b_args.len() {
                return Err((a.clone(), b.clone()));
            }
            // Defense in depth, mirroring `types::generics::substitute`'s
            // own bound: a well-typed program's own `Ty::Applied`
            // nesting is already far shallower than this by the time it
            // reaches unification (`hir::lower` rejects deeper type
            // applications at the syntax level, R0019), so this only
            // ever stops a malformed/hand-built `Ty` from recursing
            // unboundedly, never a real program's inference.
            if depth >= MAX_GENERIC_DEPTH {
                return Err((a.clone(), b.clone()));
            }
            for (x, y) in a_args.iter().zip(b_args.iter()) {
                unify_at_depth(ctx, x, y, depth + 1)?;
            }
            Ok(())
        }
        _ => Err((a, b)),
    }
}

/// Merges two distinct, still-unresolved variables, preserving whichever
/// kind constraint either side already carries on the surviving root
/// (`vb`). Fails if the two variables carry different, incompatible
/// kinds (`Integer` merged with `Float`) — e.g. `value x = 1 + 2.0;`
/// must be rejected here, not silently resolved by picking one side's
/// default and discarding the other's constraint.
fn merge_vars(ctx: &mut TypeContext, va: TyVar, vb: TyVar, a: &Ty, b: &Ty) -> Result<(), (Ty, Ty)> {
    let merged_kind = match (ctx.kind_of(va), ctx.kind_of(vb)) {
        (Some(x), Some(y)) if x != y => return Err((a.clone(), b.clone())),
        (Some(x), _) => Some(x),
        (None, y) => y,
    };
    ctx.bind(va, b.clone());
    ctx.set_kind(vb, merged_kind);
    Ok(())
}

/// Whether `target` (already resolved, and known not to itself be a
/// variable) is consistent with `var`'s kind constraint, if any.
fn kind_allows(ctx: &TypeContext, var: TyVar, target: &Ty) -> bool {
    match ctx.kind_of(var) {
        Some(VarKind::Integer) => is_integer(target),
        Some(VarKind::Float) => matches!(target, Ty::F32 | Ty::F64),
        None => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identical_concrete_types_unify() {
        let mut ctx = TypeContext::new();
        assert!(unify(&mut ctx, &Ty::I64, &Ty::I64).is_ok());
    }

    #[test]
    fn distinct_concrete_types_fail_to_unify() {
        let mut ctx = TypeContext::new();
        let result = unify(&mut ctx, &Ty::I64, &Ty::Bool);
        assert_eq!(result, Err((Ty::I64, Ty::Bool)));
    }

    #[test]
    fn unifying_a_variable_with_a_concrete_type_binds_it() {
        let mut ctx = TypeContext::new();
        let v = ctx.fresh_var();
        assert!(unify(&mut ctx, &Ty::Var(v), &Ty::F64).is_ok());
        assert_eq!(ctx.resolve(&Ty::Var(v)), Ty::F64);
    }

    #[test]
    fn unifying_two_variables_links_them() {
        let mut ctx = TypeContext::new();
        let a = ctx.fresh_var();
        let b = ctx.fresh_var();
        assert!(unify(&mut ctx, &Ty::Var(a), &Ty::Var(b)).is_ok());
        assert!(unify(&mut ctx, &Ty::Var(b), &Ty::I32).is_ok());
        assert_eq!(ctx.resolve(&Ty::Var(a)), Ty::I32);
    }

    #[test]
    fn unifying_a_variable_with_itself_does_not_loop() {
        let mut ctx = TypeContext::new();
        let v = ctx.fresh_var();
        assert!(unify(&mut ctx, &Ty::Var(v), &Ty::Var(v)).is_ok());
        assert_eq!(ctx.resolve(&Ty::Var(v)), Ty::Var(v));
    }

    #[test]
    fn error_unifies_with_anything() {
        let mut ctx = TypeContext::new();
        assert!(unify(&mut ctx, &Ty::Error, &Ty::Bool).is_ok());
        assert!(unify(&mut ctx, &Ty::Str, &Ty::Error).is_ok());
    }

    #[test]
    fn never_unifies_with_anything() {
        let mut ctx = TypeContext::new();
        assert!(unify(&mut ctx, &Ty::Never, &Ty::I64).is_ok());
        assert!(unify(&mut ctx, &Ty::Bool, &Ty::Never).is_ok());
    }

    #[test]
    fn integer_kinded_variable_unifies_with_an_integer_type() {
        let mut ctx = TypeContext::new();
        let v = ctx.fresh_var_with_kind(Some(VarKind::Integer));
        assert!(unify(&mut ctx, &Ty::Var(v), &Ty::I32).is_ok());
    }

    #[test]
    fn integer_kinded_variable_refuses_to_unify_with_bool() {
        let mut ctx = TypeContext::new();
        let v = ctx.fresh_var_with_kind(Some(VarKind::Integer));
        assert!(unify(&mut ctx, &Ty::Var(v), &Ty::Bool).is_err());
        // A failed unification must not have bound the variable.
        assert_eq!(ctx.resolve(&Ty::Var(v)), Ty::Var(v));
    }

    #[test]
    fn float_kinded_variable_refuses_to_unify_with_an_integer_type() {
        let mut ctx = TypeContext::new();
        let v = ctx.fresh_var_with_kind(Some(VarKind::Float));
        assert!(unify(&mut ctx, &Ty::Var(v), &Ty::I64).is_err());
    }

    #[test]
    fn float_kinded_variable_unifies_with_a_float_type() {
        let mut ctx = TypeContext::new();
        let v = ctx.fresh_var_with_kind(Some(VarKind::Float));
        assert!(unify(&mut ctx, &Ty::Var(v), &Ty::F32).is_ok());
    }

    #[test]
    fn merging_integer_and_float_kinded_variables_is_rejected() {
        // This is the bug regression for `value x = 1 + 2.0;`: unifying
        // an Integer-kinded variable with a Float-kinded one (before
        // either resolves to a concrete type) must fail, not silently
        // pick one side and discard the other's constraint.
        let mut ctx = TypeContext::new();
        let int_var = ctx.fresh_var_with_kind(Some(VarKind::Integer));
        let float_var = ctx.fresh_var_with_kind(Some(VarKind::Float));
        assert!(unify(&mut ctx, &Ty::Var(int_var), &Ty::Var(float_var)).is_err());
    }

    #[test]
    fn merging_two_integer_kinded_variables_preserves_the_kind() {
        let mut ctx = TypeContext::new();
        let a = ctx.fresh_var_with_kind(Some(VarKind::Integer));
        let b = ctx.fresh_var_with_kind(Some(VarKind::Integer));
        assert!(unify(&mut ctx, &Ty::Var(a), &Ty::Var(b)).is_ok());
        // The merged root must still refuse a non-integer type.
        assert!(unify(&mut ctx, &Ty::Var(b), &Ty::Bool).is_err());
    }

    #[test]
    fn merging_a_kinded_variable_into_an_unkinded_one_preserves_the_kind() {
        // The unkinded variable (`b`, from a context with no literal
        // default pending) becomes the root when `a` (Integer-kinded)
        // unifies with it; the merged root must still carry `a`'s
        // Integer constraint rather than losing it because `b` itself
        // had none.
        let mut ctx = TypeContext::new();
        let a = ctx.fresh_var_with_kind(Some(VarKind::Integer));
        let b = ctx.fresh_var();
        assert!(unify(&mut ctx, &Ty::Var(a), &Ty::Var(b)).is_ok());
        assert!(unify(&mut ctx, &Ty::Var(b), &Ty::Bool).is_err());
    }

    #[test]
    fn variable_chain_of_three_preserves_the_root_constraint() {
        // a -> b -> c: unify a with b, then b with c, then check that
        // c (now the ultimate root) still enforces a's original
        // Integer constraint even though it was never unified with a
        // directly.
        let mut ctx = TypeContext::new();
        let a = ctx.fresh_var_with_kind(Some(VarKind::Integer));
        let b = ctx.fresh_var();
        let c = ctx.fresh_var();
        assert!(unify(&mut ctx, &Ty::Var(a), &Ty::Var(b)).is_ok());
        assert!(unify(&mut ctx, &Ty::Var(b), &Ty::Var(c)).is_ok());
        assert!(unify(&mut ctx, &Ty::Var(c), &Ty::Bool).is_err());
        assert!(unify(&mut ctx, &Ty::Var(c), &Ty::I64).is_ok());
        assert_eq!(ctx.resolve(&Ty::Var(a)), Ty::I64);
    }

    #[test]
    fn applied_types_with_a_variable_argument_infer_it_from_a_concrete_one() {
        // `unify(Box[Var(T)], Box[i64])` is exactly what a generic
        // call's own argument-vs-parameter check does once `T` is a
        // fresh inference variable substituted into `Box[T]` --
        // unification must reach inside the applied argument list to
        // bind it, not just fail at the top level.
        let mut ctx = TypeContext::new();
        let box_item = crate::hir::ItemId(0);
        let v = ctx.fresh_var();
        let expected = Ty::Applied(box_item, vec![Ty::Var(v)]);
        let actual = Ty::Applied(box_item, vec![Ty::I64]);
        assert!(unify(&mut ctx, &expected, &actual).is_ok());
        assert_eq!(ctx.resolve(&Ty::Var(v)), Ty::I64);
    }

    #[test]
    fn applied_types_unify_recursively_through_nested_arguments() {
        // `Box[Maybe[Var(T)]]` vs `Box[Maybe[i64]]` -- the variable is
        // two applications deep, not just one.
        let mut ctx = TypeContext::new();
        let box_item = crate::hir::ItemId(0);
        let maybe_item = crate::hir::ItemId(1);
        let v = ctx.fresh_var();
        let expected = Ty::Applied(box_item, vec![Ty::Applied(maybe_item, vec![Ty::Var(v)])]);
        let actual = Ty::Applied(box_item, vec![Ty::Applied(maybe_item, vec![Ty::I64])]);
        assert!(unify(&mut ctx, &expected, &actual).is_ok());
        assert_eq!(ctx.resolve(&Ty::Var(v)), Ty::I64);
    }

    #[test]
    fn applied_types_with_different_declarations_never_unify() {
        // Same arity and argument, different declaration -- e.g.
        // `sales.Box[i64]` vs `admin.Box[i64]`: nominal identity means
        // these must never unify even though they'd look identical
        // structurally.
        let mut ctx = TypeContext::new();
        let a = Ty::Applied(crate::hir::ItemId(0), vec![Ty::I64]);
        let b = Ty::Applied(crate::hir::ItemId(1), vec![Ty::I64]);
        assert_eq!(unify(&mut ctx, &a, &b), Err((a, b)));
    }

    #[test]
    fn applied_types_with_different_arity_never_unify() {
        let mut ctx = TypeContext::new();
        let item = crate::hir::ItemId(0);
        let a = Ty::Applied(item, vec![Ty::I64]);
        let b = Ty::Applied(item, vec![Ty::I64, Ty::Bool]);
        assert_eq!(unify(&mut ctx, &a, &b), Err((a, b)));
    }

    #[test]
    fn applied_types_with_conflicting_arguments_never_unify() {
        let mut ctx = TypeContext::new();
        let item = crate::hir::ItemId(0);
        let a = Ty::Applied(item, vec![Ty::I64]);
        let b = Ty::Applied(item, vec![Ty::Bool]);
        assert!(unify(&mut ctx, &a, &b).is_err());
    }

    #[test]
    fn applied_types_with_identical_arguments_unify_with_no_bindings_needed() {
        let mut ctx = TypeContext::new();
        let item = crate::hir::ItemId(0);
        let a = Ty::Applied(item, vec![Ty::I64]);
        let b = Ty::Applied(item, vec![Ty::I64]);
        assert!(unify(&mut ctx, &a, &b).is_ok());
    }
}
