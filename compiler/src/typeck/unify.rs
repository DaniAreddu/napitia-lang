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
pub fn unify(ctx: &mut TypeContext, a: &Ty, b: &Ty) -> Result<(), (Ty, Ty)> {
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
}
