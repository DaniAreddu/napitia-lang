//! Type unification.

use super::context::{TypeContext, VarKind};
use crate::types::{Ty, TyVar, is_integer};

/// Unifies `a` and `b`, binding type variables in `ctx` as needed.
/// `Error` and `Never` unify with anything (an unchecked/malformed
/// expression, or one that never produces a value, should not cause
/// unrelated cascading diagnostics). A kinded variable (`VarKind`) only
/// unifies with a concrete type consistent with its kind — e.g. an
/// integer-literal's variable refuses to unify with `bool` — so a
/// literal's pending default can't be silently overwritten by something
/// it was never actually compatible with. On failure, returns both sides
/// fully resolved, for the caller to report.
pub fn unify(ctx: &mut TypeContext, a: &Ty, b: &Ty) -> Result<(), (Ty, Ty)> {
    let a = ctx.resolve(a);
    let b = ctx.resolve(b);

    if a == b {
        return Ok(());
    }

    let compatible = match (&a, &b) {
        (Ty::Error, _) | (_, Ty::Error) => true,
        (Ty::Never, _) | (_, Ty::Never) => true,
        (Ty::Var(v), _) => kind_allows(ctx, *v, &b),
        (_, Ty::Var(v)) => kind_allows(ctx, *v, &a),
        _ => false,
    };

    if !compatible {
        return Err((a, b));
    }

    match (&a, &b) {
        (Ty::Var(v), _) => ctx.bind(*v, b),
        (_, Ty::Var(v)) => ctx.bind(*v, a),
        _ => {}
    }
    Ok(())
}

fn kind_allows(ctx: &TypeContext, var: TyVar, target: &Ty) -> bool {
    if matches!(target, Ty::Var(_)) {
        return true;
    }
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
}
