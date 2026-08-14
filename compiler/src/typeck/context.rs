//! Type-checking context: type-variable allocation and substitution.

use crate::types::{Ty, TyVar};

/// A constraint on what a type variable is allowed to resolve to, beyond
/// "whatever it gets unified with". Every variable in this milestone
/// comes from an integer or float literal (`spec/0003`), so `kind`
/// exists specifically to stop e.g. an integer literal's variable from
/// silently unifying with `bool` before it has had a chance to default
/// to `i64` — without this, `value x = 1; x = true;` would type-check,
/// because unifying an unconstrained variable with anything normally
/// just binds it.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum VarKind {
    Integer,
    Float,
}

/// Owns the substitution table for every type variable allocated while
/// checking one module. A variable's slot is `None` until
/// [`unify`](super::unify::unify) binds it to a concrete type (or to
/// another variable).
#[derive(Debug, Default)]
pub struct TypeContext {
    substitutions: Vec<Option<Ty>>,
    kinds: Vec<Option<VarKind>>,
}

impl TypeContext {
    pub fn new() -> Self {
        TypeContext {
            substitutions: Vec::new(),
            kinds: Vec::new(),
        }
    }

    pub fn fresh_var(&mut self) -> TyVar {
        self.fresh_var_with_kind(None)
    }

    pub fn fresh_var_with_kind(&mut self, kind: Option<VarKind>) -> TyVar {
        let id = TyVar(self.substitutions.len() as u32);
        self.substitutions.push(None);
        self.kinds.push(kind);
        id
    }

    pub(super) fn kind_of(&self, var: TyVar) -> Option<VarKind> {
        self.kinds[var.0 as usize]
    }

    pub(super) fn bind(&mut self, var: TyVar, ty: Ty) {
        self.substitutions[var.0 as usize] = Some(ty);
    }

    /// Follows `ty` through the substitution table until it reaches a
    /// concrete type or an unbound variable.
    pub fn resolve(&self, ty: &Ty) -> Ty {
        let mut current = ty.clone();
        while let Ty::Var(v) = &current {
            match &self.substitutions[v.0 as usize] {
                Some(next) => current = next.clone(),
                None => break,
            }
        }
        current
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_variables_are_distinct_and_unresolved() {
        let mut ctx = TypeContext::new();
        let a = ctx.fresh_var();
        let b = ctx.fresh_var();
        assert_ne!(a, b);
        assert_eq!(ctx.resolve(&Ty::Var(a)), Ty::Var(a));
    }

    #[test]
    fn binding_a_variable_resolves_to_the_bound_type() {
        let mut ctx = TypeContext::new();
        let v = ctx.fresh_var();
        ctx.bind(v, Ty::I64);
        assert_eq!(ctx.resolve(&Ty::Var(v)), Ty::I64);
    }

    #[test]
    fn resolve_follows_a_chain_of_variable_to_variable_bindings() {
        let mut ctx = TypeContext::new();
        let a = ctx.fresh_var();
        let b = ctx.fresh_var();
        ctx.bind(a, Ty::Var(b));
        ctx.bind(b, Ty::Bool);
        assert_eq!(ctx.resolve(&Ty::Var(a)), Ty::Bool);
    }

    #[test]
    fn resolving_a_concrete_type_returns_it_unchanged() {
        let ctx = TypeContext::new();
        assert_eq!(ctx.resolve(&Ty::Str), Ty::Str);
    }

    #[test]
    fn fresh_var_with_kind_remembers_its_kind() {
        let mut ctx = TypeContext::new();
        let v = ctx.fresh_var_with_kind(Some(VarKind::Integer));
        assert_eq!(ctx.kind_of(v), Some(VarKind::Integer));
    }

    #[test]
    fn plain_fresh_var_has_no_kind() {
        let mut ctx = TypeContext::new();
        let v = ctx.fresh_var();
        assert_eq!(ctx.kind_of(v), None);
    }
}
