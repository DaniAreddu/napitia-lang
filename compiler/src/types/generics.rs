//! Canonical generic-instance identity and substitution (`rfcs/0008`).
//!
//! One central place for two concerns every generics-aware stage
//! (`typeck`, `nir::lower`, `nir::verify`) otherwise risked
//! reimplementing independently and letting drift apart: substituting a
//! declaration's own type parameters with concrete arguments inside one
//! of its types, and the canonical key that identifies one particular
//! instantiation.

use std::collections::HashMap;

use crate::hir::{ItemId, TypeParamId};
use crate::limits::MAX_GENERIC_DEPTH;
use crate::types::Ty;

/// One concrete instantiation of a generic declaration: the exact
/// declaring `ItemId` (never re-derived from a name, so an import alias
/// never affects it, `rfcs/0007`) plus its type arguments in the
/// declaration's own parameter order. Equality and hashing are
/// structural over `arguments` and nominal over `declaration` -- exactly
/// `Ty::Applied`'s own identity contract, since this is that same
/// identity lifted out to a reusable, standalone key (e.g. for budgeting
/// how many distinct instances a compilation has produced).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericInstanceKey {
    pub declaration: ItemId,
    pub arguments: Vec<Ty>,
}

impl GenericInstanceKey {
    pub fn new(declaration: ItemId, arguments: Vec<Ty>) -> Self {
        GenericInstanceKey {
            declaration,
            arguments,
        }
    }
}

/// Substitutes every occurrence of a type parameter in `subst` with its
/// mapped concrete type, walking through `Ty::Applied`'s own argument
/// list recursively (so a field/payload/parameter typed `Box[T]` becomes
/// `Box[i64]` once `T -> i64` is in `subst`). A parameter with no entry
/// in `subst` (never expected once every one of a declaration's own
/// parameters has a substitution, but not assumed) is left as-is rather
/// than panicking, so a caller passing an incomplete map degrades to a
/// partially-substituted type instead of crashing.
///
/// Bounded by [`MAX_GENERIC_DEPTH`] the same way every other stage that
/// walks a nested type application is: past that depth, recursion simply
/// stops and returns the type unchanged at that point, rather than
/// exhausting the native call stack. A type that deep was already
/// rejected with its own diagnostic wherever it was first resolved
/// (`hir::lower`), so this is defense in depth, not the primary bound.
pub fn substitute(ty: &Ty, subst: &HashMap<TypeParamId, Ty>) -> Ty {
    substitute_at_depth(ty, subst, 0)
}

fn substitute_at_depth(ty: &Ty, subst: &HashMap<TypeParamId, Ty>, depth: usize) -> Ty {
    if depth > MAX_GENERIC_DEPTH {
        return ty.clone();
    }
    match ty {
        Ty::Param(id, _) => subst.get(id).cloned().unwrap_or_else(|| ty.clone()),
        Ty::Applied(item, args) => Ty::Applied(
            *item,
            args.iter()
                .map(|a| substitute_at_depth(a, subst, depth + 1))
                .collect(),
        ),
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::Interner;

    #[test]
    fn substitutes_a_bare_type_parameter() {
        let mut interner = Interner::new();
        let t_symbol = interner.intern("T");
        let t = TypeParamId(0);
        let mut subst = HashMap::new();
        subst.insert(t, Ty::I64);
        assert_eq!(substitute(&Ty::Param(t, t_symbol), &subst), Ty::I64);
    }

    #[test]
    fn substitutes_recursively_through_applied_arguments() {
        let mut interner = Interner::new();
        let t_symbol = interner.intern("T");
        let t = TypeParamId(0);
        let box_item = ItemId(5);
        let mut subst = HashMap::new();
        subst.insert(t, Ty::Str);
        let applied = Ty::Applied(box_item, vec![Ty::Param(t, t_symbol)]);
        assert_eq!(
            substitute(&applied, &subst),
            Ty::Applied(box_item, vec![Ty::Str])
        );
    }

    #[test]
    fn a_type_with_no_parameters_is_unchanged() {
        let subst = HashMap::new();
        assert_eq!(substitute(&Ty::Bool, &subst), Ty::Bool);
    }

    #[test]
    fn an_unmapped_parameter_is_left_as_is_not_panicking() {
        let mut interner = Interner::new();
        let t_symbol = interner.intern("T");
        let t = TypeParamId(0);
        let subst = HashMap::new();
        assert_eq!(
            substitute(&Ty::Param(t, t_symbol), &subst),
            Ty::Param(t, t_symbol)
        );
    }

    #[test]
    fn instance_keys_compare_structurally() {
        let a = GenericInstanceKey::new(ItemId(1), vec![Ty::I64]);
        let b = GenericInstanceKey::new(ItemId(1), vec![Ty::I64]);
        let c = GenericInstanceKey::new(ItemId(1), vec![Ty::Str]);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }
}
