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

/// One capability requirement, canonically (`uses Equal[T]`,
/// `rfcs/0009`): the exact declaring protocol's `ItemId` (never
/// re-derived from a name, so a local import alias never creates a
/// different requirement identity) plus its type arguments. Same
/// identity contract as [`GenericInstanceKey`] -- nominal over the
/// declaration, structural over the arguments -- kept as its own type
/// rather than a type alias since a capability requirement and a generic
/// instantiation are different concepts that only happen to share a
/// shape.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CapabilityRequirement {
    pub protocol: ItemId,
    pub arguments: Vec<Ty>,
}

impl CapabilityRequirement {
    pub fn new(protocol: ItemId, arguments: Vec<Ty>) -> Self {
        CapabilityRequirement {
            protocol,
            arguments,
        }
    }
}

/// One resolved piece of capability evidence (`rfcs/0009`): how a single
/// `uses` requirement, at one specific call site, is actually satisfied.
/// Computed once, entirely at compile time, by `typeck`'s capability
/// solver -- never re-derived, re-checked, or re-resolved by `nir::lower`,
/// the verifier, or the interpreter, which only ever copy these values
/// between call frames. This is dictionary-passing (the same technique
/// implementing e.g. Haskell typeclasses without specialization), not a
/// Rust vtable/trait object and not a C++ template instantiation: one
/// piece of data describing *which* extension answers a requirement,
/// passed alongside an ordinary call, with the callee's own body
/// existing exactly once regardless of how many concrete types ever
/// call it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Evidence {
    /// A concrete `extend` declaration, selected once, entirely at
    /// compile time, for this call site. `nested` is that same extend's
    /// own `uses` requirements (if any -- e.g. a conditional `extend[T]
    /// Equal[Box[T]] uses Equal[T]`), already resolved the same way: by
    /// the time a concrete extend is selected, every type it was
    /// selected for is already fully concrete too, so every leaf of
    /// `nested` is itself always `Extension`, never `Forwarded`.
    Extension {
        extend: ItemId,
        nested: Vec<Evidence>,
    },
    /// "Use whatever evidence the *currently executing* frame's own
    /// requirement at this index already holds." How a still-symbolic
    /// generic function or extend method forwards its own requirement to
    /// a callee without ever needing to know the concrete type its own
    /// caller will eventually supply -- resolved by the interpreter with
    /// one frame-relative lookup, never by re-running any resolution.
    Forwarded(usize),
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
