//! Stable structural place identity (`rfcs/0012`), shared unchanged by
//! `resourceck`, `nir::lower`, and `nir::verify` so no layer invents its
//! own incompatible notion of "the same field of the same aggregate."
//!
//! A place is a root value (a HIR [`crate::hir::LocalId`], or a NIR
//! [`crate::nir::ValueId`] once lowered) plus zero or more projections
//! reaching into it -- `session`, or `session.input`, or (arbitrarily
//! deep) `session.input.descriptor`. Every projection step is a *stable*
//! semantic identity (an aggregate's own [`ItemId`], paired with that
//! field's own declaration-order position), never a source span or a
//! name string: two places are the same place exactly when their roots
//! and projection sequences compare equal, independent of how either
//! was spelled or in what order a checker happened to visit them.
//!
//! [`FieldId`]/[`CaseId`] wrap a bare declaration-order position rather
//! than exposing a plain `usize` field access index directly, so every
//! consumer is forced to validate it against the owning aggregate's own
//! field/case vector length before indexing -- never trusted as already
//! in range just because it type-checks.

use crate::hir::ItemId;

/// A field's stable position within its declaring record/resource's own
/// field vector (declaration order) -- see the module doc comment.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FieldId(pub u32);

/// A variant case's stable position within its own declared case list.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CaseId(pub u32);

/// One hop of a place's own projection path.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Projection {
    /// A record or resource's own declared field, by stable identity.
    /// Reached through ordinary `.field` syntax at the source level, or
    /// synthesized by structural cleanup planning for an aggregate
    /// nested arbitrarily deep under some other place.
    Field { owner: ItemId, field: FieldId },
    /// One payload field of a variant's own specific case -- never
    /// reached through source-level `.field` syntax (variant payloads
    /// are only ever extracted through a pattern), but still part of
    /// this shared representation because structural destruction of a
    /// variant value still needs to name exactly which of its case's
    /// own payload fields it is destroying.
    VariantField {
        variant: ItemId,
        case: CaseId,
        field: FieldId,
    },
}

/// A stable reference to one exact storage location: `root` plus every
/// projection reaching into it, outermost first. Generic over `Root` so
/// `resourceck` (rooted at a HIR [`crate::hir::LocalId`]) and
/// `nir::lower`/`nir::verify` (rooted at a NIR [`crate::nir::ValueId`])
/// share this exact same projection/equality/ordering logic rather than
/// each maintaining an incompatible parallel copy of it.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Place<Root> {
    pub root: Root,
    pub projections: Vec<Projection>,
}

impl<Root: Copy> Place<Root> {
    /// The whole-value place: a bare root with no projections at all --
    /// what a plain, non-structural `resource` local already was in
    /// Alpha 0.1.7, and still is here, as the zero-projection case of
    /// this same representation.
    pub fn root(root: Root) -> Self {
        Place {
            root,
            projections: Vec::new(),
        }
    }

    /// This place's own immediate parent (one projection shorter), or
    /// `None` if this is already a root place. `session.input`'s parent
    /// is `session`; `session`'s parent is `None`.
    pub fn parent(&self) -> Option<Place<Root>> {
        if self.projections.is_empty() {
            return None;
        }
        Some(Place {
            root: self.root,
            projections: self.projections[..self.projections.len() - 1].to_vec(),
        })
    }

    /// Appends one more projection, reaching one field deeper.
    pub fn field(&self, owner: ItemId, field: FieldId) -> Self {
        let mut projections = self.projections.clone();
        projections.push(Projection::Field { owner, field });
        Place {
            root: self.root,
            projections,
        }
    }

    /// `true` iff `self` is `other`, or a place `other` was projected
    /// out of (directly or transitively) -- `session` is an ancestor of
    /// `session.input`, and of itself.
    pub fn is_ancestor_of(&self, other: &Place<Root>) -> bool
    where
        Root: PartialEq,
    {
        self.root == other.root
            && other.projections.len() >= self.projections.len()
            && other.projections[..self.projections.len()] == self.projections[..]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_root_place_has_no_projections_and_no_parent() {
        let p: Place<u32> = Place::root(7);
        assert_eq!(p.root, 7);
        assert!(p.projections.is_empty());
        assert!(p.parent().is_none());
    }

    #[test]
    fn field_appends_one_projection_and_parent_undoes_it() {
        let root: Place<u32> = Place::root(1);
        let child = root.field(ItemId(10), FieldId(0));
        assert_eq!(child.projections.len(), 1);
        assert_eq!(child.parent(), Some(root.clone()));
        let grandchild = child.field(ItemId(11), FieldId(2));
        assert_eq!(grandchild.parent(), Some(child.clone()));
        assert_ne!(grandchild, child);
    }

    #[test]
    fn equality_and_ordering_are_structural_not_pointer_based() {
        let a = Place::root(1u32).field(ItemId(5), FieldId(0));
        let b = Place::root(1u32).field(ItemId(5), FieldId(0));
        assert_eq!(a, b);
        let c = Place::root(1u32).field(ItemId(5), FieldId(1));
        assert_ne!(a, c);
        assert!(a < c);
    }

    #[test]
    fn is_ancestor_of_covers_self_and_every_descendant_only() {
        let session = Place::root(1u32);
        let input = session.field(ItemId(9), FieldId(0));
        let deeper = input.field(ItemId(20), FieldId(3));
        assert!(session.is_ancestor_of(&session));
        assert!(session.is_ancestor_of(&input));
        assert!(session.is_ancestor_of(&deeper));
        assert!(input.is_ancestor_of(&deeper));
        assert!(!input.is_ancestor_of(&session));
        let sibling = session.field(ItemId(9), FieldId(1));
        assert!(!input.is_ancestor_of(&sibling));
        assert!(!sibling.is_ancestor_of(&input));
    }
}
