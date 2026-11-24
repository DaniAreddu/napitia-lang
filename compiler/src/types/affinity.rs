//! The one affinity classification every stage uses (`rfcs/0012`,
//! `rfcs/0016`).
//!
//! A type is *affine* when a value of it owns a `resource`: it is a
//! declared `resource`, or an aggregate one of whose fields or payloads
//! is affine, after substituting a generic instantiation's own
//! arguments. Type checking, resource checking, NIR lowering, the NIR
//! verifier and the interpreter all need that answer, and until Alpha
//! 0.2.3 each computed it with its own copy of this walk. The copies
//! disagreed exactly where it mattered: four of them stopped at
//! `MAX_GENERIC_DEPTH` and answered "not affine", one did not stop at
//! all, one cached the answer a cut-off walk produced as the type's
//! final one, and three recomputed shared substructure on every path,
//! which is exponential in the depth of a perfectly legal program.
//!
//! This module is now the walk. Each stage supplies its own view of the
//! declarations through [`AggregateShapes`] -- the stages keep their own
//! registries, which are not interchangeable -- and gets back the same
//! answer for the same declarations.
//!
//! # The three outcomes
//!
//! [`classify`] answers [`Affinity::Affine`], [`Affinity::NonAffine`],
//! or an [`AffinityError`] naming why no answer exists. There is no
//! fallback from the third to either of the first two: a caller that
//! has to act on an error decides what failing closed means in its own
//! terms (a diagnostic, a refusal, or treating the type as affine so no
//! ownership obligation is dropped).
//!
//! # What the budget measures
//!
//! The *affinity depth* of a type is the largest number of aggregates
//! on any containment path the classification has to walk:
//!
//! * a primitive, a type parameter or any other non-aggregate counts 0;
//! * a declared `resource` counts 1 and is not walked into -- it is
//!   affine whatever it contains;
//! * any other record or variant counts 1 plus the largest depth among
//!   its fields and payloads.
//!
//! [`MAX_AFFINITY_DEPTH`] bounds it. A type whose affinity depth exceeds
//! the budget is [`AffinityError::DepthExceeded`], whether or not a
//! resource sits anywhere inside it: the walk cannot know there is none
//! without walking all of it. The same bound is what keeps the host
//! stack of this recursive walk bounded.
//!
//! A containment cycle (`record Node { next: Node }`) has no finite
//! layout and is [`AffinityError::CyclicLayout`]. Source with one is
//! already rejected by type checking (`T0020`); the outcome exists for
//! hand-built NIR and for stages that keep running after that
//! diagnostic.
//!
//! # Why caching is safe
//!
//! [`AffinityCache`] stores a type's result only when its walk
//! completed: no cycle and no budget refusal anywhere beneath it. Such
//! a result is a property of the declarations alone -- the same walk
//! from the same type always finds the same aggregates -- so it does not
//! depend on which query computed it, from what depth, or what the
//! cache held at the time. A later query reaching a cached type at
//! depth `d` refuses exactly when `d` plus the cached depth exceeds the
//! budget, which is what an uncached walk from that point would find.
//! Errors are never cached: whether a type at depth `d` exceeds the
//! budget depends on `d`. Every complete type is walked once per cache,
//! and the first error ends the query, so the work of a classification
//! is linear in the number of distinct types it reaches.

use std::collections::{HashMap, HashSet};

use crate::hir::{ItemId, TypeParamId};

use super::{Ty, checked_substitution, substitute};

/// The largest affinity depth any stage classifies (see the module
/// documentation for what is counted). Shared with every other nesting
/// budget in the compiler.
pub const MAX_AFFINITY_DEPTH: usize = crate::limits::MAX_GENERIC_DEPTH;

/// Whether a value of a type owns a resource.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Affinity {
    Affine,
    NonAffine,
}

impl Affinity {
    pub fn is_affine(self) -> bool {
        self == Affinity::Affine
    }
}

/// Why a type could not be classified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AffinityError {
    /// Some containment path holds more than `limit` aggregates. Which
    /// aggregate the walk noticed it at is deliberately not part of the
    /// error: with a warm cache that is an ancestor of the one an
    /// uncached walk would name, and an outcome must not depend on what
    /// the cache held.
    DepthExceeded { limit: usize },
    /// `item` contains itself, directly or through other aggregates.
    CyclicLayout { item: ItemId },
}

/// One stage's view of the aggregate declarations a classification
/// walks.
pub trait AggregateShapes {
    /// `item` is a declared `resource`.
    fn is_declared_resource(&self, item: ItemId) -> bool;

    /// `item`'s own type parameters in declaration order, or `None` when
    /// this stage knows no record or variant with that id.
    fn type_params(&self, item: ItemId) -> Option<Vec<TypeParamId>>;

    /// Every field type of a record, or every payload type of every case
    /// of a variant, as declared (unsubstituted). Empty for an item this
    /// stage knows no layout for.
    fn field_types(&self, item: ItemId) -> Vec<Ty>;
}

/// The completed classifications one stage has computed, keyed by the
/// type they answer for. See the module documentation for why reusing
/// them cannot change an answer.
#[derive(Debug, Default, Clone)]
pub struct AffinityCache {
    named: HashMap<ItemId, Summary>,
    applied: HashMap<Ty, Summary>,
}

impl AffinityCache {
    pub fn new() -> Self {
        Self::default()
    }

    /// How many completed classifications are stored (for tests).
    pub fn len(&self) -> usize {
        self.named.len() + self.applied.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Summary {
    affine: bool,
    /// The affinity depth of the type this summary answers for.
    depth: usize,
}

/// Classifies `ty` against `shapes`, reusing and extending `cache`.
pub fn classify(
    ty: &Ty,
    shapes: &impl AggregateShapes,
    cache: &mut AffinityCache,
) -> Result<Affinity, AffinityError> {
    let mut visiting = HashSet::new();
    walk(ty, shapes, cache, &mut visiting, 0).map(|summary| {
        if summary.affine {
            Affinity::Affine
        } else {
            Affinity::NonAffine
        }
    })
}

/// Classifies `ty` with a cache of its own. Every query is still linear;
/// it simply shares nothing with any other.
pub fn classify_uncached(
    ty: &Ty,
    shapes: &impl AggregateShapes,
) -> Result<Affinity, AffinityError> {
    classify(ty, shapes, &mut AffinityCache::new())
}

/// `ty`'s summary, reached at `depth` aggregates below the query's root
/// (the root itself is at depth 0).
fn walk(
    ty: &Ty,
    shapes: &impl AggregateShapes,
    cache: &mut AffinityCache,
    visiting: &mut HashSet<ItemId>,
    depth: usize,
) -> Result<Summary, AffinityError> {
    let (item, args): (ItemId, &[Ty]) = match ty {
        Ty::Named(item, _) => (*item, &[]),
        Ty::Applied(item, args) => (*item, args.as_slice()),
        _ => {
            return Ok(Summary {
                affine: false,
                depth: 0,
            });
        }
    };
    // This aggregate is the (depth + 1)-th on the path from the root.
    if depth >= MAX_AFFINITY_DEPTH {
        return Err(AffinityError::DepthExceeded {
            limit: MAX_AFFINITY_DEPTH,
        });
    }
    if shapes.is_declared_resource(item) {
        return Ok(Summary {
            affine: true,
            depth: 1,
        });
    }
    let cached = match ty {
        Ty::Applied(..) => cache.applied.get(ty).copied(),
        _ => cache.named.get(&item).copied(),
    };
    if let Some(summary) = cached {
        if depth + summary.depth > MAX_AFFINITY_DEPTH {
            return Err(AffinityError::DepthExceeded {
                limit: MAX_AFFINITY_DEPTH,
            });
        }
        return Ok(summary);
    }

    let field_types = match ty {
        Ty::Applied(..) => {
            let params = shapes.type_params(item).unwrap_or_default();
            let Some(subst) = checked_substitution(&params, args) else {
                // An instantiation nothing could build a substitution
                // for: an unsubstituted parameter would answer "not
                // affine" and drop every obligation the instantiation
                // carries. Fail closed. This is a property of the
                // declaration and its arguments, so it is cached like
                // any other answer.
                let summary = Summary {
                    affine: true,
                    depth: 1,
                };
                cache.applied.insert(ty.clone(), summary);
                return Ok(summary);
            };
            shapes
                .field_types(item)
                .iter()
                .map(|field| substitute(field, &subst))
                .collect::<Vec<_>>()
        }
        _ => shapes.field_types(item),
    };

    // A cycle is detected per declaration, not per instantiation: a
    // generic declaration legitimately reaches itself again with other
    // arguments (`Box[Box[File]]`), and only the depth budget bounds
    // that. A non-generic one never can.
    let guarded = matches!(ty, Ty::Named(..));
    if guarded && !visiting.insert(item) {
        return Err(AffinityError::CyclicLayout { item });
    }
    let mut summary = Summary {
        affine: false,
        depth: 1,
    };
    let mut outcome = Ok(());
    for field in &field_types {
        match walk(field, shapes, cache, visiting, depth + 1) {
            Ok(child) => {
                summary.affine |= child.affine;
                summary.depth = summary.depth.max(1 + child.depth);
            }
            Err(error) => {
                outcome = Err(error);
                break;
            }
        }
    }
    if guarded {
        visiting.remove(&item);
    }
    outcome?;
    match ty {
        Ty::Applied(..) => cache.applied.insert(ty.clone(), summary),
        _ => cache.named.insert(item, summary),
    };
    Ok(summary)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::Interner;

    /// A declaration table built by hand: records only (a variant's
    /// payloads are walked through the same `field_types` view).
    #[derive(Default)]
    struct Decls {
        resources: HashSet<ItemId>,
        params: HashMap<ItemId, Vec<TypeParamId>>,
        fields: HashMap<ItemId, Vec<Ty>>,
    }

    impl AggregateShapes for Decls {
        fn is_declared_resource(&self, item: ItemId) -> bool {
            self.resources.contains(&item)
        }
        fn type_params(&self, item: ItemId) -> Option<Vec<TypeParamId>> {
            self.params.get(&item).cloned()
        }
        fn field_types(&self, item: ItemId) -> Vec<Ty> {
            self.fields.get(&item).cloned().unwrap_or_default()
        }
    }

    struct World {
        interner: Interner,
        decls: Decls,
    }

    impl World {
        fn new() -> Self {
            World {
                interner: Interner::new(),
                decls: Decls::default(),
            }
        }
        fn named(&mut self, id: u32) -> Ty {
            let symbol = self.interner.intern(&format!("T{id}"));
            Ty::Named(ItemId(id), symbol)
        }
        fn record(&mut self, id: u32, fields: Vec<Ty>) -> Ty {
            self.decls.params.insert(ItemId(id), Vec::new());
            self.decls.fields.insert(ItemId(id), fields);
            self.named(id)
        }
        fn resource(&mut self, id: u32) -> Ty {
            self.decls.resources.insert(ItemId(id));
            self.record(id, vec![Ty::I64])
        }
        /// `record Box[T] { item: T }`, as item `id`.
        fn generic_box(&mut self, id: u32) {
            let t = TypeParamId(id);
            let symbol = self.interner.intern("T");
            self.decls.params.insert(ItemId(id), vec![t]);
            self.decls
                .fields
                .insert(ItemId(id), vec![Ty::Param(t, symbol)]);
        }
        /// `record R0 { inner: R1 } ... record R{n-1} { inner: leaf }`,
        /// records numbered from `first`; returns `R0`.
        fn chain(&mut self, first: u32, n: u32, leaf: Ty) -> Ty {
            let mut inner = leaf;
            for k in (0..n).rev() {
                inner = self.record(first + k, vec![inner]);
            }
            inner
        }
        fn classify(&self, ty: &Ty) -> Result<Affinity, AffinityError> {
            classify_uncached(ty, &self.decls)
        }
    }

    #[test]
    fn primitives_and_parameters_are_not_affine() {
        let world = World::new();
        assert_eq!(world.classify(&Ty::I64), Ok(Affinity::NonAffine));
        assert_eq!(world.classify(&Ty::Unit), Ok(Affinity::NonAffine));
        let symbol = Interner::new().intern("T");
        assert_eq!(
            world.classify(&Ty::Param(TypeParamId(0), symbol)),
            Ok(Affinity::NonAffine)
        );
    }

    #[test]
    fn a_declared_resource_and_anything_holding_one_are_affine() {
        let mut world = World::new();
        let file = world.resource(1);
        let holder = world.record(2, vec![Ty::I64, file.clone()]);
        let plain = world.record(3, vec![Ty::I64, Ty::Bool]);
        assert_eq!(world.classify(&file), Ok(Affinity::Affine));
        assert_eq!(world.classify(&holder), Ok(Affinity::Affine));
        assert_eq!(world.classify(&plain), Ok(Affinity::NonAffine));
    }

    #[test]
    fn a_generic_instantiation_answers_from_its_own_arguments() {
        let mut world = World::new();
        let file = world.resource(1);
        world.generic_box(2);
        let of_file = Ty::Applied(ItemId(2), vec![file.clone()]);
        let of_int = Ty::Applied(ItemId(2), vec![Ty::I64]);
        let nested = Ty::Applied(ItemId(2), vec![of_file.clone()]);
        assert_eq!(world.classify(&of_file), Ok(Affinity::Affine));
        assert_eq!(world.classify(&of_int), Ok(Affinity::NonAffine));
        // `Box[Box[File]]` reaches `Box` twice with different arguments,
        // which is nesting, not a cycle.
        assert_eq!(world.classify(&nested), Ok(Affinity::Affine));
    }

    #[test]
    fn an_instantiation_with_the_wrong_arity_fails_closed_to_affine() {
        let mut world = World::new();
        world.generic_box(2);
        let wrong = Ty::Applied(ItemId(2), vec![Ty::I64, Ty::I64]);
        let unknown = Ty::Applied(ItemId(99), vec![Ty::I64]);
        assert_eq!(world.classify(&wrong), Ok(Affinity::Affine));
        assert_eq!(world.classify(&unknown), Ok(Affinity::Affine));
    }

    #[test]
    fn a_containment_cycle_is_an_error_not_an_answer() {
        let mut world = World::new();
        let node = world.named(1);
        world.record(1, vec![Ty::I64, node.clone()]);
        assert_eq!(
            world.classify(&node),
            Err(AffinityError::CyclicLayout { item: ItemId(1) })
        );
        // Through another declaration as well.
        let a = world.named(2);
        let b = world.record(3, vec![a.clone()]);
        world.record(2, vec![b]);
        assert!(matches!(
            world.classify(&a),
            Err(AffinityError::CyclicLayout { .. })
        ));
    }

    #[test]
    fn the_budget_admits_exactly_its_own_depth() {
        let mut world = World::new();
        let file = world.resource(1);
        // 63 records around a resource: depth 64, the budget itself.
        let at_budget = world.chain(100, 63, file.clone());
        assert_eq!(world.classify(&at_budget), Ok(Affinity::Affine));
        // One more record: depth 65.
        let past = world.record(99, vec![at_budget]);
        assert_eq!(
            world.classify(&past),
            Err(AffinityError::DepthExceeded {
                limit: MAX_AFFINITY_DEPTH,
            })
        );
    }

    #[test]
    fn exceeding_the_budget_is_an_error_whether_or_not_a_resource_is_inside() {
        let mut world = World::new();
        let plain = world.chain(100, 65, Ty::I64);
        let shallow = world.chain(300, 64, Ty::I64);
        assert!(matches!(
            world.classify(&plain),
            Err(AffinityError::DepthExceeded { .. })
        ));
        assert_eq!(world.classify(&shallow), Ok(Affinity::NonAffine));
    }

    #[test]
    fn a_deep_generic_instantiation_is_bounded_by_the_same_budget() {
        let mut world = World::new();
        let file = world.resource(1);
        world.generic_box(2);
        let mut ty = file;
        for _ in 0..63 {
            ty = Ty::Applied(ItemId(2), vec![ty]);
        }
        assert_eq!(world.classify(&ty), Ok(Affinity::Affine));
        let past = Ty::Applied(ItemId(2), vec![ty]);
        assert!(matches!(
            world.classify(&past),
            Err(AffinityError::DepthExceeded { .. })
        ));
    }

    /// The defect this module replaced: a cut-off walk's answer for an
    /// inner type was cached as that type's final answer, so a later
    /// query got "not affine" for a type that owns a resource.
    #[test]
    fn a_refusal_deep_in_one_query_does_not_change_a_later_answer() {
        let mut world = World::new();
        let file = world.resource(1);
        let inner = world.chain(100, 10, file);
        let outer = world.chain(200, 60, inner.clone());
        let mut cache = AffinityCache::new();
        assert!(matches!(
            classify(&outer, &world.decls, &mut cache),
            Err(AffinityError::DepthExceeded { .. })
        ));
        assert_eq!(
            classify(&inner, &world.decls, &mut cache),
            Ok(Affinity::Affine)
        );
        assert_eq!(world.classify(&inner), Ok(Affinity::Affine));
    }

    /// Every order of the same queries over one cache gives every query
    /// the answer it gets alone.
    #[test]
    fn query_order_and_cache_history_do_not_change_any_answer() {
        let mut world = World::new();
        let file = world.resource(1);
        world.generic_box(2);
        let inner = world.chain(100, 30, file.clone());
        let middle = world.chain(200, 30, inner.clone());
        let deep = world.chain(300, 10, middle.clone());
        let boxed = Ty::Applied(ItemId(2), vec![middle.clone()]);
        let plain = world.chain(400, 20, Ty::I64);
        let node = world.named(500);
        world.record(500, vec![node.clone()]);
        let queries = [inner, middle, deep, boxed, plain, node, file];
        let alone: Vec<_> = queries.iter().map(|q| world.classify(q)).collect();

        // Every rotation and its reverse, through one shared cache each.
        for start in 0..queries.len() {
            for reverse in [false, true] {
                let mut order: Vec<usize> = (0..queries.len())
                    .map(|i| (start + i) % queries.len())
                    .collect();
                if reverse {
                    order.reverse();
                }
                let mut cache = AffinityCache::new();
                for &i in &order {
                    assert_eq!(
                        classify(&queries[i], &world.decls, &mut cache),
                        alone[i],
                        "query {i} in order {order:?}"
                    );
                }
            }
        }
    }

    /// `L0 { a: L1, b: L1 }`, `L1 { a: L2, b: L2 }`, ...: 2^60 paths and
    /// 60 distinct types. Answered by visiting each type once.
    #[test]
    fn shared_substructure_is_classified_in_linear_work() {
        let mut world = World::new();
        let file = world.resource(1);
        let mut inner = file;
        for k in (0..60).rev() {
            inner = world.record(100 + k, vec![inner.clone(), inner]);
        }
        let mut cache = AffinityCache::new();
        assert_eq!(
            classify(&inner, &world.decls, &mut cache),
            Ok(Affinity::Affine)
        );
        assert_eq!(cache.len(), 60);
    }

    /// A type reached at depth `d` refuses exactly when an uncached walk
    /// from there would: the cached depth plus `d`.
    #[test]
    fn a_cached_type_reached_deeper_than_before_still_respects_the_budget() {
        let mut world = World::new();
        let file = world.resource(1);
        let inner = world.chain(100, 40, file);
        let mut cache = AffinityCache::new();
        assert_eq!(
            classify(&inner, &world.decls, &mut cache),
            Ok(Affinity::Affine)
        );
        let outer = world.chain(200, 25, inner);
        assert_eq!(
            classify(&outer, &world.decls, &mut cache),
            world.classify(&outer)
        );
        assert!(world.classify(&outer).is_err());
    }
}
