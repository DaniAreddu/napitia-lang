//! Canonical, deterministic per-item identity metadata (`rfcs/0007`).
//!
//! Every function, record, and variant `ItemId` is mapped to exactly
//! one [`ItemIdentity`]: the declaring module's canonical dotted path,
//! the item's own declared name (never a local import alias), its
//! kind, and where it was declared. This is the single, canonical
//! source of truth for "what is this item's qualified name" -- built
//! once from an already-lowered/merged [`HirModule`], never re-derived
//! independently by `typeck`, `nir`, or diagnostic formatting, so there
//! is nothing for two separate name maps to disagree about.
//!
//! The semantic identity of an item remains its `ItemId` everywhere
//! else in the compiler; everything in this module is display/debug
//! metadata layered on top, never a substitute for it.

use std::collections::HashMap;

use super::{HirModule, ItemId};
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};

/// Which kind of module-level item an [`ItemIdentity`] describes.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ItemKind {
    Function,
    Record,
    Variant,
}

impl ItemKind {
    pub fn describe(self) -> &'static str {
        match self {
            ItemKind::Function => "function",
            ItemKind::Record => "record",
            ItemKind::Variant => "variant",
        }
    }
}

/// One item's canonical metadata: enough to print or diagnose it by its
/// true identity rather than by whatever local (possibly aliased) name
/// happened to resolve a particular reference to it.
#[derive(Clone, Debug)]
pub struct ItemIdentity {
    /// The declaring module's dotted path (e.g. `sales.user`) -- empty
    /// for single-file compilation, which has no project-level module
    /// path at all; callers display an empty path as no qualification,
    /// never as a literal leading dot.
    pub module_path: String,
    /// The item's own declared name -- never a local import alias.
    pub name: Symbol,
    pub kind: ItemKind,
    pub source: SourceId,
    pub span: Span,
}

/// A deterministic `ItemId -> ItemIdentity` lookup table, built once
/// per compilation. Point lookups only: nothing here is ever iterated
/// in a way whose order would matter (a consumer that needs a stable
/// order -- e.g. the NIR printer -- always derives it from the HIR's
/// own `Vec` order instead), so a plain `HashMap` costs nothing.
#[derive(Debug, Default)]
pub struct ItemRegistry {
    entries: HashMap<ItemId, ItemIdentity>,
}

impl ItemRegistry {
    pub fn get(&self, id: ItemId) -> Option<&ItemIdentity> {
        self.entries.get(&id)
    }

    /// The canonical, module-qualified display name for `id` -- e.g.
    /// `sales.user.User`, or just `User` when there is no module path
    /// (single-file compilation, or an id this registry never learned
    /// about). Never influenced by any import alias: this always
    /// resolves through the item's own registered declaration.
    pub fn qualified_name(&self, id: ItemId, interner: &Interner) -> String {
        match self.entries.get(&id) {
            Some(identity) if identity.module_path.is_empty() => {
                interner.resolve(identity.name).to_string()
            }
            Some(identity) => {
                format!(
                    "{}.{}",
                    identity.module_path,
                    interner.resolve(identity.name)
                )
            }
            // Never reached by a well-formed compilation (every item a
            // consumer could hold an `ItemId` for was registered by
            // `build` below) -- kept readable rather than panicking, so
            // a caller that somehow holds a stale or foreign `ItemId`
            // degrades to a labeled placeholder instead of crashing.
            None => format!("<item #{}>", id.0),
        }
    }
}

/// Builds a registry from an already-lowered/merged [`HirModule`].
/// `module_path_of` maps each item's own declaring [`SourceId`] to its
/// module's dotted path; single-file compilation passes an empty map
/// (every lookup then misses, leaving `module_path` empty for every
/// item -- exactly the "no qualification" case `qualified_name`
/// documents).
pub fn build(hir: &HirModule, module_path_of: &HashMap<SourceId, String>) -> ItemRegistry {
    let mut registry = ItemRegistry::default();
    for f in &hir.functions {
        registry.entries.insert(
            f.id,
            ItemIdentity {
                module_path: module_path_of.get(&f.source).cloned().unwrap_or_default(),
                name: f.name,
                kind: ItemKind::Function,
                source: f.source,
                span: f.name_span,
            },
        );
    }
    for r in &hir.records {
        registry.entries.insert(
            r.id,
            ItemIdentity {
                module_path: module_path_of.get(&r.source).cloned().unwrap_or_default(),
                name: r.name,
                kind: ItemKind::Record,
                source: r.source,
                span: r.span,
            },
        );
    }
    for v in &hir.variants {
        registry.entries.insert(
            v.id,
            ItemIdentity {
                module_path: module_path_of.get(&v.source).cloned().unwrap_or_default(),
                name: v.name,
                kind: ItemKind::Variant,
                source: v.source,
                span: v.span,
            },
        );
    }
    registry
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::{HirCase, HirFunction, HirRecord, HirVariant};
    use crate::source::SourceMap;
    use crate::symbol::Interner;

    #[test]
    fn qualifies_a_record_name_with_its_module_path() {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let source = map.add_file("sales/user.npt", "");
        let name = interner.intern("User");
        let hir = HirModule {
            functions: Vec::new(),
            records: vec![HirRecord {
                id: ItemId(0),
                name,
                span: Span::dummy(),
                source,
                public: true,
                type_params: Vec::new(),
                fields: Vec::new(),
            }],
            variants: Vec::new(),
            other_items: Vec::new(),
        };
        let mut module_path_of = HashMap::new();
        module_path_of.insert(source, "sales.user".to_string());

        let registry = build(&hir, &module_path_of);
        assert_eq!(
            registry.qualified_name(ItemId(0), &interner),
            "sales.user.User"
        );
    }

    #[test]
    fn single_file_mode_has_no_module_path_prefix() {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let source = map.add_file("t.npt", "");
        let name = interner.intern("add");
        let hir = HirModule {
            functions: vec![HirFunction {
                id: ItemId(0),
                name,
                name_span: Span::dummy(),
                source,
                public: false,
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: None,
                uses: Vec::new(),
                raises: Vec::new(),
                body: crate::hir::HirBlock {
                    id: crate::hir::ExprId(0),
                    statements: Vec::new(),
                    tail: None,
                    span: Span::dummy(),
                },
                span: Span::dummy(),
            }],
            records: Vec::new(),
            variants: Vec::new(),
            other_items: Vec::new(),
        };
        let registry = build(&hir, &HashMap::new());
        assert_eq!(registry.qualified_name(ItemId(0), &interner), "add");
    }

    #[test]
    fn two_modules_declaring_the_same_name_qualify_differently() {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let sales_source = map.add_file("sales/user.npt", "");
        let admin_source = map.add_file("admin/user.npt", "");
        let name = interner.intern("User");
        let hir = HirModule {
            functions: Vec::new(),
            records: vec![
                HirRecord {
                    id: ItemId(0),
                    name,
                    span: Span::dummy(),
                    source: sales_source,
                    public: true,
                    type_params: Vec::new(),
                    fields: Vec::new(),
                },
                HirRecord {
                    id: ItemId(1),
                    name,
                    span: Span::dummy(),
                    source: admin_source,
                    public: true,
                    type_params: Vec::new(),
                    fields: Vec::new(),
                },
            ],
            variants: Vec::new(),
            other_items: Vec::new(),
        };
        let mut module_path_of = HashMap::new();
        module_path_of.insert(sales_source, "sales.user".to_string());
        module_path_of.insert(admin_source, "admin.user".to_string());

        let registry = build(&hir, &module_path_of);
        assert_ne!(
            registry.qualified_name(ItemId(0), &interner),
            registry.qualified_name(ItemId(1), &interner)
        );
        assert_eq!(
            registry.qualified_name(ItemId(0), &interner),
            "sales.user.User"
        );
        assert_eq!(
            registry.qualified_name(ItemId(1), &interner),
            "admin.user.User"
        );
    }

    #[test]
    fn a_variant_is_qualified_the_same_way_as_a_record() {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let source = map.add_file("shapes.npt", "");
        let name = interner.intern("Shape");
        let case_name = interner.intern("Circle");
        let hir = HirModule {
            functions: Vec::new(),
            records: Vec::new(),
            variants: vec![HirVariant {
                id: ItemId(0),
                name,
                span: Span::dummy(),
                source,
                public: true,
                type_params: Vec::new(),
                cases: vec![HirCase {
                    name: case_name,
                    span: Span::dummy(),
                    payload: Vec::new(),
                }],
            }],
            other_items: Vec::new(),
        };
        let mut module_path_of = HashMap::new();
        module_path_of.insert(source, "shapes".to_string());

        let registry = build(&hir, &module_path_of);
        assert_eq!(
            registry.qualified_name(ItemId(0), &interner),
            "shapes.Shape"
        );
    }

    #[test]
    fn an_unregistered_item_id_degrades_to_a_placeholder_not_a_panic() {
        let interner = Interner::new();
        let registry = ItemRegistry::default();
        assert_eq!(registry.qualified_name(ItemId(42), &interner), "<item #42>");
    }
}
