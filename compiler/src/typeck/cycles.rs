//! Detects infinitely-sized direct (or indirect) aggregate cycles.
//!
//! Napitia has no indirection/ownership feature yet
//! (`rfcs/0002-ownership-and-regions.md`), so every `record`/`variant`
//! is laid out as a flat, directly-nested value. A cycle in the
//! field/payload dependency graph -- `record Node { next: Node }`, or
//! the indirect `First -> Second -> First` -- would be an infinitely
//! sized type, so it is rejected here, once, before any function body
//! is checked.

use std::collections::HashMap;

use crate::diagnostics::Diagnostic;
use crate::hir::{HirModule, ItemId};
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
use crate::types::Ty;

const INFINITE_AGGREGATE_LAYOUT: &str = "T0020";

/// One declaration's outgoing edges: every other record/variant its
/// fields/payloads directly reference, in declaration order, alongside
/// the field/case name that introduced the edge (for the diagnostic's
/// containment path) and the span to point at.
struct Node {
    name: Symbol,
    span: Span,
    /// The declaring module -- a cycle spanning more than one module is
    /// structurally impossible (it would require a module import cycle,
    /// already rejected before typeck ever runs), so every node
    /// actually reached by a single cycle always shares one `source`;
    /// stored per-node anyway rather than threaded in from a single
    /// external parameter, so that guarantee is never load-bearing for
    /// correctness.
    source: SourceId,
    edges: Vec<Edge>,
}

struct Edge {
    to: ItemId,
    /// e.g. `next` (a field name) or `Cons.0` (a payload position).
    label: String,
    span: Span,
}

/// Checks every declared record/variant for a direct or indirect cycle
/// through its fields/payloads. `field_types`/`payload_types` are the
/// already-resolved `Ty` for each record's fields (in declaration
/// order) and each variant's case payloads (in declaration order) --
/// this pass only follows `Ty::Named` edges, so it does not need (and
/// must not need) the aggregate types to already be acyclic to resolve
/// them.
pub fn check_cycles(
    hir: &HirModule,
    field_types: &HashMap<ItemId, Vec<Ty>>,
    payload_types: &HashMap<ItemId, Vec<Vec<Ty>>>,
    interner: &Interner,
) -> Vec<Diagnostic> {
    // Traversal order is exactly declaration order (records first, then
    // variants, each in the `Vec` they were parsed into) -- never a
    // `HashMap`'s iteration order -- so the reported cycle is identical
    // across runs regardless of hashing.
    let mut order: Vec<ItemId> = Vec::new();
    let mut nodes: HashMap<ItemId, Node> = HashMap::new();

    for record in &hir.records {
        order.push(record.id);
        let types = field_types.get(&record.id).cloned().unwrap_or_default();
        let mut edges = Vec::new();
        for (field, ty) in record.fields.iter().zip(types.iter()) {
            if let Ty::Named(target, _) = ty {
                edges.push(Edge {
                    to: *target,
                    label: interner.resolve(field.name).to_string(),
                    span: field.span,
                });
            }
        }
        nodes.insert(
            record.id,
            Node {
                name: record.name,
                span: record.span,
                source: record.source,
                edges,
            },
        );
    }
    for variant in &hir.variants {
        order.push(variant.id);
        let case_types = payload_types.get(&variant.id).cloned().unwrap_or_default();
        let mut edges = Vec::new();
        for (case, payload) in variant.cases.iter().zip(case_types.iter()) {
            for (i, ty) in payload.iter().enumerate() {
                if let Ty::Named(target, _) = ty {
                    edges.push(Edge {
                        to: *target,
                        label: format!("{}.{}", interner.resolve(case.name), i),
                        span: case.span,
                    });
                }
            }
        }
        nodes.insert(
            variant.id,
            Node {
                name: variant.name,
                span: variant.span,
                source: variant.source,
                edges,
            },
        );
    }

    #[derive(Copy, Clone, PartialEq, Eq)]
    enum Color {
        White,
        Gray,
        Black,
    }

    let mut color: HashMap<ItemId, Color> = order.iter().map(|id| (*id, Color::White)).collect();
    let mut diagnostics = Vec::new();
    let mut reported: std::collections::HashSet<ItemId> = std::collections::HashSet::new();

    // Iterative DFS (an explicit stack, never native recursion) so a
    // pathologically long dependency chain cannot exhaust the Rust
    // call stack -- work is bounded by the number of edges actually
    // declared in the source.
    for &start in &order {
        if color[&start] != Color::White {
            continue;
        }
        // Each stack frame: the node being visited, and an index into
        // its edge list of which edge to try next.
        let mut stack: Vec<(ItemId, usize)> = vec![(start, 0)];
        color.insert(start, Color::Gray);
        let mut path: Vec<ItemId> = vec![start];

        while let Some((current, edge_idx)) = stack.pop() {
            let edges_len = nodes[&current].edges.len();
            if edge_idx >= edges_len {
                color.insert(current, Color::Black);
                path.pop();
                continue;
            }
            // Re-push the current frame with the next edge index before
            // descending, so control returns here after the child
            // finishes.
            stack.push((current, edge_idx + 1));
            let edge = &nodes[&current].edges[edge_idx];
            let target = edge.to;
            match color.get(&target).copied().unwrap_or(Color::Black) {
                Color::White => {
                    color.insert(target, Color::Gray);
                    path.push(target);
                    stack.push((target, 0));
                }
                Color::Gray => {
                    // Found a cycle: `target` is still on the current
                    // path. Report it once per distinct cycle entry
                    // point, using the path from `target`'s first
                    // occurrence back to itself.
                    if let Some(start_idx) = path.iter().position(|id| *id == target)
                        && reported.insert(target)
                    {
                        diagnostics.push(cycle_diagnostic(
                            &path[start_idx..],
                            &nodes,
                            edge,
                            interner,
                        ));
                    }
                }
                Color::Black => {}
            }
        }
    }

    diagnostics
}

fn cycle_diagnostic(
    cycle: &[ItemId],
    nodes: &HashMap<ItemId, Node>,
    closing_edge: &Edge,
    interner: &Interner,
) -> Diagnostic {
    let source = nodes[&cycle[0]].source;
    let mut path_text = String::new();
    for id in cycle {
        if !path_text.is_empty() {
            path_text.push_str(" -> ");
        }
        path_text.push_str(interner.resolve(nodes[id].name));
    }
    // The cycle always closes back to its own entry point (`cycle[0]`,
    // the same node `closing_edge` targets) -- never to whichever node
    // happened to be current when the closing edge was found, which for
    // an indirect cycle is a different, *later* node on the path (e.g.
    // `A -> B -> A` must render as exactly that, not `A -> B -> B`).
    path_text.push_str(" -> ");
    path_text.push_str(interner.resolve(nodes[&cycle[0]].name));

    let head_name = interner.resolve(nodes[&cycle[0]].name);
    let mut diag = Diagnostic::error(
        INFINITE_AGGREGATE_LAYOUT,
        source,
        closing_edge.span,
        format!(
            "`{head_name}` has an infinite layout: {path_text} (via `.{}`), and Napitia has no \
             indirection feature yet to break the cycle with",
            closing_edge.label
        ),
    )
    .with_primary_label("this field/payload closes the cycle");
    for id in cycle {
        let node = &nodes[id];
        let name = interner.resolve(node.name);
        diag = diag.with_label(node.span, format!("part of the cycle: `{name}`"));
    }
    diag
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::{HirCase, HirField, HirRecord, HirVariant};
    use crate::source::SourceMap;

    fn record(
        id: u32,
        name: Symbol,
        field_name: Symbol,
        field_ty: Ty,
        source: SourceId,
    ) -> (HirRecord, Ty) {
        (
            HirRecord {
                id: ItemId(id),
                name,
                span: Span::dummy(),
                source,
                public: true,
                fields: vec![HirField {
                    name: field_name,
                    span: Span::dummy(),
                    public: true,
                    ty: crate::syntax::ast::Type {
                        name: crate::syntax::ast::Ident {
                            symbol: name,
                            span: Span::dummy(),
                        },
                    },
                }],
            },
            field_ty,
        )
    }

    fn variant(
        id: u32,
        name: Symbol,
        case_name: Symbol,
        payload_ty: Ty,
        source: SourceId,
    ) -> (HirVariant, Ty) {
        (
            HirVariant {
                id: ItemId(id),
                name,
                span: Span::dummy(),
                source,
                public: true,
                cases: vec![HirCase {
                    name: case_name,
                    span: Span::dummy(),
                    payload: vec![crate::syntax::ast::Type {
                        name: crate::syntax::ast::Ident {
                            symbol: name,
                            span: Span::dummy(),
                        },
                    }],
                }],
            },
            payload_ty,
        )
    }

    /// Runs `check_cycles` over a hand-built module of records only,
    /// each `records[i]` having a single field of type `records[i +
    /// 1]` (wrapping around), so `check_cycles` never needs to resolve
    /// anything itself: `field_types`/`payload_types` are already
    /// exactly the `Ty::Named` edges this test wants to exist.
    fn check_record_cycle(names: &[&str]) -> (Vec<Diagnostic>, Vec<String>, Interner) {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let symbols: Vec<Symbol> = names.iter().map(|n| interner.intern(n)).collect();
        let mut records = Vec::new();
        let mut field_types = HashMap::new();
        for (i, &sym) in symbols.iter().enumerate() {
            let next = symbols[(i + 1) % symbols.len()];
            let next_id = ItemId((i as u32 + 1) % symbols.len() as u32);
            let (r, ty) = record(i as u32, sym, next, Ty::Named(next_id, next), source);
            field_types.insert(r.id, vec![ty]);
            records.push(r);
        }
        let hir = HirModule {
            functions: Vec::new(),
            records,
            variants: Vec::new(),
            other_items: Vec::new(),
        };
        let diagnostics = check_cycles(&hir, &field_types, &HashMap::new(), &interner);
        (
            diagnostics,
            names.iter().map(|s| s.to_string()).collect(),
            interner,
        )
    }

    #[test]
    fn direct_self_cycle_path_text_is_exact() {
        let (diags, _, _) = check_record_cycle(&["A"]);
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert!(diags[0].message.contains("A -> A"), "{}", diags[0].message);
    }

    #[test]
    fn two_node_indirect_cycle_path_text_is_exact() {
        let (diags, _, _) = check_record_cycle(&["A", "B"]);
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert!(
            diags[0].message.contains("A -> B -> A"),
            "{}",
            diags[0].message
        );
        assert!(
            !diags[0].message.contains("A -> B -> B"),
            "{}",
            diags[0].message
        );
    }

    #[test]
    fn three_node_indirect_cycle_path_text_is_exact() {
        let (diags, _, _) = check_record_cycle(&["A", "B", "C"]);
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert!(
            diags[0].message.contains("A -> B -> C -> A"),
            "{}",
            diags[0].message
        );
    }

    #[test]
    fn mixed_record_and_variant_cycle_path_text_is_exact() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let field_name = interner.intern("next");
        let case_name = interner.intern("X");
        let (record_a, record_ty) = record(0, a, field_name, Ty::Named(ItemId(1), b), source);
        let (variant_b, variant_ty) = variant(1, b, case_name, Ty::Named(ItemId(0), a), source);
        let mut field_types = HashMap::new();
        field_types.insert(record_a.id, vec![record_ty]);
        let mut payload_types = HashMap::new();
        payload_types.insert(variant_b.id, vec![vec![variant_ty]]);
        let hir = HirModule {
            functions: Vec::new(),
            records: vec![record_a],
            variants: vec![variant_b],
            other_items: Vec::new(),
        };
        let diagnostics = check_cycles(&hir, &field_types, &payload_types, &interner);
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics[0].message.contains("A -> B -> A"),
            "{}",
            diagnostics[0].message
        );
    }
}
