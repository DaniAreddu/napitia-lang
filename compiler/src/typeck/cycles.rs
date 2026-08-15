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
    source: SourceId,
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
                            current,
                            edge,
                            source,
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
    closing_from: ItemId,
    closing_edge: &Edge,
    source: SourceId,
    interner: &Interner,
) -> Diagnostic {
    let mut path_text = String::new();
    for id in cycle {
        if !path_text.is_empty() {
            path_text.push_str(" -> ");
        }
        path_text.push_str(interner.resolve(nodes[id].name));
    }
    path_text.push_str(" -> ");
    path_text.push_str(interner.resolve(nodes[&closing_from].name));

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
