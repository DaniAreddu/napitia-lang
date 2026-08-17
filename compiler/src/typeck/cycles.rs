//! Detects infinitely-sized direct (or indirect) aggregate cycles.
//!
//! Napitia has no indirection/ownership feature yet
//! (`rfcs/0002-ownership-and-regions.md`), so every `record`/`variant`
//! is laid out as a flat, directly-nested value. A cycle in the
//! field/payload dependency graph -- `record Node { next: Node }`, or
//! the indirect `First -> Second -> First` -- would be an infinitely
//! sized type, so it is rejected here, once, before any function body
//! is checked.

use std::collections::{HashMap, HashSet};

use crate::diagnostics::Diagnostic;
use crate::hir::{HirModule, ItemId, TypeParamId};
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
use crate::types::Ty;
use crate::types::generics::{GenericInstanceKey, substitute};

const INFINITE_AGGREGATE_LAYOUT: &str = "T0020";

/// One declaration's own (unsubstituted) shape: its declared type
/// parameters (in declaration order, with their display names) and the
/// declared type of every field/payload position, alongside the
/// field/case label and span to use if that edge ever turns out to
/// close a cycle. Never itself concrete for a generic declaration --
/// `substitute_edges` is what turns this into one instantiation's
/// actual outgoing edges.
struct Decl {
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
    type_params: Vec<(TypeParamId, Symbol)>,
    fields: Vec<(Ty, String, Span)>,
}

/// This declaration's own type parameters, applied to themselves
/// (`Ty::Param(id, name)` for each) -- the "generic self" instance every
/// declaration's own traversal starts from, so a self-referential
/// generic layout (`Node[T] { next: Node[T] }`) closes back to its own
/// starting instance exactly like a non-generic self-cycle does, and a
/// declaration whose *own* body is not recursive (`Box[T] { value: T }`)
/// correctly contributes no edges of its own until some other, concrete
/// instantiation substitutes a real cycle into it.
fn symbolic_self(decl_id: ItemId, decl: &Decl) -> GenericInstanceKey {
    GenericInstanceKey::new(
        decl_id,
        decl.type_params
            .iter()
            .map(|(id, name)| Ty::Param(*id, *name))
            .collect(),
    )
}

/// The outgoing edges of one concrete instance: each of `decl`'s own
/// field/payload types, with `instance`'s own arguments substituted for
/// `decl`'s type parameters, then reduced to the target instance the
/// substituted type refers to (a bare declaration for a `Ty::Named`
/// target, or another applied instance for a `Ty::Applied` one). A
/// substituted type that resolves to neither (a primitive, a still-bare
/// `Ty::Param` because `instance`'s own arguments didn't cover it, ...)
/// introduces no edge, matching how such a field can never itself be the
/// source of an infinite layout.
fn substitute_edges(
    instance: &GenericInstanceKey,
    decls: &HashMap<ItemId, Decl>,
) -> Vec<(GenericInstanceKey, String, Span)> {
    let Some(decl) = decls.get(&instance.declaration) else {
        return Vec::new();
    };
    let subst: HashMap<TypeParamId, Ty> = decl
        .type_params
        .iter()
        .map(|(id, _)| *id)
        .zip(instance.arguments.iter().cloned())
        .collect();
    let mut edges = Vec::new();
    for (ty, label, span) in &decl.fields {
        let substituted = substitute(ty, &subst);
        let target = match substituted {
            Ty::Named(target, _) => Some(GenericInstanceKey::new(target, Vec::new())),
            Ty::Applied(target, args) => Some(GenericInstanceKey::new(target, args)),
            _ => None,
        };
        if let Some(target) = target {
            edges.push((target, label.clone(), *span));
        }
    }
    edges
}

/// Checks every declared record/variant for a direct or indirect cycle
/// through its fields/payloads. `field_types`/`payload_types` are the
/// already-resolved `Ty` for each record's fields (in declaration
/// order) and each variant's case payloads (in declaration order).
///
/// A cycle is detected *after* substituting the concrete type arguments
/// flowing through each edge, not just by following an applied type's
/// bare declaration -- `record Box[T] { value: T }` alone is not
/// infinite, but `record Node { next: Box[Node] }` is (`Node` ->
/// `Box[Node]`'s own `value` field, substituted, is `Node` again),
/// which a declaration-only graph can never see since `Box`'s own field
/// is just `T` until something concrete flows through it (`rfcs/0008`).
/// Traversal is over these substituted *instances*
/// (`GenericInstanceKey`s), not bare declarations, so the same
/// declaration instantiated two different ways is correctly treated as
/// two different graph nodes.
///
/// A layout that never repeats an *exact* instance but keeps
/// substituting a growing argument instead (`record Wrap[T] { inner:
/// Wrap[Box[T]] }`) is exactly as unlayoutable as a literal cycle, and is
/// caught the same structural way, immediately: a *declaration*
/// (`ItemId`, regardless of its own current arguments) reappearing
/// anywhere on the active traversal path is itself the proof of an
/// infinite layout -- `Wrap` reappears the moment its own first field is
/// substituted, at the very first step, long before any numeric bound
/// would matter. This is deliberately not a depth/length limit on the
/// path itself: a long but genuinely finite chain of distinct
/// declarations (`A -> B -> C -> ... -> i64`) never revisits any one
/// declaration and must be accepted no matter how many distinct
/// declarations it passes through -- `MAX_GENERIC_DEPTH` bounds nested
/// type *application* syntax/substitution depth, not the number of
/// aggregate declarations a containment graph may legitimately contain.
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
    let mut decls: HashMap<ItemId, Decl> = HashMap::new();

    for record in &hir.records {
        order.push(record.id);
        let types = field_types.get(&record.id).cloned().unwrap_or_default();
        let fields = record
            .fields
            .iter()
            .zip(types.iter())
            .map(|(field, ty)| {
                (
                    ty.clone(),
                    interner.resolve(field.name).to_string(),
                    field.span,
                )
            })
            .collect();
        decls.insert(
            record.id,
            Decl {
                name: record.name,
                span: record.span,
                source: record.source,
                type_params: record.type_params.iter().map(|p| (p.id, p.name)).collect(),
                fields,
            },
        );
    }
    for variant in &hir.variants {
        order.push(variant.id);
        let case_types = payload_types.get(&variant.id).cloned().unwrap_or_default();
        let mut fields = Vec::new();
        for (case, payload) in variant.cases.iter().zip(case_types.iter()) {
            for (i, ty) in payload.iter().enumerate() {
                fields.push((
                    ty.clone(),
                    format!("{}.{}", interner.resolve(case.name), i),
                    case.span,
                ));
            }
        }
        decls.insert(
            variant.id,
            Decl {
                name: variant.name,
                span: variant.span,
                source: variant.source,
                type_params: variant.type_params.iter().map(|p| (p.id, p.name)).collect(),
                fields,
            },
        );
    }

    #[derive(Copy, Clone, PartialEq, Eq)]
    enum Color {
        White,
        Gray,
        Black,
    }

    let mut color: HashMap<GenericInstanceKey, Color> = HashMap::new();
    let mut diagnostics = Vec::new();
    // Dedup key: the declaration whose own recurrence closed a reported
    // cycle -- so the same underlying problem reached from more than one
    // starting point is reported once, not once per entry point.
    let mut reported: HashSet<ItemId> = HashSet::new();

    // Iterative DFS (an explicit stack, never native recursion) so a
    // pathologically long dependency chain cannot exhaust the Rust call
    // stack. Work is bounded by the number of distinct instances actually
    // reachable, which is finite for every genuinely non-infinite layout
    // -- see `path.iter().any` below, which is what actually proves that,
    // not any numeric depth limit.
    for &start in &order {
        let start_key = symbolic_self(start, &decls[&start]);
        if color.get(&start_key).copied().unwrap_or(Color::White) != Color::White {
            continue;
        }
        color.insert(start_key.clone(), Color::Gray);
        let mut path: Vec<GenericInstanceKey> = vec![start_key.clone()];
        // The (label, span) of the edge that pushed `path[i]` onto the
        // path, parallel to `path` itself -- `incoming[0]` is never read
        // (the very first element of a whole traversal has no incoming
        // edge of its own), kept only so every other index lines up.
        // Needed to reconstruct the *correct* closing edge after
        // canonicalizing which member of a cycle is displayed first
        // (below): that rotation can pick a different pair of adjacent
        // members to call "the closing edge" than whichever one the
        // traversal itself happened to close on.
        let mut incoming: Vec<(String, Span)> = vec![(String::new(), Span::dummy())];
        let mut edges_stack: Vec<Vec<(GenericInstanceKey, String, Span)>> =
            vec![substitute_edges(&start_key, &decls)];
        let mut idx_stack: Vec<usize> = vec![0];

        while let Some(current) = path.last().cloned() {
            let idx = *idx_stack
                .last()
                .expect("path and idx_stack stay in lockstep");
            let edges = edges_stack
                .last()
                .expect("path and edges_stack stay in lockstep");
            if idx >= edges.len() {
                color.insert(current, Color::Black);
                path.pop();
                incoming.pop();
                edges_stack.pop();
                idx_stack.pop();
                continue;
            }
            let (target, label, span) = edges[idx].clone();
            *idx_stack.last_mut().unwrap() += 1;

            // A *declaration* (regardless of its own current type
            // arguments) reappearing anywhere on the currently-active
            // path is itself the proof of an infinite layout: Napitia has
            // no indirection to break the recurrence with, so reaching
            // the same declaration again while still in the middle of
            // laying it out once already -- whether via the exact same
            // instantiation (`Node` closing back to `Node`) or a
            // different, even strictly larger one (`Wrap[T]` closing back
            // to `Wrap[Box[T]]`) -- is infinite either way. Checked before
            // any instance-level memoization, so this never depends on
            // how deep the path happens to be.
            if let Some(start_idx) = path
                .iter()
                .position(|k| k.declaration == target.declaration)
            {
                if reported.insert(target.declaration) {
                    let cycle_slice = &path[start_idx..];
                    // The same cyclic sequence of declarations can be
                    // entered at any one of its own members, depending
                    // purely on which declaration the outer traversal
                    // happened to visit first (declaration order) --
                    // rotated here to a canonical starting point (the
                    // member with the smallest `ItemId`) so the reported
                    // cycle never depends on that traversal order.
                    let rotate = cycle_slice
                        .iter()
                        .enumerate()
                        .min_by_key(|(_, k)| k.declaration.0)
                        .map(|(i, _)| i)
                        .unwrap_or(0);
                    let mut rotated: Vec<GenericInstanceKey> = cycle_slice[rotate..].to_vec();
                    rotated.extend_from_slice(&cycle_slice[..rotate]);
                    // The edge that closes the (rotated) cycle back to
                    // its own new starting point is the original closing
                    // edge only when no rotation happened; otherwise it
                    // is the edge that originally pushed
                    // `cycle_slice[rotate]` onto the path -- a real edge
                    // already traversed, just not the one the DFS itself
                    // happened to detect the closure on.
                    let (closing_target, closing_label, closing_span) = if rotate == 0 {
                        (target.clone(), label.clone(), span)
                    } else {
                        let (l, s) = incoming[start_idx + rotate].clone();
                        (cycle_slice[rotate].clone(), l, s)
                    };
                    diagnostics.push(cycle_diagnostic(
                        &rotated,
                        &closing_target,
                        &decls,
                        &closing_label,
                        closing_span,
                        interner,
                    ));
                }
                continue;
            }

            match color.get(&target).copied().unwrap_or(Color::White) {
                Color::White => {
                    color.insert(target.clone(), Color::Gray);
                    edges_stack.push(substitute_edges(&target, &decls));
                    idx_stack.push(0);
                    incoming.push((label, span));
                    path.push(target);
                }
                // Already fully explored (from this start or an earlier
                // one) and proven finite -- never re-walked.
                Color::Black => {}
                // Only reachable if `target`'s exact instance is Gray
                // without its declaration already having matched above,
                // which cannot happen (an instance's declaration is
                // always itself on the path whenever that instance is
                // Gray) -- kept only so this match stays exhaustive.
                Color::Gray => {}
            }
        }
    }

    diagnostics
}

/// Renders one instance (a declaration plus its own concrete arguments,
/// if any) the way a cycle's path text names each of its steps --
/// `Node`, or `Box[Node]`, or a nested `Wrap[Box[Node]]`.
fn instance_display(
    key: &GenericInstanceKey,
    decls: &HashMap<ItemId, Decl>,
    interner: &Interner,
) -> String {
    let name = decls
        .get(&key.declaration)
        .map(|d| interner.resolve(d.name))
        .unwrap_or("?");
    if key.arguments.is_empty() {
        return name.to_string();
    }
    let parts: Vec<String> = key
        .arguments
        .iter()
        .map(|a| arg_display(a, decls, interner))
        .collect();
    format!("{name}[{}]", parts.join(", "))
}

/// Like [`instance_display`], but for one type argument found *inside*
/// an instance's own argument list (which is a plain `Ty`, not
/// necessarily a `GenericInstanceKey` -- it may be a primitive, a bare
/// named type, or another nested application).
fn arg_display(ty: &Ty, decls: &HashMap<ItemId, Decl>, interner: &Interner) -> String {
    match ty {
        Ty::Named(item, sym) => decls
            .get(item)
            .map(|d| interner.resolve(d.name).to_string())
            .unwrap_or_else(|| interner.resolve(*sym).to_string()),
        Ty::Applied(item, args) => instance_display(
            &GenericInstanceKey::new(*item, args.clone()),
            decls,
            interner,
        ),
        Ty::Param(_, name) => interner.resolve(*name).to_string(),
        other => crate::types::display_ty(other, interner),
    }
}

/// `cycle` is the path from a declaration's first occurrence through to
/// (but not including) the edge that re-reaches that same declaration;
/// `target` is the instance that closing edge actually reaches -- the
/// same declaration `cycle[0]` names, but not necessarily the exact same
/// arguments (`Wrap[T]` closing back to `Wrap[Box[T]]`, say), so it is
/// rendered separately rather than assumed identical to `cycle[0]`.
fn cycle_diagnostic(
    cycle: &[GenericInstanceKey],
    target: &GenericInstanceKey,
    decls: &HashMap<ItemId, Decl>,
    closing_label: &str,
    closing_span: Span,
    interner: &Interner,
) -> Diagnostic {
    let source = decls[&cycle[0].declaration].source;
    let mut path_text = String::new();
    for key in cycle {
        if !path_text.is_empty() {
            path_text.push_str(" -> ");
        }
        path_text.push_str(&instance_display(key, decls, interner));
    }
    // The cycle closes back to the same *declaration* it started from
    // (`cycle[0].declaration`), which for an indirect cycle is a
    // different, *later* step's own declaration on the path than
    // whichever one was current when the closing edge was found (e.g.
    // `A -> B -> A` must render as exactly that, not `A -> B -> B`) --
    // and, for a recurrence through a generic declaration instantiated
    // differently each time, may show different arguments here than
    // `cycle[0]`'s own (`Wrap[T] -> Wrap[Box[T]]`, not `Wrap[T] ->
    // Wrap[T]`), since `target` is what the closing edge actually
    // reaches, not a repeat of the starting instance's own arguments.
    path_text.push_str(" -> ");
    path_text.push_str(&instance_display(target, decls, interner));

    let head_name = interner.resolve(decls[&cycle[0].declaration].name);
    let mut diag = Diagnostic::error(
        INFINITE_AGGREGATE_LAYOUT,
        source,
        closing_span,
        format!(
            "`{head_name}` has an infinite layout: {path_text} (via `.{closing_label}`), and \
             Napitia has no indirection feature yet to break the cycle with"
        ),
    )
    .with_primary_label("this field/payload closes the cycle");
    for key in cycle {
        let decl = &decls[&key.declaration];
        diag = diag.with_label(
            decl.span,
            format!(
                "part of the cycle: `{}`",
                instance_display(key, decls, interner)
            ),
        );
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
                type_params: Vec::new(),
                fields: vec![HirField {
                    name: field_name,
                    span: Span::dummy(),
                    public: true,
                    ty: crate::hir::HirType::Unresolved {
                        name,
                        span: Span::dummy(),
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
                type_params: Vec::new(),
                cases: vec![HirCase {
                    name: case_name,
                    span: Span::dummy(),
                    payload: vec![crate::hir::HirType::Unresolved {
                        name,
                        span: Span::dummy(),
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

    /// 128 distinct records, each pointing to the next, terminating in
    /// `i64` -- must be accepted no matter how many distinct
    /// declarations it passes through. `MAX_GENERIC_DEPTH` bounds nested
    /// type-application syntax/substitution depth; it is not, and must
    /// never be conflated with, a maximum number of aggregate
    /// declarations in a containment graph.
    #[test]
    fn a_long_finite_chain_of_distinct_records_is_accepted() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let count = 128usize;
        let names: Vec<Symbol> = (0..count)
            .map(|i| interner.intern(&format!("Chain{i}")))
            .collect();
        let mut records = Vec::new();
        let mut field_types = HashMap::new();
        for i in 0..count {
            let field_ty = if i + 1 < count {
                Ty::Named(ItemId((i + 1) as u32), names[i + 1])
            } else {
                Ty::I64
            };
            let (r, ty) = record(i as u32, names[i], names[i], field_ty, source);
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
        assert!(
            diagnostics.is_empty(),
            "a long but finite chain must not be reported as infinite: {diagnostics:?}"
        );
    }

    #[test]
    fn reversed_declaration_order_does_not_change_the_reported_cycle() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let c = interner.intern("C");
        // Deliberately distinct field names per edge (not all "next") --
        // this is what actually exercises reconstructing the *correct*
        // closing edge's own label after canonicalizing which member of
        // the cycle is displayed first, rather than trivially passing
        // because every edge happens to share one name.
        let to_b = interner.intern("to_b");
        let to_c = interner.intern("to_c");
        let to_a = interner.intern("to_a");
        let (record_a, ty_a) = record(0, a, to_b, Ty::Named(ItemId(1), b), source);
        let (record_b, ty_b) = record(1, b, to_c, Ty::Named(ItemId(2), c), source);
        let (record_c, ty_c) = record(2, c, to_a, Ty::Named(ItemId(0), a), source);
        let mut field_types = HashMap::new();
        field_types.insert(record_a.id, vec![ty_a]);
        field_types.insert(record_b.id, vec![ty_b]);
        field_types.insert(record_c.id, vec![ty_c]);

        let forward = HirModule {
            functions: Vec::new(),
            records: vec![record_a.clone(), record_b.clone(), record_c.clone()],
            variants: Vec::new(),
            other_items: Vec::new(),
        };
        let reversed = HirModule {
            functions: Vec::new(),
            records: vec![record_c, record_b, record_a],
            variants: Vec::new(),
            other_items: Vec::new(),
        };
        let forward_diags = check_cycles(&forward, &field_types, &HashMap::new(), &interner);
        let reversed_diags = check_cycles(&reversed, &field_types, &HashMap::new(), &interner);
        assert_eq!(
            forward_diags.len(),
            1,
            "unexpected diagnostics: {forward_diags:?}"
        );
        assert_eq!(
            reversed_diags.len(),
            1,
            "unexpected diagnostics: {reversed_diags:?}"
        );
        assert_eq!(forward_diags[0].message, reversed_diags[0].message);
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

    /// A generic record with `type_params` (a single `T`) and one field
    /// of `field_ty` -- unlike `record`, this lets a test build a
    /// `Box[T] { payload: T }`-shaped declaration directly.
    fn generic_record(
        id: u32,
        name: Symbol,
        type_param: TypeParamId,
        type_param_name: Symbol,
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
                type_params: vec![crate::hir::HirTypeParam {
                    id: type_param,
                    name: type_param_name,
                    span: Span::dummy(),
                }],
                fields: vec![HirField {
                    name: field_name,
                    span: Span::dummy(),
                    public: true,
                    ty: crate::hir::HirType::Unresolved {
                        name,
                        span: Span::dummy(),
                    },
                }],
            },
            field_ty,
        )
    }

    /// Like `generic_record`, but a variant with a single `T`-headed
    /// case (`List[T] { Cons(T, List[T]) }`-shaped), with a caller-
    /// supplied list of payload types for that one case.
    fn generic_variant(
        id: u32,
        name: Symbol,
        type_param: TypeParamId,
        type_param_name: Symbol,
        case_name: Symbol,
        payload: Vec<Ty>,
        source: SourceId,
    ) -> (HirVariant, Vec<Ty>) {
        let payload_len = payload.len();
        (
            HirVariant {
                id: ItemId(id),
                name,
                span: Span::dummy(),
                source,
                public: true,
                type_params: vec![crate::hir::HirTypeParam {
                    id: type_param,
                    name: type_param_name,
                    span: Span::dummy(),
                }],
                cases: vec![HirCase {
                    name: case_name,
                    span: Span::dummy(),
                    payload: (0..payload_len)
                        .map(|_| crate::hir::HirType::Unresolved {
                            name,
                            span: Span::dummy(),
                        })
                        .collect(),
                }],
            },
            payload,
        )
    }

    /// `record Box[T] { payload: T } record Node { next: Box[Node] }` --
    /// the parameter-mediated case a declaration-only (head-only) cycle
    /// graph cannot see: `Box`'s own field is just `T`, and only becomes
    /// `Node` again once `Node`'s own concrete field substitutes it in.
    #[test]
    fn parameter_mediated_cycle_through_a_generic_record_is_detected() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let node = interner.intern("Node");
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        let next = interner.intern("next");
        let payload = interner.intern("payload");
        let box_id = ItemId(1);
        let node_id = ItemId(0);

        let (node_record, node_field_ty) = record(
            0,
            node,
            next,
            Ty::Applied(box_id, vec![Ty::Named(node_id, node)]),
            source,
        );
        let (box_record, box_field_ty) = generic_record(
            1,
            boxed,
            TypeParamId(0),
            t,
            payload,
            Ty::Param(TypeParamId(0), t),
            source,
        );

        let mut field_types = HashMap::new();
        field_types.insert(node_record.id, vec![node_field_ty]);
        field_types.insert(box_record.id, vec![box_field_ty]);
        let hir = HirModule {
            functions: Vec::new(),
            records: vec![node_record, box_record],
            variants: Vec::new(),
            other_items: Vec::new(),
        };
        let diagnostics = check_cycles(&hir, &field_types, &HashMap::new(), &interner);
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics[0].message.contains("Node -> Box[Node] -> Node"),
            "{}",
            diagnostics[0].message
        );
    }

    /// `record Box[T] { payload: T }` alone: `T` is never itself an
    /// applied/named type, so this declaration contributes no edges of
    /// its own and must not be flagged -- only instantiating it with
    /// something that recurs back (covered above) is infinite.
    #[test]
    fn a_generic_record_with_no_self_reference_has_no_diagnostics() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        let payload = interner.intern("payload");
        let (box_record, box_field_ty) = generic_record(
            0,
            boxed,
            TypeParamId(0),
            t,
            payload,
            Ty::Param(TypeParamId(0), t),
            source,
        );
        let mut field_types = HashMap::new();
        field_types.insert(box_record.id, vec![box_field_ty]);
        let hir = HirModule {
            functions: Vec::new(),
            records: vec![box_record],
            variants: Vec::new(),
            other_items: Vec::new(),
        };
        let diagnostics = check_cycles(&hir, &field_types, &HashMap::new(), &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    /// `record Outer[T] { inner: Box[T] } record Box[T] { payload: T }`
    /// -- a nested application through two distinct generic declarations
    /// with no recursion at all, which must remain accepted.
    #[test]
    fn nested_generic_application_with_no_cycle_has_no_diagnostics() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let outer = interner.intern("Outer");
        let boxed = interner.intern("Box");
        let t_outer = interner.intern("T");
        let t_box = interner.intern("T");
        let inner = interner.intern("inner");
        let payload = interner.intern("payload");
        let box_id = ItemId(1);

        let (outer_record, outer_field_ty) = generic_record(
            0,
            outer,
            TypeParamId(0),
            t_outer,
            inner,
            Ty::Applied(box_id, vec![Ty::Param(TypeParamId(0), t_outer)]),
            source,
        );
        let (box_record, box_field_ty) = generic_record(
            1,
            boxed,
            TypeParamId(1),
            t_box,
            payload,
            Ty::Param(TypeParamId(1), t_box),
            source,
        );
        let mut field_types = HashMap::new();
        field_types.insert(outer_record.id, vec![outer_field_ty]);
        field_types.insert(box_record.id, vec![box_field_ty]);
        let hir = HirModule {
            functions: Vec::new(),
            records: vec![outer_record, box_record],
            variants: Vec::new(),
            other_items: Vec::new(),
        };
        let diagnostics = check_cycles(&hir, &field_types, &HashMap::new(), &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    /// `record Node[T] { next: Node[T] }` -- the head-only case the
    /// original, declaration-only graph already caught; still must be
    /// caught by the substitution-aware traversal that replaced it.
    #[test]
    fn self_referential_generic_record_is_still_detected() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let node = interner.intern("Node");
        let t = interner.intern("T");
        let next = interner.intern("next");
        let node_id = ItemId(0);
        let (node_record, field_ty) = generic_record(
            0,
            node,
            TypeParamId(0),
            t,
            next,
            Ty::Applied(node_id, vec![Ty::Param(TypeParamId(0), t)]),
            source,
        );
        let mut field_types = HashMap::new();
        field_types.insert(node_record.id, vec![field_ty]);
        let hir = HirModule {
            functions: Vec::new(),
            records: vec![node_record],
            variants: Vec::new(),
            other_items: Vec::new(),
        };
        let diagnostics = check_cycles(&hir, &field_types, &HashMap::new(), &interner);
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics[0].message.contains("Node[T] -> Node[T]"),
            "{}",
            diagnostics[0].message
        );
    }

    /// `variant List[T] { Cons(T, List[T]) }` -- the generic-variant
    /// analog of the record self-cycle above.
    #[test]
    fn self_referential_generic_variant_is_detected() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let list = interner.intern("List");
        let t = interner.intern("T");
        let cons = interner.intern("Cons");
        let list_id = ItemId(0);
        let (list_variant, payload) = generic_variant(
            0,
            list,
            TypeParamId(0),
            t,
            cons,
            vec![
                Ty::Param(TypeParamId(0), t),
                Ty::Applied(list_id, vec![Ty::Param(TypeParamId(0), t)]),
            ],
            source,
        );
        let mut payload_types = HashMap::new();
        payload_types.insert(list_variant.id, vec![payload]);
        let hir = HirModule {
            functions: Vec::new(),
            records: Vec::new(),
            variants: vec![list_variant],
            other_items: Vec::new(),
        };
        let diagnostics = check_cycles(&hir, &HashMap::new(), &payload_types, &interner);
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics[0].message.contains("List[T] -> List[T]"),
            "{}",
            diagnostics[0].message
        );
    }

    /// `record Wrap[T] { inner: Wrap[Box[T]] } record Box[T] { payload: T }`
    /// -- every *instance* along this path is distinct (`Wrap[T]`,
    /// `Wrap[Box[T]]`, `Wrap[Box[Box[T]]]`, ...), so a literal-instance-
    /// repeat check alone would recurse forever; detected immediately
    /// instead, at the very first re-visit, because `Wrap` (the
    /// *declaration*, regardless of its own arguments) reappears on the
    /// active path right away -- never a depth budget, and never
    /// recursing anywhere near one.
    #[test]
    fn expanding_generic_substitution_is_detected_immediately_not_via_a_depth_budget() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let wrap = interner.intern("Wrap");
        let boxed = interner.intern("Box");
        let t_wrap = interner.intern("T");
        let t_box = interner.intern("T");
        let inner = interner.intern("inner");
        let payload = interner.intern("payload");
        let wrap_id = ItemId(0);
        let box_id = ItemId(1);

        let (wrap_record, wrap_field_ty) = generic_record(
            0,
            wrap,
            TypeParamId(0),
            t_wrap,
            inner,
            Ty::Applied(
                wrap_id,
                vec![Ty::Applied(box_id, vec![Ty::Param(TypeParamId(0), t_wrap)])],
            ),
            source,
        );
        let (box_record, box_field_ty) = generic_record(
            1,
            boxed,
            TypeParamId(1),
            t_box,
            payload,
            Ty::Param(TypeParamId(1), t_box),
            source,
        );
        let mut field_types = HashMap::new();
        field_types.insert(wrap_record.id, vec![wrap_field_ty]);
        field_types.insert(box_record.id, vec![box_field_ty]);
        let hir = HirModule {
            functions: Vec::new(),
            records: vec![wrap_record, box_record],
            variants: Vec::new(),
            other_items: Vec::new(),
        };
        let diagnostics = check_cycles(&hir, &field_types, &HashMap::new(), &interner);
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics[0].message.contains("Wrap[T] -> Wrap[Box[T]]"),
            "{}",
            diagnostics[0].message
        );
    }
}
