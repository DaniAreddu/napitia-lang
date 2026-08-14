# RFC 0002: Ownership and Regions

- Status: Accepted design direction. Not implemented in Alpha 0.1.

## Summary

Napitia manages memory through single ownership, move semantics, and
compiler-inferred lexical regions, instead of a mandatory garbage
collector or manual `malloc`/`free`. This RFC expands on the summary given
in `spec/0004-memory-model.md` with the reasoning behind the specific
mechanism chosen, and the open questions that block implementing it.

## Motivation

RFC 0001 commits Napitia to no mandatory GC and no undefined behavior in
safe code. Three known mechanisms satisfy both at once:

1. Tracing GC (Java) — rejected: mandatory by RFC 0001, and pause behavior
   conflicts with deterministic-destruction and predictable-performance
   goals.
2. Manual allocation (C) — rejected as the *default*: satisfies "no GC"
   but not "no undefined behavior in safe code"; use-after-free and
   double-free are exactly the bug class this RFC exists to design out.
3. Ownership + regions (Rust's borrow checker is the existing production
   proof of concept) — chosen, because it is the only one of the three
   that gets both properties simultaneously, at the cost of upfront
   compiler complexity instead of runtime cost.

Napitia diverges from Rust in emphasis, not in the core mechanism:
*regions are inferred by default*, with explicit annotation as a fallback
for the (expected rare) cases inference cannot resolve, rather than
requiring explicit lifetime annotations pervasively. Whether this is
achievable without either (a) rejecting valid programs Rust would accept,
or (b) silently degrading to a GC-like scheme for the cases inference
fails on, is the primary open question of this RFC.

## Design direction

### Ownership

Every value has exactly one owning binding. Passing, returning, or
assigning a value transfers ownership (a *move*) unless the value's type
is `Copy` (cheap to duplicate — the primitive types in `spec/0003` are
`Copy`; user types opt in explicitly, they are never `Copy` by default).
Using a binding after it has been moved from is a compile-time error.

### Regions

A region is a lexical scope that owns a set of allocations. A function
body's outermost scope is a region; nested blocks may introduce narrower
regions when the compiler can prove no value inside them escapes. When a
region ends, every allocation it owns is deterministically released, in
reverse order of creation (matching `defer` semantics in `spec/0004`).

Region inference is essentially escape analysis: a value escapes its
current region if it is returned, stored into a location that outlives
the region, or captured by something that itself escapes. Escaping values
get promoted to the nearest enclosing region that can prove ownership,
which in the worst case is the whole call's caller-provided region.

### Explicit shared ownership

When a value genuinely needs more than one simultaneous owner (a shared
cache entry, a graph node with multiple parents), the program must say so
explicitly via a library type analogous to `Rc`/`Arc`. The compiler never
infers multi-ownership on its own — if inference cannot prove single
ownership, that is a compile error asking the programmer to either
restructure the code or opt into shared ownership explicitly, not a
silent fallback to reference counting everywhere.

### `unsafe` and regions

Inside `unsafe`, code may hold a raw pointer that outlives the region the
compiler would otherwise infer for it (e.g. for FFI, where the callee
manages the pointer's lifetime). This is the *only* sanctioned way to
override region inference, and it is confined to the `unsafe` block —
callers of an `unsafe`-using function see only its ordinary, safe
signature.

## Unresolved research questions

This RFC is explicitly not a finished design. The following must be
resolved with a working prototype, not just a written decision, before
this becomes a spec:

- **Inference completeness**: how often real Napitia programs will hit
  cases the inference cannot resolve without an explicit `region`
  annotation, and whether the `region` keyword's surface syntax (reserved
  in `spec/0001`) is sufficient when that happens.
- **Interaction with structured concurrency**: a spawned concurrent task
  is a form of escape — it needs its own answer for what a task may
  legally borrow from its spawner's region versus what it must own
  outright, most likely resolved by a "task boundary" being a region
  boundary that requires owned (moved or `Copy`) captures only, but this
  has not been validated against real concurrent code patterns.
- **Aliasing rules for non-owning references**: this RFC describes
  ownership and region *lifetime*, not the borrow-checking rules for
  read-only vs. mutable non-owning references (Rust's `&T`/`&mut T`
  aliasing discipline). That is a related but distinct problem this RFC
  defers rather than folds in.
- **Error message quality**: region/ownership errors are historically
  where new users of ownership-based languages struggle most; no design
  work has started on making Napitia's diagnostics better than the
  state of the art here, only on the underlying mechanism.

## Non-goals

- This RFC does not propose a borrow-checker algorithm (e.g. a
  polonius-style analysis) — that is future work once the region model
  itself is validated.
- This RFC does not cover FFI ABI details; those belong with the FFI
  spec once one exists (see the top-level milestone description's mention
  of a stable C ABI as the first FFI target).
