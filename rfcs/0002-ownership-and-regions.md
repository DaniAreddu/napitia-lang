# RFC 0002: Ownership and Regions

- Status: Accepted design direction. Not implemented in Alpha 0.1.

## Summary

Napitia manages memory through single ownership, inferred moves, and
compiler-inferred lexical regions, instead of a mandatory garbage
collector or manual `malloc`/`free`. This RFC expands on the summary given
in `spec/0004-memory-model.md` with the reasoning behind the specific
mechanism chosen, and the open questions that block implementing it.

The vocabulary here (`owned`, `borrow`, `shared`, `region`) is the
provisional set from `rfcs/0004-language-independence.md`, and the
defining design goal is that ordinary programs never write it: the
programmer states ownership *intent* only where a boundary requires it,
and the compiler infers storage, moves, escape behavior, and region
membership everywhere else. This is a stronger claim than "inference
helps sometimes" — it is the thing this RFC is actually trying to prove
is achievable, not an assumed given.

## Motivation

RFC 0001 commits Napitia to no mandatory GC and no undefined behavior in
safe code. Three known mechanisms satisfy both at once:

1. Tracing GC (Java) — rejected: mandatory by RFC 0001, and pause behavior
   conflicts with deterministic-destruction and predictable-performance
   goals.
2. Manual allocation (C) — rejected as the *default*: satisfies "no GC"
   but not "no undefined behavior in safe code"; use-after-free and
   double-free are exactly the bug class this RFC exists to design out.
3. Ownership + regions — chosen, because it is the only one of the three
   that gets both properties simultaneously, at the cost of upfront
   compiler complexity instead of runtime cost. Rust's borrow checker is
   the existing evidence that a variant of this mechanism can work in
   production; it is cited here as evidence the property is achievable at
   all, not as the mechanism Napitia adopts wholesale (`rfcs/0004`).

Napitia's specific bet, not shared with Rust's design center, is that
regions and ownership transfer should be inferred by default in ordinary
code, with explicit `owned`/`borrow`/`shared`/`region` annotation reserved
for API boundaries and the cases inference genuinely cannot resolve —
rather than a model where the programmer routinely writes ownership and
lifetime information by hand. Whether this is achievable without either
(a) rejecting programs a hand-annotated model would accept, or (b)
silently degrading to a GC-like scheme for the cases inference fails on,
is the primary open question of this RFC.

## Design direction

### Ownership

Every value has exactly one owning binding. Passing, returning, or
assigning a value transfers ownership (a move) unless the value's type is
marked trivially duplicable (the primitive types in `spec/0003` are;
user-defined types opt in explicitly and are never trivially duplicable
by default). Using a binding after it has been moved from is a
compile-time error. Whether a use is a move or a duplication is inferred
from the value's type and the surrounding code — there is no keyword the
programmer writes at the use site to request one or the other.

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

### Explicit shared ownership (`shared`)

When a value genuinely needs more than one simultaneous owner (a shared
cache entry, a graph node with multiple parents), the program must say so
explicitly via the `shared` boundary annotation (or a library type built
on it). The compiler never infers multi-ownership on its own — if
inference cannot prove single ownership, that is a compile error asking
the programmer to either restructure the code or opt into shared
ownership explicitly, not a silent fallback to reference counting
everywhere. The compiler, not the programmer, chooses the concrete
mechanism (e.g. runtime reference counting) behind `shared` — the
annotation states intent, not implementation.

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
  legally `borrow` from its spawner's region versus what it must `own`
  outright, most likely resolved by a "task boundary" being a region
  boundary that requires owned (moved or trivially-duplicable) captures
  only, but this has not been validated against real concurrent code
  patterns.
- **Aliasing rules for `borrow`**: this RFC describes ownership and region
  *lifetime*, not the discipline governing read-only vs. mutable
  non-owning (`borrow`) access — whether multiple simultaneous borrows of
  the same value are ever restricted, and by what rule. Napitia needs its
  own answer to the problem Rust's `&`/`&mut` aliasing rules solve; this
  RFC defers that problem rather than folding it in, and does not assume
  Rust's answer is the right one to adapt.
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
