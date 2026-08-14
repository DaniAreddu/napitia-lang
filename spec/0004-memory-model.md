# Spec 0004: Memory Model

- Status: Design direction only. Not implemented in Alpha 0.1.

Alpha 0.1 has no `unsafe` blocks, no pointers, no references, and no
ownership enforcement — the NIR interpreter executes only primitive values
and stack-local storage. This spec exists so later milestones build
ownership/regions against a written-down design rather than an ad hoc one,
and so nothing here is mistaken for already being enforced by the
compiler.

## Implemented features

- **Local storage in NIR**: NIR functions have named local slots
  (`spec/0006-napitia-ir.md`) that are simple value storage with no
  ownership metadata attached yet. This is the only "memory model" that
  actually exists in the current compiler.

## Accepted design direction

### Value semantics by default

Assignment, passing an argument, and returning a value all conceptually
*move or copy* the value, matching the source binding's declared
ownership — never an implicit shared, mutable alias. Types that are cheap
to duplicate (primitives) copy; larger/owning types move. There is no
implicit reference-counting inserted by the compiler.

### Ownership and move semantics

Every value has exactly one owning binding at a time. Moving a value out
of a binding (e.g. passing it to a function that takes ownership)
invalidates the source binding for further use; using a moved-from binding
is a compile-time error, not a runtime one. Immutable bindings (`let`) may
still be moved from; move and mutability are independent axes.

### Compiler-inferred memory regions

Instead of requiring every allocation to be either garbage-collected or
manually paired with a matching free, Napitia infers *regions*: lexical
scopes that own a set of allocations and release them deterministically
when the region ends. A function's stack frame is the simplest region.
Escape analysis determines when a value's region must be widened
(returned to a caller) versus when it can stay local. This is the
mechanism intended to deliver "no mandatory garbage collector" without
pushing manual memory management onto every piece of code the way raw
`malloc`/`free` does in C.

### Deterministic destruction

A value's destructor (if it has cleanup behavior) runs at a
statically-determined point — end of its owning region, or an explicit
`drop` — never at an unpredictable time chosen by a collector. This is
required for the language to be usable for resource management (files,
sockets, locks) without a separate `try/finally`-shaped idiom.

### Explicit shared ownership

When more than one owner is genuinely required, it must be requested
explicitly through a library type (analogous to `Rc`/`Arc`), never
inferred silently by the compiler. Shared ownership is opt-in and visible
at the type level.

### Quarantined `unsafe`

`unsafe` (already a reserved keyword, `spec/0001`) will scope exactly the
operations that cannot be checked by the safe subset: raw pointer
dereference, calling `extern "C"` functions, and manual region escape
overrides. Code outside an `unsafe` block can assume every safety
invariant the type system encodes actually holds. `unsafe` is a block-level
marker, not a file- or module-level ambient mode (RFC 0001).

### `defer`

The `defer` statement (parsed today, not yet executed — `spec/0002`) is
intended to schedule an expression to run when the enclosing region ends,
in reverse order of the `defer` statements encountered, independent of
whether the region ends via normal control flow or an early
error/`return`.

## Unresolved research questions

- Whether region inference should be fully automatic or accept optional
  explicit region annotations (the `region` keyword is reserved for this)
  for cases the inference cannot prove on its own.
- How region inference interacts with structured concurrency: whether a
  spawned task can ever legally hold a value tied to a shorter-than-task
  region, and how that is rejected at compile time.
- The precise relationship between "explicit shared ownership" types and
  the borrow-checking rules that will need to exist for non-owning
  references — full details are deferred to `rfcs/0002-ownership-and-regions.md`.

## Non-goals

- No tracing garbage collector, ever, as a *mandatory* runtime component.
  An optional, opt-in collector for specific data structures is not ruled
  out as a future library, but it is not part of the language's default
  memory model.
- No manual `malloc`/`free`-style raw memory management as the *primary*
  idiom for safe code — that is exactly the class of bug (use-after-free,
  double-free, leaks) this memory model exists to design away by
  construction. Raw allocation remains available inside `unsafe` for FFI
  and low-level library authors.
