# Spec 0004: Memory Model

- Status: Partially implemented as of Alpha 0.1.8 (`resource`/`take`/
  `drop`/`defer`, `rfcs/0011-deterministic-resources.md`; structural
  field ownership, `rfcs/0012-structural-ownership.md`). The rest of
  this document (universal ownership inference over every type,
  automatic region inference, `owned`/`borrow`/`shared` boundary
  annotations, `unsafe`) remains design direction only, not implemented.

Alpha 0.1.7 adds a first, deliberately narrower memory-safety layer than
the universal ownership-inference design this document originally
sketched: rather than inferring move-vs-copy for *every* type, it
introduces one new nominal kind, `resource`, that is *always* affine and
non-copyable, tracked by a dedicated compiler stage (`resourceck/`).
Alpha 0.1.8 lifts Alpha 0.1.7's own narrower restriction that a
`resource` could never appear as a field of anything: a `record`,
`variant`, or another `resource` that reachably contains an affine field
now becomes affine *transitively*, and ownership is tracked per
structural place (a root binding plus a path of field projections), not
only per whole binding -- see `rfcs/0012-structural-ownership.md`. Every
type that is not itself affine (either a declared `resource`, or an
aggregate reachably containing one) keeps its existing, unconditional
copy semantics — this spec's own "value semantics by default" section
describing implicit move-vs-copy *inference* for every type, and its
"compiler-inferred memory regions"/`owned`/`borrow` API vocabulary, are
not what Alpha 0.1.7/0.1.8 implement; see `rfcs/0011-deterministic-
resources.md` and `rfcs/0012-structural-ownership.md` for the actual
design and their own explicit non-goals. The sections below describe the
original, broader design direction this narrower feature does not (yet)
fully realize.

The vocabulary below (`owned`, `borrow`, `shared`, `region`) is the
provisional set accepted in `rfcs/0004-language-independence.md`. It
describes semantic *categories*, not necessarily a one-to-one reference
syntax the way Rust's `&T`/`&mut T` and lifetime parameters are — the
explicit design goal is that ordinary Napitia code should express
ownership *intent* only at boundaries and let the compiler infer the rest
(storage placement, moves, temporary access, escape behavior, region
membership) everywhere else. See `rfcs/0002-ownership-and-regions.md` for
the reasoning and the open questions this raises.

## Implemented features

- **Local storage in NIR**: NIR functions have named local slots
  (`spec/0006-napitia-ir.md`) that are simple value storage with no
  ownership metadata attached for ordinary (non-`resource`) types.
- **Affine `resource` values** (`rfcs/0011`, Alpha 0.1.7): a `resource`
  declaration is a non-copyable nominal aggregate with exactly one
  owner at a time. `resourceck/` tracks each owned resource-typed
  local's own state (`Available`/`Moved`/`DropScheduled`/`Dropped`)
  through a function body; assigning, returning, storing in a field, or
  passing to a `take` parameter moves ownership; an ordinary parameter
  is a call-scoped observation that can never escape its call. `drop`
  destroys a live resource immediately; every resource still owned at
  its own function's exit is destroyed implicitly, in reverse
  declaration order; `defer` registers a call that runs exactly once,
  in LIFO order, interleaved with implicit destruction. NIR represents
  every ownership transfer explicitly, never re-derived from how many
  times a value happens to be used elsewhere: `Instruction::Drop` for
  destruction, `store`'s own `OwnershipMode` (`Observe` vs. `Transfer`)
  for a move through a slot, and dedicated `Move`/`DeferCapture` value
  kinds for a move with no intervening slot (a `take` argument, a
  `return`/`raise` operand, a `defer` argument captured at its own
  registration point, or a rebind to a different local) -- in every
  case, `resourceck`'s own already-checked decision, threaded through
  unchanged by `nir::lower`. `nir::verify` independently checks these
  markers are used consistently (never trusting `resourceck`'s own
  acceptance of the source): the exact same `ValueId` is never the
  operand of `Drop` twice on any reachable path (`V0075`); a resource's
  own underlying identity -- unified across every `Load` of the same
  slot, not just one bare `ValueId` -- is never read, stored, passed as
  an argument, dropped, moved, captured, or transferred again once
  already consumed by a `Drop`, a `store.transfer`, a `Move`/
  `DeferCapture`, a `take` argument, or a `return` (`V0076`); a resource
  this function itself created, received through a `take` parameter, or
  received through a fallible `Invoke`'s own success slot, is never
  still owned at a reachable `return`/`raise` without having been
  destroyed or transferred out (`V0077` -- the `Invoke` success case is
  seeded as owned specifically on the block reached through its own
  success edge, never a sibling failure edge that happens to share a
  block, the same per-edge distinction `V0073`'s own Alpha 0.1.6
  verification needs, adapted to this check's own reachable-union
  dataflow); and a `Move`/`DeferCapture` whose own source is not itself
  resource-typed is independently rejected, since both exist only to
  represent a transfer (`V0078`). All of these reuse the same
  reachable-union worklist shape Alpha 0.1.6's own `Invoke`-slot
  verification established.

  `nir::verify` also tracks, flow-sensitively, whether each value/slot
  currently grants owning or merely *observing* access: an ordinary
  (non-`take`) parameter, and anything ever loaded from a
  `store.observe`'d slot, is an observation, and is rejected outright
  if used anywhere only an owner may be (`V0079`; `V0080` for
  `store.transfer` specifically) -- an observation can never be
  silently promoted into an owner, however it is used. A value/slot's
  own true resource identity is also unified across an observing
  `store`/`load` pair, not only a slot's own repeated loads, so a
  `Drop` reaching one alias poisons every other alias of that same
  resource for any later use, consuming or not (`V0081`) -- this is
  what actually catches a double-free reached through two different
  aliases of one resource, which identity unified only through
  repeated loads of one shared slot could not. The runtime
  independently enforces the same owner/observer distinction on every
  `ResourceHandle`: an ordinary parameter binding and an observing
  store both mint a handle that can never `Drop`/transfer the resource
  it points to, regardless of what role the value it was built from
  had. A value/slot's own role/identity is only ever meaningful once it
  is definitely initialized on every reachable path reaching its own
  use: a missing location resolves to `Uninitialized`, never a lenient
  fresh `Owned` guess, and a join where even one reachable predecessor
  never wrote it downgrades to `MaybeUninitialized` -- either is
  independently rejected (`V0082`) before role/origin checks even run.
  `resourceck`'s own checked metadata (`consume_sites`, and each
  `defer`'s own `CheckedDeferPlan` -- callee, argument modes/types,
  return type, and LIFO registration order) is read back by `nir::
  lower` directly rather than re-derived from a callee's own `take`
  flags or a binding's own AST shape a second time, and is validated
  field-by-field against what lowering resolves on its own; missing or
  disagreeing metadata is a structured internal error, never a silent
  fallback to `Ty::Error`, `false`, or treating an argument as merely
  observing. This is a real memory-safety layer -- not the universal
  region-inference design sketched below, which remains unimplemented.

## Accepted design direction

### Value semantics by default

Assignment, passing an argument, and returning a value all conceptually
*move or copy* the value, matching the source binding's declared
ownership — never an implicit shared, mutable alias. Types that are cheap
to duplicate (primitives) copy; larger/owning types move. There is no
implicit reference-counting inserted by the compiler.

### Ownership and inferred moves

Every value has exactly one owning binding at a time. Moving a value out
of a binding (e.g. passing it to a function that takes ownership)
invalidates the source binding for further use; using a moved-from binding
is a compile-time error, not a runtime one. Immutable (`value`) bindings
may still be moved from; move and mutability are independent axes. Unlike
a model with an explicit move marker, whether a given use of a binding is
a move or a copy is inferred from the binding's type (`spec/0003`) and
context — there is no dedicated keyword the programmer writes to request
a move.

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

### Explicit shared ownership (`shared`)

When more than one owner is genuinely required, it must be requested
explicitly — either through the `shared` boundary annotation or a library
type built on it — never inferred silently by the compiler. Shared
ownership is opt-in and visible at the type level; the compiler chooses
the underlying mechanism (e.g. runtime reference counting) rather than
that mechanism being spelled out by name at every use site the way a
Rust program must name `Rc`/`Arc` explicitly.

### `owned` and `borrow` at API boundaries

Within a function body, ownership is inferred and never annotated.
`owned` and `borrow` exist only to say something at an API boundary that
inference cannot see from the outside: `owned` marks a parameter that
takes the value permanently (the caller cannot use its argument
afterward); `borrow` marks a parameter that only needs temporary access
(the caller retains the value). Neither carries a lifetime parameter —
the borrowed access is scoped to the call, not to a named region the
signature has to spell out.

### Quarantined `unsafe`

`unsafe` (already a reserved keyword, `spec/0001`) will scope exactly the
operations that cannot be checked by the safe subset: raw pointer
dereference, calling `extern "C"` functions, and manual region escape
overrides. Code outside an `unsafe` block can assume every safety
invariant the type system encodes actually holds. `unsafe` is a block-level
marker, not a file- or module-level ambient mode (RFC 0001).

### `defer`

`defer` is implemented as of Alpha 0.1.7 (`rfcs/0011`), scoped to its
own immediately enclosing block rather than the fully general
per-region design this section originally sketched: it schedules an
expression to run exactly once, in LIFO order, at that block's own
normal fallthrough, an explicit `return`, `raise`, postfix `?`
propagation, or a `break`/`continue` loop exit -- destroying exactly
that iteration's own live resources and running that iteration's own
pending defers before jumping past or back to the loop, never an
enclosing scope's.

## Unresolved research questions

- Whether region inference should be fully automatic or accept optional
  explicit region annotations (the `region` keyword is reserved for this)
  for cases the inference cannot prove on its own.
- How region inference interacts with structured concurrency: whether a
  spawned task can ever legally hold a value tied to a shorter-than-task
  region, and how that is rejected at compile time.
- The precise aliasing/mutation discipline for `borrow` — whether multiple
  simultaneous borrows of the same value are ever restricted, and if so,
  by what rule. Napitia needs its own answer to the problem Rust's
  `&`/`&mut` aliasing rules solve; it does not have one yet. Full details
  are deferred to `rfcs/0002-ownership-and-regions.md`.
- Whether `shared` implies any concurrency-safety guarantee on its own,
  or only becomes concurrency-safe when paired with another mechanism.

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
