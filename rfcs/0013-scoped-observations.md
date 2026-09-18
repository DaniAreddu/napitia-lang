# RFC 0013: Lexically Scoped Observations (Alpha 0.1.9)

- Status: Accepted, implemented in Alpha 0.1.9

## Summary

Alpha 0.1.8 gave every affine value exactly one owner and tracked that
ownership per structural place (`rfcs/0012`). The only way to read a
resource a *different* binding owns was to pass it to an ordinary
(non-`take`) parameter: observation existed, but only ever at a call
boundary, and only for exactly as long as that call.

Alpha 0.1.9 adds a second, explicit form of the same capability, with a
boundary the author writes down:

```napitia
resource File {
    descriptor: i64
}

func inspect(file: File) -> i64 {
    return file.descriptor;
}

func read(take file: File) -> i64 {
    mutable result = 0;

    observe file as view {
        result = inspect(view);
    }

    drop file;
    return result;
}
```

`observe <place> as <name> { ... }` opens a lexical block inside which
`name` denotes the value at `<place>` without owning it. The owner keeps
owning it, is unusable *as an owner* for the duration, and is fully
usable again the instant the block ends.

This is lexical observation, not general borrowing. There is no
reference type, no `&`, no lifetime syntax, no lifetime parameter, no
inference of a non-lexical extent, and no way for an observation to
outlive the block that opened it. What the block gives is exactly what
an ordinary parameter already gave, with the extent named explicitly
rather than implied by a call.

## Grammar

```text
ObserveStmt := 'observe' PlaceExpr 'as' Ident Block
PlaceExpr   := Ident ( '.' Ident )*
```

`observe` is a new reserved keyword (`spec/0001`). `as` is the existing
one, reused; the observed source is deliberately **not** a general
expression, both because the construct only accepts a place anyway and
because `x as T` is already the cast operator -- parsing a general
expression here would swallow `as` and the alias name into a cast before
this production ever saw them.

`ObserveStmt` is a *statement*. It is not an expression, produces no
value, and never appears as a block's tail. No `;` follows the closing
brace, matching `while`/`loop` and every other brace-terminated
statement in the grammar.

## The observed place

`<place>` must be:

1. **addressable** -- a local, a field of a local, or an arbitrarily
   deep chain of fields rooted in a local. The grammar already admits
   nothing else; a call result, a construction, an arithmetic
   expression or a parenthesized temporary is a parse error rather
   than a later type error, because there is no place for the
   observation to name.
2. **transitively affine** -- a declared `resource`, or a `record`/
   `variant` that reachably contains one (`rfcs/0012`'s own
   `is_affine`). Observing an `i64` is rejected (`T0070`): an ordinary
   value is freely copyable and has no ownership to suspend.
3. **live and whole** at the `observe` statement -- not moved, not
   dropped, and not partially moved. The alias has the place's own
   complete type, so half a value cannot back it.

The place may itself be reached through another observation: an
ordinary parameter, or an enclosing observation's own alias. Observing
an observation yields another observation (never an owner), which is
what makes the construct compose.

## The alias

The alias is an ordinary local binding with:

- the **same** resolved type as the observed place -- not a wrapper, not
  a reference type, not a distinct nominal type;
- **no** ownership: it carries observation capability only;
- **immutability**: it is never `mutable` and may not be assigned to
  (`T0071`);
- a **stable identity**: a fresh `LocalId` minted at HIR lowering,
  distinct for every `observe` statement, so two sibling scopes that
  spell their alias the same way never share state;
- **lexical scope**: visible only inside the block, shadowing anything
  of the same name outside it exactly like an ordinary `value` binding
  in a nested block. Using the name after the block has closed is an
  unresolved name, reported as `R0034` (which says *why* the name is
  gone) rather than the generic `R0002`.

## Overlap

Two places **overlap** when one is an ancestor of the other, which by
`Place::is_ancestor_of`'s own definition includes equality:

```text
overlaps(a, b) := a.is_ancestor_of(b) || b.is_ancestor_of(a)
```

Disjoint siblings never overlap. The same shared `Place` representation
(`compiler/src/place.rs`) that `resourceck`, `nir::lower` and
`nir::verify` already share defines this relation once; no layer
invents a second notion of "the same field."

```text
observe session.left as view { ... }

move session.left.file      -> rejected (descendant)
move session.left           -> rejected (exact place)
move session                -> rejected (ancestor)
drop session                -> rejected (ancestor)
move session.right          -> allowed  (disjoint sibling)
observe session.right       -> allowed  (disjoint sibling)
```

## Active observations

An observation is **active** from its `observe` statement until its
block ends, on whichever path the block is left. While it is active, no
place overlapping the observed place may be:

- moved (a `value`/`mutable` initializer, an assignment's value, a
  `take` argument, a variant/record construction field);
- dropped (`drop`, or an implicit scope-exit destruction);
- passed to a `take` parameter;
- captured by a consuming `defer`;
- returned or raised as ownership;
- overwritten or structurally reinitialized;
- decomposed by a `match` that takes its payload.

Each of those is `U0017`. Everything else is unchanged: reading the
owner, reading a field of it, passing it to an ordinary parameter,
passing the *alias* to an ordinary parameter, and opening further
overlapping observations all stay legal, because none of them ends
anything.

**Multiple overlapping observations are legal.** They are all
read-only, so nothing orders them against each other and nothing needs
to. An ownership operation becomes legal again only once *every*
overlapping observation has ended.

Observation state is path-sensitive and strictly lexical: a scope
opened inside one `if` branch is closed at that branch's own block end
and is invisible to the sibling branch, to the join after them, and to
the next loop iteration. Unreachable code never begins, ends or
initializes an observation on a reachable path -- `resourceck::flow`
stops walking a block at the first statement that unconditionally
diverges, and `nir::verify` joins reachable predecessors only.

## Escapes

The alias carries no ownership, so it is rejected (`U0016`) in every
position that would move one:

- `return` and the function's own implicit tail return;
- `raise`;
- a `take` argument;
- a record or variant construction field;
- an assignment or binding initializer that would store it into
  longer-lived storage;
- an explicit `drop`;
- a `match` that decomposes it;
- any `defer`, observing or consuming, whose captured expression
  mentions it anywhere -- including through a nested aggregate or a
  compound expression. A deferred action runs at the *enclosing scope's*
  exit, which is strictly later than the observation's own end, so it
  can never be handed the alias regardless of how the argument is
  written.

The same rejection applies transitively to any place reached *through*
the alias: `view.input` is exactly as unownable as `view`.

## Exits

An observation ends exactly once on every path that leaves its block:

| exit | where the end is emitted |
| --- | --- |
| normal fallthrough | after the body block's own cleanup |
| `return` | before the `return`'s own cleanup |
| implicit tail return | before the tail's own cleanup |
| `raise` | before the `raise`'s own cleanup |
| postfix `?` | on the propagating (failure) edge, before its cleanup |
| `handle` arm exit | at that arm's own body end |
| `break` / `continue` | before the loop-exit cleanup, for exactly the observations opened at or inside the loop |
| diverging match/`if` arm | through whichever of the above that arm actually reaches |

`resourceck::flow` records this as `ResourceCheckResult::
observation_exits`: one entry per exit edge id, listing the
observations that edge must end, **innermost first**. `nir::lower`
replays that list; it never re-derives scope extents from syntax.

Ending an observation performs **no** cleanup and **no** ownership
transfer. It is purely the point at which the alias stops being
readable and the owner stops being frozen. Ends are emitted *before*
the ownership cleanup on the same edge, because that cleanup is
precisely the destruction the observation exists to forbid; the
relative order of drops and deferred calls among themselves is
unchanged (`rfcs/0011`'s reverse-registration LIFO).

## Interaction with existing constructs

- **`take`** still transfers ownership. Passing an alias to a `take`
  parameter is `U0016`; passing an *owner* overlapping an active
  observation to one is `U0017`.
- **`drop`** of an overlapping place is `U0017`; of the alias itself is
  `U0016`. Neither is reinterpreted as ending the observation.
- **Structural moves** are gated per place, so moving a disjoint
  sibling field out of an observed aggregate's parent is unaffected.
- **`defer`** never captures an alias (above). A `defer` registered
  *outside* the observation keeps its existing meaning entirely: its
  own `DropScheduled` protection and the observation's freeze are
  independent facts about the same place, and the stricter of the two
  wins at any given point.
- **`raise` / `?` / `handle`** are ordinary exits. A failure edge can
  never skip an end, and a success and a failure edge reaching the same
  block can never both end the same observation, because the end is
  emitted on the edge, before the merge.

## NIR

Observations are explicit instructions, never comments, lowering-side
maps or inferred use counts:

```text
%4 = observe.place @obs0 %0.@Session#1.0
end.observe @obs0
```

- `ValueKind::ObservePlace { observation, place }` -- begins
  `observation` on `place` and produces the observer value. Its result
  type is the place's own type.
- `Instruction::EndObserve { observation }` -- ends it.

`ObservationId` is a stable `u32` identity, minted once per `observe`
statement at HIR lowering and carried through unchanged. The printer
renders both forms deterministically, with the same `format_place`
every other structural instruction already uses.

`nir::lower` consumes `resourceck`'s own `CheckedObservation` (the
canonical place, the alias, the resolved type, the body scope) and
`observation_exits` (every end edge). It re-resolves the NIR place from
the checked HIR place through the same `resolve_nir_place` every other
structural instruction uses, so a disagreement between the two stages
is an internal error rather than a silently divergent lowering; it does
not re-derive place identity, scope extents, escape decisions or end
edges from syntax.

## Verifier invariants

`nir::verify` re-establishes all of the following from the NIR alone,
trusting neither the source checker nor its metadata (there is none to
trust: `CheckedObservation` never reaches the verifier):

- every `ObservationId` begins at most once per function (`V0102`);
- every `end.observe` names an observation this function begins
  (`V0103`);
- the observed place resolves, is addressable and is transitively
  affine (`V0104`);
- the observer's result type is the place's own type (`V0105`);
- on every reachable path, an end happens only while that exact
  observation is active, and ends run innermost-first (`V0106`) --
  which subsumes end-before-begin, double end and non-LIFO nesting;
- no reachable `Return`/`Raise` leaves an observation active (`V0107`);
- two predecessors never disagree about which observations are active
  (`V0108`), which is what a missing end on one branch of an `if`, or
  an `Invoke` whose success and failure edges disagree, actually looks
  like;
- an observer value is never used at a point where its observation is
  not active (`V0109`);
- no move, drop, structural store, whole-slot store, `take` argument,
  decomposition, return or raise touches a place overlapping an active
  observation (`V0110`).

The observer value is additionally `Observed` in the existing
structural ownership lattice, so every pre-existing rule about an
observation -- it may not be transferred (`V0099`), consumed (`V0079`),
dropped, moved, stored as an owner or returned -- applies to it with no
new code and no second implementation.

Begin-dominates-use needs no new check: the observer is an ordinary SSA
result, already covered by `V0017`/`V0018`.

The analysis is a real finite lattice over a worklist, with no pass
cap. A block's state is the stack of currently-active observations;
`IncomingState` keeps "no reachable predecessor has produced an
out-state yet" distinct from "computed, and empty", exactly as
`rfcs/0012`'s own structural pass does, so an unreachable predecessor
or an unreachable cycle can never seed a reachable fact. The stack is
bounded by the begins the function actually contains, and each block's
state is computed from reachable predecessors only, so block-vector
order, predecessor discovery order and `HashMap` order are all
irrelevant to the result. Diagnostics are emitted sorted by (block id,
instruction index) so their order is deterministic too.

One root cause produces one diagnostic: a conflicting operation is
reported once, against the operation, naming the innermost overlapping
observation -- never once per nested field of the place.

## Interpreter leases

The interpreter enforces observations itself, as runtime objects, and
does not assume the module it is running passed verification.

```rust
struct RuntimeObservation {
    id: RuntimeObservationId,
    status: LeaseStatus,          // Active | Ended
    observed: Vec<ResourceId>,    // deterministic, discovery order
    parent: Option<RuntimeObservationId>,
}
```

- `ObservePlace` is a transaction: it resolves the complete place,
  rejects a handle that is moved, dropped, stale or bound to an ended
  observation, rejects a partially moved or otherwise incomplete affine
  value, checks the source against the type the instruction declares
  for the view, collects every resource identity reachable through it
  in deterministic order, and builds the complete view -- all of it
  mutating nothing. Only once nothing is left that can fail is the
  lease committed, pushed onto the frame's active stack and the view
  handed back. A rejected begin therefore leaves the records,
  generations, values, leases, active lease indexes and event log
  exactly as it found them, and repeating it on the same interpreter
  reports the same refusal -- naming the next run-time observation
  identity, as identities do, and nothing else differing.
  The resulting view is an observing view *recursively* -- every handle
  it carries at any depth is an `Observer` tagged with that lease.
- A frame that fails for any reason closes every lease it opened before
  the error leaves it, innermost first. Errors do not unwind through
  Rust's own `Drop`; the frame has a structured epilogue that records
  the lease table's height on entry and abandons everything opened
  above it on an `Err`. So no lease from a failed frame is ever left in
  the active list, a caller's own resources are never permanently
  frozen by a callee that failed, and repeated failures on one
  interpreter neither accumulate open leases nor change what is
  reported.
- Reading through a handle whose lease has ended is a structured error,
  not a silent success and not a panic.
- `EndObserve` ends the lease exactly once; ending an already-ended
  lease, or one this frame never began, is a structured error. Ending a
  lease while a lease derived from it is still active is refused, so
  the runtime does not depend on the verifier's LIFO guarantee.
- Every ownership boundary -- transfer planning, drop planning, store
  planning, the call/`take`/return/raise/defer boundary -- consults the
  active leases *during* its existing plan phase, before any generation,
  status, field, tombstone or event changes. A refused operation leaves
  the resource table, every generation and status, the frame's values,
  the lease table and the event log byte-identical, and repeating it
  reports the identical error.
- Leases are a `Vec` indexed by a monotonically increasing id. Nothing
  about them depends on a Rust pointer address or on `HashMap`
  iteration order, and Napitia semantics never rely on Rust's own
  `Drop`.

Disjoint sibling resources stay independently transferable, because a
lease names resource identities rather than whole frames; multiple and
nested leases are ordinary.

## Diagnostics

| code | meaning |
| --- | --- |
| `R0034` | an observation alias used after its own block ended |
| `T0069` | the observation source is not an addressable place |
| `T0070` | the observation source is not transitively affine |
| `T0071` | assignment to an observation alias |
| `T0072` | the observation source's own type is unresolved or symbolic |
| `U0016` | an observation alias used as ownership |
| `U0017` | an ownership operation on a place an observation is holding |
| `V0102`-`V0110` | the NIR invariants listed above |

Every one carries a stable code, a primary span, a label, and help
where there is something actionable to say. No malformed observation
metadata reaches a later stage: a rejected `observe` never mints
ownership state, never records a checked observation, and never
produces `Ty::Error`-typed metadata that a later stage would treat as
real.

## Deliberately unsupported

Each of these is a *source-level* restriction, not an accepted program
that misbehaves:

- returning an observation, storing one in an aggregate, or binding one
  to a longer-lived slot -- there is no type that could carry it out;
- an observation field inside a user aggregate;
- a general reference type, `&`/`&mut`, apostrophe lifetimes or
  lifetime parameters -- none of that syntax exists;
- non-lexical or inferred observation extents: the block is the extent,
  always, even when the alias is last read earlier;
- asynchronous or cross-thread observations;
- native code generation, heap allocation, shared ownership, reference
  counting, garbage collection, raw pointers and FFI remain out of
  scope exactly as `rfcs/0011` and `rfcs/0012` left them;
- observing a generic function's own bare `T`-typed place: a generic
  body is checked once, symbolically, so `T0072` rejects it rather than
  guessing an instantiation, exactly as `T0068` already rejects an
  affine generic instantiation.

## Differences from Rust borrowing

Stated as differences, not as claims of superiority; both designs
answer different questions.

- **Extent.** A Rust borrow's region is inferred (NLL) and can end
  before the enclosing block does. A Napitia observation's extent is
  the block, written by the author, and is never shortened or
  lengthened by analysis.
- **Type.** Rust gives a borrow its own type (`&T`, `&mut T`) that
  values, fields and signatures can carry. Napitia's alias has the
  observed place's own ordinary type and cannot be stored anywhere; the
  capability lives on the binding, not in the type system.
- **Exclusivity.** Rust distinguishes shared from unique borrows.
  Napitia has only the read-only form: every observation is shared with
  every other, and there is no mutable-through-alias form at all, which
  is why overlapping observations need no ordering.
- **Escape.** Rust permits a borrow to escape wherever a lifetime
  proves it sound. Napitia permits no escape of any kind; there is no
  lifetime to prove anything with.
- **Runtime.** Rust's borrows are erased. Napitia's are real runtime
  leases in the interpreter, checked independently of the verifier,
  because this milestone's interpreter is the executable semantics.

## Non-goals

Unchanged from `rfcs/0011` and `rfcs/0012`: no native heap allocation,
no general borrowing, no lifetime inference, no shared ownership, no
garbage collection, no thread-safety guarantees, no FFI cleanup.
Ordinary parameters remain call-scoped observations, and `take` still
transfers ownership.
