# RFC 0012: Structural Ownership (Alpha 0.1.8)

- Status: Accepted, implemented in Alpha 0.1.8

## Summary

Alpha 0.1.7 tracked ownership only for a *whole* `resource`-typed local
binding; a resource-typed field in any record, variant, or other
resource was rejected outright at its own declaration
(`RESOURCE_FIELD_IN_ORDINARY_AGGREGATE`, retired by this RFC). Alpha
0.1.8 lifts that restriction: a record, variant, or resource that
reachably contains an affine field becomes affine itself
(*transitively*), and ownership is now tracked per structural *place* --
a root local plus a path of stable field projections -- rather than only
per whole binding.

```napitia
resource File {
    descriptor: i64
}

resource Session {
    input: File,
    output: File
}

func detach(take session: Session) -> File {
    value input = session.input
    drop session
    return input
}
```

`value input = session.input` transfers only `session.input`;
`session.output` is completely unaffected. `drop session` structurally
destroys every field `session` still owns (`output`, here -- `input` is
already gone) and, since `Session` is itself declared `resource`, its
own outer identity last.

Source-level movement remains exactly as context-driven as Alpha 0.1.7
left it: there is no new `move` keyword, and no new syntax at all beyond
what already parsed (field access, field assignment). What changes is
which programs the checker, NIR, and runtime can now represent and
verify.

## Transitive affinity

```text
is_affine(T):
    true for a declared `resource` T
    true for a record/variant T when any reachable field/case payload is affine
    true for an instantiated aggregate T[Args] when substitution makes a field affine
    false for a primitive, and for a fully non-affine aggregate
```

Computed independently, the same way, by `typeck::Checker::is_affine`,
`resourceck`'s own `is_affine_item`/`is_affine_ty`, `nir::lower`'s own
`is_affine`, `nir::verify`'s own `is_affine_in`, and the interpreter's
own `is_affine` -- no stage trusts another stage's verdict blindly.
Every one of these is memoized (or, for `nir::lower`/`nir::verify`/the
interpreter, cheaply recomputed) with a `visiting` guard: a
self-referential declaration (already independently rejected as an
infinite-size layout, `typeck::cycles`) contributes `false` to that one
occurrence's own disjunction without ever being cached as the type's
final answer, so a genuine cycle elsewhere in the same query can never
poison an unrelated, non-cyclic answer.

A `record`/`resource` is decomposed field by field; a `variant` is not:
which case is active is not something static analysis can know in
general (there is no `.field` syntax onto a variant's own payload, only
pattern-matching), so a variant-typed place is always tracked, and
structurally dropped, as one opaque whole-value unit. `resourceck`'s own
`variant_items` set exists specifically so `structural_drop_targets`
never treats a variant's own flattened, cross-case payload-type list as
if it were one record's own named field vector.

### Generic aggregates

A generic record/variant's own affinity is recomputed fresh at each
concrete instantiation, directly from its substituted field types --
the same generic declaration can be affine for one instantiation
(`Box[File]`) and not another (`Box[i64]`), and this is fully sound
because a real use site's type arguments are always already fully
resolved by the time affinity is asked about them.

Substitution is applied *at every projection step*, in the same order
in every stage -- `typeck`, `resourceck`, cleanup planning, `nir::lower`,
`nir::verify`, and the interpreter:

1. validate the owner against the place's own current type;
2. retrieve the owner's stable declared type parameters;
3. require exact arity;
4. build the substitution;
5. substitute the selected field/payload type;
6. continue the walk from the substituted type.

Without step 5 a `Box[File]`'s own `item` field resolves to the bare,
never-affine `Ty::Param(T)` the declaration was written with, and a
genuinely owned resource is treated as a freely-copyable value. A
missing type-parameter list, or one whose arity disagrees with the
arguments a use supplies, is **never** papered over with an empty or
partial substitution: `nir::verify` reports it as `V0089`
(`PLACE_GENERIC_ARITY_MISMATCH`), and every affinity query that has no
diagnostic channel of its own fails *closed* -- answering "affine", so
every ownership obligation is still demanded -- rather than the "not
affine" an unsubstituted `Ty::Param` would otherwise produce, which is
the one direction that leaks.

A generic *aggregate* is therefore supported end to end: `Box[File]` is
affine and `Box[i64]` is not, `Box[File].item` moves and reinitializes
like any other structural field, `Box[Box[File]]` is affine through two
levels of substitution, and a generic variant's payload is owned at an
affine instantiation whether it is bound or ignored.

A generic *`resource`* declaration (`resource Cell[T] { .. }`) is not
parseable in this milestone's grammar, so the question does not arise:
generic parameters are accepted on `record` and `variant` declarations
only, and `resource Cell[T]` is a parse error at `check`.

The cycle guard every one of these queries carries is keyed by bare
`ItemId`, which cannot tell a genuine cycle apart from a legitimately
nested instantiation of the same declaration: `Box[Box[Box[File]]]`
reaches `Box` three times with different arguments and must answer from
the innermost one. Every stage therefore bounds the *instantiation* walk
by depth instead, and keeps `visiting` for the non-generic case where it
is keyed correctly. `typeck::cycles` independently rejects a genuinely
cyclic layout as infinite before any body is checked, so the depth bound
is a backstop rather than the only guard.

What a generic *aggregate*'s completeness does **not** extend to is a
**generic function**, whose own body is checked once, symbolically, and
shared unchanged by every instantiation (`rfcs/0008`) -- nothing would
ever track a bare
`T`-typed value's ownership if some call site substitutes `T` with an
affine type, since that body is never re-checked per instantiation the
way a concrete function is. Instantiating (or calling) a generic
function with a transitively affine type argument is rejected with a
dedicated diagnostic (`T0068`, `UNSUPPORTED_GENERIC_AFFINE_INSTANTIATION`)
rather than silently miscompiled.

## Place representation

```rust
struct Place<Root> {
    root: Root,
    projections: Vec<Projection>,
}

enum Projection {
    Field { owner: ItemId, field: FieldId },
    VariantField { variant: ItemId, case: CaseId, field: FieldId },
}
```

One shared, generic representation (`compiler/src/place.rs`), used
unchanged by `resourceck` (rooted at a HIR `LocalId`), `nir::lower`, and
`nir::verify` (both rooted at a NIR `ValueId`) -- no layer invents its
own incompatible notion of "the same field." `FieldId`/`CaseId` wrap a
bare declaration-order position specifically so every consumer is
forced to validate it against the owning aggregate's own field/case
list, never trusted as already in range just because it type-checks.
Equality and ordering are structural (`#[derive(PartialEq, Eq, Hash,
PartialOrd, Ord)]`); `Place::is_ancestor_of` gives every consumer one
shared, correct definition of "is this the same place, or a place
projected out of it."

## Structural state and partial move

A place absent from `resourceck`'s own per-function state map is
`Available` by default -- what a freshly-constructed aggregate's own
field always starts as. Moving a place inserts `Moved`; dropping it
inserts `Dropped`. A *whole-value* use of a place (observed, returned,
transferred, copied, passed as a whole) additionally requires every one
of its own affine descendants to still be `Available`
(`place_is_wholly_available`) -- a parent with one or more fields
already moved out is *partially moved*, and rejected as a whole
(`U0014`) while remaining fully usable for accessing an unaffected
sibling, reinserting into the empty field, or structural cleanup.

```napitia
inspect(session.input)   // U0002 (or U0001): field already moved
inspect(session.output)  // valid: an unaffected sibling
session.count            // valid: an ordinary, non-affine field
inspect_session(session) // U0014: whole aggregate partially moved
drop session             // valid: drops only the remaining owned fields
```

Reading an *ordinary, non-affine* field of a partially moved aggregate
is checked as the place it is -- what must still be intact is the chain
reaching it, not the whole parent. Checking the base as a whole-value
read instead would reject exactly the thing `U0014`'s own advice tells
the user to do. A use after the *parent* itself was moved or dropped is
still rejected, because the ancestor's own state dominates its
descendants'; `nir::verify`'s own `RecordField` check applies the
identical rule, so the two stages agree on precisely which programs this
admits.

### Reinsertion

```napitia
mutable session = create_session()
value previous = session.input
session.input = open_file()
consume(session)
```

A plain `=` into an affine field (`typeck::Checker::check_assign`) is
accepted only for a target place `resourceck` already proves empty
(`Moved`/`Dropped`) on *every* reachable path -- a field empty on only
one incoming branch is not sufficient, and a still-live field is
rejected (`U0010`) rather than silently leaked. Once every missing field
is restored, the parent is whole again and may be used, returned, or
transferred as one value.

### Branches, joins, and loops

A join is computed the same way `RESOURCE_LOCATION_NOT_DEFINITELY_
INITIALIZED` (`V0082`) already does: reachable predecessors only,
unioned by key (never intersected), with a three-state lattice
(`Available`/`Moved`(or `Dropped`)/disagreement) whose middle
disagreement state is absorbing and can never be silently upgraded back
out of. A place moved on only one of several continuing branches joins
to that absorbing state and is reported once (`U0006`,
`INCONSISTENT_BRANCH_STATE`) rather than guessed either way. Loops
compare the backedge's own state (the body's fallthrough, and every
`continue`) against loop entry for every place declared outside the
loop; disagreement is `U0007`, `LOOP_CARRIED_INVALIDATION`.

## Structural destruction order

One exact order, enforced identically everywhere:

1. Scopes clean up in reverse lexical registration order; deferred
   actions remain LIFO, interleaved with drops exactly as Alpha 0.1.7
   already specified.
2. An aggregate's own affine fields are destroyed in *reverse*
   declaration order, each expanded the same way first if it is itself
   a nested aggregate.
3. Only the active variant case's own live payload is destroyed --
   never a payload belonging to a case that was never constructed.
4. A place already moved or dropped contributes nothing: never
   destroyed twice, never destroyed at all if another place already
   owns it.
5. A declared `resource`'s own outer identity is destroyed *after* its
   own still-owned child resource fields, never before -- the outer
   identity has nothing left to coordinate once every field it
   delegates to has already been individually accounted for, and this
   ordering is what lets a partially-moved resource still be dropped
   safely (only the fields actually remaining are ever touched).

`resourceck::flow::FlowChecker::structural_drop_targets` computes this
full, ordered, per-place list once, from checked state; `nir::lower`
and the interpreter only ever replay it -- neither re-derives it.

## Patterns

Only the pattern shapes that already parsed are resource-aware: a bare
binding, and a variant case's own positional payload pattern
(`Found(file)`). No record-destructuring pattern syntax is introduced
(none existed before this milestone, and none is added). Matching an
affine scrutinee *decomposes* it: the scrutinee's own place (if it
names one at all) is treated as consumed by the match itself
(`resourceck::flow`'s `HirExpr::Match` handling, and `nir::verify`'s
identical treatment of `Terminator::Switch`'s own scrutinee operand) --
never left `Available` for its own separate implicit cleanup to also
try to destroy the very payload a pattern binding already took
ownership of.

### Ignored payloads

A payload position matched by `_` (or by a literal) rather than a
binding is still *owned* by the arm that matched: nothing else will ever
destroy it. It is therefore destroyed, exactly once, the instant the
decision tree commits to that arm -- **before** the arm's body runs.

```napitia
match result {
    Found(_) => 1,   // the `File` payload is destroyed here
    Missing  => 0,   // the inactive case is never touched
}
```

`nir::lower`'s own pattern matrix carries, per row, every occurrence
that row reached and left unclaimed. An occurrence is unclaimed when its
own parent was decomposed by a real case test and its own position is
matched by `_` or a literal. An occurrence some *ancestor* pattern bound
as a whole value is marked `PatternSlot::Owned` instead and is never
discarded -- that binding's own scope cleanup already destroys
everything reachable through it, and destroying it here too would be a
double drop. A variant occurrence no row tests at all is discarded as
one opaque whole, and the runtime's structural drop then destroys
whichever case is actually live.

Destroying at the commitment point, rather than on each way out of the
body, is what makes this correct for an arm that returns, raises,
propagates with `?`, handles, breaks, or continues -- without
enumerating any of them: the payload is gone before the body starts, and
`_` gives it no name through which anything could observe it. Discarded
occurrences are destroyed in reverse of the order the decision tree
consumed them, which is exactly reverse payload declaration order.

## NIR

```text
%1 = load.place %0.@Session#1.0     ; ValueKind::PlaceRead { mode: Observe }
%2 = move.place %0.@Session#1.0     ; ValueKind::PlaceRead { mode: Transfer }
store.place %0.@Session#1.0, %3     ; Instruction::StorePlace
```

`Place<ValueId>` is the same generic `Place` rooted at a NIR value
instead of a HIR local. There is no separate `drop.place` instruction:
a structural drop is `move.place` immediately followed by the ordinary,
already-existing `Instruction::Drop` -- "read the value, then drop it"
already composes the two primitives this RFC's own conceptual sketch
only lists separately.

### `Drop` is structural

One coherent model, enforced identically in lowering, the verifier, the
printer, the interpreter and the tests: **`Drop` destroys its operand
and every descendant it still owns.** A parent dropped after one of its
own children was already moved out is therefore valid and destroys only
what is left; a child read after its parent was dropped is a use of
something already consumed. The alternative model -- requiring explicit
child cleanup in NIR and making a direct parent `Drop` reject live
descendants -- is not viable here, because which case of a variant is
live (and therefore which payload a drop must destroy) is only ever a
runtime fact.

Because the same `move.place` instruction expresses both "move this
field out to use it" and "take this field out to destroy it", the
verifier distinguishes them by what the result is used for: a
`PlaceRead { mode: Transfer }` whose *only* use anywhere in the function
is as a `Drop` operand is a destruction, and is therefore legal on a
partially moved parent; one feeding anything else is a real transfer and
requires a complete value.

### The structural ownership lattice

`nir::verify` independently re-validates every place it sees (unknown
field owner, out-of-range field index, projection through the wrong or a
non-aggregate type, move of a non-affine place, generic arity mismatch
-- `V0083`-`V0086`, `V0089`) and independently re-derives per-place
ownership over the whole place **tree**, not merely per exact key:

- `resolve_place_state` returns the *shortest* non-`Full` ancestor
  prefix, so moving or dropping a parent consumes its entire descendant
  subtree whether or not each descendant was ever individually tracked.
  A child read after its parent was transferred or dropped is rejected
  by exactly the same check a child read after its own transfer is
  (`V0087`).
- `place_is_whole` additionally requires no strict descendant to be
  consumed, so a partially moved parent is rejected wherever a *whole*
  value is required -- observed, transferred, returned, raised, or
  consumed into an aggregate (`V0090`) -- while staying usable for an
  unaffected sibling, a reinitialized empty child, or a structural drop
  of what remains. Reinitializing a child retires every stale descendant
  fact, which is what restores its ancestors' completeness.
- A reinitializing store into a place not definitely empty is `V0088`;
  a whole-value destruction or transfer of something already consumed on
  a path reaching it is `V0092` (duplicate structural cleanup); and a
  transitively affine value this function owns that still has remaining
  owned affine descendants at a reachable exit is `V0091` (missing
  structural cleanup).

Ownership facts are contributed by every path that actually moves one --
`take` parameters, `Move`, `DeferCapture`, `PlaceRead`, `StorePlace`,
`Store`, `RecordCreate`, `VariantCreate`, `Call`/`Invoke` take
arguments, `Switch`, `Return`, `Raise`, `Drop` -- and are gated on
*transitive* affinity throughout, never on nominal `is_resource`: an
affine record owns real resources and is tracked in its own right.

What *becomes* an obligation is every root this function itself owns: a
`take` parameter, an aggregate it constructs, a value it moves or
captures, a field it transfers out of a place, an affine value a callee
returns to it, and a variant payload extracted from a base nothing else
ever consumes. That last distinction matters because `variant.payload`
copies its payload out without emptying the base: when the base is
itself destroyed or transferred somewhere, that destruction already
covers the payload and demanding a second one would double-count the
same obligation; when nothing else consumes the base, the extraction
*is* the transfer and the payload is this function's own.
`V0091` complements `V0077` rather than duplicating it: `V0077` covers a
nominally resource-typed root, and this one covers the gap that lattice
cannot see, a record that merely *contains* affine fields and is
therefore never a key there at all. The missing-cleanup check skips
every root the other pass already owns, so no leak is reported twice.

A value-producing instruction resets its own result's facts, so a
resource constructed inside a loop body and destroyed at the end of that
same iteration is not mistaken for a double cleanup on the next one. An
obligation is only demanded at an exit its own definition dominates, so
a value created in one branch is not reported as leaked by the other
branch's `Return`. Places are canonicalized through the same
`Load`-origin unification the whole-value pass already needs for a
`mutable` local reloaded more than once.

### The fixed point

The out-state map holds an entry for a block **only once that block's
own out-state has actually been computed**, so "not computed yet" is the
*absence* of a key and cannot be confused with a block genuinely
computed to hold no facts. Pre-seeding every block with an empty map
erases exactly that distinction, and lets an unprocessed loop back-edge
predecessor contribute a fact set nothing ever proved.

Three cases are therefore kept apart explicitly, as the variants of an
`IncomingState` type rather than as values of `PlaceFacts`, when a
block's in-state is joined:

* `Entry` -- the **entry** block has no predecessors, and its empty
  in-state is the analysis's one real boundary condition;
* `Ready` -- at least one reachable predecessor has produced an
  out-state, and this is the join of every such predecessor's;
* `Pending` -- no reachable predecessor has produced an out-state yet.
  This is not a fact set at all: the block runs no transfer and records
  no out-state, so nothing downstream can read facts nothing proved. An
  **unreachable** predecessor likewise contributes nothing, so a dead
  CFG fragment can never seed reachable ownership.

`Pending` is deliberately not representable as `Default::default()`, an
empty map or `Option::unwrap_or_default()`, because each of those is
also a perfectly valid analysis state. Every reachable block leaves
`Pending` exactly once: it is reached from the entry, whose out-state is
fixed before the worklist starts, and a predecessor's out-state landing
re-enqueues it.

A malformed CFG is owned one layer up, and reported there once: a
terminator naming a block the function does not declare is
`UNKNOWN_BRANCH_TARGET`, and a repeated block id is
`DUPLICATE_BLOCK_ID`. This pass simply never reaches past such an edge,
and invents no ownership state for it.

Joins take the *union* of both predecessors' keys, so a place touched on
only one side still joins to the absorbing disagreement state. Together
with seeding the worklist in declaration order, that makes the result
independent of predecessor discovery order, block vector order and
`HashMap` order alike.

Termination needs no pass limit and has none. Every transfer either
records a fixed state for a place or -- when its own guard fails on a
worse in-state -- records nothing and leaves the joined state standing,
so a worse in-state can only ever produce an equal-or-worse out-state.
That makes the transfer monotone in the order `Full`/`Empty` below the
absorbing `Maybe`; the tracked place set is bounded by the places the
instructions actually name, and each one's state can rise at most twice.

## Runtime

The interpreter's own `Value` enum gains two tombstone variants,
`Moved` and `Dropped`, occupying exactly the field slot a `PlaceRead {
mode: Transfer }` (or a recursive structural destruction) just emptied
-- reading either is a structured runtime error, an independent
backstop `nir::verify` already statically guarantees is unreachable for
verified NIR. A `resource`'s own fields are never held inline (they
live in the shared `ResourceTable`'s own per-record `fields: Vec<Value>`);
a plain, non-resource `Record`/`Variant`'s own fields are held directly,
by value. `RecordCreate`/`VariantCreate` transfer (not merely clone)
every affine field/payload argument, recursing into a nested
`Record`/`Variant` value too -- otherwise a source `ValueId` whose value
was consumed into a fresh aggregate would still look like a live,
undestroyed obligation of the same frame.

### Runtime type arguments

A runtime `Record`/`Variant` carries its own **concrete type arguments**
alongside its `ItemId`:

```rust
Value::Record  { item, type_args: Vec<Ty>, fields }
Value::Variant { item, type_args: Vec<Ty>, case, payload }
```

They are load-bearing, not decoration: `item` alone cannot say what a
value owns, because `Box`'s own declared field type is the symbolic
`Ty::Param(T)`, which is affine for *no* instantiation at all. Asking
the declaration therefore answers "owns nothing" for a `Box[File]` that
plainly owns a resource -- which skipped it during structural
destruction, and made `drop` of a `Maybe[File]` fail outright at run
time after `check` had accepted it.

They are never inferred from the payload values either: a moved-out
field is a tombstone with no type left to read, so a value that has
already given up a field could no longer say what it is.

Every path that rebuilds an aggregate carries them across unchanged --
place traversal, reconstruction after a partial move, `StorePlace`,
ownership transfer, and the call/return boundary. Affinity and
destruction then resolve field and payload types through the value's own
instantiation: retrieve the declaration's parameter list, require exact
arity, build a complete substitution, substitute, and decide from the
result. Missing metadata or an arity disagreement is a structured,
deterministic interpreter error -- never an empty or partial
substitution, which would skip exactly the fields whose types went
missing.

### `StorePlace` is a transfer

Reinitializing a place *transfers* ownership into it. The interpreter
runs three strictly ordered phases, so the operation is transactional:

1. **Validate**, mutating nothing: the destination chain must be
   reachable and its final field provably empty, and every resource
   reachable through the source must be a live, current, owning handle.
   Checking the source's whole tree up front is what makes a nested
   aggregate's transfer all-or-nothing -- bumping the first child's
   generation and then discovering the second is stale would leave it
   half-transferred with no way back.
2. **Transfer**: the only phase that bumps a generation, and it cannot
   fail, because phase 1 already proved every child transferable.
3. **Commit**: write the transferred value into the place, and tombstone
   the source -- both by its exact id and by the storage it
   canonicalizes to, since a `Load` result and the slot it read share
   one identity.

A failure in phase 1 therefore leaves the source valid, the destination
unchanged, and no generation bumped; the refusal is deterministic.
Without the transfer, the source and the destination both held an
apparently-current owner handle for the same resource -- two live owners
of one identity.

Storing a value into a place rooted at that very value is rejected in
both stages: `V0093` statically, and at run time for the same shape
reached through a `Load` of the destination's own slot.

### Mixed-container traversal

Because those two storage disciplines differ, a place walking a chain
that *alternates* between them needs one explicit result shape rather
than an `Option` doing double duty:

```rust
struct AccessResult {
    extracted: Value,   // what the place's final step yielded
    container: Value,   // what must now be written back where it came from
}
```

`container` is always present and always meaningful. For an inline
`Record` it is the rebuilt record; for a `Resource` it is that same
handle, unchanged, because the mutation already happened directly in the
resource table. An `Option` whose `None` meant both "already mutated in
place" and "this container's ownership disappeared" is exactly what made
a `record` -> `resource` chain lose the whole intermediate handle.

Three separate walks, with three separate guarantees:

- **Observing** (`observe_projections`) mutates nothing at any depth: no
  ancestor is tombstoned, no inline record is rebuilt, no resource field
  is written. Cloning an intermediate is safe because a `Value::Resource`
  carries only a cheap `(id, generation, role)` handle, and observing
  never bumps a generation.
- **Transferring** (`take_projections`) tombstones only the *final*
  selected place. Every intermediate inline record is handed back
  rebuilt, and every intermediate resource handle stays in its owner's
  field.
- **Reinitializing** (`store_projections`) writes only the final place.

An intermediate resource field goes back through a dedicated internal
`restore_field`, deliberately **distinct** from the user-facing
`set_field` that `StorePlace` lowers to: `set_field` correctly refuses
to overwrite a field that still owns a live value, which is right for a
reinitialization and wrong for putting back the very container the walk
just read *through*. Conflating them is what made a `resource` ->
`record` chain report a bogus live-overwrite error. Every step recurses
on a clone and writes back only once the recursion succeeded, so a
failure deeper in the chain leaves every container on the path exactly
as it was rather than half-mutated.

Place roots are canonicalized through the frame's own `Load`/slot map
before any read or write, exactly as `nir::verify` canonicalizes them: a
`mutable` binding reloads its whole current value as a fresh `ValueId`
every time a place projects into it, so tombstoning a field in the
load's own cached copy -- rather than in the slot every later load reads
back from -- would lose the mutation entirely.

### Structural destruction at runtime

One operation covers every transitively affine runtime value: a
`Resource`, a `Record` containing affine fields, a `Variant` whose
active case carries an affine payload, an instantiated generic
aggregate, and any nesting of those. It visits live affine fields in
reverse declaration order, recurses into nested affine aggregates, skips
`Moved`/`Dropped` tombstones (so a child NIR already destroyed
individually is never destroyed twice), destroys only the active variant
case, and destroys a declared `resource`'s own outer identity *after*
its remaining children. Each child is tombstoned `Dropped` before its
recursive destruction rather than after, so a failure partway through
cannot leave one reachable for a second attempt. Double drop is rejected
deterministically by the resource table itself. Rust's own `Drop` is
never involved.

Silently ignoring an affine `Value::Record` -- as an earlier draft did
-- leaked every resource a variant's record payload carried.

## Deferred actions capture exact places

`defer inspect(session.input)` protects `session.input` **itself**, not
the whole `session` root it is reached through. `CheckedDeferPlan`
retains, per argument and in declaration order, the exact stable place,
its resolved substituted type, its `Observe`/`Transfer` mode, the
resolved callee, and this `defer`'s own registration order; `nir::lower`
independently re-resolves each argument's place and rejects a
disagreement rather than trusting the plan.

At registration, an observing `defer` protects the exact captured place,
and a consuming one transfers it immediately. An unaffected sibling
therefore stays freely movable:

```napitia
defer inspect(session.input)
value output = session.output   // valid: an unaffected sibling
```

while the parent as a whole does not -- moving or dropping `session`
there is rejected (`U0004`), because LIFO replay runs that deferred call
*after* the destruction and would hand it a field the destruction
already consumed. That rejection reports the real reason rather than
reusing the partial-move diagnostic: the field is entirely intact, and
the parent becomes whole again the moment the defer's own scope ends.

At cleanup, the deferred call is invoked exactly once, its exact-place
protection is released, LIFO order is preserved, and the remaining
structural cleanup runs after it.

## Explicit `drop`

`drop <expr>` accepts any transitively affine operand, not only a
declared `resource`: a record or variant that merely contains one owns
real resources too, and `drop` on it performs exactly the structural
destruction the compiler already applies at its owning scope's exit,
named explicitly. `drop <place>` destroys one structural field in its
own right -- the field becomes `Dropped`, not `Moved`, so a second
`drop` of it is a real double drop (`U0003`) and a later use is a
use-after-drop (`U0002`). A primitive, `str`, or ordinary non-affine
aggregate is still `T0061`: there is no owned state there to destroy.

## Non-goals

Unchanged from `rfcs/0011`: no native heap allocation, no general
borrowing, no lifetime inference, no shared ownership, no garbage
collection, no thread safety guarantees, no FFI cleanup.

Out of scope for this milestone specifically, each a *source-level*
restriction rather than an accepted program that misbehaves:

- record-destructuring pattern syntax (not introduced; none existed
  before this milestone either);
- generic parameters on a `resource` declaration (`resource Cell[T]` is
  a parse error -- `record` and `variant` only);
- resource-affine generic *function* instantiation, rejected with
  `T0068` rather than supported, because a generic function body is
  checked once symbolically and shared by every instantiation, so
  nothing would track a bare `T`-typed value's ownership if some call
  site substituted an affine type for it;
- a resource-typed `if`/`match`/`handle` used in a consuming position
  other than `return`, rejected with `U0008` because `nir::lower` has no
  per-branch sink for it;
- a `defer` whose callee is generic, fallible, or returns a resource,
  rejected with `T0066`;
- a *declared field or payload* whose type reaches the same generic
  declaration again, even with strictly smaller arguments
  (`variant Holder { Carry(Box[Box[File]]) }`), rejected as an infinite
  layout by `typeck::cycles` (`T0020`). That check is keyed by
  declaration rather than by instantiation, which is sound -- it rejects
  every genuinely infinite layout -- but conservative: it also rejects
  this finite, shrinking one. Proving termination for a shrinking
  recurrence needs a size-decrease argument this milestone does not
  implement, and guessing it wrong would accept a genuinely infinite
  layout. The same nesting is accepted wherever it is *not* a declared
  field type, e.g. as a local's own type.
