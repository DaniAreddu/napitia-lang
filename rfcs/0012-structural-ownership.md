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

The one case this milestone does not support: a **generic function**
whose own body is checked once, symbolically, and shared unchanged by
every instantiation (`rfcs/0008`) -- nothing would ever track a bare
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
inspect_session(session) // U0014: whole aggregate partially moved
drop session              // valid: drops only the remaining owned fields
```

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

**Known limitation**: a case matched through a wildcard (`_`) rather
than a binding pattern, whose payload is itself affine, is not
independently diagnosed or separately cleaned up this milestone --
covering that fully requires per-case structural cleanup planning
(knowing, for a case never bound at all, which of its own payload
positions are affine and destroying them unconditionally) that is
deferred to a later milestone.

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
only lists separately. `nir::verify` independently re-validates every
place it sees (unknown field owner, out-of-range field index,
projection through the wrong or a non-aggregate type, move of a
non-affine place -- `V0083`-`V0086`) and independently re-derives
per-place move/reinitialization state (`V0087`/`V0088`) via the
identical reachable-union worklist shape `V0082` already uses, keyed by
`Place<ValueId>` instead of a bare root, and canonicalized through the
same `Load`-origin unification `nir::verify`'s whole-value pass already
needs for a `mutable` local reloaded more than once.

## Runtime

The interpreter's own `Value` enum gains two tombstone variants,
`Moved` and `Dropped`, occupying exactly the field slot a `PlaceRead {
mode: Transfer }` (or a recursive structural destruction) just emptied
-- reading either is a structured runtime error, an independent
backstop `nir::verify` already statically guarantees is unreachable for
verified NIR. A `resource`'s own fields are never held inline (they
live in the shared `ResourceTable`'s own per-record `fields: Vec<Value>`,
mutated in place through `observe_field`/`take_field`/`set_field`); a
plain, non-resource `Record`/`Variant`'s own fields are held directly,
by value, and a place access through one is rebuilt and written back
into the SSA value that held it. `RecordCreate`/`VariantCreate` transfer
(not merely clone) every affine field/payload argument, recursing into
a nested `Record`/`Variant` value too -- otherwise a source `ValueId`
whose value was consumed into a fresh aggregate would still look like a
live, undestroyed obligation of the same frame.

## Non-goals

Unchanged from `rfcs/0011`: no native heap allocation, no general
borrowing, no lifetime inference, no shared ownership, no garbage
collection, no thread safety guarantees, no FFI cleanup. Also out of
scope for this milestone specifically: record-destructuring pattern
syntax (not introduced), per-case cleanup of an affine payload
discarded through a wildcard pattern (see "Patterns" above), and
resource-affine generic *function* instantiation (rejected with
`T0068` rather than supported).
