# Spec 0003: Type System

- Status: Partially implemented (Alpha 0.1.5) — primitive types, local
  inference, nominal record/variant aggregates with pattern matching
  (Alpha 0.1.1), unconstrained generic type parameters on
  functions/records/variants (Alpha 0.1.4, `rfcs/0008`), and capability
  protocols (Alpha 0.1.5, `rfcs/0009`).

## Implemented features

### Primitive types

```text
i8 i16 i32 i64 isize
u8 u16 u32 u64 usize
f32 f64
bool
char
str
unit
never
```

`unit` is the type of an expression evaluated only for its side effects
(an empty block, a function with no `-> Type`). `never` is the type of an
expression that provably never produces a value (e.g. an unconditional
`return`); it unifies with anything, since control never reaches the point
where the mismatch would matter.

### Function signatures

Function parameter types and return types must be written explicitly.
Napitia does not infer function signatures from call sites or bodies —
only expression-local inference happens inside a body.

### Local type inference

Within a function body, `value`/`mutable` bindings without an explicit
`: Type` annotation have their type inferred from the initializer
expression via unification. Inference is purely local: no cross-function
or whole-program inference happens in this milestone.

### Type variables and unification

The checker assigns a fresh type variable to each un-annotated binding and
integer/float literal, then unifies variables against concrete types as
constraints are discovered (assignment, argument passing, operator use,
return statements). Unification failure produces a type-mismatch
diagnostic naming both sides.

### Integer and float literal inference

An integer literal has no fixed type until it is unified with something:
an explicit annotation, a parameter type at a call site, a peer operand in
a binary expression, or (failing all of those) a default of `i64`. The
same applies to float literals defaulting to `f64`. This mirrors "untyped
constant" inference in other statically typed languages with literal
inference, without introducing a separate compile-time-only numeric type.

### Checking rules implemented

- **Boolean conditions**: the condition of `if`/`while` must unify with
  `bool`.
- **Call arguments**: each argument must unify with the corresponding
  declared parameter type; arity mismatches are reported as their own
  diagnostic, distinct from a type mismatch.
- **Return type**: every `return` expression (and a function's tail
  expression, if any) must unify with the function's declared return type.
- **Assignment compatibility**: the right-hand side of `=` (and compound
  assignment operators) must unify with the binding's type. Compound
  assignment additionally requires the binding's type to support the
  underlying operator (see below).
- **Immutable-binding enforcement**: assigning to a `value` binding (as
  opposed to `mutable`) after its initialization is a checked error, not a
  runtime condition.
- **Numeric operator validation**: binary arithmetic operators (`+ - * / %`)
  and bitwise operators (`& | ^ << >>`) require both operands to unify with
  the same numeric type (integer types for bitwise/shift; integer or float
  for arithmetic). Comparison and equality operators require both operands
  to unify with the same type and produce `bool`. Logical `&&`/`||` require
  both operands to be `bool`. Equality (`==`/`!=`) on a record/variant
  value is rejected outright (see "Aggregate equality" below) rather than
  being partially implemented.

### Records and variants (Alpha 0.1.1)

- **Nominal identity**: two `record`/`variant` declarations are distinct
  types even with identical fields/cases — comparison is always by
  declaration identity (`ItemId`), never by name or structure
  (`rfcs/0001`).
- **Record construction** (`TypeName { field: expr, ... }`): the type
  name must resolve to a declared record; every field must appear
  exactly once; each field's initializer must unify with that field's
  declared type. Field name/presence checking happens during name
  resolution (it needs no inference); the type-compatibility check
  happens here.
- **Field access** (`base.field`): the base's inferred type must be a
  declared record, and the field must exist on it — field access on a
  non-record type, or a field not declared on that record, is a checked
  error. **Field mutation** (`base.field = expr`) is parsed as an
  ordinary assignment but is a dedicated, checked error in this
  milestone (there is no lowering for it yet).
- **Variant constructors** (`Variant.Case(...)`, or an unqualified case
  name when unambiguous): payload arity and each payload expression's
  type are checked against the case's declared payload types; a
  payload-less case referenced bare (no call) is itself a complete
  value.
- **Aggregate equality**: `==`/`!=` between two record or variant
  values is rejected outright, not partially implemented — deciding
  what "equal" means once a payload can itself be a record is exactly
  the kind of scope this milestone avoids taking on early.
- **Infinite aggregate layout**: since Napitia has no indirection/
  ownership feature yet (`rfcs/0002`), a direct or indirect cycle in the
  field/payload graph (`record Node { next: Node }`, or the indirect
  `First -> Second -> First`) is rejected before any function body is
  checked, via a deterministic (declaration-order, not hash-order)
  dependency-graph cycle check.

### Generics (Alpha 0.1.4)

- **Symbolic type parameters**: `func`/`record`/`variant` may declare
  their own `[T, ...]`; each parameter gets a stable, per-declaration
  identity (`TypeParamId`) — two declarations spelling their own
  parameter the same way (`first[T]`/`second[T]`) never share identity,
  and a name from one declaration has no meaning inside another that did
  not itself declare it.
- **Nominal applied types**: `Box[i64]` is a distinct type from `Box[str]`
  and from `sales.Box[i64]` when `sales.Box` is a different declaration —
  comparison is nominal on the declaration plus structural on the
  argument list, matching `record`/`variant`'s own identity contract
  above. There is no raw (zero-argument) reference to a generic
  declaration: `value x: Box;` is a checked error, and so is applying
  type arguments to a declaration that is not generic.
- **Checked once, symbolically**: a generic declaration's own body is
  type-checked exactly once, treating its own parameters as opaque and
  rigid — never re-checked per instantiation. Only the operations
  provably safe for *any* type are permitted on an unconstrained
  parameter: passing, returning, binding, assignment, construction, and
  extraction. Equality/inequality, ordering, arithmetic, bitwise
  operators, logical use (including as an `if`/`while` condition), field
  access, and calling are all rejected symbolically, before any
  instantiation exists, with a dedicated diagnostic distinct from an
  ordinary "wrong concrete type" mismatch.
- **Inference**: a call/constructor's type arguments may be given
  explicitly (`identity[i64](42)`) or inferred from argument types
  (`identity(42)`) via the same unification the rest of this spec
  describes, extended to unify two applied types when they name the same
  declaration and have matching arity (recursing into corresponding
  arguments). Record/variant *construction* and a bare unit-case
  reference always require explicit type arguments (there is nothing to
  infer construction arguments from); a function call and a variant
  constructor call both support inference. Conflicting inferred
  arguments and an argument that cannot be inferred at all are each their
  own diagnostic.
- **Instantiated field/payload types**: field access, constructor payload
  types, and match-arm binding types all use the type *after*
  substituting a value's own concrete type arguments — never the
  declaration's raw symbolic shape.
- **Infinite generic layouts**: the existing infinite-aggregate-layout
  check (below) is extended to detect a cycle mediated through a generic
  parameter (`record Box[T] { value: T } record Node { next: Box[Node] }`
  is rejected, even though `Box[T]` alone is not cyclic), and an
  ever-growing (never-repeating) instantiation chain is rejected once it
  exceeds a shared depth budget.

See `rfcs/0008-canonical-generics.md` for the complete design, the
diagnostic codes, and the current honest limitations (no native-code
specialization). A generic type parameter itself still has no inline
bound syntax (there is no `[T: Comparable]`) — as of Alpha 0.1.5, the
closest equivalent is a capability requirement on the *function*
(`uses Comparable[T]`, see "Protocols and capabilities", below), checked
independently of unification rather than as a constraint attached to `T`
itself.

### Protocols and capabilities (Alpha 0.1.5)

- **Explicit, no `Self`**: a `protocol` declares its own type parameters
  explicitly (`protocol Equal[T] { func equal(left: T, right: T) -> bool;
  }`); there is no implicit receiver and no `Self` type anywhere in this
  design. A method is invoked only via an explicit
  `Protocol[Args].method(...)` expression — never `a.equal(b)`, and never
  through operator sugar (`==` keeps its own pre-existing built-in
  meaning for primitives, entirely independent of any user-declared
  `Equal`-shaped protocol).
- **Canonical requirement identity**: `CapabilityRequirement { protocol:
  ItemId, arguments: Vec<Ty> }` identifies a `uses` requirement the same
  way `GenericInstanceKey` identifies a generic instantiation (`rfcs/0008`)
  — nominal on the declaring protocol's `ItemId` (never re-derived from a
  name, so an import alias never changes identity), structural on its
  arguments.
- **Evidence, not a vtable**: every requirement resolves to exactly one
  `Evidence` value, computed once at compile time by a dedicated
  capability solver (`typeck::capability`) — `Evidence::Extension` (a
  concrete `extend`, plus its own nested requirements resolved the same
  way) or `Evidence::Forwarded(index)` (reuse the *currently executing*
  function's own requirement at that index unchanged). This is dictionary
  passing, not a runtime vtable/trait-object mechanism and not template
  instantiation: one canonical extend implementation exists regardless of
  how many call sites resolve to it, and no runtime type inspection is
  involved.
- **Authority and coherence**: an `extend` is only legal in the module
  that owns its protocol or the outermost nominal aggregate of the
  protocol's first type argument (a primitive first argument requires the
  protocol's own module); two extends that could both match the same
  concrete instantiation are rejected as an overlap, checked by a sound
  bidirectional structural unifier over each extend's own head, entirely
  independent of any call site. This unifier's own recursion is bounded
  by a real depth *and* work-step budget, each independently tracked; a
  pair it cannot decide within budget is reported as `T0047` and both
  extends involved are excluded from the solver, never silently treated
  as non-overlapping.
- **Every extend parameter is head-determined**: an extend's own type
  parameter must occur somewhere inside its protocol's own type
  arguments (`extend[T] Equal[i64] uses Other[T]` declares a `T` nothing
  could ever bind, since `T` never occurs in `Equal[i64]`) — rejected as
  `T0046`, one diagnostic per unconstrained parameter.
- **Exact forwarding only**: a still-generic function's own `uses`
  requirement can only be satisfied by forwarding an identical caller
  requirement, or by a concrete extension once every type involved is
  fully concrete — never by deriving, weakening, or combining a
  requirement symbolically. `T0039`/`T0040` report a missing/ambiguous
  capability; `T0041`/`T0042`/`T0043` bound cyclic/too-deep/too-expensive
  resolution.
- **Entry-point restriction**: the executable entry function cannot
  declare a `uses` requirement (`T0045`) — it has no caller to receive
  evidence from. A concrete protocol call inside its own body remains
  legal without any `uses` clause.

See `rfcs/0009-capability-protocols.md` for the complete design
(including the syntax, the full diagnostic list, and honest limitations
such as no supertraits/default methods and no first-class protocol
values) and `spec/0006-napitia-ir.md` for the NIR-level representation of
protocols, extends, and evidence.

### `match` and pattern matching (Alpha 0.1.1)

`match` is a real expression: the scrutinee is checked exactly once,
each pattern is checked against the scrutinee's type (a pattern whose
shape is incompatible with that type — e.g. a variant pattern against
a `bool` scrutinee — is a checked error), and pattern-bound locals
receive their *exact* resolved payload type, never an approximation —
for a generic variant, this is the type *after* substituting the
scrutinee's own concrete type arguments (`Maybe[bool]`'s `Some` payload
is `bool`), not the declaration's raw `T` (Alpha 0.1.4, `rfcs/0008`).
Supported pattern forms: wildcard (`_`), an immutable binding, a
boolean/integer/string/char literal, a variant case without payload, a
variant case with positional sub-patterns, and nested variant patterns
(a case's payload position may itself be matched by a variant
pattern). A pattern-bound name may not be duplicated within one
pattern.

- **Exhaustiveness**: checked with a pattern-matrix usefulness
  algorithm (Maranget-style, specialized to this closed pattern
  grammar), not a fragile "every case name appears once" check — it
  correctly handles nested variant patterns, a wildcard/binding arm
  covering the remaining space, and an open literal domain (`int`/
  `str`/`char`) always requiring a catch-all (an integer match can
  never be proven exhaustive by literals alone). A non-exhaustive match
  is a checked error carrying a concrete example of a missing pattern
  (e.g. `LookupResult.Missing`, or a nested `Outer.A(Inner.Y)`), never
  just "not exhaustive" with no witness.
- **Unreachable arms**: an arm whose pattern is not "useful" against
  every earlier arm (i.e. it can never match anything an earlier arm
  didn't already match) is a checked error, in source order; its body
  is still checked for its own independent diagnostics.
- **Result type**: every reachable arm's body participates in the same
  `never`-aware join `if`/`else` branches already use (see below); a
  diverging scrutinee makes the whole `match` `never` without
  analyzing exhaustiveness at all (no arm is ever reachable).
- **Work budget**: pattern analysis is capped by a hard recursive-step
  budget per `match`, so pathologically nested patterns are a checked
  error ("pattern analysis exceeded its work budget"), never an
  unbounded hang or stack overflow.

### Control-flow divergence (`never`)

`never` is not merely "unifies with anything" in isolation — it is
propagated according to exact rules so that which branch of a construct
diverges never changes the construct's resulting type or runtime
behavior:

- **Strict evaluation propagates `never`.** Any expression that always
  evaluates a given subexpression takes on type `never` if that
  subexpression is `never`: unary operators, arithmetic/comparison/
  bitwise/shift binary operators (either operand), function calls (any
  argument), and assignment (the right-hand side).
- **Short-circuit operators are the one exception.** `&&`/`||` only
  always evaluate their left operand; a `never` left operand makes the
  whole expression `never`, but a `never` right operand does not, since
  it may never execute.
- **`if`/`else if` joins are symmetric.** The resulting type is:
  `never` join `never` = `never`; `never` join `T` = `T`; `T` join
  `never` = `T`; `T` join `U` = `unify(T, U)`. This is applied
  recursively through an `else if` chain. Only the non-diverging branch
  (if any) determines the join's type — a partially diverging `if` is
  never itself typed `never`, since one branch does still produce a
  value. If the *condition* itself is `never`, the whole `if` is
  `never` regardless of the branches (which are still checked for
  independent diagnostics, but do not contribute to the result type).
- **An `if` with no `else` is always `unit`-typed**, whether or not the
  `then` branch diverges — there is no implicit `else` branch that
  could produce a different type.
- **`while` and a binding's initializer turn divergence into statement
  divergence**: a `never`-typed condition or initializer means the
  enclosing `while`/binding statement itself diverges, not that some
  other expression silently receives type `never`.
- Every relevant divergent expression's resolved type is recorded as
  `Ty::Never` and can be inspected directly via `expr_types` — this is
  exercised by tests, not just asserted by the diagnostics a divergent
  program does or doesn't produce.

### Diagnostics

Type errors report the two types that failed to unify and a single span
for the overall expression where the mismatch was detected (a compound
assignment's operator, an `if`/`else` branch, a call's argument list) —
not a separate span per operand naming where each side's type came from;
arity-mismatch diagnostics additionally point at the declared function
signature being called against.

## Explicit non-goals of this milestone

- **No implicit narrowing conversions.** `i64` is never implicitly used
  where `i32` is expected, or vice versa, even when the literal value
  would fit. Narrowing requires an explicit `as` cast (see `spec/0002`),
  and `as` casts that can lose information are accepted syntax but are
  themselves a deliberate, visible operation, never inserted by the
  checker.
- **No `null`.** There is no type-system-level "nullable" flag on any
  type; absence is represented by a Napitia-native `variant` type
  (provisionally `Maybe[T]`, see `spec/0005`) — now expressible directly
  as an ordinary generic `variant` (Alpha 0.1.4, `rfcs/0008`), though no
  standard-library `Maybe[T]` is bundled yet — it is not part of the
  primitive type system itself, and deliberately not a copy of another
  language's type of that name (`rfcs/0004`).

## Accepted design direction

The internal type representation is deliberately structured so the
following can be added without a redesign of the checker's core
unification algorithm:

- **Inline bound syntax on a generic type parameter**
  (`func max[T: Comparable](a: T, b: T) -> T`). Alpha 0.1.5 implements the
  underlying capability requirement this bullet was originally describing
  — `func max[T](a: T, b: T) -> T uses Comparable[T]`
  (`rfcs/0009`) — as a `uses` clause on the *function*, checked by a
  dedicated capability solver independent of unification, rather than as
  a constraint attached to `T` itself. Only the `[T: Comparable]` inline-
  bound *spelling* remains unimplemented; a type parameter with no
  matching `uses` requirement is still opaque and rigid exactly as
  `rfcs/0008` describes.
- **A standard-library `Maybe[T]` absence type**: the language itself
  can express `variant Maybe[T] { Some(T), None }` directly as of
  Alpha 0.1.4 (`rfcs/0008`); what remains future work is bundling one in
  an actual standard library rather than every program declaring its
  own. Failure, by contrast, is intended to be modeled primarily through
  `raises` clauses rather than a generic wrapper type; the `never` type
  and the existing `variant`-lowering path in HIR/NIR are meant to make
  early-return-on-error patterns implementable without new compiler
  primitives regardless of which representation `raises` ultimately
  compiles to.
- **Effects** (`spec/0005`): tracked as an additional annotation on
  function types, parallel to but distinct from the return type.
- **Ownership states and region variables** (`spec/0004`,
  `rfcs/0002`): tracked as metadata attached to a binding's type
  during/after checking, not as a separate pass bolted on afterward.

None of the above is implemented in Alpha 0.1. Representations exist where
they make the eventual extension straightforward, but nothing is
special-cased or faked to look implemented.

## Unresolved research questions

- Whether an inline `[T: Protocol]` bound spelling should ever be added
  alongside `uses Protocol[T]` (`rfcs/0009`), and if so whether it should
  support associated types/const generics from the start or be added
  later without breaking existing capability requirements.
- Whether integer literal defaulting to `i64` is the right default, versus
  requiring an explicit type in more contexts.
- How much Hindley-Milner-style binding-local polymorphism (if any)
  applies inside a function body, versus every binding being fully
  monomorphic once solved — the current implementation treats every local
  binding as monomorphic.

## Non-goals

- No structural/duck typing. All type compatibility in Napitia is nominal
  (by declared type identity), matching the readability and tooling goals
  in RFC 0001.
