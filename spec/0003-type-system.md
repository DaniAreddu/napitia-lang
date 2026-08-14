# Spec 0003: Type System

- Status: Partially implemented (Alpha 0.1) — primitive types and local
  inference only.

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

Within a function body, `let`/`var` bindings without an explicit `: Type`
annotation have their type inferred from the initializer expression via
unification. Inference is purely local: no cross-function or whole-program
inference happens in this milestone.

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
- **Immutable-binding enforcement**: assigning to a `let` binding (as
  opposed to `var`) after its initialization is a checked error, not a
  runtime condition.
- **Numeric operator validation**: binary arithmetic operators (`+ - * / %`)
  and bitwise operators (`& | ^ << >>`) require both operands to unify with
  the same numeric type (integer types for bitwise/shift; integer or float
  for arithmetic). Comparison and equality operators require both operands
  to unify with the same type and produce `bool`. Logical `&&`/`||` require
  both operands to be `bool`.

### Diagnostics

Type errors report: the two types that failed to unify, the span of the
expression that introduced each side of the conflict where available, and
(for argument/arity mismatches) the declared function signature being
called against.

## Explicit non-goals of this milestone

- **No implicit narrowing conversions.** `i64` is never implicitly used
  where `i32` is expected, or vice versa, even when the literal value
  would fit. Narrowing requires an explicit `as` cast (see `spec/0002`),
  and `as` casts that can lose information are accepted syntax but are
  themselves a deliberate, visible operation, never inserted by the
  checker.
- **No `null`.** There is no type-system-level "nullable" flag on any
  type; absence is represented by `Option<T>` once generics exist (see
  "Accepted design direction" below) — it is not part of the primitive
  type system itself.

## Accepted design direction

The internal type representation is deliberately structured so the
following can be added without a redesign of the checker's core
unification algorithm:

- **Generic types**: type parameters with trait bounds
  (`fn max<T: Ord>(a: T, b: T) -> T`). The type representation already
  distinguishes a concrete `Type` from a `TypeVar`; a generic parameter is
  a `TypeVar` that is universally quantified at a function/struct boundary
  instead of being solved away by the end of checking that item.
- **Traits**: as constraints on type variables during unification, not as
  a runtime vtable mechanism at this layer.
- **`Option<T>`** and **`Result<T, E>`**: as ordinary generic enums defined
  in a future standard library, once generic enums are checkable. The
  `never` type and the existing enum-lowering path in HIR/NIR are meant to
  make `Result`'s "early return on error" pattern implementable without
  new compiler primitives.
- **Effects** (`spec/0005`): tracked as an additional annotation on
  function types, parallel to but distinct from the return type.
- **Ownership states and region variables** (`spec/0004`,
  `rfcs/0002`): tracked as metadata attached to a binding's type
  during/after checking, not as a separate pass bolted on afterward.

None of the above is implemented in Alpha 0.1. Representations exist where
they make the eventual extension straightforward, but nothing is
special-cased or faked to look implemented.

## Unresolved research questions

- Whether trait bounds should support associated types/const generics
  from the start, or be added later without breaking existing bounds.
- Whether integer literal defaulting to `i64` is the right default, versus
  requiring an explicit type in more contexts (Rust-style default vs.
  stricter-than-Rust).
- How much of Hindley-Milner-style let-polymorphism (if any) applies inside
  a function body, versus every binding being fully monomorphic once
  solved — the current implementation treats every local binding as
  monomorphic.

## Non-goals

- No structural/duck typing. All type compatibility in Napitia is nominal
  (by declared type identity), matching the readability and tooling goals
  in RFC 0001.
