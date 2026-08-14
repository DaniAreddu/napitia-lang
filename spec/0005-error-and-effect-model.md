# Spec 0005: Error and Effect Model

- Status: Design direction only. Not implemented in Alpha 0.1.

Alpha 0.1's checked "failure modes" are limited to compiler diagnostics
(lexical/syntax/name-resolution/type errors) and two runtime conditions the
NIR interpreter detects directly: division by zero and invalid internal
operations (`spec/0006-napitia-ir.md`). There is no `Result<T, E>`,
`Option<T>`, or effect syntax implemented yet. This spec records the
intended long-term model.

## Implemented features

- The NIR interpreter reports division-by-zero and malformed-instruction
  conditions as structured `InterpreterError` values rather than
  panicking or invoking undefined behavior (`spec/0006`). This is the only
  piece of the eventual error model that exists today, and it exists at
  the interpreter layer, not the language-surface layer.

## Accepted design direction

### `Result<T, E>` instead of unchecked exceptions

A function that can fail returns `Result<T, E>` (an ordinary generic enum,
once generics exist — see `spec/0003`). There is no `throw`/`catch`
control-flow construct and no unchecked exception type that can propagate
silently through a call it wasn't declared to cross. A `?`-style
propagation operator for `Result` (and `Option`) is intended, so early
returns on failure don't require verbose manual matching every call.

### `Option<T>` instead of `null`

Absence is `Option<T>`, matching RFC 0001's ban on `null`. `Option` and
`Result` share the same generic-enum machinery; there is deliberately no
special "nullable pointer" representation distinct from the ordinary enum
lowering.

### Typed effects

Beyond simple success/failure, some function behaviors are tracked as
*effects*: an annotation on a function's type (parallel to, and composed
with, its return type) describing what kind of ambient capability the
function uses — for example, performing I/O, panicking, or blocking.
Effects are meant to let calling code (and the compiler) reason about
"can this function block?" or "can this function fail?" the same way it
reasons about types, rather than that information living only in
documentation. Full design is deferred to
`rfcs/0003-extensible-effects.md`; this spec only commits to effects being
part of a function's type, not a separate ad hoc annotation system.

### Panics remain for true invariant violations only

A small set of conditions (integer overflow in checked arithmetic,
out-of-bounds indexing, an internal compiler invariant failing) are
intended to remain unrecoverable panics rather than `Result` values,
because forcing every call site to handle "the compiler itself is wrong"
or "you indexed past the end of an array with a literal you controlled"
adds ceremony without adding safety the type system could have caught
instead. Where the type system *can* catch a failure mode statically
(e.g. calling with the wrong argument count), it does, and no runtime
Result is needed at all.

## Unresolved research questions

- Whether effects are checked structurally (any function that performs the
  effect must declare it, and it propagates through callers automatically,
  Koka/OCaml-effects style) or nominally (an explicit, closed list of
  effect names a function opts into). This is the central open question
  `rfcs/0003` exists to resolve.
- Whether `panic` itself should be a trackable effect (so "this function
  can panic" is visible in its type) or remain untracked, matching most
  mainstream statically typed languages.
- How effects compose with the ownership/region model in `spec/0004` —
  e.g. whether an async/blocking effect can ever be safely combined with
  holding a region-scoped borrow across a suspension point.

## Non-goals

- No unchecked/runtime-only exception hierarchy of the Java `RuntimeException`
  or C++ `throw` variety, ever, as the primary error-propagation mechanism.
- No silent error swallowing: there is no equivalent of returning a sentinel
  value (`-1`, `null`) to mean failure anywhere in the standard model —
  every fallible operation's failure is visible in its return type.
