# Spec 0005: Error and Effect Model

- Status: Design direction only. Not implemented in Alpha 0.1.

Alpha 0.1's checked "failure modes" are limited to compiler diagnostics
(lexical/syntax/name-resolution/type errors) and two runtime conditions the
NIR interpreter detects directly: division by zero and invalid internal
operations (`spec/0006-napitia-ir.md`). The `uses`/`raises` clauses parsed
in `spec/0002-syntax.md` are not checked against any real effect/error
model in this milestone — declaring either non-empty is itself a checked,
reported error, rather than being silently accepted and ignored. This
spec records the intended long-term model, using the
provisional vocabulary from `rfcs/0004-language-independence.md`. An
earlier version of this spec named `Result<T, E>` and `Option<T>`
directly — those are Rust's own standard-library type names, not Napitia
concepts, and RFC 0004 corrects that.

## Implemented features

- The NIR interpreter reports division-by-zero and malformed-instruction
  conditions as structured `InterpreterError` values rather than
  panicking or invoking undefined behavior (`spec/0006`). This is the only
  piece of the eventual error model that exists today, and it exists at
  the interpreter layer, not the language-surface layer.

## Accepted design direction

### `raises` instead of unchecked exceptions

A function that can fail declares the error cases it can produce in a
`raises` clause on its signature (`spec/0002`), rather than returning a
generic wrapper type as its primary interface. There is no
`throw`/`catch` control-flow construct and no unchecked exception type
that can propagate silently through a call it wasn't declared to cross —
`raises` makes "this call can fail, and how" visible at the call site's
signature, the same way a parameter list makes arguments visible. A
postfix `?` operator (parsed in `spec/0002`; using it is a checked,
reported error in this milestone rather than being given behavior)
propagates a raised error to the caller without manual matching at every
call.

Whether `raises` alone is sufficient, or a value-level type is also
needed for cases where a not-yet-handled failure must be stored or passed
around as data rather than propagated immediately, is open — see
"Unresolved research questions."

### A Napitia-native absence type instead of `null`

Absence is represented by an ordinary `variant` type (provisionally named
`Maybe<T>`, with cases named `present(value)` and `absent`), matching RFC
0001's ban on `null`. This is a plain user-definable-shaped type once
generic `variant`s exist (`spec/0003`) — there is deliberately no special
"nullable pointer" representation distinct from ordinary variant lowering,
and deliberately not a reuse of another language's exact type name
(`rfcs/0004`).

### Typed effects (`uses`)

Beyond simple success/failure, some function behaviors are tracked as
*effects*: an annotation on a function's type (parallel to, and composed
with, its return type and `raises` clause) describing what kind of
ambient capability the function uses — for example, reading a database,
performing file I/O, or using a source of randomness. A function
expresses this with a `uses` clause naming one or more capability paths
(`spec/0002`), e.g. `uses Database.Read, Clock.Read`. Capability names are
dotted paths defined by whichever library introduces them — the compiler
does not need to know `Database.Read` exists as a concept; a database
library mints it. This is what lets domain libraries (REST, databases,
AI) participate in the effect system without becoming compiler special
cases (RFC 0001).

Effects are meant to let calling code (and the compiler) reason about
"can this function touch the database?" or "can this function block?"
the same way it reasons about types, rather than that information living
only in documentation. Full design is deferred to
`rfcs/0003-extensible-effects.md`; this spec only commits to effects being
part of a function's type and to capability *names* being open-ended and
library-defined, not to a specific checking algorithm.

### Panics remain for true invariant violations only

A small set of conditions (integer overflow in checked arithmetic,
out-of-bounds indexing, an internal compiler invariant failing) are
intended to remain unrecoverable panics rather than something a `raises`
clause models, because forcing every call site to handle "the compiler
itself is wrong" or "you indexed past the end of an array with a literal
you controlled" adds ceremony without adding safety the type system could
have caught instead. Where the type system *can* catch a failure mode
statically (e.g. calling with the wrong argument count), it does, and no
`raises` declaration is needed at all.

## Unresolved research questions

- Whether `uses`/`raises` are checked structurally (any function that
  performs the effect/can produce the error must declare it, and it
  propagates through callers automatically, Koka/OCaml-effects style) or
  nominally (an explicit, closed-per-function list a function opts into).
  This is the central open question `rfcs/0003` exists to resolve;
  renaming the keywords did not resolve it.
- Whether a value-level "outcome" type is needed *in addition to*
  `raises`, for storing a not-yet-propagated failure as data, or whether
  `raises` plus `?` fully replaces that need.
- Whether `panic` itself should be a trackable effect (so "this function
  can panic" is visible in its type) or remain untracked, matching most
  mainstream statically typed languages.
- How effects compose with the ownership/region model in `spec/0004` —
  e.g. whether a blocking/async effect can ever be safely combined with
  holding a `borrow` across a suspension point.

## Non-goals

- No unchecked/runtime-only exception hierarchy of the Java
  `RuntimeException` or C++ `throw` variety, ever, as the primary
  error-propagation mechanism.
- No silent error swallowing: there is no equivalent of returning a
  sentinel value (`-1`, `null`) to mean failure anywhere in the standard
  model — every fallible operation's failure is visible in its `raises`
  clause.
- No copying another language's absence/failure type by name; see
  `rfcs/0004-language-independence.md`.
