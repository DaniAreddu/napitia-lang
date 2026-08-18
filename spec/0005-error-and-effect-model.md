# Spec 0005: Error and Effect Model

- Status: `raises`/`raise`/postfix `?`/`handle` implemented (Alpha
  0.1.6) — see `rfcs/0010-typed-outcomes.md` for the accepted, concrete
  design and current honest limitations. Capability `uses` effects
  (Koka/OCaml-effects-style, distinct from `rfcs/0009`'s already-checked
  capability `uses`), `panic` as a trackable effect, and the
  ownership/region interaction below remain design direction only.

Alpha 0.1.6 checks `raises`/`raise`/postfix `?`/`handle` against a real,
nominal effect model (`rfcs/0010`): a function's own `raises` clause is a
closed, explicit, per-function list, never inferred or propagated
automatically; there is no value-level "outcome" type in addition to it
— `raises` plus `?`/`handle` fully replace that need, resolving two of
this spec's own previously-open research questions below. The NIR
interpreter's own division-by-zero/malformed-instruction reporting
(`spec/0006-napitia-ir.md`) remains a separate, lower layer, unrelated to
`raises`. This spec's remaining sections record intended long-term
direction beyond what `rfcs/0010` actually implements, using the
provisional vocabulary from `rfcs/0004-language-independence.md`. An
earlier version of this spec named `Result<T, E>` and `Option<T>`
directly — those are Rust's own standard-library type names, not Napitia
concepts, and RFC 0004 corrects that.

## Implemented features

- `raises`/`raise`/postfix `?`/`handle`, checked against a real, nominal
  effect model with mandatory explicit handling at every fallible call
  site and exhaustive, per-case `handle` coverage (`rfcs/0010`,
  Alpha 0.1.6).
- The NIR interpreter reports division-by-zero and malformed-instruction
  conditions as structured `InterpreterError` values rather than
  panicking or invoking undefined behavior (`spec/0006`) — a separate,
  lower layer than `raises`, not itself a checked language-surface effect.

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

- **Resolved by `rfcs/0010` (Alpha 0.1.6):** `raises` is checked
  nominally — an explicit, closed-per-function list a function opts
  into, never structurally inferred or auto-propagated. This resolves
  the failure-error half of this question; the analogous question for
  capability `uses` *effects* (as opposed to `rfcs/0009`'s already-solved
  capability `uses` requirements) remains open.
- **Resolved by `rfcs/0010` (Alpha 0.1.6):** no value-level "outcome"
  type exists in addition to `raises` — `raises` plus `?`/`handle` fully
  replace that need. A raised value cannot be stored, compared, or
  passed around independently of the control-flow constructs that
  produce and consume it (`rfcs/0010`'s own honest limitations).
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
