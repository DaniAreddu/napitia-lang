# RFC 0003: Extensible Effects

- Status: Accepted design direction. Not implemented in Alpha 0.1.

## Summary

Beyond a `raises` clause for expected failure (`spec/0005`), Napitia
intends to track other ambient capabilities a function uses — I/O,
blocking, randomness, GPU access — as part of its type, declared via a
`uses` clause (`spec/0002`) and collectively called *effects*. This RFC
expands on `spec/0005-error-and-effect-model.md` with the motivating
problem and the design space, without committing to a final checking
mechanism yet.

## Motivation

RFC 0001 bans unchecked exceptions and requires no undefined behavior in
safe code, but says nothing about a related, narrower problem: today, in
most languages, "can this function block the current thread?", "can this
function perform I/O?", and "can this function fail?" are either not
visible in a signature at all, or visible only for the third one (via a
generic failure-wrapper return type or checked exceptions). For a
language that also promises no GIL and structured concurrency, "does
this function block?" is not a documentation-only concern — a
structured-concurrency scheduler needs to know it to schedule correctly,
and a reviewer needs to know it to reason about whether a function is
safe to call from a non-blocking context.

Effects are the proposed mechanism to make that visible in the type
system, the same way a `raises` clause (`spec/0005`) makes failure
visible instead of leaving it to documentation and convention.

## Design space

Two broad families exist in prior art, and this RFC does not yet choose
between them:

### Structural (Koka / OCaml effect handlers style)

A function's effect set is inferred from what it does (calling an
I/O-performing function makes the caller I/O-performing too) and
propagates automatically through the call graph, similar to how
`async`/`await` propagates in most languages, but generalized to any
effect. Handlers can locally discharge an effect (e.g. catching a
panic-like effect turns it into an ordinary value for callers above the
handler).

**Appeal**: composes automatically; adding a new effect to a low-level
function doesn't require updating every transitive caller's signature by
hand if inference does it.

**Risk**: signatures can become large and implicit; without careful
diagnostics, "why does this function apparently perform I/O" can be hard
to trace through several layers of inference.

### Nominal (closed, declared effect list)

A function explicitly declares the effects it uses via its `uses` clause
(e.g. `func readConfig() -> Config uses FileSystem.Read`), and a caller
either also declares that effect or explicitly discharges it. This is
closer to how checked exceptions work in Java, but generalized beyond
just "throws", and matches the concrete `uses` syntax already parsed in
`spec/0002` (unenforced in Alpha 0.1).

**Appeal**: signatures are self-documenting and effects are always
visible without running inference in your head; closer in spirit to how
Napitia already requires explicit function signatures (`spec/0003`) rather
than inferring them.

**Risk**: more ceremony at every layer; a closed vocabulary needs to be
extensible for library authors without becoming an unbounded, ad hoc
annotation system (RFC 0001 already rejects "an unbounded ad hoc
annotation system" implicitly by requiring effects to be part of a
function's *type*, not a separate mechanism).

## Accepted direction (narrower than either family)

Regardless of which family (or hybrid) is chosen, this RFC commits to:

- Effects are represented as part of a function's *type*, composed with
  but distinct from its return type — never a separate annotation system
  bolted on outside the type checker.
- Panics remain outside the effect system for common invariant violations
  (`spec/0005`); this RFC's open question is only whether panic-*capable*
  functions should be effect-tracked at all, not whether ordinary
  declared failure should be (it already is, via `raises`, not via
  `uses` effects).
- Whatever mechanism is chosen must work with the ownership/region model
  in `rfcs/0002` — in particular, effects that suspend (blocking,
  `async`) interact with whether a suspended function can still hold a
  region-scoped value across the suspension point.

## Unresolved research questions

- Structural vs. nominal (or a hybrid) — the central open question of this
  RFC, to be resolved by prototyping both against realistic code, not by
  argument alone.
- Whether effect polymorphism (a higher-order function being generic over
  "whatever effect its callback has") is needed from day one, given
  Napitia's stated goal of eventually supporting async I/O libraries as
  ordinary code rather than a special-cased runtime.
- Whether `unsafe` should itself be modeled as an effect (making "this
  function uses unsafe internally, but its signature is safe" trackable)
  or remain a purely syntactic block-scoped marker as described in
  `spec/0004`.

## Non-goals

- This RFC does not propose a checking *algorithm* for `uses`/`raises`.
  The clauses themselves are already concrete surface syntax
  (`spec/0002`), and `async`/`await` (`spec/0001`) are existing surface
  syntax for one specific, well-understood effect-like feature
  (asynchronous suspension) — but none of this is evidence that the
  general structural-vs-nominal checking question this RFC exists to
  resolve has actually been answered.
