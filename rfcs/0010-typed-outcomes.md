# RFC 0010: Typed Outcomes and Explicit Failure Flow (Alpha 0.1.6)

- Status: Accepted, implementing in Alpha 0.1.6

## Summary

Alpha 0.1.6 adds a custom, statically checked failure model: `raises`
(function signatures), `raise` (producing a failure), postfix `?`
(explicit propagation), and `handle` (exhaustive, per-case consumption).
A function's raised error set is part of its signature, exactly like its
return type; every fallible call must be either propagated (`?`) or
consumed (`handle`) at the call site — there is no ambient exception
channel, no implicit unwinding, and no way to silently ignore a failure.

```napitia
variant FileError {
    Missing,
    PermissionDenied
}

func read_config(path: str) -> str raises FileError {
    if path == "" {
        raise FileError.Missing
    }
    return "configuration"
}

func load(path: str) -> str raises FileError {
    return read_config(path)?
}

func main() -> str {
    return handle read_config("config.npt") {
        success text => text,
        failure FileError.Missing => "default",
        failure FileError.PermissionDenied => "denied"
    }
}
```

This is a custom design, not a copy of Rust's `Result`, Java/Python/C++
exceptions, or Go's tuple-return convention: there is no `Result[T, E]`
generic wrapper type, no `try`/`catch` block, no multi-value return, and
no runtime stack unwinding. A raised value is dispatched exactly the same
way an ordinary function's return value is (an explicit CFG edge with a
typed transfer), just with two disjoint destinations instead of one.

## Non-goals

No `defer`/destructors, no ownership/borrowing/regions, no garbage
collection, no `async`/cancellation, no stack traces or `panic`/`recover`,
no partial handler effect subtraction, no first-class effect values or
effect polymorphism, no FFI exceptions, no native backend or unrelated
optimizer work. Generic error variants are out of scope (see "Effect
resolution" below). Nested refutable patterns inside a `failure` arm's
payload (matching a literal, or a nested variant, *inside* the payload
position) are out of scope this milestone — a payload position may only
bind (`x`) or discard (`_`); deeper structural matching on a raised
value's own payload is future work.

## Syntax

```text
FunctionDecl = ... [ "->" Type ] [ UsesClause ] [ RaisesClause ] Block ;
RaisesClause = "raises" IDENT { "," IDENT } ;

RaiseExpr  = "raise" Expression ;
TryExpr    = Expression "?" ;
HandleExpr = "handle" Expression "{" HandleArm { "," HandleArm } [","] "}" ;
HandleArm  = "success" Pattern "=>" ArmBody
           | "failure" FailurePattern "=>" ArmBody ;
FailurePattern = "_"
               | IDENT "." IDENT [ "(" Pattern { "," Pattern } ")" ] ;
ArmBody = Expression | Block ;
```

`RaisesClause` reuses the pre-existing `raises` grammar (`spec/0002`,
`spec/0005`) unchanged: a comma-separated list of bare identifiers, each
naming a declared `variant`. There is deliberately no bracketed
type-argument position here (unlike `uses`'s capability entries) — a
raised type can never be generic in this milestone, so the grammar itself
has no way to spell one; a program attempting `raises Box[T]` fails to
parse as a `raises` entry at all (a bare identifier grammar cannot
consume the following `[`), the same way an out-of-scope construct is
rejected by construction elsewhere in this project when no diagnostic
would be more informative than "this isn't valid syntax here." `raise`
is a primary expression, parsed at the same position as `return`/`break`,
always type `never`. `?` is postfix, binding at the same precedence tier
as `.field`/`(...)` call syntax. `handle` is a primary expression,
parsed the same way `match` is (its own keyword, an operand, then a
brace-delimited arm list); a `FailurePattern` is not an ordinary `Pattern`
(which has no dotted-qualification syntax) because a `handle` block's
failure arms may need to disambiguate between more than one raised
*type* — `Type.Case` names both explicitly, the same qualified-path shape
`variant` construction already uses (`LookupResult.Found(user)`).

## Effect resolution

A function's `raises` clause resolves each identifier to a canonical,
concrete `variant` declaration in its own declaring module (module-
qualified, alias-independent, exactly like every other name in this
project — `rfcs/0007`) — never a record, protocol, primitive, or
type parameter. Two entries naming the same canonical variant are a
duplicate (diagnosed at both spans); the checked, canonical
representation (`EffectSet`) is a deduplicated, order-independent set of
`ItemId`s, while diagnostics addressing a specific declared entry use its
own real source span, preserving meaningful source order in the rendered
message.

Generic error variants (`raises Box[T]`) are out of scope: since the
grammar has no syntax for a type-argumented `raises` entry, this is
rejected as an ordinary "expected `,` or `{`" parse recovery, not a
dedicated semantic diagnostic — consistent with how this project already
treats a grammatically-absent construct (see `rfcs/0008`'s own treatment
of `<T>` angle-bracket syntax: rejected by having no grammar for it,
not by a special-cased checker).

A private variant may not appear in a *public* function's `raises`
clause (mirroring the existing private-type-leak check for return/
parameter types); the executable entry function may declare no `raises`
clause at all (mirroring `rfcs/0009`'s entry-point capability
restriction — `main` has no caller to hand a raised value to, so an
unhandled failure reaching it would be meaningless). A function may
declare a `raises` entry it never actually raises; this is legal (a
strictly narrower observed behavior than declared is always sound).

## `raise`

`raise <expr>` evaluates `<expr>` exactly once; its type must be exactly
one of the current function's own declared raised variants (checked
nominally, like every other type in this project); `raise` itself has
type `never` and unconditionally diverges the current control-flow path.
Raising a value of an undeclared, primitive, record, protocol, or
unrelated-variant type is a compile-time diagnostic. `raise` outside any
function, or inside a function whose own `raises` clause is empty, is
rejected (an empty `raises` clause means "this function is infallible";
there is nothing for a `raise` inside it to ever propagate to). No
host-language panic or exception implements this — see "NIR" and
"Interpreter" below for the explicit two-destination control-flow model
that does.

## Postfix `?`

`expr?` evaluates `expr` exactly once; `expr` must itself be a fallible
call (a call to a function whose own `raises` clause is non-empty; `?`
on an infallible expression is rejected). On success, `expr?` evaluates
to the call's own success value; on failure, it immediately forwards the
exact raised value to the *enclosing* function's own failure path — so
every effect `?` might propagate must already be a member of the
enclosing function's own declared `raises` set (checked against the
canonical `EffectSet`, not by name). `?` is never an identity operation:
it always lowers to an explicit two-target dispatch (see "NIR"), never a
no-op wrapping/unwrapping of some intermediate value — there is no
`Result`-shaped value for it to unwrap in the first place.

## Mandatory explicit handling

A fallible call's result may only ever be consumed by `?` or by being the
operand of `handle`. Using it as an ordinary expression — a bare
statement, an operand of anything else, ignored entirely — is a
dedicated compile-time diagnostic, regardless of whether the enclosing
function's own `raises` clause happens to already be a superset of the
callee's. Explicitness is the whole point: nothing about a function's own
declared effects is allowed to make a callee's failure silently
transparent.

## `handle`

`handle <expr> { ... }` evaluates `<expr>` (which must be fallible)
exactly once. Exactly one `success` arm is required, binding the success
value by name or discarding it with `_`. One or more `failure` arms
together must cover the operand's *complete* raised effect set, at
case granularity: for every raised variant the operand could produce,
every one of that variant's declared cases must be reachable through
some `failure Type.Case(...)` arm, or a single trailing `failure _` arm
covering everything not otherwise named. This mirrors `match`'s own
exhaustiveness discipline (`spec/0003`), generalized across however many
distinct nominal error types are in play — case identity always stays
qualified by its own declaring type; two different error variants
sharing a case name are never merged or confused. A `failure` arm's
payload positions may only bind or discard (see "Non-goals"); a
`Type.Case` naming a real case of a type that is not actually one of the
operand's raised effects, or a case index that type does not declare,
is rejected before exhaustiveness is even considered. A duplicate or
already-fully-covered `failure` arm is unreachable and rejected the same
way an unreachable `match` arm already is (`T0018`'s own precedent).
Missing coverage is reported with a concrete witness (which
`Type.Case` combination is unhandled), not merely "non-exhaustive."
`success`/`failure` arm bodies join through the same never-aware type-join
rules an ordinary `match`'s arms already do; a `handle` every one of whose
reachable arms diverges has type `never`. A raised value produced
*inside* a `handle` arm's own body (by a nested fallible call) is not
implicitly caught by the enclosing `handle` — it needs its own `?` or
nested `handle`, exactly like an ordinary nested nested `match`/`if` would
never implicitly catch a `return` from one of its own sibling branches.

## Protocol and capability interaction

`uses` (capability requirements) and `raises` (typed failure) are fully
independent concepts: an ordinary function may declare either, both, or
neither, and `?`/`handle` compose with capability-forwarding exactly as
they compose with an ordinary call to a fallible function.

A protocol method's own signature declaring `raises`, an implementing
extend method narrowing it, and a `protocol.call` site's effects being
checked against the protocol's own declared set rather than a specific
implementation's are all deliberately **not** part of this milestone --
see "Honest limitations" below. `postfix ?`/`raise`/`handle` are only
ever checked and lowered against a direct call to a named ordinary
function in Alpha 0.1.6.

## NIR

Fits into the existing slot-based CFG rather than introducing a second
value representation:

- Every `Function` carries its own resolved `raises: Vec<ItemId>` (the
  canonical effect set, deduplicated, in a fixed deterministic order —
  declaration order, never a `HashMap`'s).
- `Terminator::Invoke { callee, type_args, args, evidence, ok_slot,
  ok_target, err_targets }` replaces `Call` as a *terminator* (not an
  ordinary value-producing instruction) for any call to a fallible
  function: the success value is stored into `ok_slot` on the
  `ok_target` edge; a raised value (already an ordinary variant value,
  built the same way any other `variant.create` is) is stored into
  whichever `err_targets` entry's own `variant` matches it, and control
  continues at that entry's own `target` block — exactly one entry per
  effect the callee's own `raises` declares. An ordinary,
  already-existing `ValueKind::Call` remains exactly what it always
  was — reachable only for a callee whose own `raises` is empty; a
  fallible callee reached through it is rejected by the verifier, never
  silently accepted.
- `Terminator::Raise { value }` is the terminator a `raise` expression's
  own block ends with — no successor edge at all (it always transfers
  control to whatever `Invoke` in the *caller's* own frame is waiting on
  it, resolved by the interpreter's own call-frame return path, exactly
  like `Terminator::Return` already resolves to wherever the caller's
  own call site continues). `value` is already a complete variant value
  (built by `variant.create` for a direct `raise`, or simply the value
  already loaded from an `Invoke`'s own failure slot when `?` forwards
  one unchanged) — there is no separate variant/case/payload field here.
- `?` lowers to an `Invoke` whose every failure target is a fresh block
  that loads its own slot and ends in `Terminator::Raise` re-raising the
  exact received value — explicit forwarding, never a no-op.
- `handle` lowers to an `Invoke` whose every failure target is a
  dispatch block: a `switch`-shaped decision over the raised value's own
  nominal variant/case (reusing the existing `Terminator::Switch` shape
  per raised type), each case extracting its own payload via the
  existing `variant.payload` instruction and joining into the handler's
  own shared result slot exactly like `match`'s arms already do — a
  `failure` arm covering more than one case (a trailing wildcard) is
  lowered exactly once, in a block shared by every case it covers,
  mirroring how `match`'s own wildcard arm reuses one target across
  several `Switch` cases.
- A fully-diverging `raise`/`handle` allocates no result slot, mirroring
  `if`/`match`'s own existing discipline for a fully-diverging join.
- Lowering the whole module remains atomic: either every function lowers
  or the whole module fails with diagnostics, never a partially-lowered
  result.

## NIR verifier

Independently re-checks, exactly as skeptically as every other construct
this verifier already distrusts hand-built NIR for: a function's own
`raises` list references only real, distinct variant `ItemId`s; an
ordinary `Call` never targets a fallible function; an `Invoke` never
targets an infallible one; `Invoke`'s success/failure slots are
allocated and correctly typed, its `err_targets` cover exactly the
callee's own declared `raises` set with no duplicate or unknown variant,
its evidence/type-argument/argument checks reuse exactly the same checks
`Call` already has, and every branch target exists; `Raise`'s own value
is one of the current function's own declared `raises` types; every
`Invoke`/`Raise` respects slot dominance and terminator-only placement
(no instruction ever follows one in the same block). One diagnostic per
malformed root, never one per nested level, bounded by the same
generic-depth budget every other recursive check already shares.

## Interpreter

A call's outcome is one of two explicit variants, internal to the
interpreter — conceptually `Returned(Value)` or `Raised(Value)` (the
raised value already carrying its own nominal variant identity) — never
a Rust panic/unwind. `Invoke` dispatches on this outcome directly:
`Returned` continues at `ok_target` with the value stored in `ok_slot`;
`Raised` looks up the matching `err_targets` entry by the raised value's
own variant identity, stores it into that entry's own slot, and
continues at that entry's own target block. `Terminator::Raise` itself
simply *produces* `Raised` and returns it up to whichever frame's own
`Invoke` is waiting — call arity, evidence count, and effect metadata
are all validated the same way an ordinary call's already are, before
the callee's body ever runs. The public interpreter API is unaffected:
a well-typed `main` can never legally raise, so a `Raised` outcome
reaching the top level (only reachable through malformed hand-built
NIR) is reported as a structured error rather than surfaced as if it
were an ordinary return value.

## Diagnostics

New codes are allocated in the correct existing layers (`R` for
resolution, `T` for type-checking, `V` for the NIR verifier), continuing
the running numbering each family already has — see the compiler source
for the authoritative, current list (this document does not duplicate a
number that could drift out of sync with it). Every new diagnostic
points at its own real source file and the narrowest useful span, and is
byte-identical across repeated runs; reversed import/declaration order
changes rendered output only where the primary span honestly must (the
same principle `rfcs/0009`'s own overlap-diagnostic determinism section
already establishes).

## Complexity limits

Effect-set resolution, handler exhaustiveness, and NIR verifier recursion
each reuse this project's existing depth/work-budget discipline
(`crate::limits`) rather than introducing an unbounded new one; exceeding
a budget is always its own diagnostic, never a hang, a panic, or a
silently-truncated result.

## Honest limitations

- A protocol method's own signature cannot declare `raises`, and
  `postfix ?`/`raise`/`handle` are only checked/lowered against a direct
  call to a named ordinary function -- there is no protocol/capability
  integration for typed failure in this milestone at all. `uses` and
  `raises` remain independent concepts everywhere they can currently
  coexist (an ordinary function may declare either, both, or neither),
  but a protocol method cannot yet be one of the places that coexistence
  is expressed.
- Generic error variants do not exist; every `raises` entry names a
  concrete, non-generic variant.
- A `failure` arm's payload positions may only bind or discard — no
  nested literal/variant matching on a raised value's own payload.
- Partial handling (consuming only some of an operand's raised effects
  and re-raising/propagating the rest from within the same `handle`) does
  not exist; a `handle` must cover every raised case, always.
- There is no first-class effect/error value: a raised value cannot be
  stored, compared, or passed around independently of the `raise`/`?`/
  `handle` control-flow constructs that produce and consume it.
- No stack traces, no `panic`/`recover`, no resource cleanup (`defer`)
  tied to a raised failure — none of this milestone's other explicitly
  out-of-scope items are implemented by this feature either.
- No native-code backend exists yet; this remains a tree-walking
  interpreter over NIR, exactly as before.
