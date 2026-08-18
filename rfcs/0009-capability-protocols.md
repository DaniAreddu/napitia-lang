# RFC 0009: Capability Protocols (Alpha 0.1.5)

- Status: Accepted, implemented in Alpha 0.1.5

## Summary

Alpha 0.1.5 adds `protocol`/`extend`/`uses`: a capability system for
expressing "this type supports this operation" without inheritance,
implicit receivers, or runtime type discovery. A `protocol` declares one
or more explicit type parameters and a set of method signatures; an
`extend` supplies a concrete (or conditionally generic) implementation for
a specific instantiation; a function's `uses` clause declares which
capabilities its own body requires, and a `Protocol[Args].method(...)`
expression is the only way to call one. Every capability requirement is
resolved once, entirely at compile time, by unifying the exact concrete
(or still-symbolic) type in play against every declared `extend` — the
same technique known elsewhere as dictionary passing (how Haskell
typeclasses are implemented without runtime dispatch), but this is a
custom Napitia design, not a mechanical copy of Rust traits, Java
interfaces, Go interfaces, or Haskell typeclasses; none of those systems'
particular syntax, receiver conventions, or resolution rules are assumed
here.

```napitia
protocol Equal[T] {
    func equal(left: T, right: T) -> bool;
}

extend Equal[i64] {
    func equal(left: i64, right: i64) -> bool {
        return left == right
    }
}

func main() -> bool {
    return Equal[i64].equal(21, 21)
}
```

## Non-goals

No implicit receiver and no `Self` type: every protocol method's
parameters are ordinary, explicitly typed parameters, and a call names its
protocol and type arguments explicitly (`Equal[i64].equal(a, b)`), never
`a.equal(b)`. No operator sugar: `==`, `<`, and so on never route through
a protocol implicitly, even if a program happens to declare `Equal`/`Ord`-
shaped protocols with those names — `==` on primitives keeps its own
pre-existing built-in meaning (`spec/0003`), entirely unrelated to any
user-declared protocol. No default method bodies, no supertraits/protocol
inheritance, no protocol-typed values (`x: Equal[i64]` as an ordinary
parameter type is rejected — a protocol is not a nominal type,
`hir::lower`'s `R0026`), no first-class/dynamic dispatch (an `Evidence` is
never a runtime value a program can inspect, store, or branch on), and no
derive macros. Symbolic capability resolution is exact forwarding only —
see "Capability resolution" below for exactly what this means and why it
is an honest, load-bearing limitation of this milestone, not an oversight.

## Syntax

```text
protocol Equal[T] {
    func equal(left: T, right: T) -> bool;
}

extend Equal[i64] {
    func equal(left: i64, right: i64) -> bool { left == right }
}

extend[T] Equal[Box[T]] uses Equal[T] {
    func equal(left: Box[T], right: Box[T]) -> bool {
        Equal[T].equal(left.payload, right.payload)
    }
}

func pair_equal[T](a: T, b: T) -> bool uses Equal[T] {
    Equal[T].equal(a, b)
}
```

A `protocol` declares a name, one or more explicit type parameters (a
protocol with none is rejected before it reaches NIR), and a body of
method signatures (no bodies, terminated with `;`) — a plain, restricted
form of the same declaration grammar records and variants already use.
Method declaration order is load-bearing: a `protocol.call` instruction
references a method purely by its declaration-order index, never by name,
so two protocols (or the same protocol imported under two aliases, or
across a reversed import order) always agree on which index means which
method.

An `extend` names the protocol it implements, that protocol's own
concrete (or still-symbolic) type arguments at this extension's head, an
optional `[T, ...]` list of the extension's *own* type parameters
(distinct from the protocol's own — never inferred from an otherwise-
unknown name inside the protocol's argument list, which instead fails to
resolve later in `hir::lower` the same way any other unknown type name
would), an optional `uses` clause naming this extension's own capability
requirements, and a body of ordinary function declarations, one per
protocol method, matching the protocol's method set exactly (no fewer,
no more, no duplicates — `T0031`/`T0032`/`T0033`). Every method in an
extend's body shares that extend's own type-parameter scope directly
(never declares generic parameters of its own, `R0025`) and its own
`uses` clause is always exactly the owning extend's (`R0027`) — an
extend's body is not an independent set of ordinary declarations, it is
the one implementation this extend provides.

A function's `uses` clause is a comma-separated list of capability
requirements, each an optionally-type-argumented dotted path
(`Equal[T]`), appearing after the return type and before an optional
`raises` clause and the function's body — reusing the exact same `uses`
token `spec/0005`'s pre-existing (still largely unchecked) effect
declarations already use; whether a given `uses` entry is a capability
requirement or a bare effect name is decided later, from whether it
carries type arguments, not by the parser.

A protocol-call expression, `Protocol[Args].method(args)`, is the *only*
way to invoke a protocol method. There is no other call syntax for one —
naming a protocol method as a bare value (`Equal.equal`) is rejected
(`T0029`, `R0026`).

## Authority and coherence

An `extend` is legal only if its own declaring module has *authority*
over it: either it declares the protocol itself, or it declares the
outermost nominal aggregate used as the protocol's first type argument
(`extend Equal[Point]` is legal only in `Point`'s own module, or
`Equal`'s own module). A primitive first argument (`extend Equal[i64]`)
has no owning module of its own, so only the protocol's own declaring
module may extend it. Every other module attempting the same extension is
rejected as `T0035` — this is what stops two unrelated modules from
quietly compiling two different, contradictory implementations of the
same capability for the same type. Single-file compilation has exactly
one module, so authority always trivially holds there; the check only
ever has teeth across a multi-file project (`rfcs/0006`).

Two extensions are *coherent* only if no concrete instantiation of the
protocol could ever match both. `extend[T] P[T, T]` and `extend[U] P[U,
i64]` both match `P[i64, i64]`, and are rejected as an overlap (`T0037`,
or `T0036` for an exact duplicate) — before any call site referencing
either even exists, since a specialization rule that picked "the more
specific one" would be exactly the kind of unpredictable resolution this
system deliberately avoids (no specialization, ever). Overlap detection is
a sound, deterministic, bidirectional structural unifier over each
extend's own head (`typeck::capability::heads_can_overlap`): each side's
own type parameters form a disjoint free-variable set, substitutions chase
transitively through both sides, an occurs check rejects a self-
referential match, and the whole search is bounded by a real depth
*and* work-step budget, each independently enforced — not merely a depth
check, since a shallow but wide pair of heads could otherwise still make
this pathologically expensive. `heads_can_overlap` returns a tri-state
outcome (disjoint, overlap, or budget-exceeded), never collapsing a
budget-exceeded comparison to plain "disjoint": doing so could let two
extensions that might genuinely overlap both stay registered. A pair this
checker cannot decide within budget is reported as `T0047`, and *both*
extends involved are excluded from the solver — coherence can be claimed
for neither. The result (and its diagnostic's exact wording, file, and
span) is independent of declaration order — reversing which extend was
written first produces byte-identical output.

Separately, every extend's own type parameter must be *determined* by its
protocol head: `extend[T] Equal[i64] uses Other[T]` declares `T` with
nothing that could ever bind it, since `T` never occurs anywhere in
`Equal[i64]`'s own arguments. This is exact-forwarding-only's own
declaration-time counterpart (see "Capability resolution" below) —
rejected as `T0046`, one diagnostic per unconstrained parameter, in
declared order, excluding the whole extend from the solver. A parameter
occurring anywhere inside a nested application (`Equal[Box[T]]`) is fully
determined and accepted; this is a purely structural occurrence check
(`typeck::capability::collect_occurring_type_params`), not a fresh
unification. `nir::verify` independently re-derives the same check as
`V0059`, since it never trusts hand-built NIR to already satisfy what
`typeck` enforces for ordinary source.

## Capability resolution: exact forwarding only

Every `uses` requirement is resolved exactly once, entirely at compile
time, by `typeck`'s capability solver, producing one `Evidence` value per
requirement:

- `Evidence::Extension { extend, nested }` — a concrete extend was
  selected once and for all for this call site; `nested` is that same
  extend's own `uses` requirements, resolved the same way. By the time a
  concrete extend is selected, every type it applies to is already fully
  concrete, so every entry in `nested` is itself always `Extension`,
  never `Forwarded`.
- `Evidence::Forwarded(index)` — "use whatever the *currently executing*
  function's own requirement at this index already is." This is the only
  mechanism a still-generic function has for satisfying its own `uses`
  clause: it does not (and structurally cannot) inspect, unify, or derive
  anything about its own symbolic type parameter's capabilities — it can
  only pass its own already-declared requirement through unchanged to a
  callee with the *exact* same requirement (same protocol, same
  arguments, once substituted). If a generic function's own requirement
  does not exactly match what a callee needs, resolution fails with
  `T0039`/`T0040` — there is no partial, symbolic, or "derive from a
  weaker constraint" resolution path in this milestone. Concretely: a
  generic `extend[T] Equal[Box[T]] uses Equal[T]`'s own `equal` method can
  call `Equal[T].equal(...)` (forwarding its own requirement), but cannot
  call, say, `Ord[T].compare(...)` unless it *also* declares `uses
  Ord[T]` — nothing infers a stronger or different capability from a
  weaker one. Consequently `Evidence::Extension` is never legal for a
  still-symbolic requirement (one whose arguments still contain a
  `Ty::Param`): a concrete extend can only ever have been legitimately
  selected once every argument is fully concrete. `nir::verify`
  independently enforces this as `V0060`, checked before attempting any
  structural match against the candidate extension's own head — a
  hand-built NIR reusing the same raw `TypeParamId` on both sides could
  otherwise coincidentally "match" a hostile `Extension` entry against a
  symbolic requirement.

This is dispatched at runtime with one frame-relative lookup
(`interpreter::resolve_evidence`) — the interpreter never re-runs any part
of resolution; it only ever copies an already-resolved `Evidence` between
call frames. Both the solver and the independent NIR verifier bound
recursive evidence work by an explicit depth limit
(`MAX_CAPABILITY_DEPTH`, 64) and a work-step budget
(`MAX_CAPABILITY_RESOLUTION_STEPS`, 4096); exceeding either is a
diagnostic (`T0041` cyclic, `T0042` depth, `T0043` work-budget, at
typeck; `V0055`/`V0056` at the verifier), never a hang or a stack
overflow. The solver's cache stores only successful resolutions —
`missing`/`ambiguous` failures are re-diagnosed at every call site (since
which extend, if any, is missing/ambiguous can depend on the call site's
own context), and path-dependent failures (cyclic, depth-exceeded, work-
budget-exceeded) are never cached at all, so a budget exhausted while
exploring one branch never poisons an unrelated, independently-resolvable
requirement elsewhere in the same compilation.

## Entry-point restriction

The executable entry function (`main`) cannot declare capability
requirements: it has no caller to receive evidence from, so a `uses`
clause on it is unsatisfiable by construction and is rejected outright
(`T0045`), the same way `main` already cannot declare ordinary
parameters. A concrete protocol call *inside* `main`'s own body remains
entirely legal and requires no `uses` clause of its own — only a
requirement `main` would need someone else to satisfy is rejected. The
interpreter independently enforces the same invariant in
`Interpreter::call_function`, validating that a call's evidence count
exactly matches its callee's own declared requirement count before
executing the callee's body at all, so a `main` (or any function) invoked
directly with the wrong evidence shape fails with a structured error
immediately rather than deferring the failure until some later
`Forwarded` lookup happens to miss.

## NIR representation

```text
protocol @Equal#4[T] {
    method[0] equal(T, T) -> bool;
}

extend @extend#7 for @Equal#4[i64] {
    method[0] = @equal_i64#8;
}

func @f#9(%0: i64, %1: i64) -> bool {
bb0:
    %2 = protocol.call @Equal#4[i64].method[0](%0, %1) evidence [@extend#7]
    ret %2
}
```

A protocol's own NIR identity is its canonical, module-qualified name
plus its own `ItemId` (`rfcs/0007`), exactly like a function, record, or
variant. An `extend` has no user-declared name of its own — its canonical
identity is the bare keyword plus its `ItemId` (`@extend#<id>`), never a
placeholder and never borrowed from its protocol or first method; every
one of its methods is registered as an ordinary function identity in its
own right, under its own true declaring source and name, so two different
extends' same-named methods (`equal` in one extend, `equal` in another)
remain distinct through their `ItemId`s alone. This registration is the
canonical `ItemRegistry`'s job (`hir::registry`), built once from the
merged HIR; valid protocol/extend/method NIR never prints the registry's
`<item #...>` placeholder, aliases never affect a canonical printed
identity, and output is byte-identical across repeated compiles and
import-order permutations.

A `Call`'s evidence list and a `protocol.call`'s single evidence value are
the only two places `Evidence` appears in NIR; both are printed the same
way (`evidence [...]`), with `Evidence::Extension` printed as `@<extend>`
and `Evidence::Forwarded(k)` as `forwarded[k]`.

## The NIR verifier

`nir::verify` independently re-checks every protocol/extend declaration
and every `Call`/`protocol.call` instruction's evidence, distrusting
hand-built NIR exactly as thoroughly as it already distrusts hand-built
records/variants/generics — it never assumes `nir::lower` (or, further
back, `typeck`) already got this right:

- **Protocol layouts**: no duplicate/escaping type parameters; every
  method's parameter/return type is a valid root (no `Ty::Error`,
  unresolved `Ty::Var`, unknown nominal identity, wrong arity, or
  excessive generic depth).
- **Function requirements**: every ordinary function's own `uses`
  requirements get exactly the same independent validation an extend's
  own requirements do — referenced protocol exists with correct arity,
  and every argument is a valid root scoped to the function's own type
  parameters. This is not merely re-checking what `typeck` already
  accepted: it is the same defense-in-depth this verifier applies to
  every other declaration kind.
- **Extend layouts**: the named protocol and every `uses` requirement's
  protocol actually exist, with correct arity; every declared type is a
  valid root scoped to the extend's own type parameters (and every one of
  the extend's own type parameters must occur somewhere inside its
  protocol arguments — `V0059`, `nir::verify`'s own re-derivation of
  `T0046`); the method table has exactly one entry per protocol method,
  referencing a real, distinct function that shares its owning extend's
  exact type-parameter scope, declares *exactly* its owning extend's own
  `requirements` in the same declared order (`V0058` — `ProtocolCall`
  passes an extension's own `nested` evidence straight to its implementing
  function as that function's evidence, and `Interpreter::call_function`
  validates that evidence against the callee's own declared
  `Function::requirements`, so a mismatch here could otherwise pass every
  other check yet still misdispatch, or fail, only once interpreted), and
  whose signature matches the protocol method once substituted through
  the extend's own head.
- **`Call` evidence**: entry count matches the callee's own requirement
  count; each entry is checked against that requirement, substituted
  using the call's own type arguments — `Forwarded(k)` must be in range
  for the *currently verified* function's own requirements and exactly
  compatible with what is required; `Extension` must reference a real
  extend targeting the right protocol, whose own head structurally
  matches the required arguments (a one-directional match distinct from
  the two-sided overlap unifier, since only the extend's own parameters
  are free here), with the right number of `nested` entries, each in turn
  checked the same way — except `Forwarded` is never legal inside
  `nested` (an extension's own nested evidence, once selected, is always
  fully concrete).
- **`protocol.call`**: the protocol and method index exist; type-argument
  arity and every type root are valid; argument count/types and the
  result type match the method's signature substituted with this call's
  own type arguments; its evidence is checked the same way `Call`'s is,
  against exactly the protocol/arguments this specific call site
  requires.

Every failure class gets its own stable `V`-code (`V0036`-`V0060`, see
below), never reused for an unrelated shape of failure. Recursive
evidence validation is bounded by the same depth/work budget the solver
itself uses, and produces exactly one diagnostic per malformed evidence
root, never one per nested node — a hostilely deep or wide hand-built
evidence tree fails cleanly with a single, specific diagnostic rather
than a flood of them, a hang, or a stack overflow.

## Determinism

Every diagnostic this milestone adds — authority, overlap, missing/
ambiguous capability, poisoned protocol calls, entry-point restriction,
every new `V`-code — is independent of declaration order, import order,
and which of two aliases a program happens to use: the same program,
reversed in whichever of these ways applies, produces byte-identical
diagnostics (same code, file, span, and message) or byte-identical NIR.

## Required examples

Nine fixtures exercising the required scenarios end-to-end through the
real `napitia` binary (`examples/`, `compiler/tests/projects/`): a
concrete `Equal[i64]` protocol and extension; a conditional `extend[T]
Equal[Box[T]] uses Equal[T]`; generic capability forwarding through two
still-symbolic functions; a protocol declared in one module and imported/
called from another; a missing-capability call; an unauthorized cross-
module primitive extension; an incoherent pair of overlapping extensions;
an extension whose method signature does not match its protocol method;
and an entry function illegally declaring a `uses` clause.

## Diagnostic codes

New this milestone:

```text
R0021  duplicate method name within one protocol declaration
R0022  reference to an undeclared protocol
R0023  a uses requirement written with a dotted (multi-segment) path
R0024  reference to a protocol method a protocol does not declare
R0025  an extend method declaring its own generic type parameters
R0026  a protocol referenced as if it were an ordinary type/value
R0027  an extend method declaring its own uses clause

T0029  a protocol method referenced as a bare value, not called
T0030  wrong number of type arguments applied to a protocol
T0031  an extend missing one or more of its protocol's methods
T0032  an extend declaring the same method twice
T0033  an extend declaring a method its protocol does not have
T0034  an extend method's signature does not match its protocol method
T0035  an extension declared without authority over its protocol/type
T0036  two extends are exact duplicates of the same instantiation
T0037  two extends can both match the same concrete instantiation
T0038  a uses entry that does not resolve to a declared capability
T0039  no extend/forwarded requirement satisfies a uses requirement
T0040  more than one extend equally satisfies a uses requirement
T0041  capability resolution revisited the same requirement (cyclic)
T0042  capability resolution nested past the depth limit
T0043  capability resolution exceeded its work-step budget
T0044  a protocol-call expression names an unknown protocol/method in
       hand-built HIR (defensive; typeck's own parser/resolver paths
       never produce this for ordinary source)
T0045  the executable entry function declares a uses requirement
T0046  an extend's own type parameter does not occur in its protocol
       arguments and cannot be determined by its own head
T0047  overlap checking between two extends could not be decided within
       the shared depth/work budget; both are excluded from the solver

V0036  an extend names a protocol id that does not exist
V0037  an extend's protocol-argument count does not match its protocol
V0038  an extend's uses requirement names an unknown protocol
V0039  an extend's uses requirement has the wrong argument count
V0040  an extend's method-table length does not match its protocol
V0041  an extend's method table references an unknown function
V0042  an extend method's own type parameters do not match its extend
V0043  an extend method's signature does not match its protocol method
V0044  an extend's method table uses the same function for two slots
V0045  two protocols/extends reuse the same id
V0046  (see V0045; the extend-specific half of the same check)
V0047  a Call's evidence count does not match its callee's requirements
V0048  a Forwarded evidence index is out of range
V0049  a Forwarded evidence entry does not exactly match what is required
V0050  evidence references an extend id that does not exist
V0051  evidence selects an extension for the wrong protocol
V0052  evidence selects an extension whose head cannot match
V0053  evidence's nested-entry count does not match its extend's uses
V0054  a Forwarded entry appears inside another extension's own nested
       evidence, where only a concrete extension is ever legal
V0055  evidence nested past the capability depth limit
V0056  evidence validation exceeded its work-step budget
V0057  a protocol.call names an unknown protocol or method index
V0058  an extend method's own requirements do not exactly match its
       owning extend's requirements, in the same declared order
V0059  an extend's own type parameter does not occur in its protocol
       arguments (nir::verify's own re-derivation of T0046)
V0060  Evidence::Extension was selected for a still-symbolic requirement;
       only an exact Evidence::Forwarded match is legal in that case
```

## Honest limitations

- Capability resolution is exact-forwarding-only, as described above: a
  still-symbolic function can only pass its own declared requirement
  through unchanged, never derive, weaken, strengthen, or combine one
  symbolically. Every conditional extend in this milestone (and every
  test/example exercising one) relies only on this exact mechanism —
  nothing here implies richer symbolic capability inference exists.
- There is no supertrait/protocol-inheritance mechanism, no default
  method bodies, and no way to express "any protocol implementing X also
  implements Y."
- A protocol is not a first-class type: it cannot appear as an ordinary
  variable/field/parameter type, only inside a `uses` clause or a
  `Protocol[Args].method(...)` call. There is no dynamic dispatch, no
  protocol-typed value, and no way to store or compare an `Evidence` from
  user code.
- Coherence checking is sound but not maximally permissive: it rejects
  (`T0047`) every case it cannot prove non-overlapping within its real
  depth *and* work-step budget, which means a pathologically deep or wide
  pair of generic extend heads can be excluded as unprovable rather than
  accepted, even if no genuine runtime overlap would ever occur. This
  mirrors `rfcs/0008`'s own generic instantiation/depth budgets, not a new
  kind of imprecision.
- Type-argument inference from a *bare* integer/float literal argument
  still does not resolve through a generic capability-requiring function,
  for the same pre-existing reason `rfcs/0008` documents for ordinary
  generics (`identity(42)` reports `T0026`) — every worked example here
  supplies an explicit type argument at the call site that would
  otherwise need bare-literal inference.
- No native-code monomorphization or specialized dispatch table exists:
  NIR stays fully parametric, `Evidence` is resolved once at compile time
  and copied between interpreter frames, and there is no backend yet
  (`spec/0006`).
- No production-readiness claim is made anywhere in this document; Alpha
  0.1.5 remains an early-stage research/engineering milestone, exactly
  like every milestone before it.
