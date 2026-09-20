# RFC 0015: Fixed-Width Numeric Semantics (Alpha 0.2.1)

- Status: Accepted, implemented in Alpha 0.2.1
- Supersedes the integer-width parts of `rfcs/0014-native-aot-preview.md`

## Summary

Napitia has always *spelled* its default integer type `i64`. Up to and
including Alpha 0.2.0 it did not *behave* like one. The interpreter held
every integer in an `i128` and wrapped at 128 bits; the native backend
copied that choice into Cranelift's `I128` so the two would agree; the
checker never looked at a literal's magnitude at all. `i64` was a label
on a 128-bit machine, and `rfcs/0014` recorded that as a known
divergence rather than a decision.

This milestone removes the divergence. `i64` becomes a signed
two's-complement 64-bit integer in every stage of the compiler, its
arithmetic becomes checked, and every numeric construct the checker
accepts is one *the interpreter* genuinely implements -- the
interpreter being the complete execution path the language is defined
by.

That is deliberately not a claim about the native backend, which
compiles one subset of the language and refuses the rest. `f64`,
`div`, `rem` and the shifts are all accepted by the checker, executed
by the interpreter, and refused by the backend. "Interpreter/native
equivalence" below says exactly which constructs the two share, and
this RFC claims parity for those and no others.

It is a stabilization release. It adds no numeric type, no conversion,
no cast, no literal suffix and no wrapping operator.

## The `i64` domain

```text
minimum = -9223372036854775808
maximum =  9223372036854775807
```

That is the domain in all of: literal checking, inferred and annotated
expression types, HIR metadata, NIR constants and operations, NIR
verification, interpreter values, Cranelift representation, parameters,
return values, slots, calls, branches, comparisons, and the conversion
to a process exit status.

There is one representation per stage, and each stage's is the narrowest
one that can be right:

| Stage | Carries | Type |
| --- | --- | --- |
| lexer, AST, HIR | the literal's *magnitude*, unsigned | `u128` |
| typeck | the literal's *resolved type* | `Ty` |
| NIR | a *typed constant*, signed, validated by the verifier | `i128` |
| interpreter | a *runtime integer value* | `i64` |
| native backend | a *machine representation* | Cranelift `I64` |

The widths above `i64` are not slack in the model. A source magnitude is
unsigned because `-5` is not a literal -- it is a negation applied to
`5` -- so the lexer cannot represent a sign it has not seen yet. A NIR
integer constant is `i128` because NIR is a hand-buildable IR whose
constants arrive unvalidated, and the verifier's job is to *reject* one
its own type cannot hold. Nothing downstream of verification ever sees a
value outside `i64`.

## `i64::MIN` and the negated literal

`-9223372036854775808` is the one literal whose magnitude
(`9223372036854775808`) is not itself a valid `i64`. Napitia handles it
without special-casing the source text:

* the lexer produces the magnitude `9223372036854775808` and no sign;
* the checker, when validating a literal's magnitude against its
  resolved type, asks whether that literal is the *direct operand of a
  unary negation*, and if so validates against the type's negated
  domain (`magnitude <= 9223372036854775808` for `i64`) instead of its
  positive one;
* NIR lowering folds a negation applied directly to an integer literal
  into a single signed constant, so `-9223372036854775808` reaches NIR
  as one `i64` constant and never as a negation of a value that could
  not exist.

"Directly" means directly in the HIR, where parentheses no longer
exist: `-(9223372036854775808)` is the same negated literal and is
equally accepted. A negation applied to anything else -- a variable, a
call, another negation -- is an ordinary checked `neg`. So
`- -9223372036854775808` checks cleanly, because its *inner* operator is
the one applied to the literal, and then fails at run time when the
outer one negates the minimum.

## Checked arithmetic

`add`, `sub`, `mul` and `neg` on `i64` are checked. So is `div` when the
divisor is `-1` and the dividend is `i64::MIN`. An operation whose exact
mathematical result is outside the `i64` domain does not produce a
value: it produces a Napitia runtime failure.

Runtime failures are not `raises` values. They are the unrecoverable
class `spec/0005` already reserves for "integer overflow in checked
arithmetic", and no Napitia construct catches one.

Their codes are `X0001` through `X0004`; the table near the end of this
document lists every diagnostic this RFC introduces, at every stage.

### A runtime failure is a fatal abort

An X-class arithmetic failure is **not** a Napitia control-flow exit. It
is not a `raise`, it does not unwind scopes, and it runs no cleanup:

* execution stops at the failing operation;
* no later statement in any enclosing scope runs;
* no `defer` action registered before it runs;
* no automatic or explicit `drop` after it runs;
* a nested call propagates the original failure unchanged, and every
  frame it passes through is abandoned the same way.

A resource that was live when the failure happened is therefore **not
destroyed**. The runtime does not pretend otherwise: it emits no
destruction event for it, and reports nothing about it at all. Cleanup
that had *already* completed before the failure stays completed and is
never repeated.

`rfcs/0011`'s deterministic-cleanup guarantee is about Napitia
*control-flow* exits -- normal fallthrough, `return`, `break`,
`continue`, `raise`, `?` and `handle`. A fatal abort is none of those,
and is the one documented exception to it.

Because the state a fatal abort leaves is the middle of a statement
rather than any state the language describes, the interpreter that was
running it is finished. A later attempt to start another execution on
the same interpreter is refused with `X0004` -- an invalid operation on
the engine, not a second arithmetic failure, which would wrongly claim
the new call performed the failing operation. The ordinary compiler
driver builds a fresh interpreter per execution, so this is reachable
only by a caller that keeps one and reuses it.

A structured refusal of malformed input (`X0004`) is the opposite case:
it is decided before anything changes, leaves the interpreter exactly as
it was, and does not terminate it.

What a runtime failure is never allowed to be: wrapping without explicit
syntax, saturation, a Rust panic, a Cranelift panic, undefined behavior,
a raw hardware signal presented as language semantics, or different
between `napitia run` and a built executable.

### Division, remainder and shifts

These are interpreter-only. The native capability validator refuses
`div`, `rem`, `shl` and `shr` before code generation, and Alpha 0.2.1
does not change that.

| Expression | Result |
| --- | --- |
| `x / 0` | `X0001` |
| `x % 0` | `X0001` |
| `i64::MIN / -1` | `X0002` -- the exact quotient `9223372036854775808` is not an `i64` |
| `i64::MIN % -1` | `0` -- the exact remainder *is* an `i64`, so nothing overflows |
| `x << n`, `x >> n` for `n < 0` or `n >= 64` | `X0003` |
| `x >> n` for `0 <= n < 64` | arithmetic shift: the sign bit is replicated |
| `x << n` for `0 <= n < 64` | bits shifted off the top are discarded; `1 << 63` is the minimum |
| `x % y` otherwise | takes the sign of `x`, matching truncating division |

Shift counts are themselves `i64` -- Napitia has no executable unsigned
integer type -- so a negative count is expressible, and it is a failure
rather than a mask.

## Integer literals

The checker rejects a literal whose magnitude does not fit the type it
was inferred or annotated to have, before NIR lowering runs.

```napitia
value low:  i64 = -9223372036854775808   // accepted
value high: i64 =  9223372036854775807   // accepted
value too_low:  i64 = -9223372036854775809   // T0073
value too_high: i64 =  9223372036854775808   // T0073
```

`T0073` points at the literal, not at the enclosing function or
statement. The literal is never replaced by `Ty::Error`, never
truncated, never defaulted to zero, and never deferred to the
interpreter: `check`, `ir`, `run` and `build` all stop at the same
diagnostic, and lowering does not run.

A magnitude too large for `u128` remains the lexer's `N0002`: that is a
malformed token, not an out-of-range value.

## The other numeric types

`spec/0003` lists twelve numeric type names. Alpha 0.2.1 implements
exactly two of them, and says so:

| Name | `check` | `ir` | `run` | `build` |
| --- | --- | --- | --- | --- |
| `i64` | accepted | lowered | executed, checked, 64-bit | compiled |
| `f64` | accepted | lowered | executed as an IEEE-754 double | refused (`A0006`) |
| `i8` `i16` `i32` `isize` `u8` `u16` `u32` `u64` `usize` `f32` | refused (`T0074`) | — | — | — |

The ten refused names remain reserved: they parse, they resolve, and
naming one produces a diagnostic saying this milestone does not
implement it. They are not removed, not renamed, and not aliased. A
future release implements them, or a naming RFC changes them; neither is
this release's business.

Refusing them is the point of this milestone. Before it, `func f(x: i32)
-> i32` checked cleanly and then ran as 128-bit arithmetic wearing an
`i32` label -- the exact class of quiet lie this release exists to
remove. It is now forbidden for `check` to accept a numeric construct
that later reaches a fabricated value, a silent truncation, a
`Ty::Error`, an internal diagnostic or a Rust panic.

The NIR verifier enforces the same restriction independently, so
hand-built NIR cannot reach the interpreter or the backend carrying a
numeric type they do not implement.

## The diagnostics this RFC introduces

| Code | Stage | Meaning |
| --- | --- | --- |
| `T0073` | checking | an integer literal outside the domain of the type it resolved to |
| `T0074` | checking | a numeric type name this milestone does not execute |
| `V0111` | NIR verification | an integer constant outside the domain of its own declared type |
| `V0112` | NIR verification | a numeric type with no execution semantics, anywhere in NIR |
| `X0001` | run time | `div` or `rem` by zero |
| `X0002` | run time | integer overflow |
| `X0003` | run time | a shift count outside `0..64` |
| `X0004` | run time | malformed or unverified NIR the interpreter refused to execute, **or** an invalid operation on the execution engine itself -- reusing one a fatal abort already ended |
| `A0009` | native build | a construct outside the native backend's capability boundary: `div`, `rem`, `shl`, `shr` |

`X` is a new namespace, allocated the way `A` (native) and `V`
(verifier) each got one. Nothing existing is renumbered, and no `X`
code overlaps a compile-time one: they describe a program that compiled
and then failed while running.

A verifier code is not reachable from `.npt` source -- checking rejects
the same programs first -- and exists because NIR is hand-buildable.

## Floats

`f64` is real, in the interpreter only. What is actually implemented and
tested:

* finite values, including negative ones and both zeroes;
* `+`, `-`, `*`, `/` and `%` as Rust's `f64` operators, which are the
  IEEE-754 double operations;
* division by zero producing an infinity rather than `X0001` -- a zero
  divisor is only a failure for integers;
* the six comparisons, each evaluated with its own IEEE-754 predicate;
* deterministic printing through Rust's shortest round-tripping
  `Display`.

### NaN comparisons

A NaN is unordered with every value, itself included. Each predicate is
evaluated with the floating-point operator it names, so:

| Comparison | Result |
| --- | --- |
| `nan < x`, `nan <= x`, `nan > x`, `nan >= x` | `false` |
| `x < nan`, `x <= nan`, `x > nan`, `x >= nan` | `false` |
| `nan < nan`, `nan <= nan`, `nan > nan`, `nan >= nan` | `false` |
| `nan == x`, `x == nan`, `nan == nan` | `false` |
| `nan != x`, `x != nan`, `nan != nan` | `true` |

`false` here is an *answer*, not a failure. None of these produces a
diagnostic of any kind, and in particular none produces `X0004`: that
code means the interpreter was handed NIR it cannot execute, and a
program comparing a value it legitimately computed is not that.

`<=` and `>=` are the two that get this wrong if they are derived from a
total ordering by negation -- "not greater" and "not less" are true of a
NaN under any ordering that claims to have one. They are not derived
that way.

Napitia has no syntax naming a NaN, so the only way to obtain one is an
operation that produces it, such as `0.0 / 0.0`. Infinities are the
same, and compare normally: `1.0 / 0.0` is greater than every finite
value, and `0.0 == -0.0` is `true`.

What is not implemented: any syntax naming a NaN or an infinity
directly, float conversions of any kind, float bitwise operations, and
native float lowering. This is not complete IEEE-754 support, and this
release does not claim it is.

`f32` is refused. Nothing in the pipeline ever rounded an `f32` to
single precision; it was an `f64` with a different name.

## No implicit conversions

There are none, and this release adds none. `i64` and `f64` do not mix
in an expression, an argument, a return or a comparison; a mismatch is
`T0001`. There is no cast operator, no literal suffix, and no widening
or narrowing anywhere in the language.

Explicit wrapping, saturating and checked-result operations
(`wrapping_add`, `saturating_mul`, an `Outcome`-returning `checked_div`)
are *possibilities*, not commitments. None of them exists, none is
reserved, and none should be assumed.

## Native execution

The native backend represents `i64` as Cranelift `I64`. The Alpha 0.2.0
`I128` workaround, and the `enable_llvm_abi_extensions` flag that
existed only to carry it through the x86-64 ABI, are gone.

Checked `add`, `sub`, `mul` and `neg` compile to the arithmetic plus an
explicit signed-overflow test, branching to a failure path. That path is
a small internal runtime the backend emits into the same object: one
function per overflow-producing operator, each of which writes a fixed
diagnostic to file descriptor 2 and calls `exit`.

```text
napitia: error[X0002]: integer overflow in `add`
```

That is exactly what `napitia run` prints for the same failure, with the
program's own name in front of it. The code and the sentence come from
the same table both paths read, so they cannot drift.

The status is **70**, chosen once and documented here. It is the only
status a Napitia runtime failure produces.

A built executable's exit status is otherwise the low 8 bits of what
`main` returned, which is a language rule this release does not change.
It follows that status alone *cannot* distinguish a runtime failure from
a `main` that returned 70, or 326, or any other value congruent to 70
modulo 256. The stable discriminator is standard error: a successful run
writes nothing there, and a runtime failure writes exactly the line
above. This is a real limitation of an 8-bit exit status, stated rather
than papered over.

`main() -> unit` still exits 0.

## Interpreter/native equivalence

The two paths do not implement the same language. The interpreter is the
complete execution path; the native backend compiles one subset and
refuses everything else. Equivalence is a claim about that subset only,
and it is worth stating exactly what is in it.

**Natively compiled:** `i64`, `bool` and `unit`; constants, locals,
parameters and results of those types; `add`, `sub`, `mul`, `neg`,
bitwise `and`/`or`/`xor`/`not`, and the six comparisons; `if`, `while`,
branches and loop backedges; direct calls within one non-recursive call
graph; a single `main` returning `i64` or `unit`.

**Refused by the backend, with `A0009` for an operator and its own code
otherwise, while the interpreter runs them normally:** `div`, `rem`,
`shl`, `shr`, every `f64` program, and everything outside the scalar
subset (resources, `observe`, `defer`, typed failure, records, variants,
strings, `char`, generics, protocols, recursion, multi-module builds).

For every program *inside* that subset, `napitia run` and the built
executable agree:

* on the value `main` returns, modulo the documented 8-bit truncation;
* on whether the program fails at run time;
* on the failure's category and its exact message when it does.

They agree over the whole `i64` domain, both boundaries included,
because both now compute in exactly 64 bits.

Outside it there is no parity to claim, and this RFC claims none. In
particular the division rows in the table above -- `x / 0`, `x % 0`,
`i64::MIN / -1`, `i64::MIN % -1` -- and every shift row are
**interpreter-only**: a program containing any of those operators is
refused by the backend before code generation, so it has no native
behaviour to agree or disagree with. Of the checked operations, exactly
four are compiled: `add`, `sub`, `mul` and `neg`.

Neither execution path depends on how the *compiler* was built. Rust's
own debug-mode overflow checks are irrelevant, because no Napitia
arithmetic is performed by an unchecked Rust operator.

## What this RFC does not do

No new type names. No casts. No conversions. No `int`/`float` aliases.
No unsigned execution. No native floats. No native `div`/`rem`/shifts.
No wrapping or saturating APIs. No change to the native target, the
native subset's shape, or the sealed boundary `rfcs/0014` established
between verified NIR and Cranelift.
