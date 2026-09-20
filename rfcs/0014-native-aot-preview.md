# RFC 0014: Native AOT Preview (Alpha 0.2.0)

- Status: Accepted, implemented in Alpha 0.2.0

## Summary

Every milestone up to Alpha 0.1.9 ended at the interpreter. NIR was
designed from the start as "a reasonable input to a future native
backend" (`spec/0006`), and this milestone builds the smallest honest
version of that backend: a Cranelift path from already-verified NIR to
a real `x86_64-unknown-linux-gnu` executable.

```bash
napitia build examples/native_scalar_calls.npt --output scalar
./scalar; echo $?    # 42
```

The whole design is in what it refuses. Napitia's semantics live in the
interpreter, and this release does not move any of them. Resources,
observations, `defer`, typed failure, records, variants, strings,
generics and capability protocols all behave exactly as they did in
Alpha 0.1.9 under `check`, `ir` and `run`. None of them is compiled
here -- not approximately, not with the feature erased, not with a unit
value standing in for it, and never by quietly handing the program back
to the interpreter. `napitia build` compiles one small subset and
refuses everything else with a diagnostic that names what it refused.

This is a *preview*. It is not a production backend, and the subset
below is not a plan for what the language will support -- it is a
report of what is actually compiled today.

## The command

```text
napitia build <source.npt> --output <executable>
```

`build` takes a single `.npt` file. It is not a project command: a
directory or a manifest path is a usage error rather than something
refused later with a worse message. `--output` is required; guessing
where to put a file the user will execute is not the compiler's
decision.

`check`, `ir` and `run` are unchanged, including their acceptance of
project paths. `run` remains the complete semantic execution path for
the language.

## The target

```text
x86_64-unknown-linux-gnu
```

One target, implicitly and exclusively. There is no `--target` flag,
because there is no second target to select. A second one would need
its own ABI decisions, its own linker contract and its own end-to-end
test matrix, none of which this milestone has.

Object generation is host-independent: Cranelift writes an ELF object
for that target from a Windows or macOS host just as well. *Linking*
one is not, and the requirement is all three components of the target,
environment included. A musl host is Linux on x86-64, and its `cc`
still builds against a different C runtime than the one
`x86_64-unknown-linux-gnu` names, so it does not qualify; it receives a
structured refusal (`A0021`) naming the host rather than a confusing
error from a linker handed an object it cannot use.

Qualifying as a host is necessary and not sufficient. A GNU x86-64
Linux machine can still have a `cc` that cross-compiles somewhere else,
so before anything is written the toolchain is asked directly, with
`cc -dumpmachine`. Its answer is compared by architecture, operating
system and environment through `target-lexicon` -- never by substring
-- which is what makes the spellings real toolchains report
(`x86_64-linux-gnu` on Debian, `x86_64-pc-linux-gnu` elsewhere) the
same target while musl, i686, aarch64 and darwin are not. A linker that
targets something else, or will not say what it targets, is refused
with `A0025` and no executable is published.

## The pipeline

```text
source
  -> lexer -> parser -> hir -> typeck -> resourceck
  -> nir::lower -> nir::verify
  -> native::capability -> native::lower -> system linker
  -> executable
```

The first seven stages are the ones `napitia ir` already runs, shared
rather than repeated, so `check`, `ir`, `run` and `build` agree by
construction about what a program means. A stage that fails stops the
pipeline; no later stage runs, and nothing is written.

Two properties of the ordering are load-bearing:

- **`nir::verify` is mandatory and runs first.** Code generation never
  sees NIR the verifier has not accepted.
- **Capability validation runs after verification and before
  Cranelift.** It decides exhaustively whether the reachable program is
  inside the subset, which is why lowering contains no "unsupported,
  give up" path: by the time it runs, there is nothing left to give up
  on.

That ordering is enforced by the types, not by convention. The
capability validator's own output -- the compilation plan -- has
private fields, so it is the only thing that can produce one, and
Cranelift lowering takes one by reference. There is no way to reach
code generation without having gone through the capability check, from
inside the compiler or outside it.

The public surface is `napitia build` and, for anything embedding the
compiler, `driver::build_native` -- the entry that runs the whole
frontend and the verifier. Raw code generation is not a supported entry
point: the capability validator, the lowering module and the
NIR-to-executable function are all internal to the crate. There is no
callable path from arbitrary NIR to Cranelift.

## The native subset

This table is authoritative. Every other document summarizes it and
links here rather than restating it.

| category | natively compiled |
| --- | --- |
| types | `i64`, `bool`, `unit` |
| constants | integer, boolean, unit |
| locals | scalar `alloc`/`load`/`store` slots |
| signatures | scalar parameters and results, any arity |
| arithmetic | `add`, `sub`, `mul`, `neg` |
| bitwise | `and`, `or`, `xor`, `not` |
| comparison | `==`, `!=`, `<`, `<=`, `>`, `>=` |
| control flow | `if`, `while`, `branch`, `condbranch`, loop backedges |
| calls | direct calls to functions defined in the same file |
| call graph | non-recursive only |
| entry point | exactly one `main`, `main() -> unit` or `main() -> i64` |

Everything below is *rejected by `napitia build`* and *unchanged
everywhere else*:

| category | code | still works through |
| --- | --- | --- |
| resources, `drop`, resource moves | `A0006`/`A0007` | `check`, `ir`, `run` |
| `observe` | `A0007` | `check`, `ir`, `run` |
| `defer` and deferred cleanup | `A0007` | `check`, `ir`, `run` |
| typed errors, `raise`, `?`, `handle` | `A0008`/`A0012` | `check`, `ir`, `run` |
| records | `A0006`/`A0007` | `check`, `ir`, `run` |
| variants and `match` | `A0006`/`A0007`/`A0008` | `check`, `ir`, `run` |
| strings, `char`, floats, other integer widths | `A0006` | `check`, `ir`, `run` |
| generics | `A0010` | `check`, `ir`, `run` |
| protocols and evidence dispatch | `A0011` | `check`, `ir`, `run` |
| `import`, multi-module builds | `A0016` | `check`, `ir`, `run` |
| recursion, mutual recursion | `A0015` | `check`, `ir`, `run` |
| `div`, `rem`, `shl`, `shr` | `A0009` | `check`, `ir`, `run` |
| a callee this file does not define | `A0013` | -- |
| a target other than the one above | `A0001` | -- |

There is no native heap allocation, no garbage collector, no reference
counting, no borrowing or lifetime system, no FFI, no threads, no
native typed-failure runtime, no multi-module native compilation and no
JIT. None of these is partially present.

## Representation and ABI

The ABI is internal. Nothing here is a stable interface, and the only
symbol that is documented is the exported `main`.

| Napitia | Cranelift | notes |
| --- | --- | --- |
| `i64` | `I128` | see below |
| `bool` | `I8` | canonically `0` or `1`, always normalized |
| `unit` | *nothing* | no register, no slot, no ABI position |

`i64` being 128 bits wide natively is the one surprising choice in this
release, and it is deliberate. **The interpreter holds every Napitia
integer in an `i128` and wraps at 128 bits** -- `Value::Int(i128)`,
`i128::wrapping_add` and friends -- never narrowing to the declared
width. Compiling `i64` to 64-bit machine arithmetic would therefore
disagree with the reference implementation for every operation whose
mathematical result leaves `i64`'s range. Matching the interpreter
exactly, over the whole input domain, is worth two registers. The edges
of that width are tested against the interpreter directly -- wrapping
addition, subtraction and multiplication, the one value whose negation
is itself, ordering across the sign boundary, and bitwise work on the
high half a 64-bit representation would drop -- along with the two ABI
shapes those boundaries travel through: a call with more `i64`
arguments than the platform passes in registers, and a `unit` parameter
in the middle of a signature, which must shift nothing after it.

This is an honest limitation rather than a design: Napitia's declared
`i64` width and its interpreter's actual integer width are not yet the
same thing. `spec/0005` says integer overflow should eventually be an
unrecoverable panic in checked arithmetic, which would settle both
sides at once. That is a language decision, not a backend one, and it
is out of scope here. Until it is made, the native backend reproduces
what the interpreter does rather than inventing a third answer.

`unit` is represented by no value at all, because it has exactly one
inhabitant. A `unit` parameter does not appear in a native signature, a
`unit` result makes the signature return nothing, and a `unit` slot
holds no variable. Nothing fabricates a placeholder for it.

## The entry point and exit status

Napitia's own `main` is compiled like any other function, under an
internal mangled symbol. A separate exported `main` wraps it -- that is
the symbol the C runtime calls, and the only one this release
documents.

- `main() -> unit` exits with status `0`.
- `main() -> i64` hands the low 32 bits of the returned value back as
  the C `int` result. The kernel reports a normally-exited process's
  status to its parent as the low 8 bits of that, so **the observable
  exit status is the Napitia value taken modulo 256**: `return 42` is
  observed as `42`, and `return 300` as `44`.

Tests pin exit values inside `0..=125`, where the conversion is the
identity, except for one test of `300` that exists precisely to pin the
conversion itself.

## Arithmetic

Every operator the backend accepts agrees with the interpreter on every
input, with no exceptional case. Four are refused rather than
approximated:

- **`div` and `rem`**, because the interpreter answers a zero divisor
  with `InterpreterError::DivisionByZero` -- a runtime error *value* --
  and Alpha 0.2.0 has no native runtime facility to raise, report or
  carry one. A hardware trap is a different behavior, not the same one
  implemented differently.
- **`shl` and `shr`**, for the same reason: the interpreter rejects an
  out-of-range shift amount with a runtime error
  (`i128::checked_shl`/`checked_shr` plus an explicit `u32`
  conversion), where the hardware would silently mask the amount.

These are refused with `A0009`, by name, at the instruction that uses
them. The alternative -- emitting a machine instruction whose
exceptional behavior differs from the language's -- is exactly the
borrowed-host-semantics failure this backend exists to avoid.

## Reachability

One definition applies at both levels:

- a function is reachable when `main` reaches it through a chain of
  direct calls;
- a block is reachable when its own function's entry block (`bb0`)
  reaches it through terminator edges.

The backend validates, and then compiles, exactly that set. Nothing
outside it is validated, lowered, consulted for a call edge, or allowed
to define a value, a slot or a type that reachable code generation can
see -- which makes "unreachable NIR never contaminates a live
compilation" a structural fact rather than a promise.

The visible consequence: a file may declare a `resource`, or a
recursive helper, and still build natively, as long as `main` never
reaches it. That is the same thing the interpreter does with dead code,
which is nothing.

## Determinism

The same program produces byte-identical output on the same toolchain.
What that rests on:

- functions are declared, and then defined, in ascending item-id order,
  never in the order the module happens to store them;
- blocks are created and filled in reverse postorder of a traversal
  that visits successors in ascending block order, so block storage
  order is irrelevant too;
- every map keyed by a NIR identity is a `BTreeMap`; nothing is
  iterated in hash order, and nothing depends on a pointer address;
- symbol names come from an item's own id and declared name, not from a
  counter or a position in a vector;
- the linker is invoked with an argument vector that is identical from
  one build to the next (see below), with build ids disabled -- a build
  id is a hash the linker would otherwise stamp into the executable,
  and it is the one byte range two identical builds would differ in.

Tests hold all of this: object bytes from two independent compilations,
object bytes with the module's function and block vectors reversed, and
the bytes of two separately linked executables.

## The linker

`napitia build` links with `cc`, launched as a program through
`std::process::Command`. There is no shell, no command string and no
quoting to get wrong.

The object is written into a scratch directory created *beside* the
output with `std::fs::create_dir`, which fails rather than succeeds on
a path that already exists -- so a build only ever writes into, and
only ever removes, a directory it owns. The linker runs inside that
directory and is handed two constant relative names, so no path the
user chose ever reaches its argument vector; a path containing spaces
is a non-issue for the same reason the argument vector is constant.

The output itself is written exactly once, at the end, by renaming a
finished executable over it. This is the atomicity rule, and it holds
for every stage: **if the command reports failure, the requested output
is byte-for-byte what it was before.** A link that fails cannot leave a
truncated file that looks like a build, and an executable an earlier
build left there is never replaced by a broken one.

Two consequences follow, and both are deliberate. A cleanup failure
never replaces the reason a build failed, because that reason is what
the user needs. And publication is final: once the executable is in
place, nothing afterwards can turn the build into a failure, since
reporting one would mean saying "failed" about an output that was
already replaced. Removing the scratch directory after successful
publication is therefore **best-effort** -- on the rare path where it
fails, a `.napitia-build-*` directory is left beside the output and the
build still succeeds. Cleanup is attempted on every path either way.

Launch failure, a non-zero exit, the linker's stdout and its stderr are
all captured and turned into one structured diagnostic. Nothing panics.

## Diagnostics

`A0001`-`A0019` are the capability layer: reasons a perfectly valid
Napitia program is outside the native subset. `A0020`-`A0025` are the
backend layer: something went wrong producing the executable.

| code | meaning |
| --- | --- |
| `A0001` | a target triple other than `x86_64-unknown-linux-gnu` |
| `A0002` | no `main` |
| `A0003` | more than one `main` |
| `A0004` | `main` declares parameters |
| `A0005` | `main` returns neither `unit` nor `i64` |
| `A0006` | a type outside `{i64, bool, unit}` in a reachable position |
| `A0007` | a reachable resource/observation/`defer`/aggregate instruction |
| `A0008` | a reachable `switch`, `invoke` or `raise` |
| `A0009` | a reachable `div`, `rem`, `shl` or `shr` |
| `A0010` | a reachable generic function or generic call |
| `A0011` | a reachable `uses` requirement or evidence dispatch |
| `A0012` | a reachable function declaring `raises` |
| `A0013` | a call to a function this file does not define |
| `A0014` | a direct call disagreeing with its callee's signature |
| `A0015` | a cycle in the reachable direct-call graph |
| `A0016` | an `import`, or NIR spanning more than one module |
| `A0017` | a `load` not preceded by a `store` on every path |
| `A0018` | an `alloc` result used as an ordinary value |
| `A0019` | structure `nir::verify` owns, reaching this backend |
| `A0020` | Cranelift rejected or failed to emit something |
| `A0021` | this host cannot link for the native target |
| `A0022` | the system linker could not be launched |
| `A0023` | the system linker exited non-zero |
| `A0024` | the build could not write or move a file |
| `A0025` | the system linker targets something else, or would not say |

The `A` prefix is a new namespace, allocated the way `V` (verifier) and
`U` (ownership) each got one when those layers appeared. No existing
code is renumbered.

Two rules keep the layers apart. *Malformed* NIR is the verifier's
business and keeps its `V` code; the native pass reports `A0019` and
refuses only when handed NIR that never went through the verifier,
which ordinary compilation cannot do. *Valid but unsupported* NIR is
the capability layer's business. A program that uses a resource is not
malformed, and a program with a dangling block target is not merely
unsupported.

At most one diagnostic is reported per reachable function, plus one per
call-graph cycle, plus the module-level ones (target, `import`): this
pass is a gate, not an incremental checker, and listing every
instruction that touches a resource would bury the one reason that
matters. A function that fails for its signature is not then reported
again for its body. Diagnostic order is fixed -- target, then
module-level facts, then the entry contract, then each reachable
function in ascending item order, then call-graph cycles -- so repeated
builds produce byte-identical output.

A program does commonly draw more than one diagnostic, because more
than one *function* is outside the subset: a three-function resource
program reports the constructor's result type, the reader's parameter
type and `main`'s own use of the value, which are three functions, not
three symptoms of one.

## Two slot rules worth naming

Both exist because the alternative would be a fabricated value.

- **`A0017`, a `load` with no `store` on some path.** The interpreter
  models a slot as an entry in its value table that `alloc` seeds with
  `Value::Unit`; Cranelift's SSA builder answers an undefined variable
  by silently materializing a zero. Those are two different answers and
  neither is one this backend is willing to invent, so it refuses the
  program instead. No lowering from real Napitia source produces this;
  hand-built NIR can.
- **`A0018`, an `alloc` result used as a value.** A slot is only ever
  stored into or loaded from. Treating it as its own contents would be
  a guess about which of the two was meant.

## Deliberately unsupported

Each of these is a *native backend* restriction, not a language change.
Every one still compiles, checks and runs exactly as it did in Alpha
0.1.9:

resources and resource ownership; resource moves and drops; `observe`;
`defer` and deferred cleanup; typed errors, `raise`, postfix `?` and
`handle`; records; variants and `match`; strings, `char`, floats, and
integer widths other than `i64`; `import` and multi-module compilation;
generics and monomorphization; protocols, extends and evidence
dispatch; indirect calls of any kind; recursion and mutual recursion;
native heap allocation; garbage collection; reference counting;
borrowing and lifetime inference; FFI; threads and structured
concurrency; a native typed-failure runtime; JIT execution; and any
target other than `x86_64-unknown-linux-gnu`.

## Non-goals

- This is not a performance release. Cranelift runs at `opt_level =
  none`, because the output that most obviously corresponds to the NIR
  it came from is the one a differential test against the interpreter
  can actually be trusted on.
- This is not a second semantics. Where the native backend cannot
  reproduce the interpreter exactly, it refuses; it never resolves the
  difference in its own favor.
- This is not a target abstraction. There is one target, named as a
  string, with no layer in front of it waiting for a second.

## Unresolved research questions

- **Integer width.** The interpreter's `i128` and the language's `i64`
  need to become the same thing, with `spec/0005`'s overflow panic or
  an explicit wrapping rule. Whichever is chosen, the native
  representation narrows to `I64` and this release's `I128` choice goes
  away with it.
- **`div`/`rem`/`shl`/`shr`.** These need a native runtime facility
  that can report a runtime error -- the same facility a future native
  typed-failure or panic mechanism needs. They are refused rather than
  approximated until one exists.
- **Executable determinism across toolchains.** Object determinism is
  this backend's own property and is tested directly. Executable
  determinism additionally depends on the system linker and the C
  runtime it links against; build ids are disabled, and two builds on
  one toolchain are byte-identical, but two different `cc` versions are
  not expected to agree and nothing here tries to make them.
- **Recursion.** Nothing about the machine prevents it; the call-graph
  restriction exists because a preview that guarantees termination of
  its own analyses is easier to trust than one that does not. Lifting
  it is a small change to the validator, not to the backend.
