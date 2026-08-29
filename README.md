# Napitia

Napitia is an experimental, general-purpose, statically typed programming
language. It is designed around a simple premise: engineers should not have
to choose between the readability of Python, the reliability and tooling of
Java, and the raw performance and control of C++. Napitia aims to combine
the strengths of all three while eliminating a specific list of long-standing
engineering hazards.

Napitia is **not production-ready**. It is currently a research and
engineering project in its earliest stage (Alpha). This repository contains
the reference compiler, written in Rust, and the specifications that define
the language.

Source files use the `.npt` extension.

## Design goals

Napitia is being built toward the following, in rough order of how the
project is sequenced:

- Python-like readability, local type inference, and a fast script-to-run
  feedback loop.
- Java-like reliability, modularity, and structured-concurrency-based
  application development, without a mandatory garbage collector or a GIL.
- C++-level native performance: deterministic resource management,
  predictable memory layout, SIMD, FFI, and direct hardware access.
- Memory safety by default, with `unsafe` as a small, quarantined escape
  hatch rather than an ambient capability.
- No `null`, no unchecked exceptions, no textual preprocessor, no implicit
  dangerous conversions, no undefined behavior in safe code.
- One official toolchain for building, testing, formatting, and documenting
  code — not a fragmented ecosystem of competing third-party tools.
- AOT native compilation for production builds, with a REPL and JIT
  execution path during development that shares identical semantics with
  the AOT path.

REST APIs, database access, distributed systems, and AI/ML are explicitly
**not** language features. They are intended to be ordinary libraries built
on top of Napitia's generics, protocols, and effect system, once those exist.
Nothing about the language core should need to know these domains exist.

## Current status: Alpha 0.1.8

This milestone extends Alpha 0.1.7's ownership tracking from whole
local bindings to individual resource-bearing *fields*. A `record`,
`variant`, or `resource` that reachably contains an affine field
becomes affine *transitively* — Alpha 0.1.7's blanket rejection of a
resource-typed field in any aggregate is lifted:

```napitia
resource File { descriptor: i64 }
resource Session { input: File, output: File }

func detach(take session: Session) -> File {
    value input = session.input   // transfers only this field
    drop session                   // structurally destroys `output`,
    return input                   // then `session`'s own outer identity
}
```

Ownership is tracked per structural *place* (a root binding plus a path
of stable field projections, `compiler/src/place.rs`), shared unchanged
by the resource checker, NIR lowering, and the NIR verifier. Moving one
field never affects an unaffected sibling; a partially-moved aggregate
may still be used to access a remaining field, reinitialize the moved
one (once every reachable path proves it empty), or be structurally
dropped, but is rejected outright if used as a whole (observed,
returned, transferred, or passed) until it is whole again. A variant's
own payload — never individually addressable outside a pattern match —
is tracked as one opaque unit; matching an affine scrutinee transfers
ownership of the bound case's own payload. NIR gains explicit place
operations (`load.place`/`move.place`/`store.place`), independently
re-verified by the same reachable-union dataflow shape Alpha 0.1.7's
own resource-initialization check already used, now keyed by place
rather than by bare value; the interpreter gains structural tombstones
(`Moved`/`Dropped`) so a use-after-move/drop of a field is a structured
runtime error, an independent backstop for anything the static checks
already rule out. See `rfcs/0012-structural-ownership.md` for the full
design, the exact destruction order, and current honest limitations
(no record-destructuring pattern syntax, no per-case cleanup of a
wildcard-discarded affine payload, no resource-affine generic
*function* instantiation).

### Alpha 0.1.7: deterministic resources

This milestone added `resource`/`take`/`drop`/`defer`: Napitia's first
memory/resource-safety layer, not a copy of Rust's ownership/borrow/
lifetime system, C++ destructors/`delete`, Java garbage collection, or
Go's tuple-error convention. A `resource` declaration
(`resource File { descriptor: i64 }`) is an affine, non-copyable nominal
aggregate — reusing a `record`'s own construction syntax unchanged — with
exactly one owner at a time, tracked through every function body by a
dedicated compiler stage (`resourceck/`). Assigning, returning, storing
in a field, or passing to a `take` parameter moves ownership; an
ordinary (non-`take`) parameter is a call-scoped observation the callee
never owns and can never let escape. `drop file` destroys a live
resource immediately; every resource still owned at its own function's
exit is destroyed implicitly, in reverse declaration order; `defer
close(file)` registers a call that runs exactly once, in LIFO order,
interleaved with implicit destruction. Use-after-move, use-after-drop,
double-drop, moving a value a pending `defer` still needs, and an
observation escaping its call are all compile-time diagnostics. NIR
represents destruction explicitly (a new `Drop` instruction) and an
independent verifier pass proves no value is ever read or dropped twice
on any reachable path, using the same reachability-aware forward
must-dataflow analysis Alpha 0.1.6's own `Invoke`-slot verification
uses. It builds on Alpha 0.1.6's typed outcomes (`rfcs/0010`), Alpha
0.1.5's capability protocols (`rfcs/0009`), Alpha 0.1.4's generics
(`rfcs/0008`), and Alpha 0.1.3's module-qualified identity and import
aliases (`rfcs/0007`). See `rfcs/0011-deterministic-resources.md` for
the full design and current honest limitations — this defines and
verifies memory *semantics*; it does not implement a native heap
allocator, general references, lifetime annotations, shared ownership,
reference counting, or a tracing garbage collector.

### Alpha 0.1.6: typed outcomes

Alpha 0.1.6 added `raises`/`raise`/postfix `?`/`handle`: a custom,
statically checked failure model, not a copy of Rust's `Result`,
Java/Python/C++ exceptions, or Go's tuple-return convention. A function's
raised-error set is part of its signature, exactly like its return type
(`func read_config(path: str) -> str raises FileError { ... }`); `raise
FileError.Missing` produces a failure and unconditionally diverges; `?`
explicitly propagates a fallible call's failure to the enclosing
function's own declared `raises` set; `handle <expr> { success v => ...,
failure FileError.Missing => ... }` exhaustively consumes every raised
case, at case granularity, across however many distinct raised types are
in play. A fallible call left unhandled — not propagated, not consumed —
is a compile-time diagnostic; there is no ambient exception channel and
no implicit unwinding. `Terminator::Invoke`/`Terminator::Raise` give this
an explicit two-destination NIR representation (success and failure are
both just typed CFG edges), independently re-checked by the same NIR
verifier pass every other construct already distrusts hand-built NIR for.
It builds on Alpha 0.1.5's capability protocols (`rfcs/0009`), Alpha
0.1.4's generics (`rfcs/0008`), and Alpha 0.1.3's module-qualified
identity and import aliases (`rfcs/0007`).

### Implemented in this milestone

- A byte-offset based source manager (`source/`) with line/column mapping.
- A structured diagnostics engine (`diagnostics/`) with human-readable,
  `rustc`-style rendered output.
- A symbol interner (`symbol/`).
- A hand-written lexer (`lexer/`) covering identifiers, keywords, numeric
  literals (decimal/binary/octal/hex, separators, floats, exponents),
  strings (with escapes), raw strings, characters, comments (line and
  nested block), and all initial operators/punctuation.
- A hand-written recursive-descent parser (`parser/`) with Pratt-style
  expression parsing, basic error recovery, and record-construction
  syntax (`TypeName { field: expr, ... }`, disambiguated from a
  following block the same way other brace-delimited languages resolve
  it), producing an AST (`syntax::ast`).
- Lowering from AST to a High-level IR (`hir/`) with lexical-scope based
  name resolution (`resolve/`), including nominal record/variant
  structure, qualified/unambiguous-unqualified variant constructor
  resolution, and stable pattern identity.
- A primitive type system (`types/`) and a local type checker (`typeck/`)
  performing constraint-based, monomorphic unification for integer/float
  literal inference, argument/return checking, and assignment
  compatibility — not full Hindley-Milner-style polymorphism; every
  binding is monomorphic once solved. Now also: nominal record
  construction/field access, variant constructors, an infinite-
  aggregate-layout cycle check, and `match` with a pattern-matrix
  exhaustiveness/unreachable-arm analysis that reports a concrete
  missing-pattern witness.
- A typed Napitia IR (`nir/`): explicit control-flow graphs of basic
  blocks, with a textual printer for debugging and a verifier pass that
  re-checks structural and type invariants before a module is ever
  interpreted. Record/variant construction, field/payload projection,
  `match` (lowered to a real decision tree over `switch`/`condbr`), and
  `raise`/postfix `?`/`handle` (lowered to `Invoke`/`Raise`), and
  `drop`/`defer`/implicit resource destruction (lowered to a new `Drop`
  instruction, see below) all have full NIR representation now; casts
  and a value-carrying `break` remain parsed-but-rejected, never
  silently accepted or faked. Lowering the rest of a module is atomic:
  either every function lowers, or the whole module fails with
  diagnostics.
- A tree-walking interpreter over NIR, used to execute the supported
  language subset (including records, variants, and `match`) without a
  native backend.
- A CLI (`napitia lex|parse|check|ir|run`) exposing every stage, now
  accepting either a single `.npt` file or a multi-file project.
- Multi-file projects (`project/`): a `napitia.toml` manifest, one file
  per module, cross-module `import`, and `public`/`private` enforced for
  real across module boundaries — see below.
- Import aliases (`import a.b.c as d;`), a canonical per-item identity
  registry (`hir::registry`) used by both NIR printing and verification,
  module-qualified textual NIR, and rejection of two module paths that
  resolve to the same physical file (`M0013`).
- Generics (`func`/`record`/`variant[T, ...]`): per-declaration type
  parameter identity, explicit and inferred type application, symbolic
  one-time body checking, `Ty::Applied`/`Ty::Param` with nominal identity
  and structural unification, a canonical generic-instance key reused by
  typeck/NIR/the verifier, parametric NIR (one lowering per declaration,
  concrete type arguments recorded per call/construction site), exhaustive
  `match` over an instantiated payload type, substitution-aware infinite-
  layout detection, and depth/instance-count budgets shared across every
  stage that walks a type application — see below.
- Capability protocols (`protocol`/`extend`/`uses`): explicit type
  parameters and call syntax with no `Self`/implicit receiver, authority
  and coherence checking for extensions, a dedicated capability solver
  producing compile-time evidence (dictionary passing, not a runtime
  vtable), exact-forwarding-only symbolic resolution, an entry-point
  restriction, and an independent NIR verifier pass covering every
  protocol/extend layout and every call's evidence — see below.
- Typed outcomes (`raises`/`raise`/postfix `?`/`handle`): a function's
  own canonical, deduplicated raised-error set as part of its signature;
  exhaustive, per-case `handle` coverage (a concrete missing-`Type.Case`
  witness on failure, not merely "non-exhaustive"); mandatory explicit
  handling at every fallible call site (propagate or consume — never
  silently ignored); an entry-point restriction mirroring capability
  protocols'; and an independent NIR verifier pass covering every
  `Invoke`/`Raise` the same way it already covers every other
  construct — see `rfcs/0010-typed-outcomes.md` for the full design and
  current honest limitations (there is no protocol/capability
  integration for typed failure yet).
- Deterministic resources (`resource`/`take`/`drop`/`defer`): a
  dedicated flow-sensitive resource checker (`resourceck/`) tracking
  every affine value's own state (`Available`/`Moved`/`DropScheduled`/
  `Dropped`) through a function body, joins that require reachable
  branches to agree, edge-sensitive loop-carried invalidation detection
  (`break` and `continue` tracked as distinct exits from the body's own
  fallthrough, since only `continue` and fallthrough feed the loop's own
  backedge), a resource-typed value bound by a `handle` `success`
  pattern, and a resource-typed temporary reaching a position nothing
  would ever destroy it from; NIR lowering inserts real `Drop`/
  deferred-call instructions at normal return/fallthrough, `raise`,
  postfix `?` propagation, and `break`/`continue` (destroying exactly
  that iteration's own live resources before jumping past or back to
  the loop); an independent NIR verifier pass proves every `Drop`
  targets a live resource value and no value is ever dropped twice on
  any reachable path — see `rfcs/0011-deterministic-resources.md` for
  the full design and current honest limitations (no general
  references, lifetimes, shared ownership, reference counting, tracing
  GC, or native allocator). Alpha 0.1.8 extends this to structural
  fields: a `record`/`variant`/`resource` reachably containing an
  affine field becomes affine transitively, tracked per structural
  place (partial move, sibling independence, reinitialization,
  structural drop order) rather than only per whole binding — see
  `rfcs/0012-structural-ownership.md`.

See `spec/` for the language specifications this milestone implements
against, and `rfcs/` for accepted design direction and open research
questions that go beyond what is implemented today.

### Multi-file projects

A project is a directory with a manifest:

```toml
# napitia.toml
[package]
name = "hello"
version = "0.1.0"

[project]
source-root = "src"
entry = "main.npt"
```

One `.npt` file is one module — there is no `module` declaration, and a
module never spans more than one file. A module's dotted path is its file
path relative to `source-root` with the extension stripped
(`src/models/user.npt` → `models.user`). `import models.user.User;` brings
item `User`, declared in module `models.user`, into the importing
module's own namespace by that unqualified name; every segment before the
last is the module path, the last is the imported item.

Items (`func`/`record`/`variant`) and individual record fields are
private by default and only reachable from another module if declared
`public` *and* actually imported — a private item, or a private field on
an otherwise-public record, can never be named from outside its
declaring module:

```napitia
// src/models/user.npt
public record User {
    public id: i64,
    email: str,      // private: not reachable from another module
}

public func make_user(id: i64) -> User {
    User { id: id, email: "" }
}
```

```napitia
// src/main.npt
import models.user.User;
import models.user.make_user;

func main() -> i64 {
    value u = make_user(7);
    return u.id
}
```

`check`/`ir`/`run` all accept a directory, a manifest path, or a `.npt`
file directly:

```bash
cargo run --manifest-path compiler/Cargo.toml -- run path/to/project
cargo run --manifest-path compiler/Cargo.toml -- run path/to/project/napitia.toml
cargo run --manifest-path compiler/Cargo.toml -- run path/to/project/src/main.npt
```

The manifest path itself can also be a bare relative path — `cd` into a
project directory and run `napitia check napitia.toml` — or `./napitia.toml`,
not just an absolute path.

The third form is legacy single-file mode: an explicit `.npt` path always
compiles just that one file through the same lex/parse/HIR/typeck/NIR
pipeline single-file compilation always used, even if a `napitia.toml`
happens to sit next to it.

See `rfcs/0006-multi-file-projects-and-modules.md` for the full
architecture and the complete list of project-level diagnostic codes.

### Import aliases and module identity

`import <path> as <alias>;` gives one imported item a local name distinct
from its own declared name — the only way to bring two same-named
declarations from different modules into one scope at once:

```napitia
import sales.user.User as SalesUser;
import admin.user.User as AdminUser;

func main() -> i64 {
    value s = SalesUser { id: 40 };
    value a = AdminUser { id: 2 };
    return s.id + a.id                 // 42
}
```

`SalesUser` and `AdminUser` remain exactly the two distinct types they
already were — an alias is a local spelling only, never a merge: passing
a `SalesUser` value anywhere `admin.user`'s own declaration is expected is
still an ordinary type error, and the message names both sides
unambiguously, showing `admin.user.User` and `sales.user.User` rather
than the same bare `User` twice. `napitia ir`'s textual output qualifies
every item, and every type in a parameter/return/allocation position, by
its declaring module (`sales.user.User#2`, not just `User`), so two
same-named items from different modules always print distinguishably
there too. Nominal types in both typechecker diagnostics and textual NIR
always use an item's canonical, module-qualified declaration name, never
an import alias substituted in its place; an alias-related resolution
diagnostic (an import colliding with something else, say) is a different
case and may naturally display the local alias that caused it, since
that alias is exactly what the diagnostic is about. See
`rfcs/0007-module-identity-and-import-aliases.md` for the full design,
the collision rules, and the current honest limitations.

### Generics

`func`/`record`/`variant` may each declare their own square-bracket type
parameters, applied explicitly or inferred at every reference:

```napitia
record Box[T] {
    value: T,
}

func unwrap[T](box: Box[T]) -> T {
    box.value
}

func main() -> i64 {
    unwrap(Box[i64] { value: 42 })   // 42, T inferred as i64
}
```

A generic declaration's own body is checked exactly once, symbolically,
against its own opaque `T` — never re-checked per instantiation, and never
permitting an operation nothing proves safe for an unconstrained type
parameter (equality, ordering, arithmetic, bitwise operators, logical use,
field access, and calling all require a concrete type; plain
passing/returning/binding/construction do not). Two same-named generic
declarations from different modules remain nominally distinct, and an
import alias never bridges them, exactly like every other declaration
(`rfcs/0007`). `match` exhaustiveness uses the *instantiated* payload type
(`Maybe[bool]`'s `Some` payload is checked as `bool`, a closed two-value
space, not the declaration's own unresolved `T`). NIR stays fully
parametric — a generic function lowers once, and a call site records only
its own concrete type arguments — and there is no native-code
monomorphization yet. See `rfcs/0008-canonical-generics.md` for the full
design, the diagnostic codes, and the current honest limitations.

### Capability protocols

```napitia
protocol Equal[T] {
    func equal(left: T, right: T) -> bool;
}

extend Equal[i64] {
    func equal(left: i64, right: i64) -> bool {
        left == right
    }
}

func pair_equal[T](a: T, b: T) -> bool uses Equal[T] {
    Equal[T].equal(a, b)   // forwards this function's own requirement
}

func main() -> bool {
    return pair_equal[i64](21, 21)
}
```

An `extend` is only legal in the module that owns its protocol or the
outermost nominal aggregate of its first type argument (a primitive
first argument requires the protocol's own module) — this is what stops
two unrelated modules from silently compiling contradictory
implementations of the same capability for the same type. Two extends
that could both match the same concrete instantiation are rejected as an
overlap, checked by a sound, deterministic, bidirectional structural
unifier over each extend's own head, entirely independent of any call
site or declaration order. A still-generic function can only satisfy its
own `uses` requirement by forwarding an identical caller requirement —
never by deriving, weakening, or combining one symbolically — and the
executable entry function cannot declare a `uses` requirement at all (it
has no caller to receive evidence from). An independent NIR verifier pass
re-checks every protocol/extend declaration's own shape and every call's
evidence against hand-built NIR, bounded by an explicit depth/work
budget, producing exactly one diagnostic per malformed evidence root.
See `rfcs/0009-capability-protocols.md` for the full design, the
diagnostic codes, and the current honest limitations.

### Explicitly not yet implemented

Field mutation, record/variant equality, pattern guards, or-patterns,
record-destructuring/slice/range patterns, an inline `[T: Protocol]`
bound spelling on a generic type parameter (the underlying capability
requirement exists via `uses Protocol[T]` on the function — see above),
protocol default methods/supertraits/first-class protocol values, a
protocol method (or its own implementing `extend` method, rejected the
same way) declaring `raises` (typed failure has no protocol/capability
integration yet — see `rfcs/0010`), generic error variants (explicitly
diagnosed, not merely unspellable — a `raises` entry naming a generic
variant is rejected), partial `handle` (consuming only some raised
effects and re-raising the rest), first-class effect/error values, stack
traces or
`panic`/`recover`, general references/borrowing, lifetime annotations,
raw pointers, shared ownership, reference counting, a tracing garbage
collector, a native heap allocator (Alpha 0.1.7's `resource` values are
semantic runtime objects the interpreter tracks, not pointers into
process memory — see `rfcs/0011`), a resource-affine *generic function*
instantiation (rejected with a dedicated diagnostic rather than
supported — a generic aggregate's own affinity, unlike a generic
function's body, is recomputed per instantiation and does work — see
`rfcs/0012`), protocols over resource (or otherwise affine) types, a
user-defined destructor body attached directly to a `resource`
declaration, record-destructuring pattern syntax (only the pattern
shapes that already parsed — a bare binding, a variant case's own
positional payload — are resource-aware), per-case structural cleanup
of an affine payload discarded through a wildcard match pattern, a
resource-typed `match`/`handle`/non-tail `if`, the indirection that
would lift the recursive-aggregate restriction, structured concurrency,
remote packages/dependency declarations, wildcard/grouped imports,
re-exports, package/module aliases (as opposed to the per-item import
aliases that do exist — see above), incremental/cached compilation, an
LLVM (or any native) backend, native-code generic
specialization/monomorphization, garbage collection, and any
domain-specific library (REST, ORM, tensors, GPU). Design direction for
most of these exists in `rfcs/`; none of it is faked in the
implementation.

## Building

Napitia's compiler is a single Cargo package rooted at `compiler/` (not
a Cargo workspace — there is one crate: a `compiler` library plus a thin
binary named `napitia`). Built and tested against `rustc 1.97.1`
(edition 2024, which itself requires `rustc >= 1.85`); `rust-toolchain.toml`
at the repository root pins this as the tested toolchain (and is what
`rustup` picks up automatically), not a guaranteed lower bound —
`compiler/Cargo.toml` deliberately does not set `rust-version`, since no
minimum has actually been established.

```bash
cargo build --manifest-path compiler/Cargo.toml
cargo test --manifest-path compiler/Cargo.toml
```

## Using the CLI

```bash
cargo run --manifest-path compiler/Cargo.toml -- lex examples/hello.npt
cargo run --manifest-path compiler/Cargo.toml -- parse examples/hello.npt
cargo run --manifest-path compiler/Cargo.toml -- check examples/hello.npt
cargo run --manifest-path compiler/Cargo.toml -- ir examples/hello.npt
cargo run --manifest-path compiler/Cargo.toml -- run examples/hello.npt
```

See `examples/` for sample `.npt` programs, including intentionally invalid
ones used to exercise diagnostics.

## Repository layout

```text
compiler/    Rust package (single crate): the reference Napitia compiler
spec/        Normative specifications for implemented language behavior
rfcs/        Accepted design direction and long-term research questions
examples/    Sample .npt programs, including invalid ones for diagnostics
```

## Contributing

See `CONTRIBUTING.md`.

## License

See `LICENSE`.
