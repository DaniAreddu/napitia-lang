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

## Current status: Alpha 0.1.3

This milestone rounds out Alpha 0.1.2's multi-file projects with import
ergonomics and precise cross-module identity: `import a.b.c as d;` lets
one item be given a local alias, so two same-named declarations from
different modules (two unrelated `User` records, say) can be used
together in one scope without colliding — the alias is purely a local
spelling and never changes an item's own identity, declared name, or
the type it names. Textual NIR (`napitia ir`) is now module-qualified
(`sales.user.User#2`, not just `User`), so two same-named items from
different modules always print distinguishably, and two different
module paths that resolve to the same physical file (a symlink or
junction) are now rejected outright. It builds on Alpha 0.1.2's
multi-file projects (a `napitia.toml` manifest, one file per module,
cross-module `import`, `public`/`private` enforced across module
boundaries) and Alpha 0.1.1's data model (nominal records and variants,
construction, field access, qualified variant constructors, and
exhaustive pattern matching, executed end to end by the interpreter).

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
  and `match` (lowered to a real decision tree over `switch`/`condbr`)
  all have full NIR representation now; casts, `defer`, postfix `?`,
  non-empty `uses`/`raises` clauses, and a value-carrying `break`
  remain parsed-but-rejected, never silently accepted or faked.
  Lowering the rest of a module is atomic: either every function
  lowers, or the whole module fails with diagnostics.
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
  resolve to the same physical file (`M0013`) — see below.

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
unambiguously: `expected `admin.user.User`, found `sales.user.User``.
`napitia ir`'s textual output qualifies every item, and every type in a
parameter/return/allocation position, by its declaring module
(`sales.user.User#2`, not just `User`), so two same-named items from
different modules always print distinguishably there too; aliases never
appear in either diagnostics or NIR output, only each item's own true
declared name. See `rfcs/0007-module-identity-and-import-aliases.md` for
the full design, the collision rules, and the current honest limitations.

### Explicitly not yet implemented

Field mutation, record/variant equality, pattern guards, or-patterns,
record-destructuring/slice/range patterns, generics, protocols, a
`Maybe<T>` absence type, checked `uses`/`raises` effects and errors,
ownership/region enforcement (and the indirection that would lift the
recursive-aggregate restriction), structured concurrency, remote
packages/dependency declarations, wildcard/grouped imports, re-exports,
package/module aliases (as opposed to the per-item import aliases that do
exist — see above), incremental/cached compilation, an LLVM (or any
native) backend, garbage collection, and any domain-specific library
(REST, ORM, tensors, GPU).
Design direction for most of these exists in `rfcs/`;
none of it is faked in the implementation.

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
