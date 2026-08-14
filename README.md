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

## Current status: Alpha 0.1

This milestone implements a compiler **frontend** and a typed intermediate
representation, plus a small interpreter to validate semantics before any
native backend exists.

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
  expression parsing and basic error recovery, producing an AST
  (`syntax::ast`).
- Lowering from AST to a High-level IR (`hir/`) with lexical-scope based
  name resolution (`resolve/`).
- A primitive type system (`types/`) and a local type checker (`typeck/`)
  performing constraint-based, monomorphic unification for integer/float
  literal inference, argument/return checking, and assignment
  compatibility — not full Hindley-Milner-style polymorphism; every
  binding is monomorphic once solved.
- A typed Napitia IR (`nir/`): explicit control-flow graphs of basic
  blocks, with a textual printer for debugging and a verifier pass that
  re-checks structural and type invariants before a module is ever
  interpreted. `match`, field access, casts, `defer`, postfix `?`, and
  non-empty `uses`/`raises` clauses are all parsed, but using any of them
  is a checked, reported error rather than being lowered or executed —
  none of them are silently accepted or faked. Lowering the rest of a
  module is atomic: either every function lowers, or the whole module
  fails with diagnostics.
- A tree-walking interpreter over NIR, used to execute the supported
  language subset without a native backend.
- A CLI (`napitia lex|parse|check|ir|run`) exposing every stage.

See `spec/` for the language specifications this milestone implements
against, and `rfcs/` for accepted design direction and open research
questions that go beyond what is implemented today.

### Explicitly not yet implemented

Generics, protocols, a `Maybe<T>` absence type, checked `uses`/`raises`
effects and errors, ownership/region enforcement, structured concurrency,
modules beyond a single file, an LLVM (or any native) backend, garbage
collection, a package manager, and any domain-specific library (REST,
ORM, tensors, GPU). Design direction for most of these exists in `rfcs/`;
none of it is faked in the implementation.

## Building

Napitia's compiler is a single Cargo package rooted at `compiler/` (not
a Cargo workspace — there is one crate: a `compiler` library plus a thin
binary named `napitia`). Built and tested against `rustc 1.97.1`
(edition 2024, which itself requires `rustc >= 1.85`); `rust-version` in
`compiler/Cargo.toml` records this as the verified toolchain, not a
guaranteed lower bound.

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
