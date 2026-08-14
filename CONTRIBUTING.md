# Contributing to Napitia

Napitia is an early-stage, experimental language. This document describes
how the reference compiler is developed so contributions stay consistent
with the rest of the codebase.

## Scope discipline

Before adding a feature, check `spec/` and `rfcs/`:

- If a spec already describes the behavior, implement exactly that
  behavior — no more, no less.
- If only an RFC describes it as accepted direction, open a discussion
  before implementing; RFCs describe *where the language is going*, not
  a green light to build ahead of the current milestone.
- If neither mentions it, propose an RFC first. Do not add REST, database,
  AI/ML, or other domain-specific behavior to the compiler itself — those
  are meant to be libraries built on top of the language, never special
  cases inside it.

## Toolchain

All contributions must pass, from the repository root:

```bash
cargo fmt --manifest-path compiler/Cargo.toml --check
cargo clippy --manifest-path compiler/Cargo.toml --all-targets -- -D warnings
cargo test --manifest-path compiler/Cargo.toml
```

Do not silence Clippy with a blanket `#[allow(...)]` to make a warning
disappear. If a lint genuinely does not apply, suppress it at the narrowest
possible scope with a comment explaining why. Do not leave placeholder
`unwrap()` calls, `TODO` comments without a tracking rationale, or
dead-code exceptions in code that is meant to be complete.

## Compiler architecture

The compiler is one library crate (`compiler`) plus a thin binary
(`main.rs`). Keep `main.rs` and `cli.rs` free of compiler logic — they
should only parse arguments and call into `driver.rs`, which sequences the
compiler stages.

Compiler stages, in pipeline order:

```text
source -> lexer -> parser (AST) -> hir (+ resolve) -> typeck -> nir -> nir::verify -> (interpreter | future backend)
```

Each stage lives in its own module and communicates failure through
`diagnostics`, never through panics. A panic in any stage given arbitrary
user input is a bug. Reserve `panic!`/`unreachable!`/`.expect(...)` for
conditions that are true internal invariants (document the invariant at
the panic site) — for example, an NIR block that a prior verified stage
guarantees is non-empty.

Use byte offsets (`Span`) for all source positions inside the compiler.
Convert to line/column only at the diagnostics-rendering boundary, via the
source manager — never carry line/column through intermediate stages.

## Tests

Every new syntax form, type rule, or diagnostic needs a test. When you fix
a bug, add a regression test derived from the input that triggered it,
even if the fix looks obviously correct — regressions in a hand-written
lexer/parser tend to reappear as adjacent inputs change.

Prefer small, focused unit tests colocated with the module they test
(`#[cfg(test)] mod tests` at the bottom of the file) for internal behavior,
and integration tests under `compiler/tests/` for whole-pipeline behavior
(e.g. "this `.npt` snippet produces exactly this diagnostic").

## Commits

Use [Conventional Commits](https://www.conventionalcommits.org/). Each
commit should be one logical, buildable change, with any tests it needs
included in the same commit. Do not bundle unrelated changes.

## Branching

Feature work branches from `alpha` as `feat/<name>`. The flow is:

```text
feat/* -> alpha -> beta -> prod
```

Do not commit directly to `alpha`, `beta`, or `prod`.
