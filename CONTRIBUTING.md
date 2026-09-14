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

Built and tested against `rustc 1.97.1` (edition 2024, which itself
requires `rustc >= 1.85`); this exact toolchain is pinned in
`rust-toolchain.toml` at the repository root, which `rustup` picks up
automatically. `compiler/Cargo.toml` deliberately leaves `rust-version`
unset — it would claim a verified minimum supported Rust version, and
none has been established. CI (`.github/workflows/ci.yml`) installs the
same pinned toolchain and runs the same three checks on every branch
push, every pull request, and on manual `workflow_dispatch`.

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
(`main.rs`, built as `napitia`). Keep `main.rs` and `cli.rs` free of
compiler logic — they should only parse arguments and call into
`driver.rs`, which sequences the compiler stages.

Compiler stages, in pipeline order:

```text
source -> lexer -> parser (AST) -> hir (+ resolve) -> typeck -> nir -> nir::verify -> (interpreter | future backend)
```

Each `.npt` file goes through that pipeline once. A multi-file project
(`project/`, `rfcs/0006`) is a layer in front of it, not a replacement:
`project::loader` discovers and parses every module reachable from the
manifest's entry point and orders them dependency-first; `project::resolve`
resolves one module's `import`s against its already-lowered dependencies;
`hir::lower` then runs once per module (resolving every aggregate type
*reference* — not just names — against that module's own namespace,
before it is ever merged with another); only after every module is
individually lowered are they concatenated into one `HirModule` and fed,
unchanged, into the same `typeck`/`nir` stages single-file compilation
already uses. Anything that needs to know "which file did this come from"
belongs in `project::mod`'s orchestration, never smuggled into
`typeck`/`nir` as project-awareness they don't otherwise need.

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

## Releasing

A release is cut by pushing a tag. There is no release branch to prepare
and no separate version input to keep in step: the tag names the
version, and `.github/workflows/release.yml` refuses to publish if
anything about it does not line up.

1. Land the version bump like any other change — edit `version` in
   `compiler/Cargo.toml`, commit it as `chore(release): <version>`, and
   let it flow `feat/* -> alpha -> beta -> prod`.
2. Tag a commit that is **reachable from `alpha`**, with a leading `v`,
   matching the manifest exactly:

   ```bash
   git tag v0.1.8-alpha.1
   git push origin v0.1.8-alpha.1
   ```

3. The workflow takes it from there.

### What the workflow refuses

Each of these fails the release before anything is built or published:

- the tag does not match `version` in `compiler/Cargo.toml`;
- the tagged commit is **not reachable from `origin/alpha`** — releases
  come from reviewed history, not from whatever commit happened to be
  tagged, and `alpha` is the protected branch everything merges through;
- a release with that name already exists;
- any of the ordinary gates fails — formatting, clippy with
  `--all-features`, debug tests, release tests, docs under
  `-D warnings`. These are rerun rather than assumed: a tag can be
  pushed at any commit, including one CI never saw;
- a runner's real host triple disagrees with the target its artifact
  claims to be for.

### Supported targets

| Archive name | Target triple | Runner |
| --- | --- | --- |
| `napitia-linux-x86_64` | `x86_64-unknown-linux-gnu` | `ubuntu-latest` |
| `napitia-macos-aarch64` | `aarch64-apple-darwin` | `macos-latest` |
| `napitia-windows-x86_64` | `x86_64-pc-windows-msvc` | `windows-latest` |

The triple is not inferred from the runner label. Each job compares
`rustc -vV`'s host against the triple its matrix entry declares and
fails on a mismatch — GitHub has repointed `macos-latest` at different
architectures before, and quietly shipping an arm64 binary labelled
x86_64 is worse than failing.

Archives are named `<archive name>-<tag>.tar.gz`, alongside one
`SHA256SUMS` covering all of them.

### Verifying a release

Checksums:

```bash
sha256sum --check SHA256SUMS
```

Provenance — every archive is attested, so you can verify it was built
by this workflow from this repository rather than merely that it matches
a checksum published beside it:

```bash
gh attestation verify napitia-linux-x86_64-v0.1.8-alpha.1.tar.gz \
  --repo DaniAreddu/napitia-lang
```

### Reproducibility

The archives are byte-reproducible: the same commit produces the same
bytes, so anyone can rebuild and compare rather than trusting the
published checksums. Four things would otherwise differ per run, and
each is pinned — entry order (`--sort=name`), owner and group
(`--owner=0 --group=0 --numeric-owner`), modification times (normalized
to the tagged commit's own commit date), and the timestamp gzip writes
into its own header (`gzip -n`).

### Prereleases

A tag containing `-alpha`, `-beta` or `-rc` is published as a
prerelease, so an in-progress milestone never becomes the release people
land on by default. While this project is pre-1.0 that is every tag.

### Rehearsing

To exercise building and packaging without publishing anything, run the
workflow manually (`workflow_dispatch`). Everything runs except the
publishing job, which is guarded on the ref being a tag — there is no
input that turns a rehearsal into a release. The artifacts are attached
to the run.

### If a release fails partway

Nothing is published until every platform has built, so a failure during
`verify` or `build` leaves no release behind and the tag can simply be
re-pushed after the fix. A failure *during* publishing may leave a
partial release: delete it in the GitHub UI, then re-run the workflow
for that tag. The existing-release check is what stops a re-run from
quietly appending to a half-finished one.

Nothing about a release is manual beyond the tag — deliberately. A
release built from a working copy is a release nobody else can
reproduce.

### Branch and tag protection

The ancestry check assumes `alpha` means something, which is a
repository setting rather than anything this workflow can enforce.
Configure, in the GitHub UI:

- `alpha`, `beta` and `prod` as protected branches requiring a pull
  request and passing checks, with force-pushes disallowed;
- a tag protection rule for `v*`, so only maintainers can create the
  tags that trigger a release.

Without those, the ancestry check still runs, but the history it checks
against could itself have been rewritten.
