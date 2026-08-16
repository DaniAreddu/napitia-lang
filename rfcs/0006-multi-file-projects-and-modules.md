# RFC 0006: Multi-File Projects and Modules (Alpha 0.1.2)

- Status: Accepted, implemented in Alpha 0.1.2

## Summary

Every prior milestone compiled exactly one `.npt` file. Alpha 0.1.2 makes
Napitia a real multi-file project language: a `napitia.toml` manifest names
a source root and an entry file, every `.npt` file under the source root is
its own module (one file, one module, no `module` declaration), and
`import a.b.c;` brings a single public item from module `a.b` into the
importing module's namespace by its unqualified name `c`.

This is deliberately not Rust's module system. There is no `mod`, `crate`,
`self`, `super`, no wildcard/grouped/aliased imports, no re-exports, and
`::` never appears — Napitia keeps `import`, `public`/`private`, and dotted
paths throughout.

## Non-goals (explicit)

Remote packages, dependency declarations/registries, a standard library,
one module spanning multiple files, `module` declarations, wildcard/grouped/
aliased imports, re-exports, generics, protocol/extension imports, field
mutation, aggregate equality, and effect checking are all out of scope.
Every one of these is rejected with a diagnostic, never silently parsed and
ignored.

## Architecture

### Why not concatenate source files

Textually concatenating every module's source into one synthetic file
before lexing would collapse every file's line/column space into one,
making "diagnostics always point to the correct source file" (a hard
invariant below) impossible to satisfy honestly, and would make discovery
order (which file got concatenated first) an accidental input to
`ItemId` assignment. Alpha 0.1.2 instead lexes/parses/lowers each module
**separately**, each keeping its own real `SourceId`, and only combines
already-lowered `HirModule`s afterward.

### New project-level concepts

- **`ModuleId`** (`project::module::ModuleId`, a `u32` newtype): identifies
  one discovered module for the lifetime of one project compilation,
  distinct from `ItemId`/`SourceId`.
- **`ModulePath`**: a module's dotted path (e.g. `models.user`), derived
  deterministically from its file path relative to `source-root`
  (`src/models/user.npt` → `models.user`), never from declaration order or
  directory-iteration order.
- **`Manifest`**: the parsed, validated contents of `napitia.toml`
  (`package.name`, `package.version`, `project.source-root`,
  `project.entry`).
- **Module graph**: a `ModuleId → ModulePath`/`SourceId` table plus a
  dependency edge set built from every module's `import` declarations,
  discovered by reachability from the entry module and checked for cycles
  with an **iterative** algorithm (Kahn's algorithm), never native
  recursion over an attacker-sized project.
- **Global item identity**: `ItemId`/`LocalId`/`ExprId`/`PatternId` keep
  their existing flat `u32` shape (no crate-wide type change), but a
  project compilation threads one shared counter across every module's HIR
  lowering pass, in dependency (topological) order, so two items in
  different modules can never collide by reusing the same numeric id. This
  is "the smallest architecture that preserves invariant 1" the milestone
  brief asks for: no new wrapper type, no per-module id namespace to keep
  in sync, just a counter that is never reset between modules.
- **Cross-file definition locations**: `Diagnostic::Label` gains its own
  `SourceId` (previously implicitly the diagnostic's own source), so an
  import diagnostic can point at both the import site and the original
  declaration in a different file.

### Compilation order and import resolution

1. Parse the manifest, resolve `source-root`/`entry` to real paths, reject
   any that escape the project directory.
2. Discover every module reachable from the entry module: parse it, scan
   its `import` declarations, resolve each import's module path to a file
   path, parse that file if not already loaded, repeat until no new module
   is discovered. This is a breadth-first walk, but the *set* of modules it
   finds is order-independent — only the reachable set matters, not the
   order modules were visited in.
3. Compute a deterministic topological order over the discovered module
   graph (Kahn's algorithm, always picking the lexicographically-smallest
   ready module path when more than one is ready) and reject any module
   left over as a cycle, reporting one deterministic witness path.
4. Lower modules **in that topological order**. Before lowering a module,
   resolve every one of its `import` statements against the
   *already-lowered* HIR of the modules it depends on (which, by
   construction, were all lowered earlier): look up the target module,
   look up the item by name (regardless of visibility, to distinguish
   "not found" from "private"), check it is `public` and an importable
   kind (function/record/variant — protocols and extensions are
   explicitly rejected, not silently ignored), and seed the importing
   module's own name/type/field/case namespaces with the resolved
   `ItemId` before that module's own declarations are processed — so a
   local declaration reusing an imported name is caught by the same
   duplicate-detection path a same-file duplicate already goes through,
   just with a different diagnostic code and a cross-file label.
5. Concatenate every module's already-lowered `HirModule` (functions,
   records, variants, other-items) into one combined `HirModule`, in the
   same topological order, and feed that unchanged into the existing
   `typeck::check_module` and `nir::lower_module`. Because every item's
   `ItemId` is already globally unique and every cross-module reference
   was already resolved to a real `ItemId` during step 4, the merged
   module is exactly as self-consistent as a single hand-written file —
   typeck and NIR lowering need no project-awareness of their own. This is
   the "flattening the final project into one verified NIR module" option
   the milestone brief explicitly allows.
6. The entry point is the `main` function declared in the **entry
   module's own** `HirFunction` list, found by `ItemId` once step 5
   completes — never a name lookup over the merged module, which would
   silently accept a `main` in the wrong module. The interpreter gained
   `run_item`/`call_item` (by `ItemId`) alongside its existing name-based
   `run`/`call`, which single-file compilation keeps using unchanged.

### Visibility

- Item-level (`public func`/`record`/`variant`): checked once, at import
  resolution (step 4 above) — an import naming a private item never
  reaches HIR lowering at all, so "private access is rejected before NIR
  lowering" holds trivially.
- Field-level: `HirField` now carries its own `public` flag (previously
  discarded from the AST). A field access or construction-literal field is
  checked against the **declaring** module's identity, not the record's:
  a field is only reachable from outside its declaring module if it is
  `public`. Because Alpha has no partial-construction syntax, a public
  record with even one private field can never be constructed from another
  module — every attempt names at least the private field, and that name
  is rejected the same way any other private field access is.
- Public-API leakage (a `public` function/field/case exposing a `private`
  record/variant type): checked once per declaration, at the point its
  signature is lowered. Because any type name that isn't declared in the
  *same* module must have already gone through a successful (and
  therefore `public`) import to be usable at all, this reduces to one
  question: does a `public` signature name a `private` type declared in
  its *own* module? If so, that is the leak.

## Manifest format

```toml
[package]
name = "hello"
version = "0.1.0"

[project]
source-root = "src"
entry = "main.npt"
```

All four fields are required strings; unknown fields, missing fields, and
wrong-typed fields are all `M0001`. Parsing uses the `toml` crate (a
single, standard, actively-maintained dependency — writing a bespoke
partial TOML parser risks silently accepting malformed manifests the real
format would reject, which is exactly the failure mode this milestone
must not introduce). `entry` is resolved relative to `source-root`; `..`
segments and any path canonicalizing outside the project directory are
`M0002`.

## Module paths

One `.npt` file is one module. A module's path is its file path relative
to `source-root`, with the extension stripped and path separators replaced
by `.`:

```text
src/math.npt        -> math
src/models/user.npt -> models.user
src/main.npt        -> main
```

`import models.user.User;` names item `User` in module `models.user`; the
final segment is always the imported item, every segment before it is the
module path. An import needs at least two segments (one module segment,
one item segment) — `import math;` alone is `M0003`.

Module paths are normalized (path separators, not `\`/`/` directly) before
comparison so a project behaves identically built from a Windows or Unix
checkout. Two distinct files whose module paths differ only by ASCII case
(`Math.npt` vs `math.npt`) are `M0009` — real on case-sensitive filesystems,
and exactly the ambiguity that would silently corrupt on a case-insensitive
one.

## Diagnostic codes

```text
M0001  invalid manifest (malformed TOML, missing/unknown/mistyped field)
M0002  invalid project/source path (escapes the project, does not exist)
M0003  invalid import path (fewer than two segments)
M0004  module not found
M0005  imported item not found (including protocols/extensions, which
       are not an importable kind in this milestone)
M0006  item is private
M0007  duplicate or conflicting import (same import twice, two imports
       introducing the same local name, or a local declaration
       conflicting with an imported name)
M0008  module import cycle
M0009  duplicate/case-colliding module path
M0010  invalid or missing project entry point (no `main` in the entry
       module, or more than one)
M0011  inaccessible record field (construction or access, from outside
       the declaring module)
M0012  private type leaked through a public API
```

## CLI

`lex`/`parse` are unchanged: they always take a `.npt` file. `check`/`ir`/
`run` now accept an optional path:

- omitted → current directory;
- a path ending `.npt` → legacy single-file mode, byte-for-byte the same
  pipeline as before;
- a directory → look for `napitia.toml` inside it;
- any other path → treated as a manifest file directly.

`run` executes the entry module's `main`; exit codes (`0`/`1`/`2`) are
unchanged.

## Honest limitations

- Import resolution is name/visibility only in this milestone; there is no
  namespacing beyond "one flat name per module," matching Alpha's existing
  single-namespace-per-file model.
- Protocols and extensions cannot be imported at all yet (`M0005`) —
  protocol conformance checking does not exist yet (`rfcs/0003`), so there
  is nothing meaningful an import could resolve to.
- A project is still flattened into one NIR module before verification and
  execution; there is no per-module incremental compilation or caching.
