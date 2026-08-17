# RFC 0007: Module Identity and Import Ergonomics (Alpha 0.1.3)

- Status: Accepted, implemented in Alpha 0.1.3

## Summary

Alpha 0.1.2 (`rfcs/0006`) gave every `.npt` file its own module and let
`import a.b.c;` bring item `c` from module `a.b` into scope by its bare
declared name. That is enough until two modules need to be used together
under the same name — `sales.user.User` and `admin.user.User`, say — which
0.1.2 had no way to express: both would try to occupy the single local name
`User` and collide.

Alpha 0.1.3 adds exactly one new piece of syntax to close that gap:

```text
import <module-path>.<item> as <alias>;
```

An alias is a **local, cosmetic rename** — it changes what name the
importing module uses to refer to an item, never the item's own identity,
declared name, or the type it names. `sales.user.User as SalesUser` and
`admin.user.User as AdminUser` remain exactly the two distinct types they
already were; the alias just lets both be named in one scope at once.

This milestone also makes every module-crossing identity concern that
0.1.2 left informal fully precise: a canonical, reusable per-item identity
map (`hir::registry`), module-qualified textual NIR so two same-named
items from different modules always print distinguishably, and a new
diagnostic (`M0013`) rejecting two logical module paths that resolve to
the very same physical file.

## Non-goals (explicit, unchanged from 0.1.2's list plus these)

Wildcard imports (`import a.*;`), grouped imports (`import a.{b, c};`),
package aliases, module aliases (aliasing `a.b` itself rather than one item
in it), re-exports, `public import`, and any form of glob resolution are
all still out of scope and still rejected with a diagnostic — an alias
renames one already-named item being imported, nothing more. Aliasing a
`Variant.Case` unit-case path is also out of scope: cases are not
independently importable in 0.1.2 or 0.1.3 (only the variant type itself
is), so there is nothing standalone to alias.

## Import aliases

### Syntax

```text
import sales.user.User;                 // unaliased -- unchanged from 0.1.2
import sales.user.User as SalesUser;    // aliased
```

`as <alias>` is optional and, when present, must be followed immediately
by `;`. The alias is a plain identifier — the same grammar an ordinary
binding name uses, not a full path. `parser::declaration::parse_import`
consumes it with the same recoverable-diagnostic discipline as the rest of
the parser: a missing alias identifier (`as;`), a non-identifier alias
token (`as 42;`), and a trailing token after a valid alias (`as X extra;`)
are all `P0001`, never a panic and never silently accepted — parsing
still recovers and continues with the rest of the file (`X`'s import
itself keeps whatever alias it did parse; only the unexpected trailing
token is rejected). No new parser diagnostic code was needed for any of
this.

`ast::ImportDecl` carries the parsed alias as `pub alias: Option<Ident>`,
with its own span distinct from the imported item's own name span (both
are real tokens in the source).

### Resolution

`project::resolve::resolve_one_import` already had to distinguish two
things 0.1.2 conflated by never needing to: the name used to **find** the
item in its declaring module, and the name **bound** by the import in the
importing module. 0.1.3 makes that split real:

- `declared_name`: the import path's last segment — always used to look
  the item up in the target module's own namespace, regardless of any
  alias.
- `local_name`: the alias's text if `import.alias` is `Some`, otherwise
  the same as `declared_name` — the only thing that ever changes based on
  aliasing, and the only thing `hir::lower` ever sees as this item's name
  in the importing module's namespace.

`hir::ImportedItemKind::Record`/`::Variant` each gained a `declared_name:
Symbol` field alongside their existing `item: ItemId` — the canonical
name, kept alongside the local (possibly aliased) one so a type reference
can always recover its true declared name even when the map key it was
found under is an alias (see "Nominal identity" below for why this
matters). `ImportedItemKind::Function` needed no such field: a function
reference is only ever a call by name, resolved straight to its `ItemId`,
with no separate "reconstructed type annotation" path the way records and
variants have.

### Collision detection

An alias participates in exactly the same collision machinery an ordinary
import or local declaration already did — `hir::lower` seeds the
importing module's namespaces keyed by `local_name`, so a second import
(aliased or not) or a local declaration reusing that same local name is
caught by the pre-existing `M0007` duplicate-name check, with no special
case for "one side is an alias." `M0007`'s diagnostic labels both
declarations by their real source location, in both directions (alias vs
alias, alias vs plain import, alias vs local declaration) — never a
silent "last one wins," and precisely: the label sits on the alias
identifier itself (`import a.b as Alias;` labels `Alias`), or, for an
unaliased import, on the imported item's own written name — never the
whole `import` statement, which used to be the only span available and
pointed a collision at an entire line regardless of which token was
actually responsible. An alias literally spelled like a primitive type
name (`import x.User as i64;`) still never shadows the primitive: the
primitive namespace is checked before the module's own aggregate
namespace regardless of whether the aggregate name reached that namespace
via an alias or its own declared name (a rule 0.1.2 already established
for declared/imported names; 0.1.3 only had to confirm it still holds
when the name arrived through an alias, which it does — the check never
distinguishes the two).

### Multiple aliases of one variant

Importing the very same variant under two different aliases is legal —
`import shapes.Shape as Figure; import shapes.Shape as Form;` — and both
resolve to the exact same `ItemId`. This must not make the variant's own
*cases* look ambiguous: an unqualified `Circle(4)` still resolves cleanly
even though `Shape` (and therefore `Circle`) is reachable under two local
names at once, and `Figure.Circle`/`Form.Circle` both construct the same
case through either alias.

**Bug found and fixed while implementing this**: `hir::lower`'s
`case_lookup` table (case name → every `(variant ItemId, case index)` it
could mean, used to resolve an unqualified constructor and to detect
genuine ambiguity across *different* variants) was populated once per
*import*, not once per *variant* — so importing one variant under two
aliases pushed the same `(ItemId, index)` candidate twice, and an
unqualified `Circle` then looked ambiguous against itself purely because
its variant had two local names in scope. Fixed by deduplicating at
insertion (`add_case_candidate`, shared by both imported and
locally-declared cases): `case_lookup` now holds each unique `(ItemId,
index)` pair exactly once regardless of how many aliases reach it, so
`candidates.len() > 1` only ever fires for two *distinct* variants
sharing a case name, which remains correctly rejected.

A second, related bug: `variant_name` (used only to build the
ambiguous-constructor diagnostic's message) reverse-searched
`type_names` — a `HashMap` — to find *some* local name for a candidate
`ItemId`. A variant reachable under more than one alias has more than one
matching key, so which one the message showed depended on that
`HashMap`'s iteration order — unspecified, and in practice randomized
per process. Fixed by collecting every matching name and picking the
lexicographically smallest, deterministically; the ambiguous-constructor
message's own candidate list is likewise sorted and deduplicated before
display, so the reported text is independent of both `case_lookup`'s
insertion order (a function of import declaration order) and
`variant_name`'s internal traversal.

## Nominal identity

Two declarations named `User` in two different modules were already two
different `ItemId`s under 0.1.2; 0.1.3's job is making sure an alias can
never blur that. Concretely: `sales.user.User as SalesUser` and
`admin.user.User as AdminUser`, even with byte-identical field lists,
remain two distinct types for every purpose that matters — function
calls, record/variant construction, field access, variant construction
and match patterns, parameter/return types, aggregate layout metadata,
NIR lowering and verification, and interpreter execution all key on
`ItemId`, never on the name in scope at the reference site (aliased or
not). None of this required new machinery beyond what 0.1.2 already built
(`Ty::Named`'s hand-written `PartialEq`/`Hash` already compare only the
`ItemId`; `HirType::Aggregate` already carries the resolved `ItemId`
alongside a display name) — it required one real fix:

**Bug found and fixed while implementing this**: `hir::lower`'s
`type_names` map (`HashMap<Symbol, (ItemId, TypeNameKind)>` in 0.1.2)
was keyed by whatever name resolved a type reference — which, once
aliasing existed, could be an alias — with no way to recover the item's
*true* declared name from a lookup alone. `HirType::Aggregate`'s carried
`name: Symbol` was built directly from that lookup, so annotating a
parameter as `sales_id: SalesUser` produced an `HirType::Aggregate` naming
the *alias*, not `User`. `nir::verify`'s `check_named_type_identity`
(`V0029`/`V0030`) exists precisely to assert that a value's carried type
name matches its declaration's own true name — so this bug was caught
immediately as a false-positive `V0030` ("names its type `SalesUser`, but
its declaration is actually named `User`") on the very worked example this
RFC documents below. The fix: `type_names` became
`HashMap<Symbol, (ItemId, TypeNameKind, Symbol)>`, the third element being
the item's real declared name captured once at the declaration site (or,
for an import, the `declared_name` described above) — `resolve_type_ref`
now always builds `HirType::Aggregate` from that canonical name, never
from whatever key the lookup happened to succeed under. `Variant.Case`
qualified-path lookups deliberately keep using the *local* (map-key) name
for the `Variant` part, since that is genuinely what the source text
must write to be in scope — only the type-identity annotation itself
needed the canonical name.

An alias is never a way to create a new type: there is no way to combine,
merge, or otherwise unify two aliased imports of different declarations,
even if they share a name and shape. The negative worked example below
demonstrates the compiler still rejecting exactly that.

## Canonical item identity metadata (`hir::registry`)

A new module, `hir::registry`, is the single reusable source of truth for
"what is this item's qualified name," built once per compilation from an
already-lowered/merged `HirModule`:

```rust
pub enum ItemKind { Function, Record, Variant }

pub struct ItemIdentity {
    pub module_path: String,   // "" for single-file compilation
    pub name: Symbol,          // the item's own declared name, never an alias
    pub kind: ItemKind,
    pub source: SourceId,
    pub span: Span,
}

pub struct ItemRegistry { /* ItemId -> ItemIdentity, point lookups only */ }

impl ItemRegistry {
    pub fn get(&self, id: ItemId) -> Option<&ItemIdentity>;
    pub fn qualified_name(&self, id: ItemId, interner: &Interner) -> String;
}

pub fn build(hir: &HirModule, module_path_of: &HashMap<SourceId, String>) -> ItemRegistry;
```

`build` is deterministic and non-iteration-order-dependent by construction
— it only ever inserts by `ItemId` key from the HIR's own `Vec` order and
is consulted only by point lookup (`get`/`qualified_name`), never
iterated in a way whose order could leak into output. `qualified_name`
returns e.g. `sales.user.User`, or the bare name when `module_path` is
empty (single-file compilation, which has no project-level module path at
all — this is not a special case bolted on, it is simply what an empty
prefix formats to). Both `driver::ir` (single file) and
`project::compile_project` build one registry each and thread it into
`nir::print_module` and `nir::verify_module`; single-file compilation
passes an empty `module_path_of`, so its registry always has empty
prefixes and every qualified name is exactly the bare declared name.

Nothing else builds a competing name-to-`ItemId` map: this reuses
`hir::HirModule`'s own already-existing per-item name/source/span fields,
just centralized behind one lookup instead of re-derived independently by
whichever consumer needed a name.

## Module-qualified textual NIR

`napitia ir`'s output now names every function, record, variant, call,
construction, field/payload access, and pattern switch by its full
qualified identity, `module.path.name#id`, not a bare (and, pre-0.1.3,
potentially ambiguous) name — and, just as importantly, every place a
*type itself* is printed (a parameter, a return type, an `alloc`, a
typed operator) is qualified too, not only item declarations/references:

```text
func @admin.user.user_id#1(%0: admin.user.User#0) -> i64 {
bb0:
    %1 = record.field @admin.user.User#0.0 %0
    ret %1
}

func @sales.user.user_id#3(%0: sales.user.User#2) -> i64 {
bb0:
    %1 = record.field @sales.user.User#2.0 %0
    ret %1
}

func @main.main#8() -> i64 {
bb0:
    %0 = const.i64 40
    %1 = record.create @sales.user.User#2(%0)
    %2 = const.i64 2
    %3 = record.create @admin.user.User#0(%2)
    %4 = call @sales.user.user_id#3(%1)
    %5 = call @admin.user.user_id#1(%3)
    %6 = add.i64 %4, %5
    ret %6
}
```

Two same-named items from different modules (`sales.user.User` and
`admin.user.User` here) always print distinguishably — in a parameter
position (`%0: admin.user.User#0` above), a return position, an
allocation (`alloc.sales.user.User#2`, not shown above but printed the
same way when a `mutable` binding forces one), and every other typed
instruction — and the `#id` suffix means two references can never be
confused even in the (impossible, but never assumed away) case that two
qualified names somehow collided. Aliases never appear in this output at
all — the qualified name always comes from `ItemRegistry::qualified_name`,
which by construction can only ever produce an item's true declared
identity. Single-file compilation still prints valid, readable NIR: with
an empty module path, `@add#0` is what a bare `func add` becomes, and a
bare `record User`'s own parameter/return/alloc positions print `User#0`
(the `#id` suffix itself is new in this milestone — 0.1.2's printer
emitted a bare `func @add`, with no id at all; single-file mode simply
goes through the same now-qualified printer every other compilation does,
so it gains the same `#id` suffix rather than being a special case).

`nir::printer` and `nir::verify` both gained an `&ItemRegistry` parameter
threaded alongside their existing `&Interner` one; every prior call to
`interner.resolve(name)` for an item name became
`registry.qualified_name(id, interner)`, and every prior call to
`display_ty` for a type in the printer became a new registry-aware
`format_ty` (primitives unchanged, `Ty::Named` renders through the same
`qualified_ref` every item reference uses). This is a real, if
mechanical, signature change that ripples through every caller
(`driver.rs`, `project/mod.rs`, `cli.rs`) simultaneously, since Rust
compiles the whole crate as a unit — there is no smaller change that
keeps every intermediate state buildable, so it landed as one commit
explained as such rather than split into an artificially broken
sequence.

## Better qualified diagnostics

`M0007` (duplicate/conflicting import or declaration) labels both the
conflicting and the original declaration by real source location — and
precisely: the alias identifier itself for an aliased import, or the
imported item's own written name for an unaliased one, never the whole
`import` statement (`ImportedItem::local_name_span`, threaded through
`NameOrigin::Imported` and `import_collision_diagnostic`). Only the whole
import's own span (`import_span`) is still used where the entire import
genuinely is the failing construct — module-not-found, private-item
access — since there is no more specific token to blame there.

Typeck's own diagnostics are qualified too: `check_module_with_registry`
(the real implementation `check_module` now wraps, passing an
empty-module-path registry for single-file compilation) threads
`&ItemRegistry` into `Checker`, and `display_for_diagnostic` — the one
formatter every typeck diagnostic that names a type goes through, so none
of them could drift into a different format — renders a `Ty::Named`
through `registry.qualified_name` instead of its bare declared name.
Project compilation passes its own already-built project-wide registry
(built before typeck runs, for exactly this purpose), so a genuine cross-
module mismatch now reads unambiguously:

```text
error[T0001]: argument type does not match the parameter's declared type: expected `admin.user.User`, found `sales.user.User`
```

This applies to every typeck diagnostic that names a type, not only
`T0001` — argument/return/assignment/field-access/match-scrutinee
mismatches, "not callable", "expected a numeric/integer type", all go
through the same formatter. Single-file compilation's diagnostics are
unaffected in wording (its registry has no module path, so every name is
still just its own bare declared name), and a primitive-type diagnostic's
text is completely unchanged either way. Diagnostics do not, as of this
milestone, additionally spell out "`SalesUser` refers to
`sales.user.User`" the way the milestone brief allows but does not
require — no existing diagnostic needed it to remain correct or
unambiguous, so it was not added speculatively. No diagnostic anywhere
exposes a raw `ItemId` as a user-facing name, nor does any typeck
diagnostic attach a bare `#id` the way textual NIR does (there is no
canonical-name collision for a qualified name to disambiguate, since two
distinct items always have distinct declaring-module paths, names, or
both); the worst case in NIR/verifier output (an `ItemId` the registry
never learned about, which a well-formed compilation cannot produce)
degrades to a labeled placeholder (`<item #N>`), never a panic.

## Duplicate physical-module identity protection

A symlink, junction, or otherwise-aliased path under `source-root` could,
before this milestone, let two different logical module paths both
resolve to the very same physical file with no diagnostic at all —
loading and lowering the same source twice under two different
identities. `project::loader::load_project` now tracks each module's
canonical (symlink-resolved) file as it is discovered
(`by_canonical_file: BTreeMap<PathBuf, (String, SourceId, Span)>`) and
rejects a second, differently-named module path that canonicalizes to a
file already seen, as a new code:

```text
M0013  two different module paths resolve to the same physical file
```

The diagnostic names both module paths — in a fixed alphabetical order in
the message text, independent of which one the loader's depth-first
traversal happened to discover first — the physical file, and both
import sites (the current one as the primary label, the first-seen one
as a secondary label via `Diagnostic::with_label_in`, which may point
into a different source file than the primary span). This is layered on
top of, not a replacement for, 0.1.2's existing containment and
symlink-escape protections (`M0002`): a symlink that escapes
`source-root` is still rejected before this check would ever run; `M0013`
only fires for a symlink (or other aliasing) that stays validly inside
`source-root` but duplicates a file already loaded under a different
name.

## Determinism

Every determinism property 0.1.2 established still holds and 0.1.3
extends it to the new surface area:

- Module discovery, `ItemId` assignment, and topological ordering are
  unchanged — aliasing only affects what local name an already-assigned
  `ItemId` is reachable under, never assignment order.
- `M0013`'s reported module-name pair is independent of import
  declaration order (verified by a dedicated test constructing the same
  duplicate-physical-file scenario two ways, with the two imports
  written in opposite order, and asserting the reported pair is
  identical).
- `hir::registry::build` is a deterministic function of the HIR's own
  `Vec` order; `ItemRegistry` is consulted only by point lookup.
- Textual NIR remains byte-identical across repeated compiles of the same
  project, and identical regardless of which import is written first
  (verified for a two-same-named-cross-module-records project, forward
  and reversed import order, byte-for-byte).
- The ambiguous-constructor diagnostic's reported variant-name pair (two
  genuinely distinct variants sharing a case name) is independent of
  import declaration order (verified the same way as `M0013` above:
  the same scenario built two ways, imports reversed, asserting an
  identical message).

## Required examples

Three fixture projects under `compiler/tests/projects/`, each exercised
end-to-end through the real `napitia` binary (`tests/project_cli.rs`):

- `alias_same_named_records`: `sales.user.User` (aliased `SalesUser`) and
  `admin.user.User` (aliased `AdminUser`) constructed, field-accessed,
  and passed to each module's own function in `main`'s single scope —
  `40 + 2 = 42`, the exact worked example this RFC documents above.
- `alias_nominal_mismatch`: the same two same-named, same-shaped `User`
  types, but a `SalesUser` value passed where `admin.user`'s own
  `user_id` expects its own `User` — still rejected as an ordinary
  `T0001` type mismatch, proving an alias never bridges two distinct
  types.
- `alias_same_named_functions`: `ops_a.calculate` and `ops_b.calculate`
  share a name; aliased into `main` as `inc`/`double`, each call reaches
  its own exact declaration (`11 + 20 = 31`).

## Diagnostic codes

Every code from `rfcs/0006` is unchanged. One new code:

```text
M0013  two different module paths resolve to the same physical file
```

No parser, resolution, type-checking, or verifier code needed a new
diagnostic code for aliasing itself — every alias-specific failure mode
(malformed alias syntax, alias/import/declaration collisions, an alias
shadowing a primitive) already had an existing code whose meaning covers
it exactly (`P0001`, `M0007`).

## Honest limitations

- An alias is never surfaced in a diagnostic alongside its canonical name
  (e.g. "`SalesUser` refers to `sales.user.User`") — the milestone brief
  allows this ("may") but does not require it, and no existing diagnostic
  needed it to remain correct, so it was not added speculatively.
- `M0013`'s fixture tests are `#[cfg(unix)]`-gated, matching 0.1.2's own
  existing symlink-based tests: constructing two module paths that
  resolve to one physical file, without a real symlink, is not possible
  given that a module's file path is a pure deterministic function of its
  dotted path (no `.`/`..` can ever appear in an import path's segments —
  they are identifiers, not path text) — so the only real-world trigger
  for this check is a symlink or junction, and Windows junction creation
  in an unprivileged test process is not portable enough to test the same
  way.
