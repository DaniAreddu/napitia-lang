# RFC 0005: Records, Variants, and Pattern Matching (Alpha 0.1.1)

- Status: Accepted, implemented in Alpha 0.1.1

## Summary

Alpha 0.1 parses and name-resolves `record`/`variant`/`match` but rejects
every use of them beyond primitive-typed signatures: field access,
construction, variant payloads, and `match` are all checked, reported
errors (`spec/0002`, `spec/0003`). This RFC makes all of that real:
nominal record/variant values with actual runtime representation, field
access, construction syntax, qualified variant constructors, and
exhaustive `match` with nested variant patterns, lowered to explicit NIR
and executed by the interpreter.

Alpha 0.1.1 is a language-development release (`0.1.x`, per the
project's version policy): its purpose is to take Napitia from a
primitive/control-flow language to one that can model structured data
end to end, not merely to patch bugs in Alpha 0.1.

## Audit of the Alpha 0.1 starting point

Before designing anything, here is what was actually true of the code
(traced through actual control flow, not comments):

- **AST** (`syntax::ast`) already had `RecordDecl`/`Field`,
  `VariantDecl`/`Case`, `MatchExpr`/`MatchArm`, and a `Pattern` enum
  (`Wildcard`, `Ident`, `Variant{name, args}`, `Int`, `Str`, `Char`,
  `Bool`). The parser (`parser::declaration`, `parser::expression`)
  already parsed all of these. There was **no record construction
  syntax** (`Type { field: value }`) anywhere in the grammar.
- **HIR** (`hir::lower`) resolved `record`/`variant` *names* into
  `OtherItem`s (an `ItemId` plus a `name`/`kind` pair) but discarded
  their internal structure entirely — no field list, no case list, no
  payload types survived past the AST. `HirPattern::Ident` unconditionally
  treated a bare identifier pattern as a fresh binding, never as a
  payload-less variant case (the comment on that arm says as much).
- **Typeck** (`typeck::mod`) resolved named types nominally by `ItemId`
  (`Ty::Named`) and accepted them anywhere a type could appear, but
  `HirExpr::Field` was unconditionally an unsupported-feature diagnostic
  (`T0007`), and `HirExpr::Match` was unconditionally `T0007` regardless
  of whether its patterns/arms were actually well-formed — pattern
  binding types were just `Ty::Error`, never the payload's real type.
- **NIR** (`nir::lower`, `nir::verify`, `nir::instruction`) had no
  aggregate value representation at all: `ValueKind` only carries
  scalar operations, and a named type reaching a function signature was
  rejected at lowering with `I0001` specifically because there was
  nowhere to put it. `match` lowering was an unconditional `I0001`.
- **Interpreter** (`interpreter::mod`) only has a `Value` enum of
  scalars (`Int`, `Float`, `Bool`, `Char`, `Str`, `Unit`) — no record or
  variant runtime representation existed.
- **Diagnostics**: `T0007` ("unsupported feature") was the catch-all for
  field access, casts, `match`, and more. None of this milestone's new
  errors overload that code — each gets its own stable code (below).

This RFC's job is to replace every one of those "not implemented"
points with a real, principled implementation, without touching
anything this audit didn't find broken (casts, `?`, `defer`, ranges,
`uses`/`raises` remain exactly as unsupported as they were).

## Surface syntax

### Record declaration (unchanged from `spec/0002`)

```napitia
record User {
    id: i64,
    enabled: bool,
}
```

### Record construction (new)

```napitia
value user = User {
    id: 42,
    enabled: true,
};
```

`RecordLiteral = IDENT "{" [ FieldInit { "," FieldInit } [ "," ] ] "}"`,
`FieldInit = IDENT ":" Expression`. Fields may be written in any order;
each must appear exactly once. This is parsed as a new postfix form
following a bare identifier in primary-expression position, **not** as
generalized "any expression followed by `{`" — only `IDENT "{" ...`
constructs a record literal, exactly like every other language with this
ambiguity.

**The classic `if`/`while`/`match`-scrutinee ambiguity.** `if user { ... }`
must not be misread as `if (user { ... }) { ... }`. Napitia resolves this
the same way most brace-delimited languages with struct literals do:
record construction is syntactically disabled while parsing the
condition of `if`/`while` and the scrutinee of `match`. Writing
`if (user { ... }) { }` (parenthesized) is unaffected, since parentheses
already delimit a full expression. This is implemented as a parser-state
flag (`no_struct_literal`), not a lookahead hack, and is the one
deliberate surface-syntax restriction this RFC introduces.

### Field access (unchanged grammar, now real)

```napitia
value identifier = user.id;
```

`user.id` was already parsable (`spec/0002`'s `FieldAccess`); this RFC
makes it resolve against the base's nominal record type instead of being
a checked, reported error.

### Qualified variant constructors (dotted, not `::`)

```napitia
variant LookupResult {
    Found(User),
    Missing,
}

value first = LookupResult.Found(user);
value second = LookupResult.Missing;
```

**Design decision: dots, not `::`.** `spec/0002` already states, for
`import`/`uses` paths: *"Paths are dotted (`a.b.c`), not
double-colon-separated ... rather than Rust's `::` path syntax"* — and
the lexer has no `::` token at all. Introducing `::` now for exactly one
new feature would give Napitia two competing qualified-name syntaxes for
no reason. `LookupResult.Found(user)` needs **no new grammar at all**: it
is exactly `PostfixExpr = PrimaryExpr FieldAccess Call`, already in the
grammar (`Ident("LookupResult")` → `Field{base, name: "Found"}` →
`Call{callee, args: [user]}`). What's new is purely semantic: HIR
resolution recognizes a `Field` whose base names a declared `variant`
(not a local/function) and whose field name is one of its cases, and
turns it into a case reference instead of an ordinary field access.

**Constructors are always written qualified in expression position.**
`Found(user)` alone (unqualified) is *also* accepted when the case name
`Found` is unambiguous across every declared variant in the module (see
"Namespaces" below); when two variants both declare a case with that
name, the unqualified form is a checked, reported ambiguity error naming
both variants and asking for the qualified form. This is what makes
"constructor used without qualification when ambiguous" a real,
reachable diagnostic rather than a hypothetical.

**Patterns keep the existing bare-name grammar.** A `match` arm's
scrutinee type is always statically known before its patterns are
checked, so `LookupResult.Found(user)` and bare `Found(user)` are
equally unambiguous in pattern position — there is only ever one variant
being matched. Alpha 0.1.1 therefore does not extend `Pattern`'s grammar
at all: `Found(user)` / `Missing` in a `match` arm is exactly the
`Pattern::Variant{name, args}` the parser already builds, resolved
against the scrutinee's specific variant declaration. (The example in
this project's originating design brief writes `LookupResult::Found`
inside `match` arms too; per the "adjust only superficial punctuation"
instruction, the shipped examples use the plain, already-implemented
`Found(user)` pattern form with a dotted-qualified equivalent accepted
as well — see `record_and_variant_flow.npt`.)

## Namespaces

Four separate namespaces, matching how names are actually looked up:

1. **Value namespace**: locals and functions (unchanged from Alpha 0.1).
2. **Type namespace**: primitive names plus every declared
   `record`/`variant` name (unchanged from Alpha 0.1, now also consulted
   by record-literal/constructor resolution, not just type positions).
3. **Field namespace**: per-record, field name → declaration index.
   Never global — two different records may both declare a field named
   `id` with no conflict, exactly as RFC 0001's nominal-typing stance
   implies.
4. **Case namespace**: per-variant, case name → declaration index, plus
   a module-wide `case name → [(variant, case)]` table used *only* to
   resolve an unqualified constructor reference and to detect ambiguity.
   A `match` arm's pattern is always resolved through the per-variant
   table (using the already-known scrutinee type), never the module-wide
   one — patterns can't be ambiguous.

## Nominal identity

Unchanged from Alpha 0.1's already-implemented stance (`types::Ty::Named`
compares/hashes by `ItemId` alone): two records or variants with
identical shapes are different types. This RFC extends that identity to
runtime values (interpreter) and NIR metadata (below) — a record/variant
value carries its declaring `ItemId`, never re-derived from shape.

## Evaluation order and `never`

- **Record construction**: each field initializer is evaluated exactly
  once, in **source order** (the order written at the construction site,
  not declaration order). If any initializer diverges (`Ty::Never`), the
  whole construction expression is `never`, and no initializer written
  after the diverging one is lowered as reachable code — mirroring how
  `if`/binary operators already propagate `never` (`spec/0003`).
- **Field access**: the base expression is evaluated exactly once; a
  diverging base makes the access `never`.
- **Variant construction**: payload expressions evaluate exactly once,
  left to right; divergence propagates the same way call arguments
  already do.
- **`match`**: the scrutinee is evaluated exactly once, before any
  pattern is tested. A diverging scrutinee makes the whole `match`
  `never` and no arm is lowered as reachable code (mirroring `if`'s
  diverging-condition rule exactly).
- **Runtime layout follows declaration order**, independent of
  construction-site order — NIR's `record.create` always receives its
  field values already reordered into declaration order (see "NIR").

## Type checking

- **Record construction**: the type name must resolve to a declared
  record (else `R0007 unknown record type`). Every declared field must
  appear exactly once (`R0009 missing field` / `R0010 duplicate field
  initializer`); every named field must exist on the record
  (`R0008 unknown field`); each field's initializer must unify with its
  declared type (`T0001`, reused).
- **Field access**: the base must resolve to a record type
  (`T0013 field access on a non-record type`); the field must exist on
  *that* record (`T0014 unknown field`) — a field declared on a
  different record with the same name is not found (nominal, nothing
  structural leaks in).
- **Field mutation is explicitly rejected, not silently reinterpreted.**
  `user.age = 20;` is not treated as an ordinary assignment target: HIR's
  `Assign` already special-cases `Local`/`Field`/`Error` targets, and
  this RFC keeps `Field` out of the "valid mutable target" set, giving it
  its own diagnostic (`T0015`, *"field mutation is not implemented in
  Alpha 0.1.1"*) instead of `T0008`'s generic "invalid assignment
  target" — the point being made is different (mutation itself is
  unimplemented, not that the target shape is wrong).
- **Variant construction**: the qualified/unqualified name must resolve
  to exactly one case (`R0011 unknown variant type`, `R0012 unknown
  variant case`, `R0013 case belongs to a different variant` when a
  qualifier and case disagree, `R0006 ambiguous constructor`); payload
  arity and each payload expression's type against the case's declared
  payload types reuse `T0002`/`T0001`.
- **Record/variant equality is not implemented.** `==`/`!=` on two
  aggregate values is rejected the same way arithmetic on a `bool` is —
  `require_numeric`-style, but for equality specifically: `T0016
  aggregate equality is not implemented in Alpha 0.1.1`. This is a
  deliberate scope cut (see "Intentionally unsupported"), not an
  oversight — implementing it well means deciding what "equal" means
  once a variant payload can itself be a record, which is exactly the
  kind of scope creep this milestone avoids.

## `never` and match typing

Reuses the existing join machinery exactly (`spec/0003`): every
non-diverging arm body participates in a pairwise `never`-aware join
(the same `join_diverging_branches` helper `if`/`else` already uses,
generalized to more than two branches by folding); if every arm
diverges, the match's type is `never`. Pattern-bound locals receive
their **exact resolved payload type** (never `Ty::Error`) by construction:
the payload's type is known before any pattern for that case is checked,
so the checker never has to guess and correct later.

## Exhaustiveness and unreachability

Implemented as a real usefulness/exhaustiveness algorithm over a
**pattern matrix** (`typeck::exhaustive`), specialized to this
milestone's closed pattern grammar (`bool`, `Variant`, integer literal,
wildcard/binding — no or-patterns, guards, records, slices, or ranges):

- A pattern matrix is `Vec<Row>`, each `Row` a list of `(Ctor, args)`
  positions still pending against a list of scrutinee occurrences (the
  original scrutinee, plus one new occurrence per payload position
  introduced by a `Variant` sub-pattern — this is what lets nested
  variant patterns like `Outer.A(Inner.X)` work: matching `Inner.X`
  introduces `Inner`'s payload positions as fresh occurrences of their
  own, recursively).
- **Usefulness** (`is_useful`) is computed exactly as Maranget's
  algorithm specializes it per constructor: specialize the matrix by the
  candidate row's head constructor (or, for a wildcard/binding row,
  build the *default* matrix — every row whose head is itself a wildcard
  — and recurse into the remaining occurrences) and recurse; a row is
  useful iff there is some concrete value it matches that no earlier row
  already matches.
- **Exhaustiveness** asks: is a synthetic wildcard row useful against the
  matrix built from every actual arm? If yes, that witness is
  systematically expanded back into a concrete missing pattern (e.g.
  `LookupResult.Missing`, or `Outer.A(Inner.Y)` for a nested miss) and
  reported (`T0017 non-exhaustive match`) with that pattern printed
  verbatim — never merely "not exhaustive" with no example.
- **Unreachability** asks, per arm in source order: is this arm's
  pattern useful against the matrix of every *earlier* arm? If not,
  it's dead — reported as `T0018 unreachable pattern`, still with the
  arm's own body separately checked for independent diagnostics (dead
  code is not silently skipped).
- **Booleans**: a closed two-constructor domain (`true`/`false`);
  exhaustive iff both are covered or a wildcard/binding arm is present.
- **Integers**: an open/infinite domain — no finite list of literals is
  ever exhaustive on its own; a catch-all (wildcard or binding) arm is
  always required, matching this RFC's "unsupported: range patterns"
  scope cut (a range pattern would be the usual escape hatch here, and
  is deliberately not implemented yet).
- **Work budget and stack safety are two separate mechanisms, not one.**
  `is_useful` (and witness expansion) is native recursion -- it calls
  itself once per specialize/default step, and recursion depth tracks
  pattern nesting depth linearly. `MAX_USEFULNESS_STEPS` (100,000) caps
  *total* recursive calls across an entire match's analysis, as a hard
  backstop against pathological arm counts; it is **not**, on its own,
  a safe bound on any single call's *stack depth* -- 100,000 native
  stack frames is well past what a real call stack can hold. What
  actually keeps a single deeply-nested pattern from ever exhausting
  the stack is a second, much smaller, independent bound
  (`limits::MAX_PATTERN_DEPTH`, 200) that `is_useful` checks on every
  call, regardless of remaining step budget. Both report the same
  diagnostic either way (`T0019 pattern analysis budget exceeded`), so
  the distinction is invisible to a program, but load-bearing for
  safety: removing either bound (or widening `MAX_PATTERN_DEPTH` to
  `MAX_USEFULNESS_STEPS`'s size) would reopen the stack-overflow this
  RFC's exhaustiveness analysis exists to rule out.
- **The same structural depth limit is enforced at every stage that
  recurses per pattern nesting level**, not just `is_useful`: the
  parser (`parse_pattern`), HIR lowering (`hir::lower_pattern`), and
  NIR match-decision lowering (`nir::lower::lower_decision`) each track
  their own nesting depth independently and fail with a stage-appropriate
  diagnostic past the same shared `limits::MAX_PATTERN_DEPTH` bound,
  rather than relying on an earlier stage to have already caught it --
  a single constant, not four independently-maintained copies claimed
  to stay in lockstep. In the normal pipeline the parser's bound is
  what actually fires first (source text nested this deep never
  reaches HIR lowering, typeck, or NIR lowering at all); the later
  stages' bounds exist as defense-in-depth for a caller invoking
  `hir::lower_module`, `typeck::check_module`, or `nir::lower_module`
  directly with hand-built input that bypasses an earlier stage.

## Recursive aggregate rejection

Napitia has no boxing/indirection yet (`rfcs/0002` is unimplemented), so
every `record`/`variant` is a flat, directly-nested value — a direct or
indirect cycle in the field/payload graph would be an infinitely-sized
type. This is checked with a **deterministic dependency graph** keyed by
`ItemId` (`typeck::cycles`):

- One node per declared record/variant; one edge `A → B` per field (or
  payload element) of `A` whose resolved type is `Ty::Named(B, _)`.
- Iterative (explicit-stack, not native-recursion) cycle detection, so
  a pathological input cannot exhaust the Rust call stack — visiting
  each node/edge at most a small constant number of times, bounded by
  the number of declarations actually written.
- Traversal order is the declaration order records/variants were parsed
  in (their `ItemId` order), and each node's outgoing edges are visited
  in field/case declaration order — never a `HashMap`'s iteration order
  — so the reported cycle and its path are identical across runs.
- Diagnostic (`T0020 infinite aggregate layout`) names every declaration
  on the cycle, shows the containment path (`Node.next: Node`, or
  `First.second: Second` → `Second.first: First`), and explains that
  Napitia has no indirection feature yet to break the cycle with.
- This is checked once, before per-function type checking begins (so a
  cyclic declaration is reported even if nothing ever constructs it),
  and does **not** introduce an implicit heap box to make the recursive
  type "work" — it is rejected outright, matching this milestone's
  "prefer explicit rejection" stance from the originating brief.

## NIR representation

New `ValueKind` variants (`nir::instruction`):

```text
%d = record.create @Record { %a, %b, ... }   ; args already in declaration order
%d = record.field @Record.<idx> %base
%d = variant.create @Variant.<case> { %a, ... }
%d = variant.payload @Variant.<case>.<idx> %base
```

`record.create`/`variant.create` reference fields/cases by **resolved
declaration index**, never by name — the same principle Alpha 0.1
already applies to `call @<ItemId>`. A new terminator,
`variant.switch`, is added to `Terminator` (not `ValueKind`, since it is
control flow, not a value-producing operation):

```text
switch %scrutinee : @Variant { bb_case0, bb_case1, ... }
```

one target per declared case, index-aligned — every case is covered
because exhaustiveness already proved it, so lowering never needs a
separate "default" arm; a wildcard/binding pattern that covers several
cases simply repeats the same target block for each of them.

`nir::Module` gains deterministic layout metadata
(`Vec<(ItemId, RecordLayout)>` / `Vec<(ItemId, VariantLayout)>`, in
declaration order — never a bare `HashMap` iterated for output) so the
verifier, printer, and interpreter can all resolve a field/case index to
its declared type without re-deriving it from HIR.

## Match lowering

`match` lowers to explicit control flow, never to repeated scrutinee
evaluation and never via interpreter trial-and-error:

1. Evaluate the scrutinee exactly once into a `ValueId`.
2. If the whole match is `never` (diverging scrutinee), lower exactly
   like a fully-diverging `if`: no result slot, no merge block — each
   arm's own terminator is already a complete CFG on its own, and no arm
   is lowered as reachable code past the point of divergence.
3. Otherwise, allocate one shared result slot (skipped if the match's
   type is `never` for another reason — an all-diverging match) and one
   shared merge block, exactly mirroring `if`/`else`'s existing
   result-slot discipline, generalized from two branches to the
   decision tree below.
4. Recursively compile the **pattern matrix** into blocks: at each
   occurrence, if every remaining row is wildcard/binding, no branch is
   emitted (the occurrence is consumed without cost); otherwise a
   `variant.switch` (or, for a literal/boolean occurrence, a chained
   `eq` + `condbr`, since those constructor spaces aren't a single
   closed `switch` the way one variant's cases are) is emitted, and each
   case recurses into a fresh block with that case's payload values
   extracted via `variant.payload` and appended to the pending
   occurrence list. A pattern binding is a `load`-free direct reference
   to whichever occurrence's value it names (dominance holds by
   construction: a binding's occurrence value is always computed in a
   block that strictly dominates the arm body block that reads it).
   This is the same recursive shape Maranget's algorithm uses for
   compiling matches to decision trees, restricted to this milestone's
   closed constructor grammar.
5. Every arm's own body either stores its value into the shared slot and
   branches to the merge block, or (if it diverges) does neither — the
   block it lowered into is already terminated by its own
   `return`/nested-diverging-construct.

This satisfies every one of Alpha 0.1's carried-over invariants: no
instruction after a terminator, no unreachable merge block manufactured
just to produce a value, atomic module lowering (one failed function
still fails the whole module, exactly as today), and switch targets
that are always valid, always exactly the exhaustiveness-proven case
set.

## NIR verifier hardening

The verifier (`nir::verify`) is extended, not replaced, with checks for
every new construct: referenced record/variant/case/field exist and
agree with the operation's own recorded type; `record.create` initializes
every field of its record exactly once (by index, not by count alone —
a duplicate index is caught, not just a wrong total); `variant.switch`
covers every case exactly once with valid, unique block targets;
`variant.payload`/`record.field` results match the layout's declared
type; and the existing dominance/use-before-definition analysis is
reused unchanged (it already operates on abstract `ValueId`s and
`operands_of`, which this RFC extends rather than forks). A valid
program can never surface a `Vxxxx` code; only hand-built, deliberately
malformed NIR (this milestone's verifier test suite) can.

## Interpreter representation

```text
Value::Record { item: ItemId, fields: Vec<Value> }   // declaration order
Value::Variant { item: ItemId, case: usize, payload: Vec<Value> }
```

Field projection and payload extraction both re-validate the base
value's `item`/`case` identity against what the NIR operation expects
(defense-in-depth matching the project's "no unchecked lookup" rule);
a mismatch is a structured `InterpreterError::InvalidOperation`, never
an out-of-bounds panic, exactly like every other internal-invariant
check this interpreter already has. `variant.switch` reads the active
`case` index directly off the `Value::Variant` and jumps to the
matching target — no re-testing of payload shape, no re-derivation from
the module's static layout table at the value level.

## Diagnostics

New stable codes, none colliding with Alpha 0.1's `T0001`–`T0012`,
`R0001`–`R0003`, `I0001`–`I0002`, `V0001`–`V0018`. The dividing line
between an `R`-code (`hir::lower`) and a `T`-code (`typeck`) is exactly
the one Alpha 0.1 already draws for `Function`/local resolution: a name
that can be resolved from **syntax alone** (a construction site's
written type name, a qualified/unqualified constructor path, a pattern's
own shape) is an `R`-code, mirroring how a call's callee is resolved at
`hir::lower` time; a diagnostic that depends on an **inferred type**
(field access's base type, a pattern's compatibility with its inferred
scrutinee type, aggregate equality) is a `T`-code, mirroring
`resolve_named_type`/`check_call`'s existing split. Where an existing
generic code already fits exactly (a field's initializer type
disagreeing with its declared type, or a payload's arity/type
disagreeing with its case), this RFC reuses `T0001`/`T0002` rather than
minting a redundant synonym — exactly how Alpha 0.1 already reuses
`T0001` for return/assignment/if-branch mismatches alike.

```text
R0004  duplicate field in a record declaration
R0005  duplicate case in a variant declaration
R0006  ambiguous unqualified constructor (matches cases in 2+ variants)
R0007  unknown record type at a construction site
R0008  unknown field in a record construction
R0009  missing field in a record construction
R0010  duplicate field initializer in a record construction
R0011  unknown variant type in a constructor path
R0012  unknown variant case
R0013  case belongs to a different variant than the one written
R0014  duplicate binding within the same pattern
R0015  pattern nested too deeply to resolve (hir::lower_pattern's own
       structural depth bound; unreachable through the normal pipeline
       since the parser's matching bound already stops it first, kept
       as defense-in-depth for a direct hir::lower_module caller)

T0013  field access on a non-record type
T0014  unknown field (field access)
T0015  field mutation is not implemented in Alpha 0.1.1
T0016  aggregate equality is not implemented in Alpha 0.1.1
T0017  non-exhaustive match (carries a concrete missing-pattern witness)
T0018  unreachable match arm
T0019  pattern analysis budget exceeded
T0020  infinite aggregate layout
T0021  incompatible pattern (pattern kind disagrees with the scrutinee's
       type, e.g. a literal pattern against a variant-typed scrutinee)

V0019  record.create references an unknown record
V0020  record.create does not initialize every field exactly once
V0021  record.field references an unknown/mismatched field
V0022  variant.create references an unknown variant/case, or a payload
       arity/type mismatch
V0023  variant.switch does not cover every case exactly once, or targets
       an invalid block
V0024  variant.payload used outside its case's refinement, or its
       resolved type disagrees with the case's declared payload type
V0025  variant.switch scrutinee's resolved type disagrees with the
       variant its cases belong to
V0026  two records in the same module declare the same ItemId
V0027  two variants in the same module declare the same ItemId
V0028  the same ItemId is used by two different kinds of module-level
       item (e.g. a function and a record)
V0029  a Ty::Named refers to an ItemId matching no declared record or
       variant in this module
V0030  a Ty::Named's carried display symbol disagrees with its own
       declaration's name
```

Record-field-type, payload-arity, and payload-type errors are reported
through the existing `T0001` (type mismatch) and `T0002` (arity
mismatch) codes, with call-site-specific wording, rather than minting a
redundant new code per position.

`I0001` (unsupported-in-NIR) remains reachable for every construct this
RFC does not touch (casts, `?`, ranges, `defer`, function-as-value,
value-carrying `break`) — records/variants/`match` are removed from
that list, not merged into it.

## Intentionally unsupported in Alpha 0.1.1

Kept out deliberately, each with its own rejection rather than silent
partial support:

- **Field mutation** (`user.age = 20;`) — `T0015`.
- **Record/variant equality** (`==`/`!=`) — `T0016`.
- **Pattern guards**, **or-patterns**, **record destructuring patterns**,
  **slice patterns**, **range patterns**, **mutable pattern bindings** —
  none of these have surface grammar in Alpha 0.1.1 at all (the parser
  simply doesn't accept them); a program that tries them gets the
  parser's ordinary "expected a pattern"/`P0001` diagnostic, not a
  silently-accepted-then-ignored construct.
- **Generics** on `record`/`variant`/`func` — unchanged accepted
  direction from `spec/0002`/`spec/0003`.
- **Recursive aggregates through indirection** (`owned`/`borrow`-boxed
  fields) — blocked on `rfcs/0002`; this RFC only rejects the
  *unindirected* cycle, and documents that an indirection feature is the
  intended way to lift the restriction later (see "Forward
  compatibility").
- **Native code generation** — unchanged; NIR remains interpreter-executed
  only in this milestone.

## Forward compatibility with ownership

Nothing in this RFC's NIR shape presumes a particular ownership model:
`record.create`/`variant.create` take values, not addresses, and the
interpreter's `Value::Record`/`Value::Variant` are ordinary owned Rust
values (a `Vec<Value>`), matching how every other `Value` variant already
works. When `rfcs/0002-ownership-and-regions.md` lands, a boxed/indirect
field is expected to need only a new field-kind annotation (direct vs.
indirect) in the record layout metadata this RFC introduces — not a
redesign of `record.create`/`record.field` themselves — and indirection
is exactly what is expected to lift this RFC's recursive-layout
restriction (a `Node` record with a boxed `next: Node` field would no
longer be an infinite direct cycle).

## Summary of what changes, by stage

```text
source     -- new: record construction syntax (Type { field: expr, ... })
lexer      -- unchanged (no new tokens: dotted paths and field access
              already had every token this RFC needs)
parser     -- new: record-literal parsing; no-struct-literal context
              around if/while conditions and match scrutinees
AST        -- new: Expr::RecordLiteral, FieldInit
HIR        -- new: HirRecord/HirField, HirVariant/HirCase (real field/
              case lists, not just a name); HirExpr::RecordLiteral,
              HirExpr::CaseRef; PatternId on every HirPattern
resolution -- new: field/case/type namespaces; qualified + unambiguous
              unqualified constructor resolution
typeck     -- new: record/variant construction and field-access
              checking; exhaustiveness/usefulness analysis; recursive-
              layout cycle detection
NIR        -- new: record.create/record.field/variant.create/
              variant.payload instructions, variant.switch terminator,
              module-level layout metadata
verify     -- new: aggregate + switch invariants, reusing existing
              dominance/use-before-definition analysis unchanged
interpreter-- new: Value::Record/Value::Variant, field/payload
              projection, switch dispatch
```
