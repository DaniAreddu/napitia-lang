# Spec 0006: Napitia IR (NIR)

- Status: Partially implemented (Alpha 0.1.5)

NIR is a typed, explicit control-flow-graph intermediate representation,
lower-level than HIR, produced by lowering type-checked HIR
(`spec/0003-type-system.md`). It is designed to be a reasonable input to a
future LLVM (or other native) backend, while also being directly
executable by the tree-walking interpreter shipped in this milestone
(`compiler`'s `nir` module and its interpreter).

## Implemented features

### Structure

```text
Module   = { Function }
Function = name, params: [Param], return_type: Type, blocks: [BasicBlock]
Param    = name, type: Type, value_id: ValueId
BasicBlock = label, instructions: [Instruction], terminator: Terminator
```

Every function has at least one basic block (`bb0`, its entry block).
Every basic block ends in exactly one terminator (`ret`, `br`, `condbr`)
and terminators only ever appear last; NIR does not permit
"fall-through" between blocks. This makes every block independently
meaningful and is what makes the interpreter (and any future backend) a
simple block-dispatch loop with no implicit successor.

### Typed values

Every instruction that produces a value produces exactly one, identified
by a `ValueId` (`%N`), and records its `Type` (from `spec/0003`'s
primitive set). There is no untyped/`void*`-shaped value in NIR — a `unit`
value is a real, typed value, not an absence of one.

### Locals and constants

- A **local** is introduced by `value`/`mutable` in HIR. Only a
  `mutable` local gets real storage: `alloc.<ty>` (reserve a slot) plus
  `load`/`store` instructions against it, since it is the only kind that
  can ever be reassigned after its initializer. A `value` local is never
  reassigned, so it is simply the `ValueId` its initializer already
  produced — referencing it needs no `load` at all, and it is never the
  target of a `store`.
- A **constant** is an immediate value materialized by a `const.<ty>`
  instruction (an integer, float, bool, or char literal folded in from
  HIR).

### Instructions implemented

```text
%d = alloc.<ty>                       ; reserve a local slot of type ty
%d = const.<ty> <literal>              ; materialize a literal constant
%d = load <local>                      ; read a local slot
      store <local>, %s                ; write a local slot (no result)
%d = add.<ty> %a, %b
%d = sub.<ty> %a, %b
%d = mul.<ty> %a, %b
%d = div.<ty> %a, %b                   ; interpreter checks divisor != 0
%d = rem.<ty> %a, %b
%d = neg.<ty> %a
%d = not.<ty> %a                       ; logical/bitwise not
%d = and.<ty> %a, %b
%d = or.<ty>  %a, %b
%d = xor.<ty> %a, %b
%d = shl.<ty> %a, %b
%d = shr.<ty> %a, %b
%d = eq.<ty>  %a, %b   -> bool
%d = ne.<ty>  %a, %b   -> bool
%d = lt.<ty>  %a, %b   -> bool
%d = le.<ty>  %a, %b   -> bool
%d = gt.<ty>  %a, %b   -> bool
%d = ge.<ty>  %a, %b   -> bool
%d = call @<function>[<type-args>](%a, %b, ...)
%d = record.create @<record>[<type-args>](%a, %b, ...)      ; fields in declaration order
%d = record.field @<record>.<index> %base
%d = variant.create @<variant>[<type-args>].<case>(%a, ...) ; payload in declaration order
%d = variant.payload @<variant>.<case>.<index> %base
```

`record.create`/`variant.create` reference fields/cases by resolved
**declaration index**, never by name, matching how `call` already
references a function by `ItemId`. `record.field`/`variant.payload`
carry the record/variant identity alongside the index so the verifier
can check the base's actual type, not just index-bounds. A unit case's
`variant.create` supplies no payload values at all -- no fabricated
placeholder is ever allocated for it.

`[<type-args>]` (Alpha 0.1.4, `rfcs/0008`) is present only when the
callee/record/variant is generic — a call/construction against a
non-generic declaration prints and carries no bracket at all, not an
empty one. These are the *concrete* type arguments this one call site or
construction resolved to (already validated by typeck, never re-inferred
here); a generic declaration's own body/layout still lowers exactly once,
keeping its own parameter types symbolic (`Ty::Param`) — a call site
never causes it to be cloned or re-checked.

### Terminators implemented

```text
ret %v         ; ret (no value) when the function returns unit
br bbN         ; unconditional branch
condbr %cond, bbT, bbF   ; conditional branch
switch %v : @<variant> { bb0, bb1, ... }  ; one target per case, index-aligned
```

`switch` dispatches on a variant value's active case; every case has a
target (a wildcard/binding pattern that covers several cases simply
repeats the same target for each of them), since exhaustiveness is
already proven before this is ever built -- there is no "default" arm
at the NIR level.

### Textual printer

The implementation includes a deterministic textual printer, used for
debugging and for the `napitia ir` CLI subcommand:

```text
func @add#0(%0: i64, %1: i64) -> i64 {
bb0:
    %2 = add.i64 %0, %1
    ret %2
}
```

Every function, record, variant, call, construction, field/payload
access, and pattern switch is named by its full identity,
`module.path.name#id` (`add#0` above has an empty module path — legacy
single-file compilation has no project-level module path at all) — and so
is every *type* a nominal record/variant appears as: a parameter, a
return type, an `alloc`, and any other typed instruction print a
`Ty::Named` the same qualified way (`%0: sales.user.User#2`), not just
item declarations and references. In project (multi-file) compilation
this qualification is what lets two same-named items or types declared in
different modules (`sales.user.User` and `admin.user.User`, say) always
print distinguishably (`sales.user.User#2` vs. `admin.user.User#0`)
rather than as the same ambiguous bare name; `#id` additionally guarantees
two references can never be confused even in the degenerate case of two
qualified names somehow colliding (Alpha 0.1.3, `rfcs/0007`). An import
alias never appears in this output: the printed name is always an item's
own canonical declared name.

Printer output is stable across runs for the same input (no
pointer-derived or nondeterministic identifiers), which is what makes it
usable in tests as a golden-output comparison.

### Generics (Alpha 0.1.4)

A generic declaration prints its own type parameters on the declaration
itself, in declared order; a call/construction site prints its own
concrete type arguments the same bracketed way:

```text
func @identity#12[T](%0: T) -> T {
bb0:
    ret %0
}

func @main#13() -> i64 {
bb0:
    %0 = const.i64 42
    %1 = call @identity#12[i64](%0)
    ret %1
}
```

`identity#12` lowers exactly once regardless of how many call sites
instantiate it — there is no per-instantiation clone, and a symbolic
parameter type (`T` above) never leaks outside the one declaration that
binds it. `record.create`/`variant.create` print and carry their own
concrete arguments identically (`record.create @Box#8[i64](%0)`), and a
nested application formats unambiguously the same way a type in any other
position does (`Box[Maybe[i64]]`). This output is byte-identical across
repeated compiles, exactly like every other property in "Textual printer"
above, and an import alias never appears here either. See
`rfcs/0008-canonical-generics.md` for the complete semantics, the
canonical generic-instance-key design, and the verifier rules described
below.

### Protocols and capabilities (Alpha 0.1.5)

A `Module` carries every declared protocol's and extend's own layout,
each keyed by its own `ItemId`, in declaration order:

```text
protocol @Equal#4[T] {
    method[0] equal(T, T) -> bool;
}

extend @extend#7 for @Equal#4[i64] {
    method[0] = @equal_i64#8;
}

func @f#9(%0: i64, %1: i64) -> bool {
bb0:
    %2 = protocol.call @Equal#4[i64].method[0](%0, %1) evidence [@extend#7]
    ret %2
}
```

`ProtocolLayout` is a name, its own type parameters, and its methods in
declaration order (a `protocol.call`'s own `method` index refers into this
same order, never a name). `ExtendLayout` is the protocol it implements,
its own type parameters, its own concrete/symbolic arguments at that
protocol (`protocol_arguments`), its own `uses` requirements, and a method
table (`Vec<ItemId>`) mapping each protocol method's index to the real
NIR function implementing it — every extend method is lowered as an
ordinary `Function` sharing its own extend's exact type-parameter/
requirement scope (`rfcs/0009`), never a separate generic scope of its
own, and registered in the canonical `ItemRegistry` (`rfcs/0007`) like any
other function; an extend itself has no user-declared name, so its own
canonical identity is the bare `extend` keyword plus its `ItemId`
(`@extend#7` above), never the registry's `<item #...>` placeholder and
never borrowed from its protocol or first method.

Capability evidence (`crate::types::Evidence`) appears in exactly two
places: a `Call`'s own evidence list (one entry per callee requirement)
and a `protocol.call`'s single evidence value (satisfying the protocol
requirement the call itself names). `Evidence::Extension { extend,
nested }` prints as `@<extend>`, with `nested` printed the same way,
recursively, when non-empty; `Evidence::Forwarded(k)` prints as
`forwarded[k]`. Both are resolved once, entirely at compile time, by
`typeck`'s capability solver — the interpreter only ever copies an
already-resolved `Evidence` between call frames (one frame-relative
lookup for `Forwarded`), never re-running any part of resolution. See
`rfcs/0009-capability-protocols.md` for the complete semantic model
(authority, coherence, exact-forwarding-only resolution, the entry-point
restriction) and `spec/0003-type-system.md` for the type-system-level
detail.

### Lowering from HIR

HIR control-flow constructs (`if`/`else`, `while`, `loop`, `break`,
`continue`) lower to plain `br`/`condbr` between basic blocks — NIR
itself has no structured-control instructions. `while`/`loop` lower to
a loop-header block that `condbr`s into a body block (which
unconditionally branches back to the header) or an exit block;
`break`/`continue` lower to direct branches to the loop's known
exit/header block. `return`/`break`/`continue` lower straight to a
real terminator; nothing is ever appended to a block after it acquires
one — the lowering builder itself refuses (as a debug-time internal
invariant, not a diagnostic a user program can trigger) to append an
instruction, allocation, or store to a block that already has a
terminator, so this is a property the builder enforces at its own API
boundary rather than something every call site has to remember to
check. `if`/`else` follows the same rule for its own result slot: the
slot (when one is needed at all) is allocated in the block that still
dominates both branches, before that block's `condbr` terminator is
set, never after; when both branches diverge, `if` allocates no result
slot, stores no fabricated merge value, and creates no unreachable
merge block at all — each branch's own terminator is already a
complete CFG on its own.

`match` (Alpha 0.1.1) lowers to a real decision tree over its pattern
matrix, mirroring the same recursive specialize/default structure
`typeck`'s exhaustiveness analysis uses: a variant-typed occurrence
becomes a `switch` (one target per case); a `bool` occurrence becomes a
direct two-way `condbr` on the value itself (a closed, enumerable
domain, exactly like a variant's case set); an open-domain occurrence
(`int`/`str`/`char`) becomes a chained `eq` + `condbr`. Descending into
a `Variant` pattern's payload positions introduces fresh occurrences,
extracted via `variant.payload`, only inside that case's own block.
The shared result slot/merge block (when the match produces a value)
is allocated once, before any branching starts, exactly like `if`/
`else`'s own discipline; a fully-diverging match allocates neither.

Lowering the whole module is atomic: either every function lowers and a
complete `Module` is produced, or one or more failed and the only thing
produced is diagnostics, never a `Module` with some functions silently
missing.

The public `nir::lower_module` entry point does not rely on the type
checker having already rejected every construct Alpha 0.1's NIR cannot
represent — it is defense-in-depth against being called directly,
bypassing the normal `check`-then-`ir` driver. Casts, postfix `?`,
ranges, `defer`, function values, and a value-carrying `break` each
produce an `I0001` diagnostic from the lowerer itself, never identity
lowering, a range's left endpoint, `Const::Unit`, silently ignored
cleanup, or a discarded value. (A named aggregate type in a function
signature, field access, and `match` were on this list through
Alpha 0.1 — all three now have real lowering, described above and in
"Typed values" above.)

### Verification

Between lowering and interpretation, a verifier pass re-checks the
produced NIR independently of how it was built — it does not trust the
lowerer, and re-derives every invariant from the `Module` value itself:

- **Structure**: every function/block id is unique; every branch target
  and called function exists; call argument counts match.
- **Entry block**: every function has exactly one block with id
  `BlockId(0)`, which is its entry block *by id*, regardless of where it
  sits in the function's block vector — nothing (verifier, interpreter,
  or printer) is permitted to treat `blocks[0]` as the entry point.
- **Unique definitions**: every `ValueId` is defined exactly once across
  a function's parameters and instruction results combined; a duplicate
  parameter, a duplicate instruction result, or a parameter colliding
  with an instruction result are each rejected.
- **Definition before use**: a same-block use of a value must occur
  after the instruction that defines it (parameters are defined at
  function entry, before every block); an unknown or purely
  forward-referenced value is rejected.
- **Dominance**: a cross-block use of a value must be dominated by its
  definition, computed from real CFG predecessor/dominator analysis —
  block-vector order is never a substitute. This also governs
  `alloc`/`load`/`store`: an `alloc` must dominate every `load`/`store`
  against its slot. A value defined only in one arm of a branch cannot
  be used in the sibling arm or in a merge block that does not sit
  strictly after both arms converge.
- **Types**: stored values match the slot's declared type, branch
  conditions are `bool`, returned values match the declared return
  type, instruction operand/result types agree, and no unresolved type
  variable or `Ty::Error` survives into executable NIR.
- **Aggregates** (Alpha 0.1.1): `record.create`/`variant.create`
  reference a declared record/variant and initialize every field/match
  their case's payload arity and types exactly once each;
  `record.field`/`variant.payload` reference a valid field/payload
  index of the base's actual (not merely declared) nominal type;
  `switch` covers every one of its variant's cases exactly once with
  valid, unique-per-case targets, and its scrutinee's resolved type
  agrees with the variant its cases belong to; and a `variant.payload`
  extraction is only legal in a block where *every* incoming CFG edge
  independently guarantees that exact case (an ordinary
  branch/conditional-branch edge guarantees nothing at all, and two
  different `switch` edges into the same block guarantee only their
  intersection) — re-derived independently from the CFG's actual
  predecessors, never trusted from how lowering happened to build it.
- **Item identity** (Alpha 0.1.1): every function/record/variant's
  `ItemId` is unique across the whole module, including across
  different kinds of item (a record and a variant may never share an
  id) — `Ty::Named` compares/hashes by `ItemId` alone, so a collision
  here would let a value of one kind be silently accepted as another.
  Every `Ty::Named` reachable from a function's signature, locals, or
  instructions must also name an `ItemId` that actually resolves to a
  declared record/variant in this module, and its carried display
  symbol must match that declaration's own name.
- **Generics** (Alpha 0.1.4, `rfcs/0008`): a `Call`/`RecordCreate`/
  `VariantCreate`'s type argument count is validated against its
  callee's/record's/variant's own declared parameter count, and those
  arguments are substituted into the declared signature/field/payload
  types before comparing against actual operand/result types — the same
  type-checking discipline above, generic-aware. A `Ty::Named` for a
  declaration that is actually generic, a `Ty::Applied` with mismatched
  arity or naming a non-generic declaration, a `Ty::Param` appearing
  outside the one declaration that binds it, and a declaration whose own
  type parameter list contains a duplicate are all rejected. Every one of
  these checks recurses through nested `Ty::Applied` arguments and is
  bounded by the same generic-depth limit every other stage that walks a
  type application shares.
- **Protocols and extends** (Alpha 0.1.5, `rfcs/0009`): every protocol's
  own type parameters and method parameter/return types; every ordinary
  function's own `uses` requirements (referenced protocol exists with
  correct arity, every argument a valid root scoped to the function's own
  type parameters -- the same independent validation an extend's own
  requirements already get); and every extend's referenced protocol/
  `uses` requirements/protocol-argument types/method table (correct
  length, each entry a real, distinct function sharing its owning
  extend's exact type-parameter scope, declaring *exactly* its owning
  extend's own requirements in the same order (`V0058`), with a signature
  matching its protocol method once substituted) -- are all independently
  re-checked the same way records/variants/generics are. Every extend's
  own type parameter must also occur somewhere inside its protocol's own
  type arguments (`V0059`, re-deriving `typeck`'s own `T0046`).
- **Capability evidence** (Alpha 0.1.5, `rfcs/0009`): a `Call`'s evidence
  count is checked against its callee's own requirement count, and a
  `protocol.call`'s protocol/method index/argument and result types are
  checked against its own substituted signature; every evidence entry —
  `Forwarded` (in range, exactly compatible with what is required) or
  `Extension` (a real extend targeting the right protocol, whose own head
  structurally matches, with the right nested-entry count and no
  `Forwarded` anywhere inside `nested`) — is checked recursively, bounded
  by the same capability depth/work budget the solver itself uses, with
  exactly one diagnostic per malformed evidence root, never one per
  nested node. `Extension` evidence is rejected outright (`V0060`) if the
  required arguments are still symbolic -- only an exact `Forwarded`
  match is legal until every argument is concrete.

It reports structured diagnostics (`V0001`–`V0060` as of this milestone)
and never panics; a module that fails verification is never handed to
the interpreter, and the interpreter's normal entry point
(`Interpreter::run`) only ever receives a verified module — there is no
path through the driver that skips verification. `Interpreter::call`
additionally validates argument count against the function's declared
parameter count and starts execution explicitly at `BlockId(0)`, never
at whatever happens to be first in the block vector.

Because valid source cannot produce a `Vxxxx` code (verifier codes are
reachable only by a lowerer bug or by constructing malformed NIR
directly, which is exactly what the verifier's own test suite does),
and because lowering itself is atomic and rejects every construct it
does not support with a source-associated `Ixxxx` diagnostic (never a
silent `Ty::Error`, identity lowering, or discarded value — see
"Lowering from HIR" above), a program that passes `napitia check` is
guaranteed to either lower and verify cleanly or fail `napitia ir` with
an `Ixxxx` diagnostic; it can never panic and can never reach the
interpreter partially lowered or unverified.

## Accepted design direction

- **Ownership/effect metadata on values and calls**: the `Instruction` and
  `Function` representations are structured so an ownership state (moved /
  borrowed / owned) or an effect set (`spec/0005`) can be attached to a
  value or a call instruction as additional fields, without changing the
  shape of the control-flow graph itself. Nothing reads or enforces this
  metadata yet.
- **Array/collection types** as NIR-level values, once the type checker
  supports them (record/variant aggregates are implemented as of
  Alpha 0.1.1 — see "Instructions implemented" above).
- **SIMD/vector instructions** and **region-scoped allocation/free**
  instructions, once `spec/0004` is implemented — NIR's explicit
  basic-block structure is intended to remain the right shape for both.
- **LLVM lowering**: NIR's block/instruction/terminator shapes are close
  enough to LLVM IR's that a lowering pass is expected to be a relatively
  direct translation rather than a redesign, once a native backend is in
  scope (explicitly out of scope for Alpha 0.1 — see the top-level
  milestone description).

## Unresolved research questions

- Whether NIR should be in SSA form with explicit phi nodes at merge
  blocks, or keep mutable locals (`alloc`/`load`/`store`) as the primary
  mechanism and let a later optimization pass promote to SSA. The current
  implementation uses `alloc`/`load`/`store` for all mutable state and
  does not yet construct phi nodes.
- How calls to functions with effects should be represented once
  `spec/0005` effects exist — as plain `call` with effect metadata, or a
  distinct instruction family per effect class.

## Non-goals

- NIR is never executed as an "interpreted forever" runtime target for
  production; the interpreter exists to validate semantics ahead of a
  native backend (see the Alpha 0.1 milestone description), not to replace
  one.
