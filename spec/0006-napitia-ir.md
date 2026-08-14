# Spec 0006: Napitia IR (NIR)

- Status: Partially implemented (Alpha 0.1)

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
%d = call @<function>(%a, %b, ...)
```

### Terminators implemented

```text
ret %v         ; ret (no value) when the function returns unit
br bbN         ; unconditional branch
condbr %cond, bbT, bbF   ; conditional branch
```

### Textual printer

The implementation includes a deterministic textual printer, used for
debugging and for the `napitia ir` CLI subcommand:

```text
func @add(%0: i64, %1: i64) -> i64 {
bb0:
    %2 = add.i64 %0, %1
    ret %2
}
```

Printer output is stable across runs for the same input (no
pointer-derived or nondeterministic identifiers), which is what makes it
usable in tests as a golden-output comparison.

### Lowering from HIR

HIR control-flow constructs (`if`/`else`, `while`, `loop`, `break`,
`continue`) lower to plain `br`/`condbr` between basic blocks — NIR
itself has no structured-control instructions. `while`/`loop` lower to
a loop-header block that `condbr`s into a body block (which
unconditionally branches back to the header) or an exit block;
`break`/`continue` lower to direct branches to the loop's known
exit/header block. `return`/`break`/`continue` lower straight to a
real terminator; nothing is ever appended to a block after it acquires
one. `match` is not in this list: using it is a checked, reported error
(`spec/0002`) rather than being lowered to NIR at all.

Lowering the whole module is atomic: either every function lowers and a
complete `Module` is produced, or one or more failed and the only thing
produced is diagnostics, never a `Module` with some functions silently
missing.

### Verification

Between lowering and interpretation, a verifier pass re-checks the
produced NIR independently of how it was built: every function/block id
is unique, every function has an entry block, every branch target and
called function exists, every referenced value was actually defined,
every `load`/`store` targets a slot a matching `alloc` produced, stored
values match the slot's declared type, branch conditions are `bool`,
returned values match the declared return type, instruction operand and
result types agree, and no unresolved type variable or error type
survives into executable NIR. It reports structured diagnostics and
never panics; a module that fails verification is never handed to the
interpreter.

## Accepted design direction

- **Ownership/effect metadata on values and calls**: the `Instruction` and
  `Function` representations are structured so an ownership state (moved /
  borrowed / owned) or an effect set (`spec/0005`) can be attached to a
  value or a call instruction as additional fields, without changing the
  shape of the control-flow graph itself. Nothing reads or enforces this
  metadata yet.
- **Aggregate types** (structs, enum payloads, arrays) as NIR-level values
  with `getfield`/`setfield`/`construct`-style instructions, once the type
  checker supports them beyond the primitive subset.
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
