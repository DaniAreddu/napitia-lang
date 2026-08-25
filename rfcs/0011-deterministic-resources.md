# RFC 0011: Deterministic Resources (Alpha 0.1.7)

- Status: Accepted, implemented in Alpha 0.1.7

## Summary

Alpha 0.1.7 adds Napitia's first memory/resource-safety layer: `resource`
declarations (affine, non-copyable nominal aggregates), explicit
ownership transfer, call-scoped non-escaping observation, `drop`, and a
real `defer`. A resource value has exactly one owner at a time; the
compiler tracks that ownership through every function body and rejects
use-after-move, use-after-drop, and double-drop at compile time. Every
resource still owned at scope exit is destroyed exactly once, in a
deterministic order, on every exit path -- normal fallthrough, `return`,
`raise`, postfix `?` propagation, and every `handle` arm.

```napitia
resource File {
    descriptor: i64
}

func open(descriptor: i64) -> File {
    return File { descriptor: descriptor }
}

func inspect(file: File) -> i64 {
    return file.descriptor
}

// An ordinary (non-`take`) parameter: `close` only observes `file` for
// the duration of this call -- `main` still owns it afterward, and may
// still read it below.
func close(file: File) -> unit {
}

func main() -> i64 {
    value file = open(3);
    // Registered now, run once this scope exits (after the tail
    // expression below is computed, before `main` actually returns).
    defer close(file);
    return inspect(file)
}
```

This is a custom design, not a copy of Rust's ownership/borrow/lifetime
system, C++ destructors/`delete`, Java garbage collection, or Go's
tuple-error convention. There are no borrow annotations, no lifetime
parameters, no `Drop` trait with a user-supplied destructor body, and no
generic `Result`-shaped wrapper. Ownership is tracked structurally over
Napitia's own HIR and NIR by a dedicated compiler stage
(`resourceck`), and destruction is an explicit, always-visible NIR
instruction executed by the interpreter -- never an implicit runtime
hook riding on the host language's own destructor mechanism.

## Non-goals

No general references, no lifetime annotations, no raw pointers, no
shared ownership, no reference counting, no tracing garbage collector,
no threads or `Send`/`Sync` model, no native heap allocator, no FFI
destructors, no cyclic resource graphs, and no user-defined destructor
body attached directly to a `resource` declaration (there is no
`resource File { descriptor: i64 } drop { ... }`-shaped syntax this
milestone -- destruction is always the implicit field-less "this value
is gone" transition NIR emits, observed only through ordinary `drop`/
`defer` calls to ordinary functions). Generic resources
(`resource Box[T] { ... }`) are out of scope; the grammar does not give
`resource` a type-parameter list at all. Protocols over resource types
are out of scope for this milestone: a `resource` used as a protocol's
own type argument, or as an `extend` target, is rejected with a
dedicated diagnostic rather than silently behaving like an ordinary
value.

## Syntax

```text
ResourceDecl = ["public"] "resource" IDENT "{" [ Field { "," Field } [","] ] "}" ;
Field        = ["public"] IDENT ":" Type ;

Param  = ["take"] IDENT ":" Type ;

DropStmt  = "drop" Expression ";" ;
DeferStmt = "defer" Expression ";" ;
```

`ResourceDecl` deliberately reuses `Field`'s own grammar unchanged --
resource construction (`File { descriptor: 3 }`) is the exact same
`RecordLiteral` production a `record` construction already uses
(`spec/0002`), keyed to a `resource` item instead of a `record` item.
There is no separate construction syntax to learn.

`take` is a parameter modifier, not a type constructor and not a
reference sigil: `func consume(take file: File)` and
`func consume(file: &File)` are not the same idea, and only the former
exists in Napitia. A parameter written without `take` is an ordinary,
call-scoped **observation**: the callee may read a resource value's
fields for the duration of the call, but the value is not owned by the
callee, cannot be stored into a binding that outlives the call, returned,
or passed onward to anything that would extend its lifetime past the
call's own return. A `take` parameter is an ownership-transferring
parameter: the caller's own binding is moved into the call, exactly like
an assignment.

`drop <expr>;` and `defer <expr>;` are statements (`Stmt::Drop`,
`Stmt::Defer`; `defer` already existed in the grammar as of Alpha 0.1.6,
parsed and type-checked but rejected as an explicit unsupported feature
at NIR lowering -- this milestone is what makes it real). Both may only
appear as ordinary statements inside a block, never as an expression
result; `drop`'s own expression must denote a resource value (a bare
identifier naming an owned local, in practice -- `drop file`, never
`drop file.descriptor`), and `defer`'s own expression is evaluated for
its side effects only, matching a bare statement-expression.

## Resource state machine

Every resource-typed local binding has exactly one of four states,
tracked per binding by `resourceck` (`compiler/src/resourceck/`):

```text
Available     -- owned, live, safe to read/move/drop/observe.
Moved         -- ownership transferred elsewhere; using the old
                 binding again is a compile-time diagnostic.
DropScheduled -- registered with a `defer` that has not yet run;
                 the value is still Available for ordinary use, but
                 may no longer be moved out from under the deferred
                 action (the deferred call needs it later).
Dropped       -- destroyed, by an explicit `drop` or by scope-exit
                 implicit destruction; using it again, or dropping it
                 again, is a compile-time diagnostic.
```

`Error` is a fifth, checker-internal state (never user-visible): once a
binding's real state cannot be determined (because an earlier
diagnostic already fired against it), further checks treat it as
already-diagnosed and suppress cascading duplicate errors for the same
root cause, mirroring the rest of the compiler's own "one diagnostic per
root violation" discipline (`rfcs/0009`, `rfcs/0010`).

## Ownership rules

- Constructing a resource (`File { descriptor: 3 }`) creates one new,
  owned value in `Available` state.
- Assigning a resource-typed value to another binding (`value g = file;`)
  moves it: `file` becomes `Moved`, `g` becomes `Available`.
- `return`ing a resource-typed value moves it out of the function; the
  returning function's own local no longer owns it, so it is not also
  destroyed at scope exit.
- Storing a resource-typed value as a field of a record, variant case,
  or another resource being constructed moves it into that container.
- Passing a resource-typed value to a `take` parameter moves it into the
  call; the caller's own local becomes `Moved`.
- Passing a resource-typed value to an ordinary (non-`take`) parameter
  is a call-scoped observation: the caller's own binding is untouched
  (still `Available` afterward) and the callee receives read access to
  the same value for the duration of the call only.
- Primitives, `str`, and ordinary (non-`resource`) record/variant values
  are entirely unaffected by any of this and keep their existing copy
  semantics (`spec/0002`) -- only a value whose static type is a
  declared `resource` (or an aggregate that itself contains one,
  transitively) is affine.
- Reading a resource's own field (`file.descriptor`) does not move the
  resource itself; it observes the field, exactly like a record.
- Using a binding after it becomes `Moved` or `Dropped` is a
  compile-time diagnostic (`resourceck`, not a runtime failure).
- Dropping (explicitly or implicitly) a value already `Moved` or
  `Dropped` is a compile-time diagnostic -- a resource is destroyed
  exactly once, always.

## Destruction

`drop file;` consumes a live (`Available`) resource immediately: it
transitions to `Dropped` and its NIR destruction instruction runs at
that exact program point, not at scope exit.

Every resource-typed local still `Available` (not `Moved`, not already
`Dropped`) at its own scope's exit receives an *implicit* `drop`,
inserted by the compiler -- never left for a host-language destructor,
a tracing collector, or a "the interpreter happens to notice" runtime
check. Implicit destruction order is the reverse of declaration order
within a scope (the last resource declared is the first destroyed),
matching `defer`'s own LIFO discipline below. A value moved out by
`return`, assignment to an outer binding, storage in a returned
aggregate, or a `take` argument is not implicitly dropped by the scope
that used to own it -- the new owner is responsible from that point on.
An explicit `drop` earlier in the same scope means that binding is
simply skipped by the implicit end-of-scope sweep (it is already
`Dropped`, and dropping it again would itself be the double-drop
diagnostic above).

### `defer`

`defer close(file);` registers an action to run when the *enclosing
lexical scope* exits, exactly once, regardless of which exit path is
taken:

- Multiple `defer`s in one scope run in LIFO order (last registered,
  first run) -- the same reverse-declaration-order discipline implicit
  resource destruction itself follows, so the two interleave in exactly
  the declaration-reversed order across a scope that mixes resource
  locals and `defer` statements.
- A deferred action runs exactly once: normal fallthrough off the end
  of its scope, an explicit `return`, a `raise`, postfix `?`
  propagation out of the scope, and every relevant `handle` arm exit
  all run it -- there is no path out of the scope that skips it, and no
  path that runs it twice.
- A value a live `defer` will still need is protected: once
  `defer f(x)` is registered, `x` (if it is a resource) enters
  `DropScheduled` and cannot be moved away or explicitly dropped before
  the deferred call actually runs -- doing so is a compile-time
  diagnostic, not a dangling-value runtime hazard.
- Nested scopes unwind inside-out: an inner scope's own defers all run,
  in its own LIFO order, before control reaches the outer scope's exit
  handling at all.
- There is no silent no-op lowering: a `defer` that reaches NIR always
  lowers to a real cleanup-block call; nothing about this feature is
  a parsed-but-ignored placeholder past this milestone.

## Joins

Where two or more reachable branches of an `if`, `match`, or `handle`
rejoin (or a loop's body reaches its own back edge), every resource
local's state must agree across every branch that actually contributes
to the join:

- A branch that unconditionally diverges (`return`, `raise`, an
  infinite `loop` with no reachable `break`) contributes nothing to the
  join -- exactly like typeck's own `Ty::Never` handling
  (`rfcs/0010`) -- so a resource moved only inside a diverging branch
  never poisons the state seen after the join.
- If every contributing branch agrees a binding is `Available` (or
  agrees it is `Moved`/`Dropped`), the join carries that same state
  forward unambiguously.
- If contributing branches disagree (one moves it, one does not), the
  binding becomes checker-internal `Error` after the join: any
  unconditional later use is rejected, since there is no single
  well-defined state to check it against. (Napitia has no `if`-without-
  `else` for a value-producing branch, so this only arises where the
  language already requires exhaustive coverage -- `match`/`handle` --
  or between an `if`'s two arms; there is deliberately no attempt to
  prove a "the only way to reach here is through the branch that kept
  it" refinement beyond what the CFG already makes syntactically
  unambiguous.)
- A `while`/`loop` body is checked against its own entry state; if the
  state it produces at the body's own end disagrees with its entry
  state for any resource local declared *outside* the loop, that is a
  loop-carried invalidation, reported once at the loop.

## Explicit non-goals (repeated for the implementation phases)

No general references, no lifetime annotations, no raw pointers, no
shared ownership, no reference counting, no tracing garbage collector,
no threads/`Send`/`Sync`, no native allocator, no FFI destructors, no
cyclic resource graphs, no user-defined destructor body attached
directly to a `resource` declaration. This milestone defines and
verifies memory *semantics*; it does not implement a native heap
allocator -- an interpreter resource is a semantic runtime object
(a tagged, uniquely identified interpreter value with a state), not a
pointer into process memory.
