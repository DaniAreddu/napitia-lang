# RFC 0001: Project Constitution

- Status: Accepted
- Applies to: the whole project, present and future

## Summary

This RFC records the non-negotiable goals and non-goals of Napitia, and the
process by which the language and compiler are allowed to grow. It is the
document every other spec and RFC must remain consistent with.

## Motivation

Python, Java, and C++ each solve part of the problem of writing reliable,
performant software, and each imposes costs the others don't:

- Python: excellent readability and iteration speed, but no static types by
  default, a GIL, and weak control over memory layout and performance.
- Java: strong tooling, structured concurrency primitives, and reliability
  culture, but a mandatory GC, verbose ceremony, and no low-level control.
- C++: unmatched control over memory and hardware, but undefined behavior
  is reachable from ordinary code, textual preprocessing corrupts
  modularity, and build/tooling fragmentation is severe.

Napitia exists to ask whether a single language can keep the strengths of
each without inheriting the corresponding cost. This RFC does not claim the
answer is yes — it commits the project to trying, and to being honest in
its own documentation about how far it has actually gotten.

## Hard requirements

These are treated as constraints on every future design decision, not
aspirations to be traded away for convenience:

1. Memory safety by default in safe code. `unsafe` is an explicit,
   lexically-scoped, quarantined escape hatch — never an ambient property
   of a module or file.
2. No mandatory garbage collector. Deterministic destruction and
   compiler-inferred memory regions are the default resource-management
   model (see `spec/0004-memory-model.md`, `rfcs/0002`).
3. No global interpreter lock. Concurrency is structured and the language
   must not need a global lock to remain memory-safe.
4. No undefined behavior in safe code. Anything that would be UB in C++
   must be either a compile error, a checked runtime error, or restricted
   to code inside an `unsafe` block.
5. No `null`. Absence is represented by `Option<T>`.
6. No unchecked exceptions. Failure is represented by `Result<T, E>` and,
   longer-term, a typed effect system (see `spec/0005`, `rfcs/0003`).
7. No textual preprocessor. Compile-time metaprogramming, when it exists,
   operates on typed structures, never raw text substitution.
8. No implicit dangerous conversions (e.g. narrowing integer casts,
   silent truncation). Conversions that can lose information or change
   sign must be explicit at the call site.
9. No mandatory VM or heavyweight runtime for production builds. AOT
   native compilation is the production target; a REPL/JIT path exists for
   development and must share identical semantics with AOT, not a
   different dialect.
10. One official toolchain for build, test, formatting, and documentation.
    Third-party tools may exist, but the project ships and maintains its
    own rather than depending on an uncoordinated ecosystem for basics.

## Explicit non-goals of the language core

REST, HTTP, database access, ORMs, distributed systems primitives, and
AI/ML (tensors, autograd, GPU kernels) are never keywords, builtin types,
or compiler special cases. If the language's generics, traits, and effect
system are not expressive enough to build these as ordinary libraries, that
is treated as a deficiency in the generics/traits/effects design — the fix
is to strengthen those facilities, not to carve out a special case.

## Process

- A **spec** (`spec/NNNN-*.md`) describes behavior that is implemented (in
  full or in a clearly labeled subset) and normative for the compiler.
  Specs must distinguish implemented behavior from planned behavior.
- An **RFC** (`rfcs/NNNN-*.md`) records accepted design direction that is
  not fully implemented yet, or open research questions. An RFC is not
  permission to fake the corresponding feature in the compiler.
- Every spec and RFC must contain four explicit sections: implemented
  features, accepted design direction, unresolved research questions, and
  non-goals. A section may be empty, but it must be present, so readers
  never have to guess which category a claim falls into.
- Marketing language ("production-ready", "blazing fast", "enterprise
  grade") is not permitted in project documentation. State what the
  compiler does and does not do.

## Non-goals of this RFC

This RFC does not define syntax, type-system rules, or memory-model
mechanics — those live in their own specs/RFCs. It also does not commit
the project to a specific delivery timeline; it commits it to a set of
invariants that must hold regardless of timeline.
