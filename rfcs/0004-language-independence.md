# RFC 0004: Language Independence

- Status: Accepted corrective direction. Supersedes the surface
  vocabulary (not the underlying engineering) of `spec/0001`, `spec/0002`,
  `spec/0003`, `spec/0004`, `spec/0005`, `rfcs/0002`, and `rfcs/0003` as
  they stood before this RFC.

## Summary

Napitia's compiler is implemented in Rust, and Rust is the strongest
existing proof that "memory safety without a mandatory GC" is achievable.
Both facts made it easy for the earliest specs to drift from "influenced
by Rust's safety guarantees" into "Rust's surface syntax with different
file extensions." This RFC records exactly what drifted, corrects it, and
draws the line the project intends to hold going forward: Napitia's
*implementation language* is an engineering choice; Napitia's *surface
language and semantic model* are a separate design the implementation
language must not be allowed to leak into.

## What had actually become Rust-specific

Before this RFC, across `spec/0001` and `spec/0002`:

- The reserved keyword list was `fn let var const return if else while for
  in loop break continue true false struct enum match impl trait use
  module pub private as is unsafe async await move region defer` — a
  near-verbatim copy of Rust's declaration keywords (`fn`, `let`/`var`,
  `struct`, `enum`, `trait`, `impl`, `use`, `pub`) with only cosmetic
  differences (`var` instead of Rust having no direct mutable-binding
  keyword; Rust uses `let mut`).
- `spec/0003-type-system.md` and `spec/0005-error-and-effect-model.md`
  named `Option<T>` and `Result<T, E>` as the intended absence/failure
  types — these are literally Rust's own standard-library type names, not
  Napitia-native concepts that happen to solve the same problem.
- `spec/0004-memory-model.md` and `rfcs/0002-ownership-and-regions.md`
  described shared ownership by naming Rust's `Rc`/`Arc` directly, and
  used "move", "borrow", and "region" in a way that assumed Rust's
  exact ownership/borrowing discipline was the target, rather than
  treating those as one possible implementation of a more general
  "compiler infers storage, the programmer expresses intent" idea.

What had **not** yet become Rust-specific, because it does not exist yet:
there is no lexer, parser, AST, HIR, or type checker in the repository as
of this RFC. Every affected file was a specification or RFC document. This
matters practically: the corrective work below is a documentation
correction, not a rewrite of working code.

## Classification: inherited, rejected, distinctive

### Ideas Napitia inherits (from Rust, and elsewhere)

- **Memory safety without a mandatory GC is achievable at all** — Rust is
  the existence proof. Napitia inherits the *conclusion*, not Rust's
  specific mechanism for reaching it.
- **Ownership as a way to reason about resource lifetime** — the general
  idea that a value has an owner and that owner's scope determines
  cleanup timing predates Rust (C++ RAII) and is inherited from that
  broader lineage, not from Rust specifically.
- **Local type inference with mandatory explicit function signatures** —
  shared with Rust, but also with Kotlin, Swift, and C#; this is inherited
  as "good, common practice," not as a Rust fingerprint.
- **Effects/capabilities as a type-level concept** — inherited from the
  Koka/OCaml-effects research lineage referenced in the original
  `rfcs/0003`, explicitly *not* from Rust, which has no effect system.

### Ideas Napitia rejects

- **Rust's exact ownership/borrowing surface**: explicit lifetime
  parameters (`'a`), `&T`/`&mut T` reference syntax, and Rust's specific
  borrow-checker diagnostics vocabulary. Rejected because RFC 0001 and the
  correction that produced this RFC both require that ordinary Napitia
  programs never need to write lifetime algebra — region inference must
  carry far more of that weight than Rust's checker does by design.
- **Naming absence/failure types after Rust's own stdlib**: `Option<T>`
  and `Result<T, E>` as *names* are rejected, even though "a type for
  absence" and "a type/mechanism for failure" are kept as concepts. See
  "Provisional vocabulary" below.
- **`Rc`/`Arc` as the user-facing shared-ownership vocabulary**: rejected
  as names; "explicit shared ownership must be opt-in and visible," the
  underlying requirement from RFC 0001, is kept.
- **Token-based macro/metaprogramming**: was already a non-goal (RFC
  0001); this RFC reaffirms it applies to *any* Rust-style
  `macro_rules!`/proc-macro-shaped mechanism specifically, not only to a
  generic "textual preprocessor."
- **An explicit `move` keyword**: dropped from the reserved list (it was
  present before this RFC). Rust needs `move` primarily for closure
  capture semantics under an explicit-by-default borrowing model; a
  model where ownership transfer is inferred by default has less need for
  a dedicated move marker. Removed rather than kept-but-unused, so the
  keyword table doesn't imply a feature that isn't designed yet.

### Ideas that are genuinely Napitia's own combination

No single piece here is unprecedented in isolation, but the combination
is not any existing language's design:

- **Ownership intent expressed only at boundaries, storage inferred
  everywhere else** — closer to how an optimizing compiler already
  decides stack-vs-heap placement invisibly, but applied to
  *ownership/region* decisions, not just placement, and made a language
  guarantee rather than an optimization detail.
- **`uses`/`raises` as symmetric, extensible, library-defined capability
  and error vocabularies** on the same function-type footing, rather than
  a fixed checked-exception hierarchy (Java) or a single generic `Result`
  return type doing double duty for every kind of failure (Rust).
  Domain libraries mint their own capability names (`Database.Read`,
  `Gpu.Execute`) without the compiler needing to know those domains exist
  — directly serving RFC 0001's "REST/AI are libraries, not keywords"
  requirement.
- **Identical semantics across REPL, JIT, and AOT** combined with the
  above two points: neither Rust (no REPL/JIT story) nor Python/Java
  (no region inference or capability effects) combine these three the
  same way.

## Provisional vocabulary (accepted, not frozen)

Replacing the previous keyword table:

| Previous  | Provisional | Notes |
|-----------|-------------|-------|
| `fn`      | `func`      | |
| `let`     | `value`     | immutable binding |
| `var`     | `mutable`   | mutable binding |
| `struct`  | `record`    | product type |
| `enum`    | `variant`   | sum type |
| `trait`   | `protocol`  | behavioral contract |
| `impl`    | `extend`    | `extend Type with Protocol { ... }` |
| `use`     | `import`    | renamed to avoid colliding with the new `uses` effect keyword |
| `pub`     | `public`    | spelled out |
| (new)     | `uses`      | effect/capability declaration on a function signature |
| (new)     | `raises`    | typed error declaration on a function signature |
| (dropped) | —           | `move` removed; see above |

Unchanged, because they are common cross-language control-flow/literal
vocabulary rather than Rust fingerprints: `return if else while for in
loop break continue true false match as is unsafe async await defer const
module private region`. `region`, `unsafe`, `defer`, and `async`/`await`
were already reserved before this RFC and keep their previously documented
intent (`spec/0004`, `spec/0005`).

`Option<T>`/`Result<T, E>` are replaced, as *names*, by:

- `Maybe<T>` for absence, with variants named `present(value)` and
  `absent` (once generic variants exist) — still an ordinary `variant`
  type, not a compiler built-in with special syntax.
- No dedicated value-level failure type is committed to yet. The primary
  failure-propagation path is the `raises` clause on a function's
  signature plus a postfix propagation operator, written `?` in examples
  (kept, since `?`-postfix propagation is not exclusive to Rust and
  appears in this RFC's own examples). Whether a value-level "outcome"
  type is *additionally* needed — for storing a not-yet-handled failure as
  data rather than immediately propagating it — is an open question, not
  a decision; see "Unresolved safety questions."

Example, illustrating the shape (still provisional, not frozen):

```napitia
public record User {
    id: Uuid
    name: String
}

public protocol Encodable {
    func encode(self) -> String
}

extend User with Encodable {
    func encode(self) -> String {
        json.encode(self)
    }
}

public func loadUser(id: Uuid) -> User
    uses Database.Read
    raises UserNotFound
{
    value user = database.users.find(id)?
    user
}
```

## Unresolved safety questions (recorded honestly)

This RFC does not claim any of the following are solved:

- **Effect model shape**: structural vs. nominal `uses`/`raises`
  tracking is still exactly as open as `rfcs/0003` (pre-correction) left
  it. Renaming the keywords does not resolve this.
- **Region inference completeness**: whether ordinary programs can in
  practice avoid ever writing `owned`/`borrow`/`shared`/`region`
  annotations, or how often real code will need them, is unvalidated —
  no prototype region inference exists yet.
- **Whether a value-level failure type is needed alongside `raises`**:
  unresolved, as noted above.
- **Aliasing/mutation discipline for `borrow`**: this RFC defines `borrow`
  as "temporary non-owning access at an API boundary" but does not yet
  specify whether multiple simultaneous borrows of the same value are
  ever restricted, and if so, by what rule. This is the same class of
  problem Rust solves with its aliasing rules for `&`/`&mut`; Napitia
  needs its *own* answer, and does not have one yet.
- **Whether `shared` implies any particular concurrency safety
  guarantee** (e.g. is a `shared` value automatically safe to access from
  multiple concurrent tasks, or only single-threaded-safe unless paired
  with another annotation) is undecided.

Implementation must not get ahead of these answers: no borrow-checking
algorithm, no lifetime syntax, and no claim that region inference "works"
beyond what is actually implemented and tested is permitted until each
question above has its own resolved RFC or spec update.

## Non-goals

- This RFC does not freeze the provisional vocabulary table. Every entry
  in it may still change; what is frozen is the *constraint* that the
  vocabulary must not be a renamed copy of Rust's.
- This RFC does not implement anything. It corrects direction for
  specs/RFCs and for compiler work that had not yet started (lexer, AST,
  parser). See the amended `rfcs/0001-project-constitution.md` for the
  standing constraint this RFC's conclusion is folded into.
