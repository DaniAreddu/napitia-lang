# RFC 0016: The Verified Execution Boundary (Alpha 0.2.2)

- Status: Accepted, implemented in Alpha 0.2.2
- Builds on `rfcs/0014-native-aot-preview.md` and
  `rfcs/0015-numeric-semantics.md`

## Summary

Every release up to Alpha 0.2.1 ran the NIR verifier in the right place
and then handed its *input* to the executor. `driver::ir` lowered a
module, called `nir::verify_module`, discarded the answer if it was
empty, and passed the module on. The interpreter and the native backend
both took a bare `nir::Module`, and both documented -- in prose -- that
they were only ever given verified NIR.

Prose is not a boundary. Any crate-internal caller could construct a
module by hand, or reorder one after it was checked, and hand it
straight to an executor; nothing in the types said otherwise.

This milestone makes the claim structural. Verification now *consumes*
the module it checked and returns an opaque `nir::VerifiedModule`, and
that type is what the interpreter and the native backend accept. The
production pipeline becomes:

```text
source
  -> parse
  -> resolve
  -> typecheck
  -> resource checking
  -> NIR lowering
  -> NIR verification
  -> VerifiedModule
  -> interpreter or native backend
```

It is a stabilization release. It adds no language feature, no
diagnostic, no syntax and no runtime behaviour. Every diagnostic code,
every diagnostic's text and every program's meaning is exactly what
Alpha 0.2.1 produced.

## Raw NIR versus verified NIR

`nir::Module` is unchanged and stays fully public, with public fields.
It has to be:

* `nir::lower` builds one incrementally, mutating it as it goes;
* the verifier's own tests need hand-built malformed modules, since a
  verifier that can only be shown NIR the lowerer produced is testing
  the lowerer;
* the native backend's tests need the same, to prove which layer owns
  which refusal.

So "raw NIR" keeps its meaning: a `Module` is whatever built it says it
is, and nothing about the type claims it means anything.

`nir::VerifiedModule` is the other half of that statement. It wraps one
`Module` in a private field and says exactly one thing: this module was
passed to `nir::verify_module` and the verifier returned no
diagnostics.

## The sealing invariant

```rust
pub fn verify(
    module: Module,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
) -> Result<VerifiedModule, Vec<Diagnostic>>;
```

Five properties hold, and together they are the invariant:

1. **The checked module is the sealed module.** `verify` takes the
   module *by value*. There is no borrowed variant that returns a seal,
   so the module that was checked and the module that was sealed cannot
   be two different values.
2. **A seal cannot be forged.** The field is private and there is no
   public constructor. Outside this crate's own tests, `verify` is the
   only way a `VerifiedModule` comes into existence.
3. **A seal cannot be broken.** There is no `&mut Module` accessor, no
   `DerefMut`, and no `into_module`. A sealed module cannot be
   reordered, extended or edited -- not by a later stage, and not by a
   test.
4. **Reading is unrestricted.** `VerifiedModule::module` returns
   `&Module`, and `Deref<Target = Module>` is the same projection
   without the ceremony. Printers, the interpreter and the native
   backend all read freely; none of them can write.
5. **One verification, one implementation.** `nir::verify_module` is
   still the single authoritative verifier, and `nir::verify` is the
   single production path that consults it on an executor's behalf.
   Nothing verifies twice.

There is exactly one exception, and it is compiled out of every
production build: `VerifiedModule::seal_unchecked` is `#[cfg(test)]`
and `pub(crate)`. See "The test-only unchecked path" below.

## Which components take a `VerifiedModule`

| Component | Signature | Why |
| --- | --- | --- |
| `interpreter::Interpreter::new` | `&VerifiedModule` | the complete semantic execution path |
| `native::build_executable` | `&VerifiedModule` | the whole AOT pipeline |
| `native::capability::validate` | `&VerifiedModule` | its rules sit *on top of* the verifier's, never instead of them |
| `driver::IrOutput::Ready` | carries a `VerifiedModule` | `ir`, `run` and `build` all start from it |
| `driver::ProjectIrOutput::Ready` | carries a `VerifiedModule` | the project equivalent |
| `project::CompiledProject` | carries a `VerifiedModule` | the merged module a project executes |

Two components deliberately keep a raw borrow:

* `nir::print_module` takes `&Module`. Printing is read-only, and
  printing raw NIR is exactly what a verifier test needs. `ir` prints
  the verified module through the read-only projection.
* `native::lower::emit_object` takes `&Module`. It is unreachable
  without a `NativePlan`, and only `capability::validate` can mint one,
  so it is already behind the seal.

There are two sealing sites in the whole compiler, and they are the two
places the verifier was already called:

* `driver::ir_with_imports`, for single-file compilation;
* `project::compile_project`, for a project -- once, over the single
  merged module, because a per-module verification could never have
  checked a cross-module call.

`check` is upstream of NIR entirely and is unchanged: it reports
lexer, parser, resolver, type and resource diagnostics, and lowers
nothing.

## Normal verification failures

When lowering produces NIR the verifier rejects, `verify` returns the
verifier's own `Vec<Diagnostic>`: the same `Vxxxx` codes, the same
messages, the same notes, in the same deterministic order. Nothing is
summarised into a string, nothing is dropped, and nothing is replaced
with a default.

For a program compiled through the driver or the CLI, such a failure:

* happens during verification, before any executor exists;
* never enters an interpreter frame;
* never allocates or mutates a runtime resource;
* never reaches native capability validation or Cranelift;
* never panics and never prints a Rust backtrace;
* leaves `ir`, `run` and `build` with exit status `1` and diagnostics
  on standard error, and standard output empty.

In practice a user should never see one. The verifier only ever
examines NIR this compiler built itself, so a `Vxxxx` code reaching
someone who wrote a program `check` accepted is a defect in `nir::lower`
or in the verifier -- which is precisely why the check exists, and why
the CLI tests sweep every example asserting no `V` code ever escapes.

## The test-only unchecked path

Two things would become untestable if the seal had no exception:

* the interpreter's runtime defence in depth, which only has anything
  to say about NIR the verifier would have rejected;
* the layering between `nir::verify` and `native::capability`, which is
  proven by showing that a hand-built module is refused by the first and
  not merely by the second.

So there is one unchecked path, under `#[cfg(test)]`:

```rust
#[cfg(test)]
pub(crate) fn seal_unchecked(module: Module) -> VerifiedModule;

#[cfg(test)]
pub(crate) fn Interpreter::unchecked(module: &Module) -> Interpreter<'_>;
```

Neither is compiled into the production library, and neither is
nameable outside this crate. Every production caller goes through
`nir::verify`.

## Why runtime defence in depth remains

The seal is a claim about *structure*, established by a pass that is
itself code that can have bugs. Alpha 0.2.1's runtime refusals
(`rfcs/0015`) are what stands between such a bug and a panic, and they
are unchanged:

| Code | Meaning |
| --- | --- |
| `X0001` | division by zero |
| `X0002` | integer overflow |
| `X0003` | shift amount out of range |
| `X0004` | an operation this engine cannot execute, or a reused terminated context |

The unchecked path keeps them under test. Given a module that
constructs a live resource and then reaches an instruction the
interpreter cannot execute, the unchecked interpreter still returns a
structured `X0004`, still terminates the execution context per
`rfcs/0015` (so nothing runs afterwards against the partial state it
left), and still never panics. The same module handed to `nir::verify`
produces `V0112` and `V0077` and no seal at all -- which is the whole
point: the runtime refusal is the second line, not the first.

## Compatibility

Source programs, diagnostics and runtime behaviour are unchanged. A
program that compiled, ran or built under Alpha 0.2.1 does all three
identically under Alpha 0.2.2, with identical output.

The library API changes for anyone embedding the compiler crate:

* `Interpreter::new` takes `&nir::VerifiedModule` rather than
  `&nir::Module`;
* `driver::IrOutput::Ready`, `driver::ProjectIrOutput::Ready` and
  `project::CompiledProject` carry a `VerifiedModule`;
* `nir::verify` is new; `nir::verify_module` is unchanged and still
  public, as the borrowed check that reports diagnostics without
  sealing.

An embedder that previously did `Interpreter::new(&module)` on a module
it built itself now calls `nir::verify(module, ..)` first and handles
the failure case. That is the change this RFC is for.

## Limitations

* The seal records *that* a module was verified, not *when* or against
  which registry. Verifying against one `ItemRegistry` and printing
  against another is still possible; nothing here makes registries part
  of the seal.
* It is a compile-time boundary within one crate's type system, not a
  cryptographic or runtime one. A `#[cfg(test)]` build can still seal
  anything, deliberately.
* `nir::print_module` and `native::lower::emit_object` still take raw
  borrows, as described above. Both are read-only, and the second is
  unreachable without a plan.
* Nothing about *what* the verifier checks changed in this milestone.
  Every rule, code and ordering is exactly Alpha 0.2.1's.

## What this RFC does not do

No new numeric widths, casts or conversions. No `f64` native support.
No change to resource semantics, borrowing, strings, collections, the
standard library, syntax or parsing. No REST, database or AI surface.
No new native backend features. No change to existing runtime failure
semantics.
