//! Shared structural limits enforced across multiple compiler stages.
//!
//! A single deeply-nested `Variant(...)` pattern recurses on the native
//! call stack once per nesting level in every stage that walks it:
//! `parser::parse_pattern`, `hir::lower_pattern`,
//! `typeck::check_pattern`, `typeck::exhaustive::is_useful`, and
//! `nir::lower_decision`. Each stage enforces this same bound
//! independently -- not by trusting an earlier stage to have already
//! caught it -- because every one of them is also a public entry point
//! a caller can invoke directly with hand-built input that bypasses
//! whichever earlier stage would otherwise have stopped it first. A
//! single shared constant is what actually keeps them in lockstep;
//! five independently-maintained copies is what let them drift before.

/// Maximum `Variant(...)` sub-pattern nesting depth any stage will
/// descend into before failing with its own stage-appropriate
/// diagnostic (`P0001` in the parser, `R0015` in HIR lowering, `T0019`
/// in type checking and exhaustiveness analysis, `I0002` in NIR
/// lowering) instead of recursing further.
pub(crate) const MAX_PATTERN_DEPTH: usize = 200;

/// Maximum nesting depth of a bracketed generic type application
/// (`Box[Maybe[Box[...]]]`, `rfcs/0008`) any stage will descend into --
/// resolving a written type reference (`hir::lower`), substituting type
/// arguments (`typeck`, `nir::verify`), and printing a type (`nir`'s
/// printer) all recurse once per nesting level, so this one shared bound
/// keeps all of them from exhausting the native call stack on a
/// pathologically (or adversarially) deep annotation, each failing with
/// its own stage-appropriate diagnostic rather than trusting an earlier
/// stage to have already caught it.
pub(crate) const MAX_GENERIC_DEPTH: usize = 64;

/// Maximum number of distinct generic instances (one canonical
/// declaration `ItemId` plus its concrete type arguments,
/// `hir::registry`-adjacent `rfcs/0008`) one compilation will
/// instantiate before failing with a structured diagnostic instead of
/// continuing to expand. Checking generic bodies once, symbolically
/// (never eagerly monomorphizing at compile time), already rules out the
/// classic exponential-specialization blowup; this budget exists for the
/// residual case of a program that is itself well-typed but simply
/// instantiates an unreasonable number of genuinely distinct
/// declaration/argument combinations (e.g. a self-recursive generic call
/// that nests its own type argument one level deeper on every call,
/// `f[T] -> f[Box[T]] -> f[Box[Box[T]]] -> ...`).
pub(crate) const MAX_GENERIC_INSTANCES: usize = 4096;

/// Maximum recursion depth the capability solver (`typeck`'s `uses`
/// requirement resolution, `rfcs/0009`) will descend into while
/// resolving one requirement through a chain of conditional extensions
/// before failing with a dedicated complexity-budget diagnostic. A
/// budget failure is never reported as "no matching extension" -- the
/// two are different errors: one says the solve got too complex to
/// finish, the other says it finished and found nothing.
pub(crate) const MAX_CAPABILITY_DEPTH: usize = 64;

/// Maximum total number of requirement-resolution steps one call site's
/// capability solve will take (summed across the whole recursive solve,
/// not just its deepest chain) before failing with the same dedicated
/// budget diagnostic as [`MAX_CAPABILITY_DEPTH`] -- bounds a solve that
/// is wide (many sibling requirements at every level) the same way the
/// depth bound bounds one that is deep.
pub(crate) const MAX_CAPABILITY_RESOLUTION_STEPS: usize = 4096;
