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
