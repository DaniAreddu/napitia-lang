//! Verifies structural and type invariants of already-lowered NIR.
//!
//! `nir::lower` assumes its input already passed type-checking, and is
//! trusted to produce consistent NIR for a well-typed program -- but
//! trusting that silently is exactly the kind of gap this project's
//! correctness pass exists to close. This pass re-checks the NIR itself,
//! independently of how it was built, and reports every problem it finds
//! as a structured diagnostic rather than letting a malformed module
//! reach the interpreter (where it could panic or silently misbehave).
//! It runs once, after lowering and before interpretation.

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::diagnostics::Diagnostic;
use crate::hir::{ItemId, ItemRegistry, TypeParamId};
use crate::limits::{MAX_CAPABILITY_DEPTH, MAX_CAPABILITY_RESOLUTION_STEPS, MAX_GENERIC_DEPTH};
use crate::place::Place;
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
use crate::types::{CapabilityRequirement, Evidence, Ty, is_integer, is_numeric, substitute};

use super::block::{BasicBlock, BlockId, Terminator};
use super::instruction::{Const, Instruction, ValueId, ValueKind};
use super::{ExtendLayout, Function, Module, ProtocolLayout, RecordLayout, VariantLayout};

mod codes {
    pub const DUPLICATE_FUNCTION_ID: &str = "V0001";
    pub const DUPLICATE_BLOCK_ID: &str = "V0002";
    pub const EMPTY_FUNCTION: &str = "V0003";
    pub const UNKNOWN_BRANCH_TARGET: &str = "V0004";
    pub const UNKNOWN_FUNCTION_REF: &str = "V0005";
    pub const UNKNOWN_VALUE: &str = "V0006";
    pub const UNKNOWN_SLOT: &str = "V0007";
    pub const STORE_TYPE_MISMATCH: &str = "V0008";
    pub const NON_BOOL_CONDITION: &str = "V0009";
    pub const RETURN_TYPE_MISMATCH: &str = "V0010";
    pub const OPERAND_TYPE_MISMATCH: &str = "V0011";
    pub const UNRESOLVED_TYPE_VARIABLE: &str = "V0012";
    pub const UNEXPECTED_ERROR_TYPE: &str = "V0013";
    pub const ARITY_MISMATCH: &str = "V0014";
    /// A function's blocks don't include one with id `BlockId(0)`. The
    /// interpreter (and this verifier's own dominance analysis) treats
    /// `BlockId(0)` as *the* entry block by definition, regardless of
    /// where it sits in the block vector -- a function without one has
    /// no defined starting point at all.
    pub const MISSING_ENTRY_BLOCK: &str = "V0015";
    /// Two definitions (some combination of a parameter and/or an
    /// instruction result) claim the same `ValueId`. Every SSA value
    /// must have exactly one definition; silently letting the second
    /// one win (as a plain `HashMap::insert` would) hides a real
    /// structural bug in whatever produced this NIR.
    pub const DUPLICATE_VALUE_DEFINITION: &str = "V0016";
    /// A value is used earlier in a block than the instruction that
    /// defines it -- a forward reference within the same block, which
    /// no valid lowering ever produces (every instruction is appended
    /// only after everything it depends on already exists).
    pub const USE_BEFORE_DEFINITION: &str = "V0017";
    /// A value is used in a block that its definition does not
    /// dominate: there is at least one path from the entry block to
    /// this use that never passes through the block that defines it.
    /// Reading it on that path would read a value that was never
    /// actually produced.
    pub const NON_DOMINATING_DEFINITION: &str = "V0018";
    pub const UNKNOWN_RECORD: &str = "V0019";
    pub const RECORD_FIELDS_NOT_INITIALIZED_ONCE_EACH: &str = "V0020";
    pub const UNKNOWN_FIELD: &str = "V0021";
    pub const UNKNOWN_VARIANT_OR_CASE: &str = "V0022";
    pub const SWITCH_CASE_COVERAGE: &str = "V0023";
    pub const PAYLOAD_OUTSIDE_REFINEMENT: &str = "V0024";
    pub const SWITCH_SCRUTINEE_TYPE_MISMATCH: &str = "V0025";
    /// Two records in the same module declare the same `ItemId`. Every
    /// module-level item's id must be globally unique -- a plain
    /// `HashMap::insert` would silently let the second layout win,
    /// hiding a real structural bug in whatever produced this NIR.
    pub const DUPLICATE_RECORD_ID: &str = "V0026";
    pub const DUPLICATE_VARIANT_ID: &str = "V0027";
    /// The same `ItemId` is used by two different *kinds* of
    /// module-level item (a function and a record, a record and a
    /// variant, ...). `Ty::Named` compares/hashes by `ItemId` alone, so
    /// a collision like this would let a value constructed as one kind
    /// be silently accepted as the other wherever nominal identity is
    /// the only thing checked.
    pub const ITEM_ID_KIND_COLLISION: &str = "V0028";
    /// A `Ty::Named` refers to an `ItemId` that matches no declared
    /// record or variant in this module.
    pub const UNKNOWN_NAMED_TYPE: &str = "V0029";
    /// A `Ty::Named`'s carried display symbol does not match its own
    /// declaration's name. Nominal identity itself only ever depends on
    /// the `ItemId`, so this can never change what a program *does* --
    /// but it means diagnostics and textual NIR referencing this type
    /// would print the wrong name.
    pub const NAMED_TYPE_SYMBOL_MISMATCH: &str = "V0030";
    /// A `Call`/`RecordCreate`/`VariantCreate`/type application supplies a
    /// number of type arguments that does not match the number of type
    /// parameters its callee/record/variant declares (`rfcs/0008`).
    pub const GENERIC_ARITY_MISMATCH: &str = "V0031";
    /// A `Ty::Param` appears somewhere outside the body/layout of the
    /// generic declaration that actually declares it -- e.g. a function
    /// with no type parameters of its own using another declaration's
    /// symbolic parameter as if it were a concrete type. Symbolic
    /// parameters are only ever meaningful within the one declaration
    /// that binds them; anywhere else, lowering has a bug and one must
    /// never reach the interpreter.
    pub const ESCAPING_TYPE_PARAMETER: &str = "V0032";
    /// A `Ty::Named` refers to a record/variant that declares one or
    /// more type parameters, used without any applied type arguments
    /// (`rfcs/0008` requires every reference to a generic declaration to
    /// be a `Ty::Applied`; there is no raw/default/partially-applied
    /// generic type).
    pub const UNAPPLIED_GENERIC_TYPE: &str = "V0033";
    /// A function/record/variant declares the same `TypeParamId` more
    /// than once in its own type parameter list. Every declaration's own
    /// parameters must be pairwise distinct -- a duplicate would make a
    /// call/construction site's positional type-argument list ambiguous
    /// about which argument substitutes which occurrence.
    pub const DUPLICATE_TYPE_PARAMETER: &str = "V0034";
    /// A type nested deeper than `crate::limits::MAX_GENERIC_DEPTH`,
    /// found at *any* type root this verifier checks: a record field, a
    /// variant case payload, a function parameter or return type, an
    /// instruction's result type, or a `Call`/`RecordCreate`/
    /// `VariantCreate` type argument. Reported once per root, never once
    /// per nested level -- a real, structured diagnostic in place of the
    /// silent early return every other depth-bounded check in this
    /// module still falls back to past this same bound (defense in
    /// depth for those, since this check runs first and rejects the
    /// type outright before they would ever need to).
    pub const GENERIC_DEPTH_EXCEEDED: &str = "V0035";
    /// An `extend`'s own `protocol` field does not match any declared
    /// protocol in this module (`rfcs/0009`).
    pub const UNKNOWN_EXTEND_PROTOCOL: &str = "V0036";
    /// An `extend`'s `protocol_arguments` count does not match its own
    /// protocol's declared type-parameter count.
    pub const EXTEND_PROTOCOL_ARITY_MISMATCH: &str = "V0037";
    /// One capability requirement (an `extend`'s own `uses` clause, or an
    /// ordinary function's own `uses` clause) names a protocol this
    /// module never declared.
    pub const UNKNOWN_REQUIREMENT_PROTOCOL: &str = "V0038";
    /// One capability requirement (an `extend`'s own `uses` clause, or an
    /// ordinary function's own `uses` clause) supplies a number of
    /// arguments that does not match its own named protocol's declared
    /// type-parameter count.
    pub const REQUIREMENT_ARITY_MISMATCH: &str = "V0039";
    /// An `extend`'s method table has a different length than its own
    /// protocol's declared method list -- every protocol method must
    /// have exactly one implementing function, never more or fewer.
    pub const EXTEND_METHOD_COUNT_MISMATCH: &str = "V0040";
    /// An `extend`'s method table references a function id this module
    /// never declared.
    pub const EXTEND_METHOD_UNKNOWN_FUNCTION: &str = "V0041";
    /// An `extend`'s method table references a function whose own
    /// `type_params` are not exactly its owning extend's own
    /// `type_params`, in the same order -- every extend method's body is
    /// lowered sharing its extend's own type-parameter scope (never a
    /// separate generic scope of its own), so any mismatch here means
    /// this function was never actually built as this extend's method.
    pub const EXTEND_METHOD_TYPE_PARAM_MISMATCH: &str = "V0042";
    /// An `extend`'s method function's own declared parameter/return
    /// types do not match its protocol method's declared signature once
    /// substituted with this extend's own `protocol_arguments`.
    pub const EXTEND_METHOD_SIGNATURE_MISMATCH: &str = "V0043";
    /// The same underlying function id answers two different method
    /// slots in the same extend's own method table -- every protocol
    /// method an extend implements must be a distinct function.
    pub const DUPLICATE_EXTEND_METHOD_REFERENCE: &str = "V0044";
    /// A protocol or extend reuses an id already used by another
    /// protocol/extend in this module (`rfcs/0009`).
    pub const DUPLICATE_PROTOCOL_ID: &str = "V0045";
    pub const DUPLICATE_EXTEND_ID: &str = "V0046";
    /// A `Call`'s evidence does not carry exactly as many entries as its
    /// callee's own requirement count (`rfcs/0009`).
    pub const EVIDENCE_COUNT_MISMATCH: &str = "V0047";
    /// An `Evidence::Forwarded` index is out of range for the currently
    /// verified function's own `requirements`.
    pub const FORWARDED_INDEX_OUT_OF_RANGE: &str = "V0048";
    /// An `Evidence::Forwarded` index is in range, but the requirement
    /// it names is not exactly the capability actually required at this
    /// call site -- forwarding only ever passes a requirement through
    /// unchanged, never converts one into another.
    pub const FORWARDED_REQUIREMENT_MISMATCH: &str = "V0049";
    /// An `Evidence::Extension` names an extend id this module never
    /// declared.
    pub const UNKNOWN_EXTENSION_REFERENCE: &str = "V0050";
    /// An `Evidence::Extension`'s own extend targets a different
    /// protocol than the one actually required at this call site.
    pub const EXTENSION_PROTOCOL_MISMATCH: &str = "V0051";
    /// An `Evidence::Extension`'s own extend head cannot structurally
    /// match the arguments actually required at this call site -- no
    /// substitution of the extend's own type parameters makes its
    /// declared `protocol_arguments` equal the required arguments.
    pub const EXTENSION_HEAD_MISMATCH: &str = "V0052";
    /// An `Evidence::Extension`'s own `nested` evidence has a different
    /// length than its extend's own `requirements`.
    pub const NESTED_EVIDENCE_COUNT_MISMATCH: &str = "V0053";
    /// An `Evidence::Extension`'s own `nested` evidence contains a
    /// `Forwarded` entry. By the time a concrete extend is selected,
    /// every type it was selected for is already fully concrete, so
    /// every leaf of `nested` must itself always be `Extension` --
    /// `Forwarded` is only ever legal at the outermost evidence position
    /// of a `Call`/`protocol.call`, never nested inside a resolved
    /// extension.
    pub const FORWARDED_INSIDE_NESTED_EVIDENCE: &str = "V0054";
    /// Evidence nested deeper than `crate::limits::MAX_CAPABILITY_DEPTH`
    /// -- bounds a hostilely deep hand-built evidence tree the same way
    /// `GENERIC_DEPTH_EXCEEDED` bounds a hostilely deep type, so
    /// recursive evidence validation can never overflow the native
    /// stack. Reported once per malformed evidence root, never once per
    /// nested node.
    pub const EVIDENCE_DEPTH_EXCEEDED: &str = "V0055";
    /// Evidence validation visited more nodes than
    /// `crate::limits::MAX_CAPABILITY_RESOLUTION_STEPS` while checking
    /// one evidence root -- bounds a hand-built evidence tree that stays
    /// within the depth limit but branches wide enough at every level to
    /// make exhaustive validation itself pathologically expensive.
    pub const EVIDENCE_WORK_BUDGET_EXCEEDED: &str = "V0056";
    /// A `protocol.call` instruction names a protocol id this module
    /// never declared, or a `method` index out of range for that
    /// protocol's declared method list.
    pub const UNKNOWN_PROTOCOL_CALL_TARGET: &str = "V0057";
    /// An extend's method function does not declare exactly its own
    /// extend's `uses` requirements, in the same declared order.
    /// `ProtocolCall` passes an extension's own `nested` evidence
    /// straight to its implementing function as that function's own
    /// evidence; a mismatch here would let otherwise-valid-looking NIR
    /// pass every other extend/method check and still fail (or silently
    /// misdispatch) only once actually interpreted.
    pub const EXTEND_METHOD_REQUIREMENTS_MISMATCH: &str = "V0058";
    /// An extend's own type parameter does not occur anywhere inside its
    /// protocol's type arguments -- `rfcs/0009`'s exact-forwarding-only
    /// requirement (`typeck`'s own `T0046`), re-derived independently
    /// here since this verifier never trusts hand-built NIR to already
    /// satisfy it.
    pub const UNCONSTRAINED_EXTEND_PARAMETER: &str = "V0059";
    /// An `Evidence::Extension` was selected for a requirement whose
    /// arguments are still symbolic (contain a `Ty::Param`) -- Alpha
    /// 0.1.5 permits only an exact `Evidence::Forwarded` match in that
    /// situation; a concrete extend can only ever be legitimately
    /// selected once every argument is fully concrete.
    pub const EXTENSION_FOR_SYMBOLIC_REQUIREMENT: &str = "V0060";
    /// A function's own `raises` (`rfcs/0010`) names an `ItemId` that
    /// does not match any variant declared in this module.
    pub const UNKNOWN_RAISES_TYPE: &str = "V0061";
    /// A function's own `raises` names the same `ItemId` more than once
    /// -- the set of effects a function may raise is canonical, never a
    /// multiset.
    pub const DUPLICATE_RAISES_ENTRY: &str = "V0062";
    /// An ordinary `ValueKind::Call` targets a function whose own
    /// `raises` is non-empty. A fallible callee may only ever be invoked
    /// through `Terminator::Invoke`, which alone has a failure edge to
    /// route a raised value to -- an ordinary `Call` has nowhere for one
    /// to go.
    pub const CALL_TO_FALLIBLE_FUNCTION: &str = "V0063";
    /// A `Terminator::Invoke` targets a function whose own `raises` is
    /// empty. Since it can never actually raise, this callee should have
    /// been an ordinary `Call` -- an `Invoke` with no failure edges is
    /// never a valid lowering of anything typeck accepts.
    pub const INVOKE_OF_INFALLIBLE_FUNCTION: &str = "V0064";
    /// A `Terminator::Invoke`'s own `ok_slot` was never allocated with
    /// `alloc` -- mirrors `UNKNOWN_SLOT` for the slot an ordinary `Store`
    /// writes into: `Invoke`'s success edge writes into `ok_slot` in
    /// exactly the same way.
    pub const INVOKE_SUCCESS_SLOT_UNALLOCATED: &str = "V0065";
    /// A `Terminator::Invoke`'s own `ok_slot` is declared a different
    /// type than its callee's own (substituted) return type.
    pub const INVOKE_SUCCESS_TYPE_MISMATCH: &str = "V0066";
    /// A `Terminator::Invoke`'s own `err_targets` does not have exactly
    /// one entry per variant in its callee's own declared `raises`, in
    /// any order, with no duplicate or unknown variant -- every effect
    /// the callee can actually raise must have exactly one destination,
    /// and no destination may exist for an effect the callee can never
    /// raise.
    pub const INVOKE_ERR_TARGET_COVERAGE_MISMATCH: &str = "V0067";
    /// One of a `Terminator::Invoke`'s own `err_targets` entries has a
    /// `slot` that was never allocated with `alloc` (mirrors
    /// `INVOKE_SUCCESS_SLOT_UNALLOCATED`, for a failure edge instead of
    /// the success edge).
    pub const INVOKE_FAILURE_SLOT_UNALLOCATED: &str = "V0068";
    /// One of a `Terminator::Invoke`'s own `err_targets` entries has a
    /// `slot` declared a different type than `Ty::Named`/`Ty::Applied` of
    /// that entry's own `variant`.
    pub const INVOKE_FAILURE_TYPE_MISMATCH: &str = "V0069";
    /// A `Terminator::Raise`'s own `value` is not declared a type that
    /// matches any variant in the currently verified function's own
    /// `raises` set -- a function may only ever raise an effect it
    /// actually declares (`rfcs/0010`).
    pub const UNDECLARED_RAISE: &str = "V0070";
    /// A function's own `raises` names a variant declaring one or more
    /// type parameters. Generic error variants are explicitly out of
    /// scope (`rfcs/0010`); `hir::lower`'s own `resolve_raises` already
    /// rejects this for ordinary source, but this verifier never trusts
    /// hand-built NIR to already satisfy it.
    pub const GENERIC_RAISES_TYPE: &str = "V0071";
    /// An extend's method function's own `raises` is non-empty. A
    /// protocol method has no `raises` of its own yet (`rfcs/0010`'s own
    /// honest limitation), so every implementing method must be
    /// infallible too -- `hir::lower`/`typeck` both already reject this
    /// for ordinary source, but this verifier never trusts hand-built
    /// NIR to already satisfy it.
    pub const EXTEND_METHOD_MUST_BE_INFALLIBLE: &str = "V0072";
    /// A `Load` reads a slot some `Terminator::Invoke` in this same
    /// function writes on one of its own edges (`ok_slot`, or one of its
    /// `err_targets`' own `slot`), from a block the CFG does not prove is
    /// reached *only* through that one edge -- dominance from the slot's
    /// own `alloc` (already required) proves the slot exists before this
    /// point, but never that the specific edge which actually writes it
    /// is the one that was taken to get here. Mirrors
    /// `PAYLOAD_OUTSIDE_REFINEMENT`'s own single-hop "every incoming edge
    /// must agree" model, applied to Invoke's own conditional writes
    /// instead of a `Switch`'s own case refinement.
    pub const INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED: &str = "V0073";
    /// `Instruction::Drop`'s own operand is not a resource-typed value
    /// (`rfcs/0011`) -- only a declared `resource` may ever be dropped.
    pub const DROP_OF_NON_RESOURCE_VALUE: &str = "V0074";
    /// The same value is definitely already `Drop`ped on every path
    /// reaching a second `Drop` of it (`rfcs/0011`) -- a full forward
    /// must-dataflow analysis, the same shape as
    /// `INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED`'s own.
    pub const DOUBLE_DROP: &str = "V0075";
    /// A resource-typed value's own underlying identity (its exact
    /// `ValueId`, or -- for one loaded from a slot -- that slot, so a
    /// second `Load` of the same slot is recognized as the identical
    /// resource under a different id) was already consumed -- dropped,
    /// moved into a `take` parameter/`Invoke` argument, or transferred
    /// out through `Terminator::Return` -- on some path reaching this
    /// use (`rfcs/0011`). Independent of `resourceck`: this is
    /// `nir::verify`'s own reconstruction from NIR alone, the same
    /// reachable-union dataflow `DOUBLE_DROP` already uses, generalized
    /// from "was this exact value already the operand of a `Drop`" to
    /// "was this value's own underlying resource already consumed by
    /// anything".
    pub const RESOURCE_USE_AFTER_CONSUME: &str = "V0076";
    /// A resource this function itself created, or received through a
    /// `take` parameter or a fallible `Invoke`'s own success slot, is
    /// still owned (never `Drop`ped, moved into a `take` parameter/
    /// `Invoke` argument, or transferred out through `Terminator::
    /// Return`/`Raise`) at a reachable `Return`/`Raise` (`rfcs/0011`).
    /// Independent of `resourceck`: reconstructed here purely from NIR,
    /// the same reachable-union dataflow `RESOURCE_USE_AFTER_CONSUME`
    /// already uses, tracking "still live" instead of "already
    /// consumed". An `Invoke`'s own success slot is seeded as owned
    /// specifically on its own `ok_target` edge, never a sibling
    /// failure edge that happens to share a block -- see
    /// `verify_resource_ownership`'s own doc comment.
    pub const RESOURCE_LEAKED_ON_EXIT: &str = "V0077";
    /// `Move`/`DeferCapture`'s own `source` operand is not resource-
    /// typed (`rfcs/0011`) -- only a resource may ever be moved; an
    /// ordinary value is always freely observed/copied instead, and
    /// never needs (or is permitted) an explicit transfer instruction
    /// of its own. `nir::lower` never produces this shape (both are
    /// only ever emitted for an already-affine value); only a
    /// hand-built module can.
    pub const MOVE_SOURCE_NOT_RESOURCE: &str = "V0078";
    /// A resource-typed value currently holding only an *observing*
    /// role (loaded from a `store.observe`'d slot, or an ordinary
    /// non-`take` parameter) was used where only an owning value may be
    /// used: the `source` of a `Move`/`DeferCapture`, the operand of a
    /// `Drop`, a `take` call/`Invoke` argument, or a `Terminator::
    /// Return`/`Raise` operand (`rfcs/0011`). An observation is never
    /// itself an owner and must never be silently promoted into one --
    /// `nir::verify` tracks this role per value/slot, flow-sensitively,
    /// independently of `resourceck`.
    pub const RESOURCE_OBSERVER_CONSUMED: &str = "V0079";
    /// A `store.transfer`'s own `value` operand does not currently hold
    /// an owning role (`rfcs/0011`) -- `OwnershipMode::Transfer` always
    /// means "the destination becomes the one current owner", which is
    /// only ever sound if `value` was itself already an owner; storing
    /// a merely-observing value with `Transfer` mode would silently
    /// mint a second, spurious owner for the same underlying resource.
    pub const INVALID_RESOURCE_STORE_MODE: &str = "V0080";
    /// A value is used -- consumed or merely observed -- whose own
    /// underlying resource origin was already destroyed by a `Drop`
    /// reaching this point through a *different* alias of the same
    /// resource (`rfcs/0011`): an observation created before the drop,
    /// still nominally "in scope", now dangling. Distinct from
    /// `RESOURCE_USE_AFTER_CONSUME`, which only ever unifies identity
    /// through repeated `Load`s of one shared slot -- this check
    /// unifies identity across an observing `Store`/`Load` pair too, so
    /// a drop reachable through one alias is visible to every other
    /// alias of that same resource, not only the one that performed it.
    pub const RESOURCE_ORIGIN_CONFLICT: &str = "V0081";
    /// A resource-typed value/slot is used (loaded, dropped, moved,
    /// captured, passed as any argument, or transferred out) without
    /// being definitely initialized on *every* reachable path reaching
    /// that use (`rfcs/0011`) -- never written at all on this path, or
    /// written on only some of several reachable paths converging here.
    /// A full forward may-dataflow analysis over `Alloc`/`store.observe`/
    /// `store.transfer`/`Invoke`'s own success edge, the same reachable-
    /// union shape `RESOURCE_LEAKED_ON_EXIT` already uses -- never a
    /// single-hop check of a use's own immediate predecessors, and never
    /// a lenient default that treats a location this pass recorded
    /// nothing for as already owned.
    pub const RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED: &str = "V0082";
    /// A structural place (`rfcs/0012`) projects a field through a base
    /// whose own resolved type is not the declared owner record at all
    /// (a primitive, a different record, or the wrong generic
    /// instantiation).
    pub const PLACE_PROJECTION_THROUGH_NON_RECORD: &str = "V0083";
    /// A structural place names a field owner `ItemId` this module never
    /// registered as a record.
    pub const INVALID_PLACE_FIELD_OWNER: &str = "V0084";
    /// A structural place names a field index out of range for its own
    /// declared owner record.
    pub const UNKNOWN_PLACE_FIELD: &str = "V0085";
    /// A `PlaceRead`/`StorePlace` names a place whose own resolved type
    /// is not affine (`rfcs/0012`) -- there is no ownership state to
    /// move or reinitialize for an ordinary, freely-copyable field.
    pub const MOVE_OF_NON_AFFINE_PLACE: &str = "V0086";
    /// A structural place (`rfcs/0012`) is read or moved (`PlaceRead`,
    /// either mode) on a path where it is not *definitely* still holding
    /// its own value -- already moved out on every reachable path
    /// reaching this use, or moved on only some of several reachable
    /// paths converging here. The same reachable-union "may" dataflow
    /// shape `RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED` already
    /// uses, applied to individual structural fields instead of whole
    /// locations.
    pub const PLACE_USE_AFTER_MOVE: &str = "V0087";
    /// A `StorePlace` (`rfcs/0012`, structural reinitialization) targets
    /// a place that is not *definitely* empty on every reachable path --
    /// it is still holding a live value on at least one of them, which
    /// this store would silently leak.
    pub const PLACE_OVERWRITE_OF_LIVE_FIELD: &str = "V0088";
    /// A structural place projects through a *generic* aggregate whose
    /// own recorded type-parameter list disagrees with the number of
    /// type arguments the place's own current type carries
    /// (`rfcs/0008`, `rfcs/0012`) -- a `Box[i64, str]` reaching a
    /// one-parameter `Box`, or a `Box[File]` reaching a declaration this
    /// module recorded no parameters for at all. Never papered over
    /// with an empty or partial substitution: an unsubstituted
    /// `Ty::Param` leaking out of a projection would make a genuinely
    /// affine field look freely copyable.
    pub const PLACE_GENERIC_ARITY_MISMATCH: &str = "V0089";
    /// A place is used as a *whole* value -- observed, transferred,
    /// returned, raised, or consumed into an aggregate -- while one of
    /// its own affine descendants has already been moved out or dropped
    /// (`rfcs/0012`). Only accessing an unaffected sibling,
    /// reinitializing an empty child, or structurally dropping what
    /// remains is still permitted on a partially moved parent; this is
    /// `nir::verify`'s own independent reconstruction of the same rule
    /// `resourceck`'s `PARTIAL_PARENT_USED_AS_WHOLE` (U0014) applies at
    /// the source level.
    pub const PARTIAL_PLACE_USED_AS_WHOLE: &str = "V0090";
    /// A transitively affine value this function owns still has
    /// remaining owned affine descendants at a reachable
    /// `Return`/`Raise` (`rfcs/0012`) -- a structural leak.
    /// Complements `RESOURCE_LEAKED_ON_EXIT` (V0077), which covers the
    /// same obligation for a *nominally* resource-typed root: this one
    /// covers the gap that lattice cannot see, a record that merely
    /// *contains* affine fields and is therefore never a key there.
    pub const MISSING_STRUCTURAL_CLEANUP: &str = "V0091";
    /// A place is destroyed or transferred whole after it was already
    /// consumed on a path reaching it (`rfcs/0012`) -- duplicate
    /// structural cleanup, including destroying a child whose own
    /// parent was already dropped, or dropping the same structural
    /// field twice.
    pub const DUPLICATE_STRUCTURAL_CLEANUP: &str = "V0092";
    /// A `StorePlace` whose own stored value is the very root its
    /// destination place projects out of (`rfcs/0012`) -- an aggregate
    /// stored into one of its own fields. Because the store *transfers*
    /// ownership, the container would end up holding a handle its own
    /// transfer had just made stale, so this is rejected outright
    /// rather than left to fail unpredictably at run time.
    pub const STORE_PLACE_SELF_ALIAS: &str = "V0093";
    /// A `DecomposeVariant` whose own base is not *proven* to hold the
    /// case it takes apart, on every path reaching it (`rfcs/0012`).
    ///
    /// Decomposition moves ownership of one specific case's payload
    /// storage. Without a proof that the value actually holds that
    /// case, the storage may not exist at all, and the payload of
    /// whichever case really is live is abandoned with nothing owning
    /// it. The proof is a real CFG fixed point over
    /// `(canonical scrutinee, variant, case)` guarantees: it
    /// originates on a `Switch` case edge, propagates through ordinary
    /// edges, and is intersected at every join, so a block reachable
    /// through two different cases has proven neither.
    ///
    /// Complements `PAYLOAD_OUTSIDE_REFINEMENT` (V0024), which asks the
    /// same question of a payload *read*: this one covers the transfer
    /// of ownership, which a read never performs.
    pub const DECOMPOSITION_OUTSIDE_REFINEMENT: &str = "V0095";
    /// A `DecomposeVariant` claims an owner that is not the value the
    /// matching `ValueKind::VariantPayload` extraction produced
    /// (`rfcs/0012`).
    ///
    /// Decomposition transfers *storage*, so the receiving value must
    /// be the one that named that exact base, case and payload
    /// position. A different value of the same declared type is a
    /// different object: claiming it would leave the real payload owned
    /// by nothing, and hand this frame an obligation for something it
    /// never received.
    pub const DECOMPOSITION_CLAIM_MISMATCH: &str = "V0096";
    /// A payload extraction is destroyed or transferred without any
    /// decomposition having transferred ownership of it (`rfcs/0012`).
    ///
    /// `ValueKind::VariantPayload` is a read. The shell still owns what
    /// it read until a `DecomposeVariant` claims that exact extraction,
    /// so consuming the read result destroys storage the shell will
    /// destroy again.
    pub const UNCLAIMED_PAYLOAD_OWNERSHIP: &str = "V0097";
    // `V0094` is deliberately not assigned. It claimed a structural
    // ownership state invariant -- "a control-flow edge named a block
    // this function does not declare" -- that no `.npt` source and no
    // hand-built NIR can actually produce: a block's predecessors are
    // derived by walking the declared blocks' own terminators, so a
    // predecessor is always itself declared. The two malformed-CFG
    // shapes that *are* reachable already have owners one layer up: a
    // terminator naming an undeclared successor is `UNKNOWN_BRANCH_
    // TARGET`, and a repeated block id is `DUPLICATE_BLOCK_ID`. Rather
    // than keep a code whose coverage was a dead branch, the
    // distinction it existed to protect is now carried by the
    // `IncomingState` type itself.
}

/// Every function this module's `Call` instructions might reference,
/// along with the signature the verifier checks calls against.
struct KnownFunction {
    /// This function's own declared type parameters, in declaration
    /// order -- a `Call`'s type arguments are substituted into `params`/
    /// `return_type` positionally against this same order before being
    /// checked against the call's actual argument/result types.
    type_params: Vec<TypeParamId>,
    params: Vec<Ty>,
    return_type: Ty,
    /// This function's own capability requirements (`rfcs/0009`), in
    /// declared order -- a `Call` targeting it must carry exactly this
    /// many evidence entries, each independently checked against the
    /// corresponding substituted requirement here.
    requirements: Vec<CapabilityRequirement>,
    /// This function's own declared raised-error set (`rfcs/0010`) --
    /// empty means infallible (only ever legally targeted by an ordinary
    /// `Call`), non-empty means fallible (only ever legally targeted by
    /// `Terminator::Invoke`).
    raises: Vec<ItemId>,
    /// Index-aligned with `params`: whether that parameter was declared
    /// `take` (`rfcs/0011`) -- read back by `verify_resource_ownership`
    /// to tell a call's own ownership-transferring argument apart from a
    /// merely-observing one, independently of `nir::lower`'s own
    /// bookkeeping.
    take: Vec<bool>,
}

/// Every declared record's/variant's/protocol's/extend's layout, by
/// `ItemId`, for validating an operation against the module's own
/// declared shape rather than trusting whatever instruction happened to
/// be built with.
struct AggregateContext<'a> {
    records: HashMap<ItemId, &'a RecordLayout>,
    variants: HashMap<ItemId, &'a VariantLayout>,
    protocols: HashMap<ItemId, &'a ProtocolLayout>,
    /// Read by `check_evidence` to resolve an `Evidence::Extension`
    /// against its own declared extend.
    extends: HashMap<ItemId, &'a ExtendLayout>,
}

/// Verifies every function in `module`, collecting every diagnostic it
/// can rather than stopping at the first problem (mirroring `typeck`'s
/// own style) -- an empty result means the module is safe to interpret.
pub fn verify_module(
    module: &Module,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    // `ItemId` is required to be globally unique across every
    // module-level item this NIR represents (functions, records,
    // variants) -- not just unique within its own kind. Two different
    // kinds of item sharing an id is exactly the gap that would let a
    // value constructed as one kind (say, a record) be silently
    // switched over as another (a variant) sharing that id, since
    // `Ty::Named` only ever compares by `ItemId`. Tracked independently
    // of `known_functions`/`agg` below (which use plain `HashMap`s and
    // would otherwise silently let a duplicate's later entry win).
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum ItemRole {
        Function,
        Record,
        Variant,
        Protocol,
        Extend,
    }
    let mut item_roles: HashMap<ItemId, ItemRole> = HashMap::new();
    let mut check_item_identity =
        |id: ItemId, role: ItemRole, name: &str, diagnostics: &mut Vec<Diagnostic>| {
            if let Some(&existing) = item_roles.get(&id) {
                if existing != role {
                    diagnostics.push(Diagnostic::error(
                    codes::ITEM_ID_KIND_COLLISION,
                    source,
                    Span::dummy(),
                    format!(
                        "`{name}` reuses an id already used by a different kind of item in this module"
                    ),
                ));
                }
            } else {
                item_roles.insert(id, role);
            }
        };

    let mut known_functions: HashMap<ItemId, KnownFunction> = HashMap::new();
    let mut seen_function_ids = HashSet::new();
    for function in &module.functions {
        let name = registry.qualified_name(function.id, interner);
        if !seen_function_ids.insert(function.id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_FUNCTION_ID,
                source,
                Span::dummy(),
                format!(
                    "function `{name}` reuses an id already used by another function in this module"
                ),
            ));
        }
        check_item_identity(function.id, ItemRole::Function, &name, &mut diagnostics);
        known_functions.insert(
            function.id,
            KnownFunction {
                type_params: function.type_params.iter().map(|(id, _)| *id).collect(),
                params: function.params.iter().map(|p| p.ty.clone()).collect(),
                return_type: function.return_type.clone(),
                requirements: function.requirements.clone(),
                raises: function.raises.clone(),
                take: function.params.iter().map(|p| p.take).collect(),
            },
        );
    }

    let mut seen_record_ids = HashSet::new();
    for (id, _record) in &module.records {
        let name = registry.qualified_name(*id, interner);
        if !seen_record_ids.insert(*id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_RECORD_ID,
                source,
                Span::dummy(),
                format!(
                    "record `{name}` reuses an id already used by another record in this module"
                ),
            ));
        }
        check_item_identity(*id, ItemRole::Record, &name, &mut diagnostics);
    }
    let mut seen_variant_ids = HashSet::new();
    for (id, _variant) in &module.variants {
        let name = registry.qualified_name(*id, interner);
        if !seen_variant_ids.insert(*id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_VARIANT_ID,
                source,
                Span::dummy(),
                format!(
                    "variant `{name}` reuses an id already used by another variant in this module"
                ),
            ));
        }
        check_item_identity(*id, ItemRole::Variant, &name, &mut diagnostics);
    }
    let mut seen_protocol_ids = HashSet::new();
    for (id, _protocol) in &module.protocols {
        let name = registry.qualified_name(*id, interner);
        if !seen_protocol_ids.insert(*id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_PROTOCOL_ID,
                source,
                Span::dummy(),
                format!(
                    "protocol `{name}` reuses an id already used by another protocol in this module"
                ),
            ));
        }
        check_item_identity(*id, ItemRole::Protocol, &name, &mut diagnostics);
    }
    let mut seen_extend_ids = HashSet::new();
    for (id, _extend) in &module.extends {
        let name = format!("extend #{}", id.0);
        if !seen_extend_ids.insert(*id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_EXTEND_ID,
                source,
                Span::dummy(),
                format!("{name} reuses an id already used by another extend in this module"),
            ));
        }
        check_item_identity(*id, ItemRole::Extend, &name, &mut diagnostics);
    }

    let agg = AggregateContext {
        records: module.records.iter().map(|(id, r)| (*id, r)).collect(),
        variants: module.variants.iter().map(|(id, v)| (*id, v)).collect(),
        protocols: module.protocols.iter().map(|(id, p)| (*id, p)).collect(),
        extends: module.extends.iter().map(|(id, e)| (*id, e)).collect(),
    };

    // Every record field's and every variant case payload's own
    // declared type must be independently valid -- unresolved,
    // erroneous, or dangling-named types are never allowed to hide
    // inside an aggregate's layout just because nothing ever
    // constructs one.
    for (id, record) in &module.records {
        let context = format!("record `{}`", registry.qualified_name(*id, interner));
        check_no_duplicate_type_params(&record.type_params, source, &context, &mut diagnostics);
        let own_params: HashSet<TypeParamId> =
            record.type_params.iter().map(|(id, _)| *id).collect();
        for (field_name, ty) in &record.fields {
            let field_context = format!("{context}'s field `{}`", interner.resolve(*field_name));
            check_type_root(
                ty,
                &agg,
                &own_params,
                source,
                interner,
                registry,
                &field_context,
                &mut diagnostics,
            );
        }
    }
    for (id, variant) in &module.variants {
        let context = format!("variant `{}`", registry.qualified_name(*id, interner));
        check_no_duplicate_type_params(&variant.type_params, source, &context, &mut diagnostics);
        let own_params: HashSet<TypeParamId> =
            variant.type_params.iter().map(|(id, _)| *id).collect();
        for case in &variant.cases {
            for (i, ty) in case.payload.iter().enumerate() {
                let payload_context = format!(
                    "{context}'s case `{}` payload position {i}",
                    interner.resolve(case.name)
                );
                check_type_root(
                    ty,
                    &agg,
                    &own_params,
                    source,
                    interner,
                    registry,
                    &payload_context,
                    &mut diagnostics,
                );
            }
        }
    }

    // Every protocol's own type parameters must be pairwise distinct,
    // and every method's declared parameter/return type must be a valid
    // type root scoped to that protocol's own type parameters (`rfcs/0009`)
    // -- exactly the same shape of check a record's fields or a variant's
    // case payloads already get. A protocol's method list is never
    // iterated in a way whose *checking* order matters (unlike its
    // declaration order, which is load-bearing for `protocol.call`'s own
    // `method` index and is preserved automatically by walking the `Vec`
    // in place).
    for (id, protocol) in &module.protocols {
        let context = format!("protocol `{}`", registry.qualified_name(*id, interner));
        check_no_duplicate_type_params(&protocol.type_params, source, &context, &mut diagnostics);
        let own_params: HashSet<TypeParamId> =
            protocol.type_params.iter().map(|(id, _)| *id).collect();
        for method in &protocol.methods {
            let method_context = format!("{context}'s method `{}`", interner.resolve(method.name));
            for param in &method.params {
                check_type_root(
                    param,
                    &agg,
                    &own_params,
                    source,
                    interner,
                    registry,
                    &method_context,
                    &mut diagnostics,
                );
            }
            check_type_root(
                &method.return_type,
                &agg,
                &own_params,
                source,
                interner,
                registry,
                &method_context,
                &mut diagnostics,
            );
        }
    }

    // Every `extend`'s own declared shape must independently hold
    // (`rfcs/0009`): its `protocol` must actually exist, its own
    // `protocol_arguments`/`requirements` must be well-formed types
    // referencing that protocol (and any other) with the right arity,
    // its method table must have exactly one entry per protocol method,
    // and each entry must reference a real, distinct function actually
    // built as this extend's own method (sharing its exact type-param
    // scope) with a signature matching the protocol method it
    // implements once substituted through this extend's own head.
    for (id, extend) in &module.extends {
        let context = format!("extend #{}", id.0);
        check_no_duplicate_type_params(&extend.type_params, source, &context, &mut diagnostics);
        let own_params: HashSet<TypeParamId> =
            extend.type_params.iter().map(|(id, _)| *id).collect();

        // Exact-forwarding-only symbolic semantics (`rfcs/0009`): an
        // extend's own type parameter must be determined by its protocol
        // head alone. `typeck` already rejects this for ordinary source
        // (`T0046`); re-derived here independently since this verifier
        // never trusts hand-built NIR to already satisfy it.
        let mut occurring_params: HashSet<TypeParamId> = HashSet::new();
        for ty in &extend.protocol_arguments {
            collect_occurring_type_params(ty, &mut occurring_params, 0);
        }
        for (type_param_id, type_param_name) in &extend.type_params {
            if !occurring_params.contains(type_param_id) {
                diagnostics.push(Diagnostic::error(
                    codes::UNCONSTRAINED_EXTEND_PARAMETER,
                    source,
                    Span::dummy(),
                    format!(
                        "{context}'s type parameter `{}` does not occur in the protocol arguments and cannot be determined by this extension's head",
                        interner.resolve(*type_param_name)
                    ),
                ));
            }
        }

        let arg_context = format!("{context}'s protocol argument");
        for ty in &extend.protocol_arguments {
            check_type_root(
                ty,
                &agg,
                &own_params,
                source,
                interner,
                registry,
                &arg_context,
                &mut diagnostics,
            );
        }
        for requirement in &extend.requirements {
            let requirement_context = format!("{context}'s `uses` requirement");
            for ty in &requirement.arguments {
                check_type_root(
                    ty,
                    &agg,
                    &own_params,
                    source,
                    interner,
                    registry,
                    &requirement_context,
                    &mut diagnostics,
                );
            }
            match agg.protocols.get(&requirement.protocol) {
                None => diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_REQUIREMENT_PROTOCOL,
                    source,
                    Span::dummy(),
                    format!(
                        "{requirement_context} names a protocol id {} that does not exist in this module",
                        requirement.protocol.0
                    ),
                )),
                Some(required_protocol)
                    if required_protocol.type_params.len() != requirement.arguments.len() =>
                {
                    diagnostics.push(Diagnostic::error(
                        codes::REQUIREMENT_ARITY_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "{requirement_context} supplies {} argument(s) to `{}`, which declares {}",
                            requirement.arguments.len(),
                            registry.qualified_name(requirement.protocol, interner),
                            required_protocol.type_params.len()
                        ),
                    ));
                }
                Some(_) => {}
            }
        }

        let Some(protocol) = agg.protocols.get(&extend.protocol) else {
            diagnostics.push(Diagnostic::error(
                codes::UNKNOWN_EXTEND_PROTOCOL,
                source,
                Span::dummy(),
                format!(
                    "{context} names a protocol id {} that does not exist in this module",
                    extend.protocol.0
                ),
            ));
            continue;
        };
        if protocol.type_params.len() != extend.protocol_arguments.len() {
            diagnostics.push(Diagnostic::error(
                codes::EXTEND_PROTOCOL_ARITY_MISMATCH,
                source,
                Span::dummy(),
                format!(
                    "{context} supplies {} argument(s) to `{}`, which declares {}",
                    extend.protocol_arguments.len(),
                    registry.qualified_name(extend.protocol, interner),
                    protocol.type_params.len()
                ),
            ));
        }
        if protocol.methods.len() != extend.methods.len() {
            diagnostics.push(Diagnostic::error(
                codes::EXTEND_METHOD_COUNT_MISMATCH,
                source,
                Span::dummy(),
                format!(
                    "{context} implements {} method(s), but `{}` declares {}",
                    extend.methods.len(),
                    registry.qualified_name(extend.protocol, interner),
                    protocol.methods.len()
                ),
            ));
        }
        let subst: HashMap<TypeParamId, Ty> = protocol
            .type_params
            .iter()
            .map(|(id, _)| *id)
            .zip(extend.protocol_arguments.iter().cloned())
            .collect();
        let extend_type_param_ids: Vec<TypeParamId> =
            extend.type_params.iter().map(|(id, _)| *id).collect();
        let mut seen_method_functions: HashSet<ItemId> = HashSet::new();
        for (index, method_id) in extend.methods.iter().enumerate() {
            if !seen_method_functions.insert(*method_id) {
                diagnostics.push(Diagnostic::error(
                    codes::DUPLICATE_EXTEND_METHOD_REFERENCE,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} uses the same function ({}) for two different method slots",
                        registry.qualified_name(*method_id, interner)
                    ),
                ));
            }
            let Some(implementing) = known_functions.get(method_id) else {
                diagnostics.push(Diagnostic::error(
                    codes::EXTEND_METHOD_UNKNOWN_FUNCTION,
                    source,
                    Span::dummy(),
                    format!(
                        "{context}'s method[{index}] references function id {}, which does not exist in this module",
                        method_id.0
                    ),
                ));
                continue;
            };
            if implementing.type_params != extend_type_param_ids {
                diagnostics.push(Diagnostic::error(
                    codes::EXTEND_METHOD_TYPE_PARAM_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "{context}'s method[{index}] ({}) does not share its own extend's type-parameter scope",
                        registry.qualified_name(*method_id, interner)
                    ),
                ));
            }
            // `ProtocolCall` passes an extension's own `nested` evidence
            // straight to its implementing function as that function's
            // evidence (`interpreter::ValueKind::ProtocolCall`), and
            // `Interpreter::call_function` validates that evidence
            // against the callee's own declared `Function::requirements`
            // -- so an implementing function's own requirements must be
            // exactly its extend's own `requirements`, in the same
            // declared order, or a well-formed extend could still fail
            // at runtime (or worse, silently accept mismatched evidence)
            // despite passing every other check above.
            if implementing.requirements != extend.requirements {
                diagnostics.push(Diagnostic::error(
                    codes::EXTEND_METHOD_REQUIREMENTS_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "{context}'s method[{index}] ({}) does not declare exactly its own extend's `uses` requirements, in the same order",
                        registry.qualified_name(*method_id, interner)
                    ),
                ));
            }
            // A protocol method has no `raises` of its own yet
            // (`rfcs/0010`'s own honest limitation) -- an implementing
            // method whose own `raises` is non-empty could otherwise
            // satisfy an apparently infallible protocol method, and
            // `ProtocolCall` (an ordinary value instruction with only
            // one destination) would have nowhere for a raised value to
            // go.
            if !implementing.raises.is_empty() {
                diagnostics.push(Diagnostic::error(
                    codes::EXTEND_METHOD_MUST_BE_INFALLIBLE,
                    source,
                    Span::dummy(),
                    format!(
                        "{context}'s method[{index}] ({}) declares `raises`, but its protocol method has no raised-effect signature to narrow",
                        registry.qualified_name(*method_id, interner)
                    ),
                ));
            }
            let Some(protocol_method) = protocol.methods.get(index) else {
                // Already reported above as EXTEND_METHOD_COUNT_MISMATCH;
                // there is no protocol method at this index to check the
                // signature against.
                continue;
            };
            let expected_params: Vec<Ty> = protocol_method
                .params
                .iter()
                .map(|t| substitute(t, &subst))
                .collect();
            let expected_return = substitute(&protocol_method.return_type, &subst);
            if implementing.params != expected_params || implementing.return_type != expected_return
            {
                diagnostics.push(Diagnostic::error(
                    codes::EXTEND_METHOD_SIGNATURE_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "{context}'s method[{index}] ({}) does not match `{}`'s method `{}` signature once substituted",
                        registry.qualified_name(*method_id, interner),
                        registry.qualified_name(extend.protocol, interner),
                        interner.resolve(protocol_method.name)
                    ),
                ));
            }
        }
    }

    for function in &module.functions {
        verify_function(
            function,
            &known_functions,
            &agg,
            source,
            interner,
            registry,
            &mut diagnostics,
        );
    }

    diagnostics
}

fn verify_function(
    function: &Function,
    known_functions: &HashMap<ItemId, KnownFunction>,
    agg: &AggregateContext,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Computed once, as the item's canonical qualified name
    // (`rfcs/0007`) -- every message below that names this function
    // (including the ones built deeper in verify_dominance/
    // verify_payload_refinement/verify_value_kind, which only ever see
    // this same string) automatically stays qualified and alias-
    // independent without needing its own registry lookup.
    let name = registry.qualified_name(function.id, interner);

    if function.blocks.is_empty() {
        diagnostics.push(Diagnostic::error(
            codes::EMPTY_FUNCTION,
            source,
            Span::dummy(),
            format!("function `{name}` has no basic blocks (no entry block)"),
        ));
        return;
    }
    // `BlockId(0)` is the entry block by definition (the interpreter
    // starts there explicitly, not at whatever happens to be first in
    // the vector) -- a function whose blocks don't include one has no
    // defined starting point, regardless of vector ordering.
    if !function.blocks.iter().any(|b| b.id == BlockId(0)) {
        diagnostics.push(Diagnostic::error(
            codes::MISSING_ENTRY_BLOCK,
            source,
            Span::dummy(),
            format!("function `{name}` has no block with id bb0 (the required entry block)"),
        ));
        return;
    }

    let fn_context = format!("function `{name}`");
    check_no_duplicate_type_params(&function.type_params, source, &fn_context, diagnostics);
    let own_params: HashSet<TypeParamId> = function.type_params.iter().map(|(id, _)| *id).collect();
    check_type_root(
        &function.return_type,
        agg,
        &own_params,
        source,
        interner,
        registry,
        &fn_context,
        diagnostics,
    );
    for param in &function.params {
        check_type_root(
            &param.ty,
            agg,
            &own_params,
            source,
            interner,
            registry,
            &fn_context,
            diagnostics,
        );
    }
    for requirement in &function.requirements {
        let requirement_context = format!("{fn_context}'s `uses` requirement");
        for ty in &requirement.arguments {
            check_type_root(
                ty,
                agg,
                &own_params,
                source,
                interner,
                registry,
                &requirement_context,
                diagnostics,
            );
        }
        match agg.protocols.get(&requirement.protocol) {
            None => diagnostics.push(Diagnostic::error(
                codes::UNKNOWN_REQUIREMENT_PROTOCOL,
                source,
                Span::dummy(),
                format!(
                    "{requirement_context} names a protocol id {} that does not exist in this module",
                    requirement.protocol.0
                ),
            )),
            Some(required_protocol)
                if required_protocol.type_params.len() != requirement.arguments.len() =>
            {
                diagnostics.push(Diagnostic::error(
                    codes::REQUIREMENT_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "{requirement_context} supplies {} argument(s) to `{}`, which declares {}",
                        requirement.arguments.len(),
                        registry.qualified_name(requirement.protocol, interner),
                        required_protocol.type_params.len()
                    ),
                ));
            }
            Some(_) => {}
        }
    }

    // A function's own declared effect set (`rfcs/0010`) must be
    // well-formed independently of whatever built this NIR: every entry
    // must actually be a variant declared in this module, and the set
    // must be canonical (no `ItemId` repeated) -- exactly the two
    // invariants `hir::lower` already establishes for ordinary source,
    // re-derived here since this verifier never trusts hand-built NIR to
    // already satisfy them.
    let mut seen_raises: HashSet<ItemId> = HashSet::new();
    for raised in &function.raises {
        match agg.variants.get(raised) {
            None => diagnostics.push(Diagnostic::error(
                codes::UNKNOWN_RAISES_TYPE,
                source,
                Span::dummy(),
                format!(
                    "{fn_context}'s `raises` names id {}, which is not a variant declared in this module",
                    raised.0
                ),
            )),
            Some(layout) if !layout.type_params.is_empty() => diagnostics.push(Diagnostic::error(
                codes::GENERIC_RAISES_TYPE,
                source,
                Span::dummy(),
                format!(
                    "{fn_context}'s `raises` names `{}`, which declares {} type parameter(s); generic error variants are not supported",
                    registry.qualified_name(*raised, interner),
                    layout.type_params.len()
                ),
            )),
            Some(_) => {}
        }
        if !seen_raises.insert(*raised) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_RAISES_ENTRY,
                source,
                Span::dummy(),
                format!("{fn_context}'s `raises` names the same type more than once"),
            ));
        }
    }

    let known_blocks: HashSet<BlockId> = function.blocks.iter().map(|b| b.id).collect();
    let mut seen_block_ids = HashSet::new();
    for block in &function.blocks {
        if !seen_block_ids.insert(block.id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_BLOCK_ID,
                source,
                Span::dummy(),
                format!(
                    "function `{name}` has two blocks with the same id (bb{})",
                    block.id.0
                ),
            ));
        }
    }

    // Every value this function ever defines (params, every
    // instruction's result), and its declared type -- built once so
    // every later check is a lookup, never a re-derivation. Tracked
    // through `seen_value_ids` rather than relying on `value_types`
    // itself, since a plain `HashMap::insert` silently accepts a
    // duplicate key (the second definition would just overwrite the
    // first with no diagnostic) -- every SSA value must have exactly
    // one definition, across parameters *and* instruction results,
    // regardless of which block they're in.
    let extractions = payload_extractions(function);
    let mut value_types: HashMap<ValueId, Ty> = HashMap::new();
    let mut alloc_slots: HashSet<ValueId> = HashSet::new();
    let mut seen_value_ids: HashSet<ValueId> = HashSet::new();
    let mut param_values: HashSet<ValueId> = HashSet::new();
    for param in &function.params {
        param_values.insert(param.value);
        if !seen_value_ids.insert(param.value) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_VALUE_DEFINITION,
                source,
                Span::dummy(),
                format!(
                    "function `{name}` has a parameter reusing value id %{}, already defined elsewhere in this function",
                    param.value.0
                ),
            ));
        }
        value_types.insert(param.value, param.ty.clone());
    }
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value { result, ty, kind } = instruction {
                if !seen_value_ids.insert(*result) {
                    diagnostics.push(Diagnostic::error(
                        codes::DUPLICATE_VALUE_DEFINITION,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` has an instruction reusing value id %{}, already defined elsewhere in this function",
                            result.0
                        ),
                    ));
                }
                value_types.insert(*result, ty.clone());
                if matches!(kind, ValueKind::Alloc) {
                    alloc_slots.insert(*result);
                }
            }
        }
    }

    let known_values: HashSet<ValueId> = value_types.keys().copied().collect();
    let mut require_value = |id: ValueId, diagnostics: &mut Vec<Diagnostic>| {
        if !known_values.contains(&id) {
            diagnostics.push(Diagnostic::error(
                codes::UNKNOWN_VALUE,
                source,
                Span::dummy(),
                format!(
                    "function `{name}` references value %{} which is never defined",
                    id.0
                ),
            ));
        }
    };

    for block in &function.blocks {
        for instruction in &block.instructions {
            match instruction {
                Instruction::Value { result, ty, kind } => {
                    check_type_root(
                        ty,
                        agg,
                        &own_params,
                        source,
                        interner,
                        registry,
                        &fn_context,
                        diagnostics,
                    );
                    verify_value_kind(
                        *result,
                        ty,
                        kind,
                        &value_types,
                        &alloc_slots,
                        known_functions,
                        agg,
                        &own_params,
                        &function.requirements,
                        source,
                        &name,
                        interner,
                        registry,
                        diagnostics,
                        &mut require_value,
                    );
                }
                Instruction::Store { slot, value, .. } => {
                    require_value(*slot, diagnostics);
                    require_value(*value, diagnostics);
                    if !alloc_slots.contains(slot) {
                        diagnostics.push(Diagnostic::error(
                            codes::UNKNOWN_SLOT,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}` stores into %{} which was never allocated with `alloc`",
                                slot.0
                            ),
                        ));
                    } else if let (Some(slot_ty), Some(value_ty)) =
                        (value_types.get(slot), value_types.get(value))
                        && slot_ty != value_ty
                    {
                        diagnostics.push(Diagnostic::error(
                            codes::STORE_TYPE_MISMATCH,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}` stores a value of type `{}` into a slot declared `{}`",
                                crate::types::display_ty(value_ty, interner),
                                crate::types::display_ty(slot_ty, interner)
                            ),
                        ));
                    }
                }
                // Declaration identity, case index, payload indexes and
                // every claimed value's own type are revalidated here
                // rather than trusted from lowering: this instruction
                // names storage, so a malformed one would move ownership
                // of something that does not exist.
                Instruction::DecomposeVariant {
                    value,
                    variant,
                    case,
                    taken,
                } => {
                    require_value(*value, diagnostics);
                    for (_, owner) in taken {
                        require_value(*owner, diagnostics);
                    }
                    let base_ok = value_types.get(value).is_some_and(|ty| {
                        matches!(ty, Ty::Named(item, _) | Ty::Applied(item, _) if item == variant)
                    });
                    if !base_ok {
                        diagnostics.push(Diagnostic::error(
                            codes::PLACE_PROJECTION_THROUGH_NON_RECORD,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}`: %{} is taken apart as variant {}, which is \
                                 not its own declared type",
                                value.0, variant.0
                            ),
                        ));
                        continue;
                    }
                    let Some(layout) = agg
                        .variants
                        .get(variant)
                        .and_then(|v| v.cases.get(*case))
                        .cloned()
                    else {
                        diagnostics.push(Diagnostic::error(
                            codes::UNKNOWN_PLACE_FIELD,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}`: %{} is taken apart into case {case} of \
                                 variant {}, which has no such case",
                                value.0, variant.0
                            ),
                        ));
                        continue;
                    };
                    let args: Vec<Ty> = match value_types.get(value) {
                        Some(Ty::Applied(_, args)) => args.clone(),
                        _ => Vec::new(),
                    };
                    let Ok(subst) = item_substitution(*variant, &args, agg) else {
                        diagnostics.push(Diagnostic::error(
                            codes::PLACE_GENERIC_ARITY_MISMATCH,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}`: %{} is taken apart as variant {}, whose \
                                 declared type parameters disagree with its own type arguments",
                                value.0, variant.0
                            ),
                        ));
                        continue;
                    };
                    let mut seen: HashSet<usize> = HashSet::new();
                    let mut seen_owners: HashSet<ValueId> = HashSet::new();
                    for (index, owner) in taken {
                        // One value claiming two positions would be two
                        // separate obligations collapsed into one, and
                        // one of the two payloads would end up owned by
                        // nothing.
                        if !seen_owners.insert(*owner) {
                            diagnostics.push(Diagnostic::error(
                                codes::DECOMPOSITION_CLAIM_MISMATCH,
                                source,
                                Span::dummy(),
                                format!(
                                    "function `{name}`: %{} is claimed by more than one payload \
                                     position of a single decomposition",
                                    owner.0
                                ),
                            ));
                            continue;
                        }
                        // Decomposition transfers *storage*: the
                        // receiving value must be the very extraction
                        // that read this base, case and position. A
                        // different value of the same declared type is
                        // a different object, and claiming it would
                        // leave the real payload owned by nothing.
                        if !extractions.claim_matches(*owner, *value, *variant, *case, *index) {
                            diagnostics.push(Diagnostic::error(
                                codes::DECOMPOSITION_CLAIM_MISMATCH,
                                source,
                                Span::dummy(),
                                format!(
                                    "function `{name}`: %{} is claimed as payload position \
                                     {index} of %{}, but it is not the extraction that read it",
                                    owner.0, value.0
                                ),
                            ));
                            continue;
                        }
                        let Some(payload_ty) = layout.payload.get(*index) else {
                            diagnostics.push(Diagnostic::error(
                                codes::UNKNOWN_PLACE_FIELD,
                                source,
                                Span::dummy(),
                                format!(
                                    "function `{name}`: %{} claims payload position {index} of a \
                                     case that has no such position",
                                    owner.0
                                ),
                            ));
                            continue;
                        };
                        // One position claimed twice would hand the same
                        // storage to two owners.
                        if !seen.insert(*index) {
                            diagnostics.push(Diagnostic::error(
                                codes::DUPLICATE_STRUCTURAL_CLEANUP,
                                source,
                                Span::dummy(),
                                format!(
                                    "function `{name}`: payload position {index} of %{} is \
                                     claimed more than once by one decomposition",
                                    value.0
                                ),
                            ));
                            continue;
                        }
                        let expected = substitute(payload_ty, &subst);
                        if value_types.get(owner) != Some(&expected) {
                            diagnostics.push(Diagnostic::error(
                                codes::STORE_TYPE_MISMATCH,
                                source,
                                Span::dummy(),
                                format!(
                                    "function `{name}`: %{} is declared a different type from the \
                                     payload position it claims",
                                    owner.0
                                ),
                            ));
                        }
                    }
                }
                Instruction::Drop { value } => {
                    require_value(*value, diagnostics);
                    let is_resource = value_types
                        .get(value)
                        .is_some_and(|ty| is_affine_in(ty, agg));
                    if !is_resource {
                        diagnostics.push(Diagnostic::error(
                            codes::DROP_OF_NON_RESOURCE_VALUE,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}` drops %{}, which is not a resource value",
                                value.0
                            ),
                        ));
                    }
                }
                Instruction::StorePlace { place, value } => {
                    require_value(place.root, diagnostics);
                    require_value(*value, diagnostics);
                    // A store whose source *is* the storage its own
                    // destination is rooted in would have to place an
                    // aggregate inside itself (`rfcs/0012`) -- and
                    // because the store transfers, it would leave the
                    // container holding a handle its own transfer just
                    // made stale. Rejected statically, not only by the
                    // interpreter's own runtime guard.
                    if place.root == *value {
                        diagnostics.push(Diagnostic::error(
                            codes::STORE_PLACE_SELF_ALIAS,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}`: %{} is stored into a place rooted at itself",
                                value.0
                            ),
                        ));
                    }
                    if let Some(root_ty) = value_types.get(&place.root).cloned() {
                        match resolve_place_ty(&root_ty, &place.projections, agg) {
                            Ok(resolved_ty) => {
                                if !is_affine_in(&resolved_ty, agg) {
                                    diagnostics.push(Diagnostic::error(
                                        codes::MOVE_OF_NON_AFFINE_PLACE,
                                        source,
                                        Span::dummy(),
                                        format!(
                                            "function `{name}` reinitializes a place of non-affine type `{}`",
                                            crate::types::display_ty(&resolved_ty, interner)
                                        ),
                                    ));
                                } else if let Some(value_ty) = value_types.get(value)
                                    && resolved_ty != *value_ty
                                {
                                    diagnostics.push(Diagnostic::error(
                                        codes::STORE_TYPE_MISMATCH,
                                        source,
                                        Span::dummy(),
                                        format!(
                                            "function `{name}` stores a value of type `{}` into a place declared `{}`",
                                            crate::types::display_ty(value_ty, interner),
                                            crate::types::display_ty(&resolved_ty, interner)
                                        ),
                                    ));
                                }
                            }
                            Err(place_error) => {
                                diagnostics
                                    .push(place_error.into_diagnostic(source, &name, place.root));
                            }
                        }
                    }
                }
            }
        }

        match &block.terminator {
            Terminator::Return(None) => {
                if function.return_type != Ty::Unit {
                    diagnostics.push(Diagnostic::error(
                        codes::RETURN_TYPE_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` returns no value from a block, but its declared return type is `{}`",
                            crate::types::display_ty(&function.return_type, interner)
                        ),
                    ));
                }
            }
            Terminator::Return(Some(v)) => {
                require_value(*v, diagnostics);
                if let Some(ty) = value_types.get(v)
                    && *ty != function.return_type
                {
                    diagnostics.push(Diagnostic::error(
                        codes::RETURN_TYPE_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` returns a value of type `{}`, but its declared return type is `{}`",
                            crate::types::display_ty(ty, interner),
                            crate::types::display_ty(&function.return_type, interner)
                        ),
                    ));
                }
            }
            Terminator::Branch(target) => {
                if !known_blocks.contains(target) {
                    diagnostics.push(Diagnostic::error(
                        codes::UNKNOWN_BRANCH_TARGET,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` branches to bb{}, which does not exist",
                            target.0
                        ),
                    ));
                }
            }
            Terminator::CondBranch {
                condition,
                then_block,
                else_block,
            } => {
                require_value(*condition, diagnostics);
                if let Some(ty) = value_types.get(condition)
                    && *ty != Ty::Bool
                {
                    diagnostics.push(Diagnostic::error(
                        codes::NON_BOOL_CONDITION,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` branches on a condition of type `{}`, which is not `bool`",
                            crate::types::display_ty(ty, interner)
                        ),
                    ));
                }
                for target in [then_block, else_block] {
                    if !known_blocks.contains(target) {
                        diagnostics.push(Diagnostic::error(
                            codes::UNKNOWN_BRANCH_TARGET,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}` branches to bb{}, which does not exist",
                                target.0
                            ),
                        ));
                    }
                }
            }
            Terminator::Switch {
                scrutinee,
                variant,
                cases,
            } => {
                require_value(*scrutinee, diagnostics);
                if let Some(ty) = value_types.get(scrutinee)
                    && !matches!(ty, Ty::Named(v, _) | Ty::Applied(v, _) if v == variant)
                {
                    diagnostics.push(Diagnostic::error(
                        codes::SWITCH_SCRUTINEE_TYPE_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` switches on a value of type `{}`, which is not the declared variant",
                            crate::types::display_ty(ty, interner)
                        ),
                    ));
                }
                let Some(layout) = agg.variants.get(variant) else {
                    diagnostics.push(Diagnostic::error(
                        codes::UNKNOWN_VARIANT_OR_CASE,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` switches on unknown variant id {}",
                            variant.0
                        ),
                    ));
                    continue;
                };
                if cases.len() != layout.cases.len() {
                    diagnostics.push(Diagnostic::error(
                        codes::SWITCH_CASE_COVERAGE,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` switches on `{}` with {} target(s), but it has {} case(s)",
                            registry.qualified_name(*variant, interner),
                            cases.len(),
                            layout.cases.len()
                        ),
                    ));
                }
                for target in cases {
                    if !known_blocks.contains(target) {
                        diagnostics.push(Diagnostic::error(
                            codes::UNKNOWN_BRANCH_TARGET,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}` switches to bb{}, which does not exist",
                                target.0
                            ),
                        ));
                    }
                }
            }
            Terminator::Invoke {
                callee,
                type_args,
                args,
                evidence,
                ok_slot,
                ok_target,
                err_targets,
            } => {
                for arg in args {
                    require_value(*arg, diagnostics);
                }
                // Every check in this block is about this `Invoke`'s own
                // structure -- its argument values, its slots, its branch
                // targets -- and never depends on the callee's own
                // registered signature. An unknown callee must not short-
                // circuit any of it: only the signature-dependent checks
                // further down (type/arity/evidence matching, and the
                // `raises`-coverage comparison, which genuinely cannot be
                // performed without a signature to compare against) are
                // skipped when the callee itself is unresolvable.
                if !alloc_slots.contains(ok_slot) {
                    diagnostics.push(Diagnostic::error(
                        codes::INVOKE_SUCCESS_SLOT_UNALLOCATED,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` invoke's success slot %{} was never allocated with `alloc`",
                            ok_slot.0
                        ),
                    ));
                }
                if !known_blocks.contains(ok_target) {
                    diagnostics.push(Diagnostic::error(
                        codes::UNKNOWN_BRANCH_TARGET,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` invokes to bb{}, which does not exist",
                            ok_target.0
                        ),
                    ));
                }
                let mut target_variants: HashSet<ItemId> = HashSet::new();
                let mut has_duplicate_target = false;
                for target in err_targets {
                    if !target_variants.insert(target.variant) {
                        has_duplicate_target = true;
                    }
                    match agg.variants.get(&target.variant) {
                        None => diagnostics.push(Diagnostic::error(
                            codes::UNKNOWN_VARIANT_OR_CASE,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}` invoke's failure target names unknown variant id {}",
                                target.variant.0
                            ),
                        )),
                        Some(layout) => {
                            if !alloc_slots.contains(&target.slot) {
                                diagnostics.push(Diagnostic::error(
                                    codes::INVOKE_FAILURE_SLOT_UNALLOCATED,
                                    source,
                                    Span::dummy(),
                                    format!(
                                        "function `{name}` invoke's failure slot %{} was never allocated with `alloc`",
                                        target.slot.0
                                    ),
                                ));
                            } else if let Some(slot_ty) = value_types.get(&target.slot)
                                && *slot_ty != Ty::Named(target.variant, layout.name)
                            {
                                diagnostics.push(Diagnostic::error(
                                    codes::INVOKE_FAILURE_TYPE_MISMATCH,
                                    source,
                                    Span::dummy(),
                                    format!(
                                        "function `{name}` invoke's failure slot %{} is declared `{}`, but its own failure target names `{}`",
                                        target.slot.0,
                                        crate::types::display_ty(slot_ty, interner),
                                        registry.qualified_name(target.variant, interner)
                                    ),
                                ));
                            }
                        }
                    }
                    if !known_blocks.contains(&target.target) {
                        diagnostics.push(Diagnostic::error(
                            codes::UNKNOWN_BRANCH_TARGET,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{name}` invokes to bb{}, which does not exist",
                                target.target.0
                            ),
                        ));
                    }
                }
                let Some(sig) = known_functions.get(callee) else {
                    diagnostics.push(Diagnostic::error(
                        codes::UNKNOWN_FUNCTION_REF,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` invokes a function with id {}, which does not exist in this module",
                            callee.0
                        ),
                    ));
                    continue;
                };
                if sig.raises.is_empty() {
                    diagnostics.push(Diagnostic::error(
                        codes::INVOKE_OF_INFALLIBLE_FUNCTION,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` invokes `{}`, which declares no `raises` and can never actually fail -- use `call` instead",
                            registry.qualified_name(*callee, interner)
                        ),
                    ));
                }
                let invoke_context = format!("function `{name}`'s invoke type argument");
                for t in type_args {
                    check_type_root(
                        t,
                        agg,
                        &own_params,
                        source,
                        interner,
                        registry,
                        &invoke_context,
                        diagnostics,
                    );
                }
                let arity_matches = type_args.len() == sig.type_params.len();
                let subst: HashMap<TypeParamId, Ty> = if arity_matches {
                    sig.type_params
                        .iter()
                        .copied()
                        .zip(type_args.iter().cloned())
                        .collect()
                } else {
                    diagnostics.push(Diagnostic::error(
                        codes::GENERIC_ARITY_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` invokes a function declaring {} type parameter(s) with {} type argument(s)",
                            sig.type_params.len(),
                            type_args.len()
                        ),
                    ));
                    HashMap::new()
                };
                let (return_ty, param_tys): (Ty, Vec<Ty>) = if arity_matches {
                    (
                        substitute(&sig.return_type, &subst),
                        sig.params.iter().map(|p| substitute(p, &subst)).collect(),
                    )
                } else {
                    (sig.return_type.clone(), sig.params.clone())
                };
                if arity_matches {
                    let evidence_context = format!("function `{name}`'s invoke evidence");
                    if evidence.len() != sig.requirements.len() {
                        diagnostics.push(Diagnostic::error(
                            codes::EVIDENCE_COUNT_MISMATCH,
                            source,
                            Span::dummy(),
                            format!(
                                "{evidence_context} carries {} entry(ies), but the callee declares {} capability requirement(s)",
                                evidence.len(),
                                sig.requirements.len()
                            ),
                        ));
                    } else {
                        for (entry, requirement) in evidence.iter().zip(sig.requirements.iter()) {
                            let required_arguments: Vec<Ty> = requirement
                                .arguments
                                .iter()
                                .map(|t| substitute(t, &subst))
                                .collect();
                            let mut budget = MAX_CAPABILITY_RESOLUTION_STEPS;
                            if let Err(problem) = check_evidence(
                                entry,
                                requirement.protocol,
                                &required_arguments,
                                true,
                                &function.requirements,
                                agg,
                                0,
                                &mut budget,
                            ) {
                                diagnostics.push(Diagnostic::error(
                                    problem.code(),
                                    source,
                                    Span::dummy(),
                                    format!("{evidence_context} {}", problem.describe()),
                                ));
                            }
                        }
                    }
                }
                if param_tys.len() != args.len() {
                    diagnostics.push(Diagnostic::error(
                        codes::ARITY_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` invokes a function expecting {} argument(s) with {}",
                            param_tys.len(),
                            args.len()
                        ),
                    ));
                } else {
                    for (param_ty, arg) in param_tys.iter().zip(args.iter()) {
                        if let Some(arg_ty) = value_types.get(arg)
                            && *arg_ty != *param_ty
                        {
                            diagnostics.push(Diagnostic::error(
                                codes::OPERAND_TYPE_MISMATCH,
                                source,
                                Span::dummy(),
                                format!(
                                    "function `{name}` invokes a function passing an argument of type `{}` where `{}` was expected",
                                    crate::types::display_ty(arg_ty, interner),
                                    crate::types::display_ty(param_ty, interner)
                                ),
                            ));
                        }
                    }
                }
                // The allocation checks for `ok_slot`/each err target's
                // slot, and the branch-target validity checks, already
                // ran above (callee-independent); only the type match
                // against the callee's own resolved return type, and the
                // coverage comparison against its own resolved `raises`
                // set, need the signature and belong here.
                if alloc_slots.contains(ok_slot)
                    && let Some(slot_ty) = value_types.get(ok_slot)
                    && *slot_ty != return_ty
                {
                    diagnostics.push(Diagnostic::error(
                        codes::INVOKE_SUCCESS_TYPE_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` invoke's success slot %{} is declared `{}`, but the callee returns `{}`",
                            ok_slot.0,
                            crate::types::display_ty(slot_ty, interner),
                            crate::types::display_ty(&return_ty, interner)
                        ),
                    ));
                }
                let raises_set: HashSet<ItemId> = sig.raises.iter().copied().collect();
                if has_duplicate_target || target_variants != raises_set {
                    diagnostics.push(Diagnostic::error(
                        codes::INVOKE_ERR_TARGET_COVERAGE_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` invoke's failure targets do not cover exactly the callee's declared `raises` set, with no duplicates"
                        ),
                    ));
                }
            }
            Terminator::Raise { value } => {
                require_value(*value, diagnostics);
                let declared_variant = value_types.get(value).and_then(|ty| match ty {
                    Ty::Named(v, _) => Some(*v),
                    _ => None,
                });
                if !declared_variant.is_some_and(|v| function.raises.contains(&v)) {
                    diagnostics.push(Diagnostic::error(
                        codes::UNDECLARED_RAISE,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{name}` raises a value not in its own declared `raises` set"
                        ),
                    ));
                }
            }
        }
    }

    verify_payload_refinement(function, agg, source, &name, diagnostics);
    verify_invoke_slot_initialization(function, source, &name, diagnostics);
    verify_drop_state(function, source, &name, diagnostics);
    verify_resource_ownership(
        function,
        &value_types,
        known_functions,
        agg,
        source,
        &name,
        diagnostics,
    );
    verify_structural_places(
        function,
        &value_types,
        known_functions,
        agg,
        source,
        &name,
        diagnostics,
    );
    verify_dominance(function, &param_values, source, &name, diagnostics);
}

/// A value used anywhere in `function` must be either a parameter, or
/// an instruction result whose defining block *dominates* the block of
/// the use (every control-flow path from the entry block to the use
/// passes through the definition first) -- and if the definition is in
/// the very same block as the use, it must come strictly earlier in
/// that block's instruction list. This is what actually backs up
/// "every value used exists" with "and was actually produced on every
/// path that could reach this use", which a plain existence check
/// (`require_value`) cannot tell apart from a value that only happens
/// to exist somewhere else in the function, e.g. in a sibling `if`
/// branch that never ran.
fn verify_dominance(
    function: &Function,
    param_values: &HashSet<ValueId>,
    source: SourceId,
    name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // (block, index within that block's instruction list) of each
    // value's *first* definition. A duplicate definition is already
    // reported on its own (V0016); picking one arbitrarily here just
    // keeps this pass from also cascading into confusing double
    // reports about the same underlying problem.
    let mut def_site: HashMap<ValueId, (BlockId, usize)> = HashMap::new();
    for block in &function.blocks {
        for (idx, instruction) in block.instructions.iter().enumerate() {
            if let Instruction::Value { result, .. } = instruction {
                def_site.entry(*result).or_insert((block.id, idx));
            }
        }
    }

    let dom = compute_dominators(function);

    let check_use = |v: ValueId,
                     current_block: BlockId,
                     current_idx: usize,
                     diagnostics: &mut Vec<Diagnostic>| {
        if param_values.contains(&v) {
            // Parameters are defined at function entry and dominate
            // every reachable block.
            return;
        }
        let Some(&(def_block, def_idx)) = def_site.get(&v) else {
            // Not defined anywhere at all -- already reported as
            // V0006 by the existence check elsewhere; nothing further
            // to say about its dominance.
            return;
        };
        if def_block == current_block {
            if def_idx >= current_idx {
                diagnostics.push(Diagnostic::error(
                    codes::USE_BEFORE_DEFINITION,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{name}` uses %{} in bb{} before it is defined later in the same block",
                        v.0, current_block.0
                    ),
                ));
            }
            return;
        }
        let dominates = dom
            .get(&current_block)
            .is_some_and(|d| d.contains(&def_block));
        if !dominates {
            diagnostics.push(Diagnostic::error(
                codes::NON_DOMINATING_DEFINITION,
                source,
                Span::dummy(),
                format!(
                    "function `{name}` uses %{} in bb{}, but its definition in bb{} does not dominate that use (some path reaches bb{} without ever defining %{})",
                    v.0, current_block.0, def_block.0, current_block.0, v.0
                ),
            ));
        }
    };

    for block in &function.blocks {
        for (idx, instruction) in block.instructions.iter().enumerate() {
            match instruction {
                Instruction::Value { kind, .. } => {
                    for operand in operands_of(kind) {
                        check_use(operand, block.id, idx, diagnostics);
                    }
                }
                Instruction::Store { slot, value, .. } => {
                    check_use(*slot, block.id, idx, diagnostics);
                    check_use(*value, block.id, idx, diagnostics);
                }
                Instruction::Drop { value } => {
                    check_use(*value, block.id, idx, diagnostics);
                }
                Instruction::DecomposeVariant { value, taken, .. } => {
                    check_use(*value, block.id, idx, diagnostics);
                    for (_, owner) in taken {
                        check_use(*owner, block.id, idx, diagnostics);
                    }
                }
                Instruction::StorePlace { place, value } => {
                    check_use(place.root, block.id, idx, diagnostics);
                    check_use(*value, block.id, idx, diagnostics);
                }
            }
        }
        // Terminator operands are treated as occurring after every
        // instruction in the block: any same-block definition, at any
        // instruction index, dominates the terminator that ends it.
        let after_all = block.instructions.len();
        match &block.terminator {
            Terminator::Return(Some(v)) => check_use(*v, block.id, after_all, diagnostics),
            Terminator::CondBranch { condition, .. } => {
                check_use(*condition, block.id, after_all, diagnostics);
            }
            Terminator::Switch { scrutinee, .. } => {
                check_use(*scrutinee, block.id, after_all, diagnostics);
            }
            Terminator::Invoke {
                args,
                ok_slot,
                err_targets,
                ..
            } => {
                for arg in args {
                    check_use(*arg, block.id, after_all, diagnostics);
                }
                // `ok_slot`/each failure target's `slot` are write
                // destinations, exactly like `Instruction::Store`'s own
                // `slot` -- the `alloc` that defined it must dominate
                // this `Invoke`, or some path could reach it without
                // ever allocating the slot it writes into.
                check_use(*ok_slot, block.id, after_all, diagnostics);
                for target in err_targets {
                    check_use(target.slot, block.id, after_all, diagnostics);
                }
            }
            Terminator::Raise { value } => {
                check_use(*value, block.id, after_all, diagnostics);
            }
            Terminator::Return(None) | Terminator::Branch(_) => {}
        }
    }
}

/// Every `ValueId` a `ValueKind` reads as an operand (not the value it
/// itself produces).
fn operands_of(kind: &ValueKind) -> Vec<ValueId> {
    match kind {
        ValueKind::Alloc | ValueKind::Const(_) => Vec::new(),
        ValueKind::Load(slot) => vec![*slot],
        ValueKind::Neg(a) | ValueKind::Not(a) => vec![*a],
        ValueKind::Add(a, b)
        | ValueKind::Sub(a, b)
        | ValueKind::Mul(a, b)
        | ValueKind::Div(a, b)
        | ValueKind::Rem(a, b)
        | ValueKind::And(a, b)
        | ValueKind::Or(a, b)
        | ValueKind::Xor(a, b)
        | ValueKind::Shl(a, b)
        | ValueKind::Shr(a, b)
        | ValueKind::Eq(a, b)
        | ValueKind::Ne(a, b)
        | ValueKind::Lt(a, b)
        | ValueKind::Le(a, b)
        | ValueKind::Gt(a, b)
        | ValueKind::Ge(a, b) => vec![*a, *b],
        ValueKind::Call(_, _, args, _) => args.clone(),
        ValueKind::RecordCreate(_, _, fields) => fields.clone(),
        ValueKind::RecordField { base, .. } => vec![*base],
        ValueKind::VariantCreate { payload, .. } => payload.clone(),
        ValueKind::VariantPayload { base, .. } => vec![*base],
        ValueKind::ProtocolCall { args, .. } => args.clone(),
        ValueKind::Move { source } | ValueKind::DeferCapture { source } => vec![*source],
        ValueKind::PlaceRead { place, .. } => vec![place.root],
    }
}

/// Computes, for every block in `function`, the set of blocks that
/// dominate it (including itself) -- the standard iterative
/// meet-over-predecessors fixpoint, restricted to blocks actually
/// reachable from the entry block (`BlockId(0)`).
///
/// A block never reached from the entry is deliberately *not* folded
/// into that fixpoint: a cycle purely among unreachable blocks (e.g. a
/// dead merge block that branches to itself) would otherwise never
/// converge below its pessimistic initial value using plain
/// intersection, which would let it dominate -- and therefore
/// silently accept -- a reference to literally anything else in the
/// function. An unreachable block is instead defined to be dominated
/// only by itself, so any operand it uses that isn't its own local
/// definition is correctly flagged as non-dominating.
fn compute_dominators(function: &Function) -> HashMap<BlockId, HashSet<BlockId>> {
    let entry = BlockId(0);
    let all_ids: HashSet<BlockId> = function.blocks.iter().map(|b| b.id).collect();
    if !all_ids.contains(&entry) {
        // Already reported as V0015; there is no meaningful entry to
        // compute dominance from.
        return HashMap::new();
    }

    let block_by_id: HashMap<BlockId, &BasicBlock> =
        function.blocks.iter().map(|b| (b.id, b)).collect();
    let successors = |id: BlockId| -> Vec<BlockId> {
        match &block_by_id[&id].terminator {
            Terminator::Return(_) => Vec::new(),
            Terminator::Branch(target) => vec![*target],
            Terminator::CondBranch {
                then_block,
                else_block,
                ..
            } => vec![*then_block, *else_block],
            Terminator::Switch { cases, .. } => cases.clone(),
            Terminator::Invoke {
                ok_target,
                err_targets,
                ..
            } => {
                let mut targets = vec![*ok_target];
                targets.extend(err_targets.iter().map(|t| t.target));
                targets
            }
            Terminator::Raise { .. } => Vec::new(),
        }
    };

    let mut reachable: HashSet<BlockId> = HashSet::from([entry]);
    let mut worklist = vec![entry];
    while let Some(id) = worklist.pop() {
        for succ in successors(id) {
            if all_ids.contains(&succ) && reachable.insert(succ) {
                worklist.push(succ);
            }
        }
    }

    let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for &id in &reachable {
        for succ in successors(id) {
            if reachable.contains(&succ) {
                preds.entry(succ).or_default().push(id);
            }
        }
    }

    let mut dom: HashMap<BlockId, HashSet<BlockId>> = HashMap::new();
    for &id in &all_ids {
        if !reachable.contains(&id) {
            dom.insert(id, HashSet::from([id]));
        } else if id == entry {
            dom.insert(id, HashSet::from([entry]));
        } else {
            dom.insert(id, reachable.clone());
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for &id in &reachable {
            if id == entry {
                continue;
            }
            let no_preds = Vec::new();
            let ps = preds.get(&id).unwrap_or(&no_preds);
            // Every predecessor recorded above is reachable, and every
            // reachable block was given a `dom` entry above, so none of
            // these lookups can miss. They are written as lookups
            // rather than indexing anyway: nothing a malformed CFG can
            // express may reach a panic in this file.
            let mut new_dom = match ps.split_first() {
                None => HashSet::from([id]),
                Some((first, rest)) => {
                    let Some(mut acc) = dom.get(first).cloned() else {
                        continue;
                    };
                    for p in rest {
                        let Some(other) = dom.get(p) else {
                            continue;
                        };
                        acc = acc.intersection(other).copied().collect();
                    }
                    acc.insert(id);
                    acc
                }
            };
            let Some(existing) = dom.get_mut(&id) else {
                continue;
            };
            if new_dom != *existing {
                std::mem::swap(existing, &mut new_dom);
                changed = true;
            }
        }
    }
    dom
}

/// A type that can never legally appear in NIR the verifier accepts: an
/// unresolved type variable (typeck must have already resolved every
/// one before lowering ever saw this expression) or `Ty::Error` (a
/// well-typed program that reached lowering should never carry one).
/// A declaration's own `type_params` list must never repeat the same
/// `TypeParamId` -- a duplicate would make positional substitution
/// ambiguous about which call-site argument binds which occurrence, and
/// silently collapsing it into a `HashMap`/`HashSet` (as every
/// substitution site here does) would otherwise just drop one binding
/// with no diagnostic at all.
fn check_no_duplicate_type_params(
    type_params: &[(TypeParamId, Symbol)],
    source: SourceId,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut seen: HashSet<TypeParamId> = HashSet::new();
    for (id, _) in type_params {
        if !seen.insert(*id) {
            diagnostics.push(Diagnostic::error(
                codes::DUPLICATE_TYPE_PARAMETER,
                source,
                Span::dummy(),
                format!("{context} declares the same type parameter more than once"),
            ));
        }
    }
}

fn check_no_bad_type(ty: &Ty, source: SourceId, context: &str, diagnostics: &mut Vec<Diagnostic>) {
    check_no_bad_type_at_depth(ty, source, context, diagnostics, 0);
}

/// `depth`-bounded the same way every other stage that walks a nested
/// type application is (`crate::limits::MAX_GENERIC_DEPTH`). Recurses
/// into `Ty::Applied`'s own argument list -- an unresolved `Ty::Var` or
/// `Ty::Error` buried *inside* a generic argument (`Box[Ty::Error]`)
/// must be rejected exactly as surely as one at the top level, never
/// silently passed through because only the outer `Ty::Applied` was
/// ever inspected (`rfcs/0008`).
fn check_no_bad_type_at_depth(
    ty: &Ty,
    source: SourceId,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
    depth: usize,
) {
    if depth > MAX_GENERIC_DEPTH {
        return;
    }
    match ty {
        Ty::Var(_) => diagnostics.push(Diagnostic::error(
            codes::UNRESOLVED_TYPE_VARIABLE,
            source,
            Span::dummy(),
            format!(
                "{context} contains an unresolved type variable; typeck must fully resolve \
                 every type before lowering"
            ),
        )),
        Ty::Error => diagnostics.push(Diagnostic::error(
            codes::UNEXPECTED_ERROR_TYPE,
            source,
            Span::dummy(),
            format!(
                "{context} contains an error type in executable NIR; an ill-typed program \
                 should never reach lowering"
            ),
        )),
        Ty::Applied(_, args) => {
            for arg in args {
                check_no_bad_type_at_depth(arg, source, context, diagnostics, depth + 1);
            }
        }
        _ => {}
    }
}

/// Checks that a `Ty::Named` refers to an actually-declared record or
/// variant in this module, and that its carried display symbol matches
/// that declaration's own name. Nominal identity itself only ever
/// depends on the `ItemId` (see `Ty`'s hand-written `PartialEq`/`Hash`),
/// so neither check can change what a well-formed program does -- but
/// an unknown id is a dangling reference no valid lowering produces,
/// and a mismatched symbol means diagnostics/textual NIR referencing
/// this type would print the wrong name.
fn check_named_type_identity(
    ty: &Ty,
    agg: &AggregateContext,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    check_named_type_identity_at_depth(
        ty,
        agg,
        source,
        interner,
        registry,
        context,
        diagnostics,
        0,
    );
}

/// `depth` bounds recursion into nested `Ty::Applied` arguments the same
/// way every other stage that walks a type application does
/// (`crate::limits::MAX_GENERIC_DEPTH`) -- this verifier is a public
/// entry point a direct caller can invoke with hand-built NIR that
/// bypasses every earlier stage's own depth guard entirely, so it never
/// trusts them to have already bounded the input (`rfcs/0008`). Past the
/// bound, recursion simply stops rather than checking (or rejecting)
/// anything deeper -- a type that deep is already malformed by
/// construction and would have been rejected with its own diagnostic far
/// earlier in any lowering that did not itself bypass every guard.
#[allow(clippy::too_many_arguments)]
fn check_named_type_identity_at_depth(
    ty: &Ty,
    agg: &AggregateContext,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
    depth: usize,
) {
    if depth > MAX_GENERIC_DEPTH {
        return;
    }
    match ty {
        Ty::Named(item, symbol) => {
            let declared = agg
                .records
                .get(item)
                .map(|r| (r.name, r.type_params.len()))
                .or_else(|| {
                    agg.variants
                        .get(item)
                        .map(|v| (v.name, v.type_params.len()))
                });
            match declared {
                None => diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_NAMED_TYPE,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} names a type that matches no declared record or variant in this module"
                    ),
                )),
                Some((name, _)) if name != *symbol => diagnostics.push(Diagnostic::error(
                    codes::NAMED_TYPE_SYMBOL_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} names its type `{}`, but its declaration is actually named `{}`",
                        interner.resolve(*symbol),
                        registry.qualified_name(*item, interner)
                    ),
                )),
                Some((_, type_param_count)) if type_param_count > 0 => {
                    diagnostics.push(Diagnostic::error(
                        codes::UNAPPLIED_GENERIC_TYPE,
                        source,
                        Span::dummy(),
                        format!(
                            "{context} names `{}` without type arguments, but it declares {type_param_count} type parameter(s)",
                            registry.qualified_name(*item, interner)
                        ),
                    ))
                }
                Some(_) => {}
            }
        }
        Ty::Applied(item, args) => {
            let declared_param_count = agg
                .records
                .get(item)
                .map(|r| r.type_params.len())
                .or_else(|| agg.variants.get(item).map(|v| v.type_params.len()));
            match declared_param_count {
                None => diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_NAMED_TYPE,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} names a type that matches no declared record or variant in this module"
                    ),
                )),
                Some(count) if count != args.len() => diagnostics.push(Diagnostic::error(
                    codes::GENERIC_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} applies {} type argument(s) to `{}`, which declares {count}",
                        args.len(),
                        registry.qualified_name(*item, interner)
                    ),
                )),
                Some(0) => diagnostics.push(Diagnostic::error(
                    codes::GENERIC_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} applies type arguments to `{}`, which is not generic",
                        registry.qualified_name(*item, interner)
                    ),
                )),
                Some(_) => {}
            }
            for arg in args {
                check_named_type_identity_at_depth(
                    arg,
                    agg,
                    source,
                    interner,
                    registry,
                    context,
                    diagnostics,
                    depth + 1,
                );
            }
        }
        _ => {}
    }
}

/// A `Ty::Param` is only ever meaningful within the one generic
/// declaration that binds it (`rfcs/0008`) -- it must never appear as a
/// concrete type anywhere else (a non-generic function's own signature,
/// another declaration's field/payload types, a call's type arguments in
/// a context that doesn't itself declare that parameter). `own_params` is
/// the set of `TypeParamId`s the *current* declaration (function, record,
/// or variant) itself declares; any `Ty::Param` found outside that set has
/// escaped its owning declaration, which no valid lowering ever produces.
fn check_type_param_scope(
    ty: &Ty,
    own_params: &HashSet<TypeParamId>,
    source: SourceId,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    check_type_param_scope_at_depth(ty, own_params, source, context, diagnostics, 0);
}

/// `depth`-bounded the same way [`check_named_type_identity_at_depth`]
/// is, and for the same reason: this verifier must never trust a
/// hand-built `Ty::Applied` to already be shallow.
fn check_type_param_scope_at_depth(
    ty: &Ty,
    own_params: &HashSet<TypeParamId>,
    source: SourceId,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
    depth: usize,
) {
    if depth > MAX_GENERIC_DEPTH {
        return;
    }
    match ty {
        Ty::Param(id, _) => {
            if !own_params.contains(id) {
                diagnostics.push(Diagnostic::error(
                    codes::ESCAPING_TYPE_PARAMETER,
                    source,
                    Span::dummy(),
                    format!(
                        "{context} uses a symbolic type parameter that does not belong to this declaration"
                    ),
                ));
            }
        }
        Ty::Applied(_, args) => {
            for arg in args {
                check_type_param_scope_at_depth(
                    arg,
                    own_params,
                    source,
                    context,
                    diagnostics,
                    depth + 1,
                );
            }
        }
        _ => {}
    }
}

/// Whether `ty`'s own nested `Ty::Applied` structure goes deeper than
/// `MAX_GENERIC_DEPTH` -- stops descending the instant the bound is
/// exceeded rather than computing the type's true depth beyond that
/// point, so *measuring* a pathologically deep hand-built type can never
/// itself overflow the native stack.
fn exceeds_generic_depth(ty: &Ty, depth: usize) -> bool {
    if depth > MAX_GENERIC_DEPTH {
        return true;
    }
    match ty {
        Ty::Applied(_, args) => args.iter().any(|a| exceeds_generic_depth(a, depth + 1)),
        _ => false,
    }
}

/// Collects every `TypeParamId` occurring anywhere inside `ty`, recursing
/// through `Ty::Applied`'s own argument list -- used to independently
/// re-derive whether an extend's own type parameter is actually
/// determined by its protocol head (`rfcs/0009`'s exact-forwarding-only
/// requirement; mirrors `typeck::capability`'s own
/// `collect_occurring_type_params`, since this verifier never trusts
/// hand-built NIR to already satisfy what `typeck` enforces for ordinary
/// source). Depth-bounded the same way every other stage that walks a
/// type application is.
fn collect_occurring_type_params(ty: &Ty, out: &mut HashSet<TypeParamId>, depth: usize) {
    if depth > MAX_GENERIC_DEPTH {
        return;
    }
    match ty {
        Ty::Param(id, _) => {
            out.insert(*id);
        }
        Ty::Applied(_, args) => {
            for arg in args {
                collect_occurring_type_params(arg, out, depth + 1);
            }
        }
        _ => {}
    }
}

/// Whether `ty` contains a symbolic `Ty::Param` anywhere, recursing
/// through `Ty::Applied` -- used to reject `Evidence::Extension` against
/// a still-symbolic required capability (`rfcs/0009`): Alpha 0.1.5
/// permits only an exact `Evidence::Forwarded` match once any part of
/// the required arguments is still symbolic, since a concrete extend's
/// own head can never be legitimately selected for a type that is not
/// yet concrete.
fn contains_symbolic_param(ty: &Ty, depth: usize) -> bool {
    if depth > MAX_GENERIC_DEPTH {
        return true;
    }
    match ty {
        Ty::Param(..) => true,
        Ty::Applied(_, args) => args.iter().any(|a| contains_symbolic_param(a, depth + 1)),
        _ => false,
    }
}

/// The single, shared check every type root `verify_module` inspects
/// goes through -- a record field, a variant case payload, a function
/// parameter or return type, an instruction's result type, or a
/// `Call`/`RecordCreate`/`VariantCreate` type argument. One place
/// validating everything any of these must satisfy, so no call site can
/// ever drift into checking a different subset of these, and no root is
/// ever checked by only some of them:
///
/// - not nested deeper than `MAX_GENERIC_DEPTH` (checked first, and
///   reported as its own dedicated diagnostic rather than the silent
///   early return every check below still falls back to past this same
///   bound as defense in depth -- a controlled single diagnostic for the
///   whole root, never one per nested level, and no further checks run
///   on a root already rejected this way);
/// - no `Ty::Error` or unresolved `Ty::Var`, however deeply nested
///   (`check_no_bad_type`);
/// - valid named/applied aggregate identity and correct nested generic
///   arity, including rejecting an unapplied reference to a generic
///   declaration (`check_named_type_identity`);
/// - no symbolic type parameter escaping the declaration that binds it
///   (`check_type_param_scope`).
///
/// This is the module's one authoritative type-integrity path: it never
/// trusts the parser, HIR, type checker, or lowering to have already
/// rejected an over-deep or otherwise malformed type, since every caller
/// here is a `verify_module` entry point that hand-built NIR can reach
/// directly, bypassing every earlier stage entirely (`rfcs/0008`).
#[allow(clippy::too_many_arguments)]
fn check_type_root(
    ty: &Ty,
    agg: &AggregateContext,
    own_params: &HashSet<TypeParamId>,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
    context: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if exceeds_generic_depth(ty, 0) {
        diagnostics.push(Diagnostic::error(
            codes::GENERIC_DEPTH_EXCEEDED,
            source,
            Span::dummy(),
            format!(
                "{context} is nested deeper than the maximum generic depth of {MAX_GENERIC_DEPTH}"
            ),
        ));
        return;
    }
    check_no_bad_type(ty, source, context, diagnostics);
    check_named_type_identity(ty, agg, source, interner, registry, context, diagnostics);
    check_type_param_scope(ty, own_params, source, context, diagnostics);
}

/// Every distinct way one [`Evidence`] node can fail to actually satisfy
/// the capability required of it (`rfcs/0009`) -- kept out of
/// `check_evidence`'s own recursion as plain data, rather than pushed as
/// a [`Diagnostic`] the instant it's found, so a nested failure produces
/// exactly one diagnostic at the call site that owns the whole evidence
/// tree, never one per nested level (`Diagnostic::error` is only ever
/// constructed once, by `check_evidence`'s caller, from whichever
/// variant this recursion bottoms out at).
#[derive(Debug)]
enum EvidenceProblem {
    DepthExceeded,
    WorkBudgetExceeded,
    ForwardedNotAllowedHere,
    ForwardedIndexOutOfRange,
    ForwardedRequirementMismatch,
    UnknownExtension(ItemId),
    ExtensionProtocolMismatch,
    ExtensionHeadMismatch,
    NestedEvidenceCountMismatch { expected: usize, found: usize },
    ExtensionForSymbolicRequirement,
}

impl EvidenceProblem {
    fn code(&self) -> &'static str {
        match self {
            EvidenceProblem::DepthExceeded => codes::EVIDENCE_DEPTH_EXCEEDED,
            EvidenceProblem::WorkBudgetExceeded => codes::EVIDENCE_WORK_BUDGET_EXCEEDED,
            EvidenceProblem::ForwardedNotAllowedHere => codes::FORWARDED_INSIDE_NESTED_EVIDENCE,
            EvidenceProblem::ForwardedIndexOutOfRange => codes::FORWARDED_INDEX_OUT_OF_RANGE,
            EvidenceProblem::ForwardedRequirementMismatch => codes::FORWARDED_REQUIREMENT_MISMATCH,
            EvidenceProblem::UnknownExtension(_) => codes::UNKNOWN_EXTENSION_REFERENCE,
            EvidenceProblem::ExtensionProtocolMismatch => codes::EXTENSION_PROTOCOL_MISMATCH,
            EvidenceProblem::ExtensionHeadMismatch => codes::EXTENSION_HEAD_MISMATCH,
            EvidenceProblem::NestedEvidenceCountMismatch { .. } => {
                codes::NESTED_EVIDENCE_COUNT_MISMATCH
            }
            EvidenceProblem::ExtensionForSymbolicRequirement => {
                codes::EXTENSION_FOR_SYMBOLIC_REQUIREMENT
            }
        }
    }

    fn describe(&self) -> String {
        match self {
            EvidenceProblem::DepthExceeded => format!(
                "is nested deeper than the maximum capability depth of {MAX_CAPABILITY_DEPTH}"
            ),
            EvidenceProblem::WorkBudgetExceeded => {
                "is too large to validate exhaustively".to_string()
            }
            EvidenceProblem::ForwardedNotAllowedHere => {
                "forwards capability evidence from inside another extension's own nested \
                 evidence, where only a concrete extension is ever legal"
                    .to_string()
            }
            EvidenceProblem::ForwardedIndexOutOfRange => {
                "forwards a capability evidence index that is out of range for the \
                 enclosing function's own requirements"
                    .to_string()
            }
            EvidenceProblem::ForwardedRequirementMismatch => {
                "forwards a capability requirement that is not exactly the capability \
                 actually required at this call site"
                    .to_string()
            }
            EvidenceProblem::UnknownExtension(id) => format!(
                "references extend id {}, which does not exist in this module",
                id.0
            ),
            EvidenceProblem::ExtensionProtocolMismatch => {
                "selects an extension for a different protocol than the one actually \
                 required at this call site"
                    .to_string()
            }
            EvidenceProblem::ExtensionHeadMismatch => {
                "selects an extension whose own head cannot structurally match the \
                 arguments actually required at this call site"
                    .to_string()
            }
            EvidenceProblem::NestedEvidenceCountMismatch { expected, found } => format!(
                "selects an extension carrying {found} nested evidence entries, but its own \
                 extend declares {expected} requirement(s)"
            ),
            EvidenceProblem::ExtensionForSymbolicRequirement => {
                "selects a concrete extension for a requirement that is still symbolic; only \
                 an exact Forwarded match is legal until every argument is concrete"
                    .to_string()
            }
        }
    }
}

/// One-directional structural match of an extend's own head
/// (`protocol_arguments`, which may reference the extend's own type
/// parameters) against the concrete/opaque arguments actually required
/// at a call site (which never contain any of the extend's own type
/// parameters, so they are never themselves bound -- only ever compared
/// against). The first occurrence of a free extend type parameter binds
/// it to whatever `target` subtree sits in that position; every later
/// occurrence of the same parameter must match the exact same bound
/// type. This is deliberately not the two-sided overlap unifier
/// (`heads_can_overlap` in `typeck::capability`): only one side ever
/// carries free variables here, so no occurs check or substitution
/// chasing is needed, only a depth bound against a hostile hand-built
/// type on either side.
fn match_extend_head(
    subst: &mut HashMap<TypeParamId, Ty>,
    free: &HashSet<TypeParamId>,
    pattern: &Ty,
    target: &Ty,
    depth: usize,
) -> bool {
    if depth > MAX_GENERIC_DEPTH {
        return false;
    }
    match pattern {
        Ty::Param(id, _) if free.contains(id) => match subst.get(id) {
            Some(bound) => bound == target,
            None => {
                subst.insert(*id, target.clone());
                true
            }
        },
        Ty::Applied(item, args) => match target {
            Ty::Applied(target_item, target_args)
                if item == target_item && args.len() == target_args.len() =>
            {
                args.iter()
                    .zip(target_args.iter())
                    .all(|(a, t)| match_extend_head(subst, free, a, t, depth + 1))
            }
            _ => false,
        },
        other => other == target,
    }
}

/// Checks one [`Evidence`] node (and, for an [`Evidence::Extension`],
/// everything nested inside it) against the exact capability required of
/// it at this position (`rfcs/0009`): a `protocol` identity plus already-
/// substituted `arguments`. `allow_forwarded` is `false` for anything
/// reached through an extension's own `nested` list -- by the time a
/// concrete extend is selected, every type it was selected for is
/// already fully concrete, so every leaf of `nested` is itself always
/// `Extension`, never `Forwarded` (see [`Evidence::Extension`]'s own doc
/// comment); it is `true` only at the outermost position a `Call`/
/// `protocol.call` instruction's own evidence list ever occupies, where
/// forwarding the *currently executing* function's own requirement
/// through unchanged is exactly what generic capability forwarding is.
/// `caller_requirements` is that enclosing function's own `requirements`,
/// against which a `Forwarded` index and its exact compatibility are
/// checked. `budget` is a shared work counter (not just a depth bound):
/// a hand-built evidence tree that stays shallow but branches wide enough
/// at every level could otherwise make exhaustive validation itself
/// pathologically expensive, even though no *cycle* is possible (this is
/// an owned tree, never a graph).
#[allow(clippy::too_many_arguments)]
fn check_evidence(
    evidence: &Evidence,
    required_protocol: ItemId,
    required_arguments: &[Ty],
    allow_forwarded: bool,
    caller_requirements: &[CapabilityRequirement],
    agg: &AggregateContext,
    depth: usize,
    budget: &mut usize,
) -> Result<(), EvidenceProblem> {
    if depth > MAX_CAPABILITY_DEPTH {
        return Err(EvidenceProblem::DepthExceeded);
    }
    if *budget == 0 {
        return Err(EvidenceProblem::WorkBudgetExceeded);
    }
    *budget -= 1;

    match evidence {
        Evidence::Forwarded(index) => {
            if !allow_forwarded {
                return Err(EvidenceProblem::ForwardedNotAllowedHere);
            }
            let Some(forwarded) = caller_requirements.get(*index) else {
                return Err(EvidenceProblem::ForwardedIndexOutOfRange);
            };
            if forwarded.protocol != required_protocol || forwarded.arguments != required_arguments
            {
                return Err(EvidenceProblem::ForwardedRequirementMismatch);
            }
            Ok(())
        }
        Evidence::Extension { extend, nested } => {
            // Exact-forwarding-only symbolic semantics (`rfcs/0009`): a
            // concrete extend can only ever have been legitimately
            // selected once every part of the required capability is
            // itself concrete -- a still-symbolic requirement can only
            // resolve by forwarding an identical caller requirement
            // unchanged, checked above. This must be checked before any
            // other `Extension` check below, since a symbolic argument
            // could otherwise coincidentally structurally "match" a
            // hand-built extend head sharing the same raw `TypeParamId`.
            if required_arguments
                .iter()
                .any(|t| contains_symbolic_param(t, 0))
            {
                return Err(EvidenceProblem::ExtensionForSymbolicRequirement);
            }
            let Some(layout) = agg.extends.get(extend) else {
                return Err(EvidenceProblem::UnknownExtension(*extend));
            };
            if layout.protocol != required_protocol {
                return Err(EvidenceProblem::ExtensionProtocolMismatch);
            }
            let free: HashSet<TypeParamId> = layout.type_params.iter().map(|(id, _)| *id).collect();
            let mut subst: HashMap<TypeParamId, Ty> = HashMap::new();
            let head_matches = layout.protocol_arguments.len() == required_arguments.len()
                && layout
                    .protocol_arguments
                    .iter()
                    .zip(required_arguments.iter())
                    .all(|(p, t)| match_extend_head(&mut subst, &free, p, t, 0));
            if !head_matches {
                return Err(EvidenceProblem::ExtensionHeadMismatch);
            }
            if nested.len() != layout.requirements.len() {
                return Err(EvidenceProblem::NestedEvidenceCountMismatch {
                    expected: layout.requirements.len(),
                    found: nested.len(),
                });
            }
            for (n, r) in nested.iter().zip(layout.requirements.iter()) {
                let sub_arguments: Vec<Ty> =
                    r.arguments.iter().map(|t| substitute(t, &subst)).collect();
                check_evidence(
                    n,
                    r.protocol,
                    &sub_arguments,
                    false,
                    caller_requirements,
                    agg,
                    depth + 1,
                    budget,
                )?;
            }
            Ok(())
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_value_kind(
    result: ValueId,
    result_ty: &Ty,
    kind: &ValueKind,
    value_types: &HashMap<ValueId, Ty>,
    alloc_slots: &HashSet<ValueId>,
    known_functions: &HashMap<ItemId, KnownFunction>,
    agg: &AggregateContext,
    own_params: &HashSet<TypeParamId>,
    own_requirements: &[CapabilityRequirement],
    source: SourceId,
    function_name: &str,
    interner: &Interner,
    registry: &ItemRegistry,
    diagnostics: &mut Vec<Diagnostic>,
    require_value: &mut impl FnMut(ValueId, &mut Vec<Diagnostic>),
) {
    let operand_mismatch = |diagnostics: &mut Vec<Diagnostic>, detail: String| {
        diagnostics.push(Diagnostic::error(
            codes::OPERAND_TYPE_MISMATCH,
            source,
            Span::dummy(),
            format!("function `{function_name}`: %{} {detail}", result.0),
        ));
    };

    let ty_of = |v: ValueId| value_types.get(&v).cloned();
    let ty_name = |ty: &Ty| crate::types::display_ty(ty, interner);

    match kind {
        ValueKind::Alloc => {}
        ValueKind::Const(c) => {
            let ok = match c {
                Const::Int(_) => is_integer(result_ty),
                Const::Float(_) => matches!(result_ty, Ty::F32 | Ty::F64),
                Const::Bool(_) => matches!(result_ty, Ty::Bool),
                Const::Char(_) => matches!(result_ty, Ty::Char),
                Const::Str(_) => matches!(result_ty, Ty::Str),
                Const::Unit => matches!(result_ty, Ty::Unit),
            };
            if !ok {
                operand_mismatch(
                    diagnostics,
                    format!("is a {c:?} constant declared with an incompatible type"),
                );
            }
        }
        ValueKind::Load(slot) => {
            require_value(*slot, diagnostics);
            if !alloc_slots.contains(slot) {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_SLOT,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}` loads from %{} which was never allocated with `alloc`",
                        slot.0
                    ),
                ));
            } else if let Some(slot_ty) = ty_of(*slot)
                && slot_ty != *result_ty
            {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "loads a slot declared `{}` but is itself declared `{}`",
                        ty_name(&slot_ty),
                        ty_name(result_ty)
                    ),
                );
            }
        }
        ValueKind::Add(a, b)
        | ValueKind::Sub(a, b)
        | ValueKind::Mul(a, b)
        | ValueKind::Div(a, b)
        | ValueKind::Rem(a, b) => {
            require_value(*a, diagnostics);
            require_value(*b, diagnostics);
            if !is_numeric(result_ty) {
                operand_mismatch(
                    diagnostics,
                    "is an arithmetic result but not numeric".into(),
                );
            }
            check_same_as_result(
                *a,
                *b,
                result_ty,
                value_types,
                &operand_mismatch,
                diagnostics,
            );
        }
        ValueKind::And(a, b) | ValueKind::Or(a, b) | ValueKind::Xor(a, b) => {
            require_value(*a, diagnostics);
            require_value(*b, diagnostics);
            if !is_integer(result_ty) {
                operand_mismatch(diagnostics, "is a bitwise result but not an integer".into());
            }
            check_same_as_result(
                *a,
                *b,
                result_ty,
                value_types,
                &operand_mismatch,
                diagnostics,
            );
        }
        ValueKind::Shl(a, b) | ValueKind::Shr(a, b) => {
            require_value(*a, diagnostics);
            require_value(*b, diagnostics);
            if !is_integer(result_ty) {
                operand_mismatch(diagnostics, "is a shift result but not an integer".into());
            }
            check_same_as_result(
                *a,
                *b,
                result_ty,
                value_types,
                &operand_mismatch,
                diagnostics,
            );
        }
        ValueKind::Neg(a) => {
            require_value(*a, diagnostics);
            if !is_numeric(result_ty) {
                operand_mismatch(diagnostics, "negates a value but is not numeric".into());
            }
            if let Some(ty) = ty_of(*a)
                && ty != *result_ty
            {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "negates an operand of type `{}` but is declared `{}`",
                        ty_name(&ty),
                        ty_name(result_ty)
                    ),
                );
            }
        }
        ValueKind::Not(a) => {
            require_value(*a, diagnostics);
            if !(is_integer(result_ty) || matches!(result_ty, Ty::Bool)) {
                operand_mismatch(
                    diagnostics,
                    "applies `not` but is neither an integer nor a bool".into(),
                );
            }
            if let Some(ty) = ty_of(*a)
                && ty != *result_ty
            {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "applies `not` to an operand of type `{}` but is declared `{}`",
                        ty_name(&ty),
                        ty_name(result_ty)
                    ),
                );
            }
        }
        ValueKind::Eq(a, b)
        | ValueKind::Ne(a, b)
        | ValueKind::Lt(a, b)
        | ValueKind::Le(a, b)
        | ValueKind::Gt(a, b)
        | ValueKind::Ge(a, b) => {
            require_value(*a, diagnostics);
            require_value(*b, diagnostics);
            if !matches!(result_ty, Ty::Bool) {
                operand_mismatch(
                    diagnostics,
                    "is a comparison but not declared `bool`".into(),
                );
            }
            if let (Some(at), Some(bt)) = (ty_of(*a), ty_of(*b))
                && at != bt
            {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "compares operands of different types `{}` and `{}`",
                        ty_name(&at),
                        ty_name(&bt)
                    ),
                );
            }
        }
        ValueKind::Call(callee, type_args, args, evidence) => {
            for arg in args {
                require_value(*arg, diagnostics);
            }
            let Some(sig) = known_functions.get(callee) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_FUNCTION_REF,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}` calls a function with id {}, which does not exist in this module",
                        callee.0
                    ),
                ));
                return;
            };
            if !sig.raises.is_empty() {
                diagnostics.push(Diagnostic::error(
                    codes::CALL_TO_FALLIBLE_FUNCTION,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} calls a fallible function through an ordinary `call`; only `invoke` may call a function declaring `raises`",
                        result.0
                    ),
                ));
            }
            let call_context = format!(
                "function `{function_name}`: %{}'s call type argument",
                result.0
            );
            for t in type_args {
                check_type_root(
                    t,
                    agg,
                    own_params,
                    source,
                    interner,
                    registry,
                    &call_context,
                    diagnostics,
                );
            }
            let arity_matches = type_args.len() == sig.type_params.len();
            let subst: HashMap<TypeParamId, Ty> = if arity_matches {
                sig.type_params
                    .iter()
                    .copied()
                    .zip(type_args.iter().cloned())
                    .collect()
            } else {
                diagnostics.push(Diagnostic::error(
                    codes::GENERIC_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} calls a function declaring {} type parameter(s) with {} type argument(s)",
                        result.0,
                        sig.type_params.len(),
                        type_args.len()
                    ),
                ));
                HashMap::new()
            };
            let (return_ty, param_tys): (Ty, Vec<Ty>) = if arity_matches {
                (
                    substitute(&sig.return_type, &subst),
                    sig.params.iter().map(|p| substitute(p, &subst)).collect(),
                )
            } else {
                (sig.return_type.clone(), sig.params.clone())
            };
            // Evidence is only checked once the call's own type
            // arguments are known-good: an already-reported arity
            // mismatch leaves `subst` empty, which would otherwise
            // cascade into spurious evidence diagnostics unrelated to
            // the actual problem.
            if arity_matches {
                let evidence_context =
                    format!("function `{function_name}`: %{}'s call evidence", result.0);
                if evidence.len() != sig.requirements.len() {
                    diagnostics.push(Diagnostic::error(
                        codes::EVIDENCE_COUNT_MISMATCH,
                        source,
                        Span::dummy(),
                        format!(
                            "{evidence_context} carries {} entry(ies), but the callee declares {} capability requirement(s)",
                            evidence.len(),
                            sig.requirements.len()
                        ),
                    ));
                } else {
                    for (entry, requirement) in evidence.iter().zip(sig.requirements.iter()) {
                        let required_arguments: Vec<Ty> = requirement
                            .arguments
                            .iter()
                            .map(|t| substitute(t, &subst))
                            .collect();
                        let mut budget = MAX_CAPABILITY_RESOLUTION_STEPS;
                        if let Err(problem) = check_evidence(
                            entry,
                            requirement.protocol,
                            &required_arguments,
                            true,
                            own_requirements,
                            agg,
                            0,
                            &mut budget,
                        ) {
                            diagnostics.push(Diagnostic::error(
                                problem.code(),
                                source,
                                Span::dummy(),
                                format!("{evidence_context} {}", problem.describe()),
                            ));
                        }
                    }
                }
            }
            if return_ty != *result_ty {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "calls a function returning `{}` but is itself declared `{}`",
                        ty_name(&return_ty),
                        ty_name(result_ty)
                    ),
                );
            }
            if param_tys.len() != args.len() {
                diagnostics.push(Diagnostic::error(
                    codes::ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}` calls a function expecting {} argument(s) with {}",
                        param_tys.len(),
                        args.len()
                    ),
                ));
            } else {
                for (param_ty, arg) in param_tys.iter().zip(args.iter()) {
                    if let Some(arg_ty) = ty_of(*arg)
                        && arg_ty != *param_ty
                    {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "passes an argument of type `{}` where `{}` was expected",
                                ty_name(&arg_ty),
                                ty_name(param_ty)
                            ),
                        );
                    }
                }
            }
        }
        ValueKind::RecordCreate(record, type_args, fields) => {
            for f in fields {
                require_value(*f, diagnostics);
            }
            let Some(layout) = agg.records.get(record) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_RECORD,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs unknown record id {}",
                        result.0, record.0
                    ),
                ));
                return;
            };
            let construct_context = format!(
                "function `{function_name}`: %{}'s record construction type argument",
                result.0
            );
            for t in type_args {
                check_type_root(
                    t,
                    agg,
                    own_params,
                    source,
                    interner,
                    registry,
                    &construct_context,
                    diagnostics,
                );
            }
            let arity_ok = type_args.len() == layout.type_params.len();
            if !arity_ok {
                diagnostics.push(Diagnostic::error(
                    codes::GENERIC_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs `{}` (declaring {} type parameter(s)) with {} type argument(s)",
                        result.0,
                        registry.qualified_name(*record, interner),
                        layout.type_params.len(),
                        type_args.len()
                    ),
                ));
            } else {
                let expected_ty = if type_args.is_empty() {
                    Ty::Named(*record, layout.name)
                } else {
                    Ty::Applied(*record, type_args.clone())
                };
                if *result_ty != expected_ty {
                    operand_mismatch(
                        diagnostics,
                        format!(
                            "constructs record `{}` but is declared `{}`",
                            registry.qualified_name(*record, interner),
                            ty_name(result_ty)
                        ),
                    );
                }
            }
            let subst: HashMap<TypeParamId, Ty> = if arity_ok {
                layout
                    .type_params
                    .iter()
                    .map(|(id, _)| *id)
                    .zip(type_args.iter().cloned())
                    .collect()
            } else {
                HashMap::new()
            };
            if fields.len() != layout.fields.len() {
                diagnostics.push(Diagnostic::error(
                    codes::RECORD_FIELDS_NOT_INITIALIZED_ONCE_EACH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs `{}` with {} field value(s), but it has {} field(s)",
                        result.0,
                        registry.qualified_name(*record, interner),
                        fields.len(),
                        layout.fields.len()
                    ),
                ));
            } else {
                for (i, (field_value, (_, declared_ty))) in
                    fields.iter().zip(layout.fields.iter()).enumerate()
                {
                    let expected = substitute(declared_ty, &subst);
                    if let Some(ty) = ty_of(*field_value)
                        && ty != expected
                    {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "field {i} has type `{}` but is declared `{}`",
                                ty_name(&ty),
                                ty_name(&expected)
                            ),
                        );
                    }
                }
            }
        }
        ValueKind::RecordField {
            base,
            record,
            field,
        } => {
            require_value(*base, diagnostics);
            let Some(layout) = agg.records.get(record) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_RECORD,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} projects a field of unknown record id {}",
                        result.0, record.0
                    ),
                ));
                return;
            };
            let base_ty = ty_of(*base);
            let base_args: Option<&[Ty]> = match &base_ty {
                Some(Ty::Named(r, _)) if r == record => Some(&[]),
                Some(Ty::Applied(r, args)) if r == record => Some(args.as_slice()),
                Some(other) => {
                    operand_mismatch(
                        diagnostics,
                        format!(
                            "projects a field of `{}` from a base of type `{}`",
                            registry.qualified_name(*record, interner),
                            ty_name(other)
                        ),
                    );
                    None
                }
                None => None,
            };
            let subst: HashMap<TypeParamId, Ty> = match base_args {
                Some(args) if args.len() == layout.type_params.len() => layout
                    .type_params
                    .iter()
                    .map(|(id, _)| *id)
                    .zip(args.iter().cloned())
                    .collect(),
                _ => HashMap::new(),
            };
            match layout.fields.get(*field) {
                Some((_, declared_ty)) => {
                    let expected = substitute(declared_ty, &subst);
                    if expected != *result_ty {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "projects field {field} of type `{}` but is declared `{}`",
                                ty_name(&expected),
                                ty_name(result_ty)
                            ),
                        );
                    }
                }
                None => diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_FIELD,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} projects field index {field} of `{}`, which has {} field(s)",
                        result.0,
                        registry.qualified_name(*record, interner),
                        layout.fields.len()
                    ),
                )),
            }
        }
        ValueKind::VariantCreate {
            variant,
            case,
            type_args,
            payload,
        } => {
            for p in payload {
                require_value(*p, diagnostics);
            }
            let Some(layout) = agg.variants.get(variant) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_VARIANT_OR_CASE,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs unknown variant id {}",
                        result.0, variant.0
                    ),
                ));
                return;
            };
            let construct_context = format!(
                "function `{function_name}`: %{}'s variant construction type argument",
                result.0
            );
            for t in type_args {
                check_type_root(
                    t,
                    agg,
                    own_params,
                    source,
                    interner,
                    registry,
                    &construct_context,
                    diagnostics,
                );
            }
            let arity_ok = type_args.len() == layout.type_params.len();
            if !arity_ok {
                diagnostics.push(Diagnostic::error(
                    codes::GENERIC_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs `{}` (declaring {} type parameter(s)) with {} type argument(s)",
                        result.0,
                        registry.qualified_name(*variant, interner),
                        layout.type_params.len(),
                        type_args.len()
                    ),
                ));
            } else {
                let expected_ty = if type_args.is_empty() {
                    Ty::Named(*variant, layout.name)
                } else {
                    Ty::Applied(*variant, type_args.clone())
                };
                if *result_ty != expected_ty {
                    operand_mismatch(
                        diagnostics,
                        format!(
                            "constructs variant `{}` but is declared `{}`",
                            registry.qualified_name(*variant, interner),
                            ty_name(result_ty)
                        ),
                    );
                }
            }
            let subst: HashMap<TypeParamId, Ty> = if arity_ok {
                layout
                    .type_params
                    .iter()
                    .map(|(id, _)| *id)
                    .zip(type_args.iter().cloned())
                    .collect()
            } else {
                HashMap::new()
            };
            let Some(case_layout) = layout.cases.get(*case) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_VARIANT_OR_CASE,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs unknown case index {case} of `{}`",
                        result.0,
                        registry.qualified_name(*variant, interner)
                    ),
                ));
                return;
            };
            if payload.len() != case_layout.payload.len() {
                diagnostics.push(Diagnostic::error(
                    codes::ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} constructs case `{}` with {} payload value(s), but it expects {}",
                        result.0,
                        interner.resolve(case_layout.name),
                        payload.len(),
                        case_layout.payload.len()
                    ),
                ));
            } else {
                for (i, (value, declared_ty)) in
                    payload.iter().zip(case_layout.payload.iter()).enumerate()
                {
                    let expected = substitute(declared_ty, &subst);
                    if let Some(ty) = ty_of(*value)
                        && ty != expected
                    {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "payload {i} has type `{}` but is declared `{}`",
                                ty_name(&ty),
                                ty_name(&expected)
                            ),
                        );
                    }
                }
            }
        }
        ValueKind::VariantPayload {
            base,
            variant,
            case,
            index,
        } => {
            require_value(*base, diagnostics);
            let Some(layout) = agg.variants.get(variant) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_VARIANT_OR_CASE,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} projects a payload of unknown variant id {}",
                        result.0, variant.0
                    ),
                ));
                return;
            };
            let base_ty = ty_of(*base);
            let base_args: Option<&[Ty]> = match &base_ty {
                Some(Ty::Named(v, _)) if v == variant => Some(&[]),
                Some(Ty::Applied(v, args)) if v == variant => Some(args.as_slice()),
                Some(other) => {
                    operand_mismatch(
                        diagnostics,
                        format!(
                            "projects a payload of `{}` from a base of type `{}`",
                            registry.qualified_name(*variant, interner),
                            ty_name(other)
                        ),
                    );
                    None
                }
                None => None,
            };
            let subst: HashMap<TypeParamId, Ty> = match base_args {
                Some(args) if args.len() == layout.type_params.len() => layout
                    .type_params
                    .iter()
                    .map(|(id, _)| *id)
                    .zip(args.iter().cloned())
                    .collect(),
                _ => HashMap::new(),
            };
            match layout.cases.get(*case).and_then(|c| c.payload.get(*index)) {
                Some(declared_ty) => {
                    let expected = substitute(declared_ty, &subst);
                    if expected != *result_ty {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "projects payload {index} of case {case} with type `{}` but is declared `{}`",
                                ty_name(&expected),
                                ty_name(result_ty)
                            ),
                        );
                    }
                }
                None => diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_VARIANT_OR_CASE,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} projects payload index {index} of case {case} of `{}`, which does not have it",
                        result.0,
                        registry.qualified_name(*variant, interner)
                    ),
                )),
            }
        }
        ValueKind::ProtocolCall {
            protocol,
            arguments,
            method,
            evidence,
            args,
        } => {
            for arg in args {
                require_value(*arg, diagnostics);
            }
            let call_context = format!(
                "function `{function_name}`: %{}'s protocol-call type argument",
                result.0
            );
            for t in arguments {
                check_type_root(
                    t,
                    agg,
                    own_params,
                    source,
                    interner,
                    registry,
                    &call_context,
                    diagnostics,
                );
            }
            let Some(layout) = agg.protocols.get(protocol) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_PROTOCOL_CALL_TARGET,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} calls a protocol with id {}, which does not exist in this module",
                        result.0, protocol.0
                    ),
                ));
                return;
            };
            if layout.type_params.len() != arguments.len() {
                diagnostics.push(Diagnostic::error(
                    codes::GENERIC_ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} supplies {} type argument(s) to `{}`, which declares {}",
                        result.0,
                        arguments.len(),
                        registry.qualified_name(*protocol, interner),
                        layout.type_params.len()
                    ),
                ));
                return;
            }
            let Some(method_layout) = layout.methods.get(*method) else {
                diagnostics.push(Diagnostic::error(
                    codes::UNKNOWN_PROTOCOL_CALL_TARGET,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} calls method index {method} of `{}`, which does not exist",
                        result.0,
                        registry.qualified_name(*protocol, interner)
                    ),
                ));
                return;
            };
            let subst: HashMap<TypeParamId, Ty> = layout
                .type_params
                .iter()
                .map(|(id, _)| *id)
                .zip(arguments.iter().cloned())
                .collect();
            let expected_params: Vec<Ty> = method_layout
                .params
                .iter()
                .map(|t| substitute(t, &subst))
                .collect();
            let expected_return = substitute(&method_layout.return_type, &subst);
            if expected_return != *result_ty {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "calls a protocol method returning `{}` but is itself declared `{}`",
                        ty_name(&expected_return),
                        ty_name(result_ty)
                    ),
                );
            }
            if expected_params.len() != args.len() {
                diagnostics.push(Diagnostic::error(
                    codes::ARITY_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}` calls a protocol method expecting {} argument(s) with {}",
                        expected_params.len(),
                        args.len()
                    ),
                ));
            } else {
                for (param_ty, arg) in expected_params.iter().zip(args.iter()) {
                    if let Some(arg_ty) = ty_of(*arg)
                        && arg_ty != *param_ty
                    {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "passes an argument of type `{}` where `{}` was expected",
                                ty_name(&arg_ty),
                                ty_name(param_ty)
                            ),
                        );
                    }
                }
            }
            let evidence_context = format!(
                "function `{function_name}`: %{}'s protocol-call evidence",
                result.0
            );
            let mut budget = MAX_CAPABILITY_RESOLUTION_STEPS;
            if let Err(problem) = check_evidence(
                evidence,
                *protocol,
                arguments,
                true,
                own_requirements,
                agg,
                0,
                &mut budget,
            ) {
                diagnostics.push(Diagnostic::error(
                    problem.code(),
                    source,
                    Span::dummy(),
                    format!("{evidence_context} {}", problem.describe()),
                ));
            }
        }
        ValueKind::Move { source: from } | ValueKind::DeferCapture { source: from } => {
            require_value(*from, diagnostics);
            if let Some(source_ty) = ty_of(*from)
                && source_ty != *result_ty
            {
                operand_mismatch(
                    diagnostics,
                    format!(
                        "transfers a value declared `{}` but is itself declared `{}`",
                        ty_name(&source_ty),
                        ty_name(result_ty)
                    ),
                );
            }
        }
        ValueKind::PlaceRead { place, .. } => {
            require_value(place.root, diagnostics);
            let Some(root_ty) = ty_of(place.root) else {
                return;
            };
            match resolve_place_ty(&root_ty, &place.projections, agg) {
                Ok(resolved_ty) => {
                    if resolved_ty != *result_ty {
                        operand_mismatch(
                            diagnostics,
                            format!(
                                "reads a place of type `{}` but is declared `{}`",
                                ty_name(&resolved_ty),
                                ty_name(result_ty)
                            ),
                        );
                    } else if !is_affine_in(&resolved_ty, agg) {
                        diagnostics.push(Diagnostic::error(
                            codes::MOVE_OF_NON_AFFINE_PLACE,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{function_name}`: %{} reads a place of non-affine type `{}`",
                                result.0,
                                ty_name(&resolved_ty)
                            ),
                        ));
                    }
                }
                Err(place_error) => {
                    diagnostics.push(place_error.into_diagnostic(source, function_name, result));
                }
            }
        }
    }
}

/// One malformed structural place, independent of which instruction
/// named it (`rfcs/0012`) -- `nir::verify`'s own reconstruction of the
/// exact same place validity `resourceck`/`nir::lower` already checked,
/// never trusted blindly for hand-built NIR that bypasses either.
enum PlaceError {
    UnknownFieldOwner(ItemId),
    ProjectionThroughNonRecord(Ty),
    UnknownField(ItemId, usize),
    /// `(owner, declared parameter count, supplied argument count)`.
    GenericArityMismatch(ItemId, usize, usize),
}

impl PlaceError {
    fn into_diagnostic(self, source: SourceId, function_name: &str, result: ValueId) -> Diagnostic {
        let (code, message) = match self {
            PlaceError::UnknownFieldOwner(owner) => (
                codes::INVALID_PLACE_FIELD_OWNER,
                format!(
                    "function `{function_name}`: %{} projects a field of unknown record id {}",
                    result.0, owner.0
                ),
            ),
            PlaceError::ProjectionThroughNonRecord(ty) => (
                codes::PLACE_PROJECTION_THROUGH_NON_RECORD,
                format!(
                    "function `{function_name}`: %{} projects a field through a non-record place of type `{ty:?}`",
                    result.0
                ),
            ),
            PlaceError::UnknownField(owner, field) => (
                codes::UNKNOWN_PLACE_FIELD,
                format!(
                    "function `{function_name}`: %{} projects field index {field} of record {}, which has no such field",
                    result.0, owner.0
                ),
            ),
            PlaceError::GenericArityMismatch(owner, declared, supplied) => (
                codes::PLACE_GENERIC_ARITY_MISMATCH,
                format!(
                    "function `{function_name}`: %{} projects through record {}, which declares \
                     {declared} type parameter(s) but is applied to {supplied} type argument(s)",
                    result.0, owner.0
                ),
            ),
        };
        Diagnostic::error(code, source, Span::dummy(), message)
    }
}

/// `true` iff `ty` is transitively affine (`rfcs/0012`) -- independently
/// recomputed from `agg`'s own declared record/variant layouts,
/// mirroring `resourceck`'s/`nir::lower`'s identical query, never
/// trusted from either. Guarded against a genuinely cyclic declaration
/// the same way every other stage's identical query is: a cycle
/// back-edge contributes `false` to that one occurrence alone, never
/// cached (this file's own resource checks are not called densely
/// enough per module to need memoizing).
fn is_affine_in(ty: &Ty, agg: &AggregateContext) -> bool {
    is_affine_in_visiting(ty, agg, &mut HashSet::new(), 0)
}

fn is_affine_in_visiting(
    ty: &Ty,
    agg: &AggregateContext,
    visiting: &mut HashSet<ItemId>,
    depth: usize,
) -> bool {
    // Bounds a genuinely cyclic declaration, which `typeck::cycles`
    // independently rejects as an infinite layout long before anything
    // reaches NIR -- and, for a `Ty::Applied`, is the *only* guard, see
    // below.
    if depth >= MAX_GENERIC_DEPTH {
        return false;
    }
    // A generic instantiation's own affinity is decided by what it was
    // instantiated *with* (`rfcs/0008`, `rfcs/0012`): `Box[File]` is
    // affine, `Box[i64]` is not, and the same declaration answers both
    // -- so its own arguments are substituted into the declaration's
    // field types before recursing. Answering `false` for every
    // `Ty::Applied` (as this once did) is what let a `Box[File]` reach
    // `Drop`/`PlaceRead` looking like an ordinary, freely-copyable
    // value.
    let (item, args): (&ItemId, &[Ty]) = match ty {
        Ty::Named(item, _) => (item, &[]),
        Ty::Applied(item, args) => (item, args.as_slice()),
        _ => return false,
    };
    if agg.records.get(item).is_some_and(|r| r.affine) {
        return true;
    }
    // `visiting` guards a *non-generic* cycle only. It is keyed by bare
    // `ItemId`, so it cannot tell a genuine cycle apart from a
    // legitimately nested instantiation of the same declaration --
    // `Box[Box[Box[File]]]` reaches `Box` three times with different
    // arguments and must answer from the innermost one. For an
    // instantiation, `depth` above is the termination guard, matching
    // `typeck::Checker::is_affine`.
    let generic = matches!(ty, Ty::Applied(..));
    if !generic && !visiting.insert(*item) {
        return false;
    }
    let subst = match item_substitution(*item, args, agg) {
        Ok(subst) => subst,
        // A malformed arity is reported as its own structured
        // diagnostic wherever a *place* projects through it
        // (`PLACE_GENERIC_ARITY_MISMATCH`). This pure query has no
        // diagnostic channel of its own, so it fails *closed*, to
        // affine -- matching every other stage. Answering `false` from
        // a substitution nobody could build is the one direction that
        // silently drops an ownership obligation.
        Err(()) => {
            if !generic {
                visiting.remove(item);
            }
            return true;
        }
    };
    let field_types: Vec<Ty> = if let Some(record) = agg.records.get(item) {
        record.fields.iter().map(|(_, t)| t.clone()).collect()
    } else if let Some(variant) = agg.variants.get(item) {
        variant
            .cases
            .iter()
            .flat_map(|c| c.payload.clone())
            .collect()
    } else {
        Vec::new()
    };
    let result = field_types.iter().any(|fty| {
        is_affine_in_visiting(
            &crate::types::substitute(fty, &subst),
            agg,
            visiting,
            depth + 1,
        )
    });
    if !generic {
        visiting.remove(item);
    }
    result
}

/// `item`'s own declared type parameters paired with `args`
/// (`rfcs/0008`), for substituting a generic aggregate's declared field
/// types down to one concrete instantiation. `Err(())` on any arity
/// disagreement -- including a non-generic declaration handed type
/// arguments, or a generic one handed none -- never a partial or empty
/// map: an unsubstituted `Ty::Param` escaping a projection would make a
/// genuinely affine field look freely copyable.
fn item_substitution(
    item: ItemId,
    args: &[Ty],
    agg: &AggregateContext,
) -> Result<HashMap<TypeParamId, Ty>, ()> {
    let params: Vec<TypeParamId> = if let Some(record) = agg.records.get(&item) {
        record.type_params.iter().map(|(id, _)| *id).collect()
    } else if let Some(variant) = agg.variants.get(&item) {
        variant.type_params.iter().map(|(id, _)| *id).collect()
    } else if args.is_empty() {
        // An item this module registered no layout for at all is
        // already reported by whichever check actually needs the
        // layout; with no arguments to substitute there is nothing to
        // get wrong here.
        return Ok(HashMap::new());
    } else {
        return Err(());
    };
    if params.len() != args.len() {
        return Err(());
    }
    Ok(params.into_iter().zip(args.iter().cloned()).collect())
}

/// Resolves a structural place's own final type, starting from
/// `root_ty` and walking each projection step against `agg`'s own
/// declared record layouts -- independently re-validating owner/field
/// identity exactly like `ValueKind::RecordField`'s own check does for
/// a single-step, non-affine projection, generalized to a whole chain.
/// Each step substitutes the owner's own type arguments into the
/// selected field's declared type before continuing from it
/// (`rfcs/0008`, `rfcs/0012`), in this exact order: validate the owner,
/// retrieve its stable type parameters, require exact arity, build the
/// substitution, substitute, continue. `Projection` itself carries no
/// type-argument list -- the arguments come from the place's own
/// *current* type at that step, which is precisely why the walk has to
/// thread the substituted type forward rather than reading each field's
/// declared type in isolation.
fn resolve_place_ty(
    root_ty: &Ty,
    projections: &[crate::place::Projection],
    agg: &AggregateContext,
) -> Result<Ty, PlaceError> {
    let mut ty = root_ty.clone();
    for projection in projections {
        let crate::place::Projection::Field { owner, field } = projection else {
            return Err(PlaceError::UnknownFieldOwner(match projection {
                crate::place::Projection::VariantField { variant, .. } => *variant,
                crate::place::Projection::Field { owner, .. } => *owner,
            }));
        };
        let args: Vec<Ty> = match &ty {
            Ty::Named(item, _) if item == owner => Vec::new(),
            Ty::Applied(item, args) if item == owner => args.clone(),
            _ => return Err(PlaceError::ProjectionThroughNonRecord(ty)),
        };
        let Some(layout) = agg.records.get(owner) else {
            return Err(PlaceError::UnknownFieldOwner(*owner));
        };
        let Some((_, field_ty)) = layout.fields.get(field.0 as usize) else {
            return Err(PlaceError::UnknownField(*owner, field.0 as usize));
        };
        if layout.type_params.len() != args.len() {
            return Err(PlaceError::GenericArityMismatch(
                *owner,
                layout.type_params.len(),
                args.len(),
            ));
        }
        let subst: HashMap<TypeParamId, Ty> = layout
            .type_params
            .iter()
            .map(|(id, _)| *id)
            .zip(args)
            .collect();
        ty = crate::types::substitute(field_ty, &subst);
    }
    Ok(ty)
}

/// The exact storage one `ValueKind::VariantPayload` read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PayloadExtraction {
    /// Canonical, so an extraction naming one read of a slot and a
    /// decomposition naming another read of that same slot agree about
    /// which value they mean.
    base: ValueId,
    variant: ItemId,
    case: usize,
    index: usize,
}

/// Every payload extraction this function performs, and what each one
/// read (`rfcs/0012`).
///
/// A `DecomposeVariant` hands ownership of one case's payload positions
/// to the values in its own `taken` list. Checking only that each such
/// value has the *declared type* of the position it claims proves
/// nothing: any other value of that type would pass, while the real
/// payload stayed owned by the shell and this frame acquired an
/// obligation for something it never received. This table is what makes
/// the claim provable.
struct ExtractionTable {
    extractions: HashMap<ValueId, PayloadExtraction>,
    load_origin: HashMap<ValueId, ValueId>,
}

impl ExtractionTable {
    /// Whether `owner` is exactly the extraction that read position
    /// `index` of `case` out of `base`.
    fn claim_matches(
        &self,
        owner: ValueId,
        base: ValueId,
        variant: ItemId,
        case: usize,
        index: usize,
    ) -> bool {
        let wanted = canonical_value(base, &self.load_origin);
        self.extractions.get(&owner).is_some_and(|extraction| {
            extraction.base == wanted
                && extraction.variant == variant
                && extraction.case == case
                && extraction.index == index
        })
    }

    /// Whether `value` is a payload extraction at all.
    fn is_extraction(&self, value: ValueId) -> bool {
        self.extractions.contains_key(&value)
    }
}

fn payload_extractions(function: &Function) -> ExtractionTable {
    let mut load_origin: HashMap<ValueId, ValueId> = HashMap::new();
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value {
                result,
                kind: ValueKind::Load(slot),
                ..
            } = instruction
            {
                load_origin.insert(*result, *slot);
            }
        }
    }
    let mut extractions = HashMap::new();
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value {
                result,
                kind:
                    ValueKind::VariantPayload {
                        base,
                        variant,
                        case,
                        index,
                    },
                ..
            } = instruction
            {
                extractions.insert(
                    *result,
                    PayloadExtraction {
                        base: canonical_value(*base, &load_origin),
                        variant: *variant,
                        case: *case,
                        index: *index,
                    },
                );
            }
        }
    }
    ExtractionTable {
        extractions,
        load_origin,
    }
}

/// A single guaranteed fact: the value `.0` is known to be case `.2` of
/// variant `.1`.
///
/// `.0` is always *canonical* -- a `Load` result is recorded as the slot
/// it read, so a `switch` on one read of a slot and a `decompose` of
/// another read of that same slot are recognised as one value.
type RefinementFact = (ValueId, ItemId, usize);

/// The canonical identity `value` stands for: the slot it was loaded
/// from, or itself.
fn canonical_value(value: ValueId, load_origin: &HashMap<ValueId, ValueId>) -> ValueId {
    load_origin.get(&value).copied().unwrap_or(value)
}

/// The canonical value whose storage `instruction` writes, if any --
/// every refinement naming it stops being proven from here on.
///
/// A `StorePlace` into a *field* is deliberately not a kill: no field
/// write can change which case of a variant is live.
fn refinement_kill(
    instruction: &Instruction,
    load_origin: &HashMap<ValueId, ValueId>,
) -> Option<ValueId> {
    match instruction {
        Instruction::Store { slot, .. } => Some(canonical_value(*slot, load_origin)),
        Instruction::StorePlace { place, .. } if place.projections.is_empty() => {
            Some(canonical_value(place.root, load_origin))
        }
        _ => None,
    }
}

/// Every case refinement each block is *guaranteed* on arrival
/// (`rfcs/0010`, `rfcs/0012`), as a real worklist fixed point over the
/// whole CFG rather than a look at the immediate predecessors.
///
/// A refinement originates on a `Switch` case edge, propagates through
/// every ordinary edge, and is **intersected** at every join, never
/// unioned. So:
///
/// * a block reached through two different cases of the same switch, or
///   through a switch edge and a plain branch, is guaranteed nothing;
/// * a refinement survives any number of ordinary hops, which a
///   single-hop rule could not express;
/// * one block's guarantee is never borrowed by a sibling, because a
///   sibling is not a predecessor;
/// * nested switches stay independent, because each fact names its own
///   scrutinee;
/// * `Branch`, `CondBranch` and `Invoke` edges generate nothing at all;
/// * an unreachable predecessor is skipped entirely rather than
///   intersected in, so a dead switch edge can never erase a guarantee
///   every live path proved;
/// * two edges from one terminator into the same block stay two edges,
///   so a target shared by two cases has proven neither.
///
/// Writing a scrutinee's own storage ends what the switch proved about
/// it -- see `refinement_kill`, and `Invoke`'s own result slots.
struct RefinementTable {
    /// Facts guaranteed on entry to each block. A block absent from the
    /// map (unreachable, or never computed) guarantees nothing.
    guaranteed: HashMap<BlockId, HashSet<RefinementFact>>,
    /// `Load` result -> the slot it read.
    load_origin: HashMap<ValueId, ValueId>,
}

impl RefinementTable {
    fn canonical(&self, value: ValueId) -> ValueId {
        canonical_value(value, &self.load_origin)
    }

    /// The facts guaranteed on entry to `block`.
    fn on_entry(&self, block: BlockId) -> HashSet<RefinementFact> {
        self.guaranteed.get(&block).cloned().unwrap_or_default()
    }

    /// Whether `value` is proven to hold `case` of `variant` at a point
    /// whose currently-proven `facts` are given.
    fn proves(
        &self,
        facts: &HashSet<RefinementFact>,
        value: ValueId,
        variant: ItemId,
        case: usize,
    ) -> bool {
        facts.contains(&(self.canonical(value), variant, case))
    }

    /// Removes from `facts` everything `instruction` invalidates.
    fn apply_kill(&self, instruction: &Instruction, facts: &mut HashSet<RefinementFact>) {
        if let Some(root) = refinement_kill(instruction, &self.load_origin) {
            facts.retain(|(value, _, _)| *value != root);
        }
    }

    /// The facts still guaranteed once `block`'s own instructions have
    /// run -- what a `Return`/`Raise` in it may rely on.
    fn at_exit(&self, block: &BasicBlock) -> HashSet<RefinementFact> {
        let mut facts = self.on_entry(block.id);
        for instruction in &block.instructions {
            self.apply_kill(instruction, &mut facts);
        }
        facts
    }
}

fn case_refinements(function: &Function) -> RefinementTable {
    let entry = BlockId(0);
    let mut load_origin: HashMap<ValueId, ValueId> = HashMap::new();
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value {
                result,
                kind: ValueKind::Load(slot),
                ..
            } = instruction
            {
                load_origin.insert(*result, *slot);
            }
        }
    }

    // Every CFG edge, as `(predecessor, the facts that edge itself
    // proves)`. Two edges from one terminator into the same block stay
    // two separate entries.
    let mut successors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    let mut incoming: HashMap<BlockId, Vec<(BlockId, HashSet<RefinementFact>)>> = HashMap::new();
    for block in &function.blocks {
        let mut edges: Vec<(BlockId, HashSet<RefinementFact>)> = Vec::new();
        match &block.terminator {
            Terminator::Branch(target) => edges.push((*target, HashSet::new())),
            Terminator::CondBranch {
                then_block,
                else_block,
                ..
            } => {
                edges.push((*then_block, HashSet::new()));
                edges.push((*else_block, HashSet::new()));
            }
            Terminator::Switch {
                scrutinee,
                variant,
                cases,
            } => {
                let root = canonical_value(*scrutinee, &load_origin);
                for (case_index, target) in cases.iter().enumerate() {
                    edges.push((*target, HashSet::from([(root, *variant, case_index)])));
                }
            }
            Terminator::Invoke {
                ok_target,
                err_targets,
                ..
            } => {
                edges.push((*ok_target, HashSet::new()));
                for target in err_targets {
                    edges.push((target.target, HashSet::new()));
                }
            }
            Terminator::Return(_) | Terminator::Raise { .. } => {}
        }
        for (target, generated) in edges {
            successors.entry(block.id).or_default().push(target);
            incoming
                .entry(target)
                .or_default()
                .push((block.id, generated));
        }
    }

    let mut reachable: HashSet<BlockId> = HashSet::from([entry]);
    let mut frontier = vec![entry];
    while let Some(id) = frontier.pop() {
        for &succ in successors.get(&id).into_iter().flatten() {
            if reachable.insert(succ) {
                frontier.push(succ);
            }
        }
    }

    // An `Invoke`'s own result slots are written on its edges, so every
    // refinement naming one stops at that terminator.
    let terminator_kills = |terminator: &Terminator| -> Vec<ValueId> {
        match terminator {
            Terminator::Invoke {
                ok_slot,
                err_targets,
                ..
            } => {
                let mut slots = vec![*ok_slot];
                slots.extend(err_targets.iter().map(|t| t.slot));
                slots
            }
            _ => Vec::new(),
        }
    };
    let kill_through = |block: &BasicBlock, facts: &HashSet<RefinementFact>| {
        let mut facts = facts.clone();
        for instruction in &block.instructions {
            if let Some(root) = refinement_kill(instruction, &load_origin) {
                facts.retain(|(value, _, _)| *value != root);
            }
        }
        for slot in terminator_kills(&block.terminator) {
            let root = canonical_value(slot, &load_origin);
            facts.retain(|(value, _, _)| *value != root);
        }
        facts
    };

    // `in_facts` answers `Pending` -- not an empty fact set -- until at
    // least one reachable predecessor has produced an out-state, so a
    // block popped before its own predecessors records nothing and is
    // simply revisited. The lattice is the finite set of facts this
    // function's switches can generate, ordered by inclusion, and both
    // effects here only ever remove facts (a predecessor's out-state
    // shrinking, or another predecessor joining the intersection), so
    // the iteration is monotone and terminates with no pass limit.
    let in_facts = |id: BlockId,
                    out: &HashMap<BlockId, HashSet<RefinementFact>>|
     -> IncomingState<HashSet<RefinementFact>> {
        if id == entry {
            return IncomingState::Entry(HashSet::new());
        }
        let mut acc: Option<HashSet<RefinementFact>> = None;
        for (pred, generated) in incoming.get(&id).into_iter().flatten() {
            if !reachable.contains(pred) {
                continue;
            }
            let Some(pred_out) = out.get(pred) else {
                continue;
            };
            let mut edge: HashSet<RefinementFact> = pred_out.clone();
            edge.extend(generated.iter().copied());
            acc = Some(match acc {
                None => edge,
                Some(previous) => previous.intersection(&edge).copied().collect(),
            });
        }
        match acc {
            Some(facts) => IncomingState::Ready(facts),
            None => IncomingState::Pending,
        }
    };

    let mut guaranteed: HashMap<BlockId, HashSet<RefinementFact>> = HashMap::new();
    let Some(entry_block) = function.blocks.iter().find(|b| b.id == entry) else {
        return RefinementTable {
            guaranteed,
            load_origin,
        };
    };
    guaranteed.insert(entry, HashSet::new());
    let mut out: HashMap<BlockId, HashSet<RefinementFact>> =
        HashMap::from([(entry, kill_through(entry_block, &HashSet::new()))]);
    let mut worklist: VecDeque<BlockId> = function
        .blocks
        .iter()
        .map(|b| b.id)
        .filter(|id| *id != entry && reachable.contains(id))
        .collect();
    let mut queued: HashSet<BlockId> = worklist.iter().copied().collect();
    while let Some(id) = worklist.pop_front() {
        queued.remove(&id);
        let Some(block) = function.blocks.iter().find(|b| b.id == id) else {
            continue;
        };
        let facts = match in_facts(id, &out) {
            IncomingState::Entry(facts) | IncomingState::Ready(facts) => facts,
            IncomingState::Pending => continue,
        };
        guaranteed.insert(id, facts.clone());
        let new_out = kill_through(block, &facts);
        if out.get(&id) != Some(&new_out) {
            out.insert(id, new_out);
            for &succ in successors.get(&id).into_iter().flatten() {
                if succ != entry && reachable.contains(&succ) && queued.insert(succ) {
                    worklist.push_back(succ);
                }
            }
        }
    }

    RefinementTable {
        guaranteed,
        load_origin,
    }
}

/// Nothing may name one specific case of a variant without a proof
/// that the value actually holds it (`rfcs/0010`, `rfcs/0012`).
///
/// Two instructions do: `ValueKind::VariantPayload` *reads* one payload
/// position of a case, and `Instruction::DecomposeVariant` *transfers
/// ownership* of every payload position of a case. Both are checked
/// here, against the same `case_refinements` fixed point, so the two can
/// never disagree about what a block proved.
///
/// The proof is re-derived from the CFG itself, independent of how
/// lowering happened to build it, and is deliberately not limited to the
/// immediately preceding block: a refinement survives any number of
/// ordinary hops, and is lost the moment a join has one predecessor that
/// did not prove it.
///
/// Within a block, the facts are walked instruction by instruction, so a
/// write to a scrutinee's own storage stops proving anything about it
/// from that point on -- including for a later instruction in the very
/// same block.
fn verify_payload_refinement(
    function: &Function,
    agg: &AggregateContext,
    source: SourceId,
    function_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let _ = agg;
    let refinements = case_refinements(function);
    for block in &function.blocks {
        let mut proven = refinements.on_entry(block.id);
        for instruction in &block.instructions {
            match instruction {
                Instruction::Value {
                    kind:
                        ValueKind::VariantPayload {
                            base,
                            variant,
                            case,
                            ..
                        },
                    ..
                } => {
                    if !refinements.proves(&proven, *base, *variant, *case) {
                        diagnostics.push(Diagnostic::error(
                            codes::PAYLOAD_OUTSIDE_REFINEMENT,
                            source,
                            Span::dummy(),
                            format!(
                                "function `{function_name}` extracts a variant payload outside the control-flow edge for its case (bb{})",
                                block.id.0
                            ),
                        ));
                    }
                }
                Instruction::DecomposeVariant {
                    value,
                    variant,
                    case,
                    ..
                } if !refinements.proves(&proven, *value, *variant, *case) => {
                    diagnostics.push(Diagnostic::error(
                        codes::DECOMPOSITION_OUTSIDE_REFINEMENT,
                        source,
                        Span::dummy(),
                        format!(
                            "function `{function_name}` takes %{} apart into case {case} of \
                             variant {} in bb{}, where nothing proves it holds that case",
                            value.0, variant.0, block.id.0
                        ),
                    ));
                }
                _ => {}
            }
            refinements.apply_kill(instruction, &mut proven);
        }
    }
}

/// For a single block, given the facts already guaranteed on entry to
/// it (`in_facts`), returns the facts guaranteed on exit from it
/// (an unconditional `Store` to a guarded slot adds one, matching a
/// real definite-assignment analysis: everything after that `Store`,
/// in this block or any later one, may rely on it) alongside every
/// `Load` of a guarded slot not yet proven initialized at the point it
/// occurs.
fn invoke_slot_block_transfer(
    block: &BasicBlock,
    guarded_slots: &HashSet<ValueId>,
    in_facts: &HashSet<ValueId>,
) -> (HashSet<ValueId>, Vec<ValueId>) {
    let mut facts = in_facts.clone();
    let mut violations = Vec::new();
    for instruction in &block.instructions {
        match instruction {
            Instruction::Value {
                kind: ValueKind::Load(slot),
                ..
            } if guarded_slots.contains(slot) && !facts.contains(slot) => {
                violations.push(*slot);
            }
            Instruction::Store { slot, .. } if guarded_slots.contains(slot) => {
                facts.insert(*slot);
            }
            _ => {}
        }
    }
    (facts, violations)
}

/// Computes `block_id`'s own guaranteed-on-entry fact set from its
/// recorded incoming edges' current exit facts (`out`) -- intersection
/// across every edge *whose predecessor is reachable from the entry*,
/// exactly like `verify_payload_refinement`'s own single-hop model,
/// except each reachable edge's own contribution here is
/// `out[predecessor] plus whatever that specific edge itself writes`,
/// which is what lets a fact keep propagating across any number of
/// ordinary hops in between. An edge whose predecessor is *not*
/// reachable is skipped entirely, never intersected in: an unreachable
/// predecessor's own `out` is always the empty set (it is never seeded
/// optimistically and never touched by the worklist), so folding it
/// into a join would incorrectly wipe out a fact every genuinely live
/// path into that join already guarantees, purely because some dead
/// code elsewhere also happens to branch to the same block. The entry
/// block, and any block with no *reachable* incoming edge at all
/// (genuinely unreachable, or reachable only from unreachable
/// predecessors), are defined to guarantee nothing.
fn invoke_slot_in_facts(
    block_id: BlockId,
    entry: BlockId,
    incoming_edges: &HashMap<BlockId, Vec<(BlockId, Option<ValueId>)>>,
    reachable: &HashSet<BlockId>,
    out: &HashMap<BlockId, HashSet<ValueId>>,
) -> HashSet<ValueId> {
    if block_id == entry {
        return HashSet::new();
    }
    let Some(edges) = incoming_edges.get(&block_id) else {
        return HashSet::new();
    };
    let mut edges = edges.iter().filter(|(pred, _)| reachable.contains(pred));
    let Some((first_pred, first_gen)) = edges.next() else {
        return HashSet::new();
    };
    let mut acc = out.get(first_pred).cloned().unwrap_or_default();
    if let Some(slot) = first_gen {
        acc.insert(*slot);
    }
    for (pred, edge_gen) in edges {
        let mut edge_facts = out.get(pred).cloned().unwrap_or_default();
        if let Some(slot) = edge_gen {
            edge_facts.insert(*slot);
        }
        acc.retain(|f| edge_facts.contains(f));
    }
    acc
}

/// Proves a `Terminator::Invoke`'s own conditionally-written slots
/// (`ok_slot`, or one of its `err_targets`' own `slot`) are *definitely
/// initialized* by the time any `Load` reads them -- a full forward
/// must-dataflow analysis, not merely a single-hop check of a `Load`'s
/// own immediate predecessors. Dominance (checked separately,
/// `verify_dominance`) only proves a slot's own `alloc` precedes a use,
/// never that the specific edge which actually writes it is the one
/// that was taken to reach that use, and a single-hop check would also
/// wrongly reject a slot correctly propagated across several ordinary
/// (non-`Invoke`) blocks before its own `Load` -- exactly the gap a
/// real dataflow closes.
///
/// This computes a *greatest* fixed point: every reachable block except
/// the entry starts optimistic (the complete guarded-slot set, i.e.
/// "everything is already initialized"), and a block's own facts only
/// ever shrink from there as real, restrictive predecessor information
/// intersects in -- the analysis settles at the largest fact set that
/// is still consistent with every edge in the CFG.
///
/// The entry block is not part of that iteration at all: its own IN is
/// always the empty set, by definition, regardless of whatever
/// `incoming_edges` a backedge into it might otherwise record, so its
/// OUT is computed exactly once, up front, as a fixed boundary value
/// the rest of the analysis is anchored to -- it is seeded into the
/// fact map and never revisited. Treating the entry as just another
/// block whose OUT starts at `{}` and gets updated later, alongside
/// everything else, is what would make correctness depend on
/// processing order: if the entry itself performs an unconditional
/// `Store` to a guarded slot, its true OUT is *larger* than that
/// placeholder `{}`, so any reachable block a still-unprocessed entry
/// feeds into could transiently (and, without care, permanently)
/// intersect down to less than it is actually owed, purely because it
/// happened to be visited before the entry was. Computing the entry's
/// boundary first removes that dependency entirely: every other
/// reachable block's own OUT is then a true, monotonically
/// non-increasing descent from the top of a finite lattice, which is
/// what guarantees the worklist below converges to the same result no
/// matter what order `function.blocks` stores them in.
///
/// A block unreachable from the entry is not part of the fixpoint
/// either, and is never seeded with the optimistic "everything already
/// initialized" start reachable blocks get -- there is no real
/// predecessor that could ever refine such a block down from that
/// starting point, so an optimistic start would simply never change,
/// hiding a genuine violation inside dead code (including a cycle
/// purely among unreachable blocks referencing only each other). Each
/// unreachable block is instead checked independently, from an empty
/// IN set, ignoring any incoming edge `incoming_edges` may have
/// recorded for it -- a `Store` earlier in that same block can still
/// initialize a `Load` later in it (the ordinary local transfer
/// function already accounts for this), but nothing crosses into it
/// from anywhere else.
/// Proves no value is ever the operand of two `Instruction::Drop`s on
/// any single reachable path (`rfcs/0011`) -- shares its reachability
/// computation, fixed entry boundary, and worklist-over-reachable-
/// non-entry-blocks shape with
/// [`verify_invoke_slot_initialization`], but is a *may* analysis, not
/// a must one: a join here unions its reachable predecessors' facts,
/// since "already dropped" only needs to hold on *one* incoming path
/// for a later unconditional `Drop` past the join to be a genuine
/// double-drop on that path -- intersecting instead would hide exactly
/// that case behind a sibling branch that never dropped the value at
/// all. Simplified by having no edge-specific gen at all: unlike an
/// `Invoke`'s own edges, which each unconditionally write a *specific*
/// slot, a `Drop` only ever "generates" its own already-dropped fact
/// from within the block that contains it, so every CFG edge here
/// carries the same, unconditional meaning ordinary (non-`Invoke`)
/// edges already do in that analysis.
fn verify_drop_state(
    function: &Function,
    source: SourceId,
    function_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut dropped_values: HashSet<ValueId> = HashSet::new();
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Drop { value } = instruction {
                dropped_values.insert(*value);
            }
        }
    }
    if dropped_values.is_empty() {
        return;
    }

    let entry = BlockId(0);
    if !function.blocks.iter().any(|b| b.id == entry) {
        return;
    }

    let mut successors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for block in &function.blocks {
        match &block.terminator {
            Terminator::Branch(target) => successors.entry(block.id).or_default().push(*target),
            Terminator::CondBranch {
                then_block,
                else_block,
                ..
            } => successors
                .entry(block.id)
                .or_default()
                .extend([*then_block, *else_block]),
            Terminator::Switch { cases, .. } => {
                successors.entry(block.id).or_default().extend(cases)
            }
            Terminator::Invoke {
                ok_target,
                err_targets,
                ..
            } => {
                successors.entry(block.id).or_default().push(*ok_target);
                successors
                    .entry(block.id)
                    .or_default()
                    .extend(err_targets.iter().map(|t| t.target));
            }
            Terminator::Return(_) | Terminator::Raise { .. } => {}
        }
    }
    let mut incoming: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for (&from, tos) in &successors {
        for &to in tos {
            incoming.entry(to).or_default().push(from);
        }
    }

    let mut reachable: HashSet<BlockId> = HashSet::from([entry]);
    let mut frontier = vec![entry];
    while let Some(id) = frontier.pop() {
        for &succ in successors.get(&id).into_iter().flatten() {
            if reachable.insert(succ) {
                frontier.push(succ);
            }
        }
    }

    fn transfer(
        block: &BasicBlock,
        dropped_values: &HashSet<ValueId>,
        in_facts: &HashSet<ValueId>,
    ) -> (HashSet<ValueId>, Vec<ValueId>) {
        let mut facts = in_facts.clone();
        let mut violations = Vec::new();
        for instruction in &block.instructions {
            match instruction {
                // A loop body's own back edge can carry an already-
                // dropped fact for %N forward into a later iteration
                // that reuses that same static `ValueId` for a brand
                // new instance (NIR gives a loop-carried temporary one
                // fixed id, not a fresh one per iteration) -- so this
                // instruction's own `result` redefining %N kills
                // whatever the *previous* iteration left behind before
                // this iteration's `Drop`s are considered at all.
                Instruction::Value { result, .. } if dropped_values.contains(result) => {
                    facts.remove(result);
                }
                Instruction::Drop { value } if dropped_values.contains(value) => {
                    if facts.contains(value) {
                        violations.push(*value);
                    } else {
                        facts.insert(*value);
                    }
                }
                _ => {}
            }
        }
        (facts, violations)
    }

    fn in_facts_for(
        block_id: BlockId,
        entry: BlockId,
        incoming: &HashMap<BlockId, Vec<BlockId>>,
        reachable: &HashSet<BlockId>,
        out: &HashMap<BlockId, HashSet<ValueId>>,
    ) -> HashSet<ValueId> {
        if block_id == entry {
            return HashSet::new();
        }
        let Some(preds) = incoming.get(&block_id) else {
            return HashSet::new();
        };
        let mut preds = preds.iter().filter(|p| reachable.contains(p));
        let Some(first) = preds.next() else {
            return HashSet::new();
        };
        // Union, not intersection: a value already dropped on *any*
        // reachable predecessor path is a live double-drop hazard the
        // moment a later `Drop` of it executes unconditionally, even
        // though some *other* predecessor never dropped it at all --
        // catching that requires remembering it happened on at least
        // one path in, not only when every path agrees.
        let mut acc = out.get(first).cloned().unwrap_or_default();
        for pred in preds {
            let other = out.get(pred).cloned().unwrap_or_default();
            acc.extend(other);
        }
        acc
    }

    let entry_block = function
        .blocks
        .iter()
        .find(|b| b.id == entry)
        .expect("presence already checked above");
    let (entry_out, _) = transfer(entry_block, &dropped_values, &HashSet::new());

    let mut out: HashMap<BlockId, HashSet<ValueId>> = function
        .blocks
        .iter()
        .map(|b| {
            // A may analysis starts every reachable non-entry block at
            // bottom (nothing yet known dropped) and grows monotonically
            // via `in_facts_for`'s own union at each join, rather than
            // starting optimistically at the full set and shrinking --
            // that shrinking approach only terminates soundly for a
            // must analysis's intersection, not this one's union.
            let initial = if b.id == entry {
                entry_out.clone()
            } else {
                HashSet::new()
            };
            (b.id, initial)
        })
        .collect();

    let mut worklist: VecDeque<BlockId> = function
        .blocks
        .iter()
        .map(|b| b.id)
        .filter(|id| *id != entry && reachable.contains(id))
        .collect();
    let mut queued: HashSet<BlockId> = worklist.iter().copied().collect();
    while let Some(id) = worklist.pop_front() {
        queued.remove(&id);
        let Some(block) = function.blocks.iter().find(|b| b.id == id) else {
            continue;
        };
        let in_facts = in_facts_for(id, entry, &incoming, &reachable, &out);
        let (new_out, _) = transfer(block, &dropped_values, &in_facts);
        if out.get(&id) != Some(&new_out) {
            out.insert(id, new_out);
            for &succ in successors.get(&id).into_iter().flatten() {
                if succ != entry && reachable.contains(&succ) && queued.insert(succ) {
                    worklist.push_back(succ);
                }
            }
        }
    }

    for block in &function.blocks {
        let in_facts = if reachable.contains(&block.id) {
            in_facts_for(block.id, entry, &incoming, &reachable, &out)
        } else {
            HashSet::new()
        };
        let (_, violations) = transfer(block, &dropped_values, &in_facts);
        for value in violations {
            diagnostics.push(Diagnostic::error(
                codes::DOUBLE_DROP,
                source,
                Span::dummy(),
                format!(
                    "function `{function_name}` drops %{} in bb{}, which was already dropped on some path reaching it",
                    value.0, block.id.0
                ),
            ));
        }
    }
}

/// Whether a value/slot currently grants owning or merely observing
/// access to its own underlying resource (`rfcs/0011`) -- tracked
/// flow-sensitively, per value/slot, entirely independently of
/// `resourceck`: an ordinary non-`take` parameter, or anything ever
/// loaded from a `store.observe`'d slot, is `Observed` and must never
/// be silently treated as an owner. Module-level (not nested inside
/// `verify_resource_ownership`) specifically so `merge_location`/
/// `merge_provenance`, below, are directly unit-testable on their own,
/// independently of the rest of that function's own closures.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Role {
    Owned,
    Observed,
}

/// A value/slot's own current provenance, once definitely initialized:
/// every resource identity it might currently denote (more than one
/// only just past a join where reachable predecessors disagree), and
/// whether *every* predecessor agrees it is currently `Owned` --
/// downgraded to `Observed` the moment even one disagrees, since an
/// `Observed` role must never be silently widened into an owner.
type Provenance = (BTreeSet<ValueId>, Role);

/// A value/slot's own current definite-initialization state
/// (`rfcs/0011`) -- deliberately has *no* variant that silently grants
/// ownership: a location this pass never otherwise recorded anything
/// for is `Uninitialized`, never a lenient fresh `Owned` guess. `Alloc`
/// starts a resource-typed slot here; every other resource-producing
/// value goes straight to `Initialized` at its own definition, since it
/// is never itself a slot with its own separate write-then-read
/// lifecycle.
#[derive(Clone, PartialEq, Eq, Debug)]
enum LocationState {
    /// Never written on this exact path -- reading it is always
    /// unsound, regardless of what some *other* path might have done,
    /// since this is the path actually taken.
    Uninitialized,
    /// Written, with a definite resolved provenance, on *every*
    /// reachable path reaching this point.
    Initialized(Provenance),
    /// Written on *some* but not *every* reachable path reaching this
    /// point -- reading it is still unsound: the specific path actually
    /// taken at runtime might be one of the ones that never wrote it.
    /// (A role/origin disagreement between two paths that *both* wrote
    /// it is not this state at all -- it stays `Initialized`, with
    /// `Provenance`'s own union-origins/conservative-role merge already
    /// representing it soundly, the same way `RESOURCE_LEAKED_ON_EXIT`'s
    /// own reachable-union dataflow already tolerates disagreement
    /// without needing a distinct "conflict" state of its own.)
    MaybeUninitialized,
}

/// Merges two predecessors' own `LocationState`s for the *same* value/
/// slot at a CFG join (`rfcs/0011`). Symmetric, associative, and
/// idempotent by construction (a plain match over an unordered pair of
/// cases, with `Initialized`'s own payload merge itself built from
/// unordered set union and a commutative role reduction) -- so the
/// three-argument fold `merge_provenance` performs never depends on
/// which predecessor is visited first, directly or transitively.
fn merge_location(a: LocationState, b: LocationState) -> LocationState {
    match (a, b) {
        (LocationState::Uninitialized, LocationState::Uninitialized) => {
            LocationState::Uninitialized
        }
        (LocationState::MaybeUninitialized, _) | (_, LocationState::MaybeUninitialized) => {
            LocationState::MaybeUninitialized
        }
        (LocationState::Initialized(_), LocationState::Uninitialized)
        | (LocationState::Uninitialized, LocationState::Initialized(_)) => {
            LocationState::MaybeUninitialized
        }
        (
            LocationState::Initialized((a_ids, a_role)),
            LocationState::Initialized((b_ids, b_role)),
        ) => {
            let ids = a_ids.union(&b_ids).copied().collect();
            let role = if a_role == Role::Owned && b_role == Role::Owned {
                Role::Owned
            } else {
                Role::Observed
            };
            LocationState::Initialized((ids, role))
        }
    }
}

/// Merges two predecessors' own location-state maps at a join,
/// reachable predecessors only (the caller already filters unreachable
/// ones out before calling this) -- symmetric over the *union* of both
/// maps' own keys, never iterating only one side's: a key present in
/// only one predecessor is treated as `Uninitialized` on the other (a
/// location never touched at all on a path is exactly as uninitialized
/// there as one explicitly never stored into), so it still correctly
/// downgrades to `MaybeUninitialized` rather than being copied through
/// unmerged as if that side had no opinion at all. The key set is
/// collected into a `BTreeSet` -- sorted, not raw `HashMap` iteration
/// order -- so the result depends only on the two states actually being
/// merged, never on either map's own hashing, predecessor order, or
/// block-vector order.
fn merge_provenance(
    a: &HashMap<ValueId, LocationState>,
    b: &HashMap<ValueId, LocationState>,
) -> HashMap<ValueId, LocationState> {
    let keys: BTreeSet<ValueId> = a.keys().chain(b.keys()).copied().collect();
    keys.into_iter()
        .map(|key| {
            let left = a.get(&key).cloned().unwrap_or(LocationState::Uninitialized);
            let right = b.get(&key).cloned().unwrap_or(LocationState::Uninitialized);
            (key, merge_location(left, right))
        })
        .collect()
}

/// Independently reconstructs two `rfcs/0011` invariants over every
/// resource-typed value in `function`, in one combined forward dataflow
/// walk (see `State`, below): that it is used at most once after its
/// own underlying resource was already consumed -- dropped, moved into
/// a `take` parameter or `Invoke` argument, or transferred out through
/// `Terminator::Return`/`Raise` (`RESOURCE_USE_AFTER_CONSUME`) -- and
/// that every resource this function itself owns (a fresh construction,
/// or a `take` parameter) is actually destroyed or transferred out on
/// every reachable exit, rather than merely abandoned
/// (`RESOURCE_LEAKED_ON_EXIT`). This does not trust `resourceck`'s own
/// acceptance of the source program: it walks the already-lowered NIR
/// on its own, using only `Function`/`Module`-level facts
/// (`value_types`, each callee's own declared `take` flags, each
/// record's own declared `affine` flag) that a hand-built NIR module --
/// never having passed through `resourceck` at all -- still carries.
///
/// Reuses `verify_drop_state`'s own reachable-union worklist shape
/// (a value already consumed -- or still live -- on *any* reachable
/// path in is a live hazard the moment this path's own next use, or
/// exit, runs), generalized in two ways: consumption is not only
/// `Drop`, and identity is not only a bare `ValueId` -- a value loaded
/// from a slot shares that slot's own identity with every other `Load`
/// of it, so a second, differently numbered `Load` of an already-
/// consumed slot is caught exactly like reusing the original `ValueId`
/// directly would be, and a resource stored into a slot relocates its
/// own leak-tracking identity onto that slot for the same reason. A
/// fresh `Store` into a slot clears whatever consumption/liveness that
/// slot's own prior occupant carried -- reassigning a slot after its
/// own resource was already dropped or moved out is `resourceck`'s own
/// concern (`U0010`), not this pass's.
///
/// A resource transferred in through `Terminator::Invoke`'s own success
/// slot *is* tracked by `RESOURCE_LEAKED_ON_EXIT`: `in_state_for`'s own
/// `incoming_edges` seeds it as newly live (and newly `Owned`)
/// specifically on the block reached through the `Invoke`'s own
/// `ok_target` edge, never on a block reached only through one of its
/// `err_targets` -- the same edge-sensitive-by-specific-edge-not-just-
/// target-block technique `verify_invoke_slot_initialization` already
/// needs for V0073, for the same underlying reason (an `Invoke`'s own
/// `ok_target` and one of its `err_targets`' own `target` can coincide
/// on the same block, which an ordinary flat predecessor list keyed
/// only by target cannot distinguish).
///
/// This pass also independently tracks, per value/slot and flow-
/// sensitively, an owning-vs-observing *role* and a true resource
/// *identity* (`Role`/`Provenance`, below) -- not merely which raw
/// `ValueId` a use happens to name. An ordinary (non-`take`) parameter,
/// and anything ever loaded from a `store.observe`'d slot, is
/// `Observed`: never itself an owner, and rejected outright
/// (`RESOURCE_OBSERVER_CONSUMED`/`INVALID_RESOURCE_STORE_MODE`) if used
/// as a `Drop`/`Move`/`DeferCapture`/`take` operand, a `store.transfer`
/// value, or a `Return`/`Raise` operand -- regardless of whether its
/// own underlying resource happens to still be live elsewhere, since an
/// observation must never be silently promoted into an owner no matter
/// what. Separately, every value/slot's own true resource identity is
/// unified across an observing `Store`/`Load` pair (not only a slot's
/// own repeated `Load`s, which `RESOURCE_USE_AFTER_CONSUME`/
/// `RESOURCE_LEAKED_ON_EXIT` already unify): a `Drop` reaching this
/// point through *any* alias of a resource poisons every other alias
/// of that same identity for every later use, consuming or not
/// (`RESOURCE_ORIGIN_CONFLICT`), so an observation created before a
/// drop, still nominally in scope, can never be used again as though
/// nothing happened. `Move`/`DeferCapture` relocate ownership to a
/// fresh `ValueId` while still sharing the *same* resolved identity as
/// their own `source` (so a drop reachable through either is
/// recognized as the same resource) -- `RESOURCE_USE_AFTER_CONSUME`'s
/// own `facts`/`live` bookkeeping, by contrast, deliberately keeps
/// treating a `Move`/`DeferCapture` result as a fresh, decoupled
/// identity of its own, exactly as before: unifying *that* bookkeeping
/// through a move too would make a legitimate later use of the new
/// owner collide with its own now-permanently-consumed `source`.
///
/// A value/slot's own role/identity is only ever meaningful once it is
/// *definitely initialized* on every reachable path reaching the point
/// it is used (`LocationState`, below) -- `Alloc` starts a resource-
/// typed slot at `Uninitialized`; `store.observe`/`store.transfer`
/// initialize it; a full reachable-union-of-predecessors forward
/// dataflow (the same shape every other check in this pass already
/// uses) propagates that fact forward, downgrading to
/// `MaybeUninitialized` the moment even one reachable predecessor never
/// wrote it. A location this pass never otherwise recorded anything for
/// resolves to `Uninitialized`, never a lenient fresh `Owned` guess --
/// every use (`Load` included) of anything not definitely `Initialized`
/// is independently rejected (`RESOURCE_LOCATION_NOT_DEFINITELY_
/// INITIALIZED`), before this pass's own role/origin checks even run.
fn verify_resource_ownership(
    function: &Function,
    value_types: &HashMap<ValueId, Ty>,
    known_functions: &HashMap<ItemId, KnownFunction>,
    agg: &AggregateContext,
    source: SourceId,
    function_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Deliberately nominal, not transitively affine (`rfcs/0012`): this
    // whole-value lattice (`live`/`facts`/`provenance`/`dropped_origins`)
    // exists to make sure every value that is *itself* ever the direct
    // target of a whole `Drop`/`Move`/`take` obligation actually
    // discharges it -- a plain, non-resource record/variant that merely
    // *contains* one is never such a target on its own: `resourceck`'s
    // own structural cleanup planning already destroys its own affine
    // fields individually (each becomes its own fresh, nominally-
    // resource-or-opaque-variant `ValueId` the moment `PlaceRead` reads
    // it out, tracked here in its own right from that point on), and
    // the container's own whole value is never itself the operand of a
    // `Drop`. Tracking it here too would double-count: it would demand
    // an explicit destruction of the *container* that `resourceck`
    // never plans (and `nir::lower` never emits) at all, alongside the
    // real one already correctly demanded of each field individually.
    // [`is_affine_whole`], below, is the transitive query for the
    // handful of checks that *do* need it (`Drop`/`Move`/`DeferCapture`
    // validity): those two *are* legitimately used on a transitively-
    // affine value directly (an opaque variant read out as a whole via
    // `PlaceRead`, or moved between locals) -- everywhere else in this
    // pass, `is_resource` is exactly the right, narrower question.
    let is_resource = |v: ValueId| -> bool {
        value_types
            .get(&v)
            .is_some_and(|ty| matches!(ty, Ty::Named(item, _) if agg.records.get(item).is_some_and(|r| r.affine)))
    };
    let is_affine_whole =
        |v: ValueId| -> bool { value_types.get(&v).is_some_and(|ty| is_affine_in(ty, agg)) };

    // Whether a `Call`/`Invoke` argument at index `i` transfers
    // ownership, given `take`'s own declared flags (`rfcs/0011`) --
    // structural malformation (`UNKNOWN_FUNCTION_REF`/argument-count
    // mismatches, already independently diagnosed elsewhere in this
    // module) is handled *conservatively*: every argument is treated as
    // consumed rather than merely observed, since wrongly assuming a
    // transfer only ever causes an over-eager "already consumed" report
    // on some later use, while wrongly assuming an observation could
    // let a resource an unknown callee actually took ownership of be
    // silently treated as still live and usable afterward -- unsound in
    // the dangerous direction. Never a silent `false` default.
    let consumes_arg = |take: Option<&[bool]>, args_len: usize, i: usize| -> bool {
        match take {
            Some(flags) if flags.len() == args_len => flags.get(i).copied().unwrap_or(true),
            _ => true,
        }
    };

    // `Role`, `Provenance`, and `LocationState` are module-level (see
    // above `verify_resource_ownership`'s own doc comment) -- this
    // function only ever consumes them, never redefines them.

    // Resolves `raw`'s own current state, defaulting a location this
    // pass never otherwise recorded anything for to `Uninitialized` --
    // never a lenient fresh `Owned` guess. A resource-typed `Alloc`
    // explicitly seeds `Uninitialized` itself (below), so a missing key
    // here only ever means a hand-built module referenced a `ValueId`
    // with no resource-typed definition this pass ever walked at all.
    let resolve_state =
        |raw: ValueId, provenance: &HashMap<ValueId, LocationState>| -> LocationState {
            provenance
                .get(&raw)
                .cloned()
                .unwrap_or(LocationState::Uninitialized)
        };

    // Resolves `raw`'s own current *identities*, for propagation
    // continuity only (never for deciding legality -- `check_alias_
    // safety` alone decides that, and always runs first): a location
    // that is not definitely `Initialized` has no real identity yet, so
    // this falls back to `raw` itself purely to keep downstream
    // bookkeeping well-formed after an already-reported violation, not
    // to grant it one.
    let resolve_ids =
        |raw: ValueId, provenance: &HashMap<ValueId, LocationState>| -> BTreeSet<ValueId> {
            match provenance.get(&raw) {
                Some(LocationState::Initialized((ids, _))) => ids.clone(),
                _ => BTreeSet::from([raw]),
            }
        };

    /// A specific consuming use rejected because its own resolved
    /// provenance was `Observed`, not `Owned` (`RESOURCE_OBSERVER_
    /// CONSUMED`/`INVALID_RESOURCE_STORE_MODE`) -- `StoreMode` names a
    /// `store.transfer` specifically, since its own diagnostic names
    /// the slot rather than a generic consuming site.
    enum RoleViolation {
        Consumed(ValueId),
        StoreMode(ValueId),
    }

    // Independently checks `raw` is safe to use at all, in three
    // strictly-ordered stages -- regardless of whether this specific
    // use is consuming. First, that it is definitely initialized on
    // every reachable path reaching this exact use (`RESOURCE_
    // LOCATION_NOT_DEFINITELY_INITIALIZED`) -- an uninitialized or
    // only-maybe-initialized location is never treated as owned *or*
    // observed, since it has no real identity to be either. Second
    // (only once initialized), that its own resolved identity was not
    // already destroyed through some *other* alias on this path
    // (`RESOURCE_ORIGIN_CONFLICT`). Third, only when this use is itself
    // consuming, that the resolved role actually grants ownership
    // (`RESOURCE_OBSERVER_CONSUMED`/`INVALID_RESOURCE_STORE_MODE`).
    // Returns whether a consuming use may actually proceed -- the
    // caller must then treat a rejected consuming use as a plain
    // (non-mutating) observation for `facts`/`live` bookkeeping, so an
    // illegal attempt never mutates ownership state as if it had
    // legitimately succeeded.
    let check_alias_safety = |raw: ValueId,
                              provenance: &HashMap<ValueId, LocationState>,
                              dropped_origins: &HashSet<ValueId>,
                              consumes: bool,
                              store_mode: bool,
                              uninitialized_uses: &mut Vec<ValueId>,
                              origin_conflicts: &mut Vec<ValueId>,
                              role_violations: &mut Vec<RoleViolation>|
     -> bool {
        if !is_resource(raw) {
            return true;
        }
        let (identities, role) = match resolve_state(raw, provenance) {
            LocationState::Initialized(prov) => prov,
            LocationState::Uninitialized | LocationState::MaybeUninitialized => {
                uninitialized_uses.push(raw);
                return false;
            }
        };
        if identities.iter().any(|o| dropped_origins.contains(o)) {
            origin_conflicts.push(raw);
        }
        if consumes && role != Role::Owned {
            role_violations.push(if store_mode {
                RoleViolation::StoreMode(raw)
            } else {
                RoleViolation::Consumed(raw)
            });
            return false;
        }
        true
    };

    // Every `Load`'s own result shares its identity with the slot it
    // loads from -- computed once, up front, rather than re-scanned per
    // lookup.
    let mut load_origin: HashMap<ValueId, ValueId> = HashMap::new();
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value {
                result,
                kind: ValueKind::Load(slot),
                ..
            } = instruction
            {
                load_origin.insert(*result, *slot);
            }
        }
    }
    let origin = |v: ValueId| -> ValueId { load_origin.get(&v).copied().unwrap_or(v) };

    // Every `Move`/`DeferCapture` whose own `source` is not even
    // resource-typed (`rfcs/0011`): a structural malformation `nir::
    // lower` never produces (both are only ever emitted for an
    // already-affine value), but a hand-built module could still
    // construct. `check_use` alone would silently ignore this (it
    // returns immediately for a non-resource operand), so it is
    // checked here instead, independently of the ownership dataflow
    // below.
    let mut non_resource_moves: Vec<(ValueId, &'static str)> = Vec::new();
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value { result, kind, .. } = instruction {
                let source = match kind {
                    ValueKind::Move { source } => Some((*source, "Move")),
                    ValueKind::DeferCapture { source } => Some((*source, "DeferCapture")),
                    _ => None,
                };
                if let Some((source, label)) = source
                    && !is_affine_whole(source)
                {
                    non_resource_moves.push((*result, label));
                }
            }
        }
    }

    let entry = BlockId(0);
    if !function.blocks.iter().any(|b| b.id == entry) {
        return;
    }

    let mut successors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    // Every edge leaving a block, paired with whatever *extra* resource
    // origin becomes newly live specifically on that one edge -- an
    // `Invoke`'s own `ok_slot`, on its own `ok_target` edge alone, never
    // any of its failure edges (`rfcs/0011`). Built the same way, and
    // for the same reason, `verify_invoke_slot_initialization`'s own
    // `incoming_edges` already is: an ordinary flat predecessor list
    // keyed only by target block cannot express this at all, since an
    // `Invoke`'s own `ok_target` and one of its `err_targets`' own
    // `target` can coincide (the same block reached through either
    // edge) -- indexing by the *edge* itself, not merely its target, is
    // what keeps the success edge's own extra liveness from also
    // leaking onto a failure edge that happens to share a target block.
    let mut incoming_edges: HashMap<BlockId, Vec<(BlockId, Option<ValueId>)>> = HashMap::new();
    for block in &function.blocks {
        match &block.terminator {
            Terminator::Branch(target) => {
                successors.entry(block.id).or_default().push(*target);
                incoming_edges
                    .entry(*target)
                    .or_default()
                    .push((block.id, None));
            }
            Terminator::CondBranch {
                then_block,
                else_block,
                ..
            } => {
                successors
                    .entry(block.id)
                    .or_default()
                    .extend([*then_block, *else_block]);
                incoming_edges
                    .entry(*then_block)
                    .or_default()
                    .push((block.id, None));
                incoming_edges
                    .entry(*else_block)
                    .or_default()
                    .push((block.id, None));
            }
            Terminator::Switch { cases, .. } => {
                successors.entry(block.id).or_default().extend(cases);
                for target in cases {
                    incoming_edges
                        .entry(*target)
                        .or_default()
                        .push((block.id, None));
                }
            }
            Terminator::Invoke {
                ok_slot,
                ok_target,
                err_targets,
                ..
            } => {
                successors.entry(block.id).or_default().push(*ok_target);
                successors
                    .entry(block.id)
                    .or_default()
                    .extend(err_targets.iter().map(|t| t.target));
                incoming_edges
                    .entry(*ok_target)
                    .or_default()
                    .push((block.id, Some(*ok_slot)));
                for target in err_targets {
                    incoming_edges
                        .entry(target.target)
                        .or_default()
                        .push((block.id, None));
                }
            }
            Terminator::Return(_) | Terminator::Raise { .. } => {}
        }
    }

    let mut reachable: HashSet<BlockId> = HashSet::from([entry]);
    let mut frontier = vec![entry];
    while let Some(id) = frontier.pop() {
        for &succ in successors.get(&id).into_iter().flatten() {
            if reachable.insert(succ) {
                frontier.push(succ);
            }
        }
    }

    // Marks `raw`'s own underlying resource as used at this point:
    // records a violation if its origin is already in `facts`, and
    // reports whether that origin was newly consumed here (the caller
    // decides whether this particular use is itself consuming). A
    // consuming use also discharges `raw`'s own leak obligation, if it
    // is still tracked as `live` -- exactly the same origin identity as
    // `facts`, so a value already reported as a use-after-consume
    // violation is never *also* reported as leaked (it has an owner: an
    // erroneous second one).
    fn check_use(
        raw: ValueId,
        is_resource: &impl Fn(ValueId) -> bool,
        origin: &impl Fn(ValueId) -> ValueId,
        facts: &mut HashSet<ValueId>,
        live: &mut HashSet<ValueId>,
        violations: &mut Vec<ValueId>,
        consumes: bool,
    ) {
        if !is_resource(raw) {
            return;
        }
        let o = origin(raw);
        if facts.contains(&o) {
            violations.push(o);
        } else if consumes {
            facts.insert(o);
        }
        if consumes {
            live.remove(&o);
        }
    }

    // `merge_location`/`merge_provenance` are module-level too (see
    // above `verify_resource_ownership`'s own doc comment).

    // `State` pairs `facts` (`RESOURCE_USE_AFTER_CONSUME`'s own already-
    // consumed set), `live` (`RESOURCE_LEAKED_ON_EXIT`'s own currently-
    // owned-and-not-yet-discharged set), `dropped_origins` (every
    // resource identity actually destroyed by a real `Drop` reaching
    // this point, for `RESOURCE_ORIGIN_CONFLICT`), and `provenance`
    // (every value/slot's own current definite-initialization state,
    // for all three of the above) -- computed together, by the same
    // single forward walk, since a consuming use always updates more
    // than one at once.
    type State = (
        HashSet<ValueId>,
        HashSet<ValueId>,
        HashSet<ValueId>,
        HashMap<ValueId, LocationState>,
    );

    // `(new_state, use_after_consume_violations, leaks, role_violations,
    // origin_conflicts, uninitialized_uses)`.
    type TransferResult = (
        State,
        Vec<ValueId>,
        Vec<ValueId>,
        Vec<RoleViolation>,
        Vec<ValueId>,
        Vec<ValueId>,
    );

    let transfer = |block: &BasicBlock, in_state: &State| -> TransferResult {
        let (mut facts, mut live, mut dropped_origins, mut provenance) = in_state.clone();
        let mut violations = Vec::new();
        let mut role_violations = Vec::new();
        let mut origin_conflicts = Vec::new();
        let mut uninitialized_uses = Vec::new();
        // A `take`/`Invoke` argument, `Move`/`DeferCapture` source,
        // `Drop`/`store.transfer` operand, or `return`/`raise` operand
        // must be definitely initialized and `Owned`; every use,
        // consuming or not, is checked against both that and
        // `dropped_origins`. A rejected consuming use is treated as
        // non-consuming below, so it never mutates `facts`/`live` as
        // though it had legitimately succeeded.
        macro_rules! alias_safe {
            ($raw:expr, $consumes:expr, $store_mode:expr) => {
                check_alias_safety(
                    $raw,
                    &provenance,
                    &dropped_origins,
                    $consumes,
                    $store_mode,
                    &mut uninitialized_uses,
                    &mut origin_conflicts,
                    &mut role_violations,
                )
            };
        }
        for instruction in &block.instructions {
            match instruction {
                Instruction::Value { result, kind, .. } => {
                    // A loop-carried temporary reuses one fixed `ValueId`
                    // across iterations; this instruction's own
                    // redefinition kills whatever a previous iteration
                    // left behind for it, exactly like `verify_drop_state`
                    // already does for `Drop`. `dropped_origins` needs
                    // the same reset: a fresh construction reusing this
                    // exact `ValueId` as its own self-identity must not
                    // inherit a stale "already destroyed" poison left by
                    // a *previous* iteration's own distinct resource,
                    // reached again only because the back-edge revisits
                    // this same static instruction.
                    facts.remove(result);
                    live.remove(result);
                    dropped_origins.remove(result);
                    provenance.remove(result);
                    match kind {
                        ValueKind::Call(callee, _, args, _) => {
                            let take = known_functions.get(callee).map(|f| f.take.as_slice());
                            for (i, arg) in args.iter().enumerate() {
                                let consumes = consumes_arg(take, args.len(), i);
                                let legal = alias_safe!(*arg, consumes, false);
                                check_use(
                                    *arg,
                                    &is_resource,
                                    &origin,
                                    &mut facts,
                                    &mut live,
                                    &mut violations,
                                    consumes && legal,
                                );
                            }
                        }
                        // Every affine field argument is unconditionally
                        // transferred into the fresh aggregate
                        // (`rfcs/0012`): there is no "observing" record/
                        // resource construction, exactly like `Move`/
                        // `DeferCapture` have no non-consuming shape --
                        // a non-affine field is simply never resource-
                        // typed at all, so `check_use` below is already
                        // a no-op for it (`is_resource` gates it).
                        ValueKind::RecordCreate(_, _, fields) => {
                            for field in fields {
                                let legal = alias_safe!(*field, true, false);
                                check_use(
                                    *field,
                                    &is_resource,
                                    &origin,
                                    &mut facts,
                                    &mut live,
                                    &mut violations,
                                    legal,
                                );
                            }
                        }
                        // Every affine payload value is unconditionally
                        // transferred into the fresh variant (`rfcs/
                        // 0012`), for the identical reason `RecordCreate`
                        // just above is: there is no "observing" variant
                        // construction either.
                        ValueKind::VariantCreate { payload, .. } => {
                            for value in payload {
                                let legal = alias_safe!(*value, true, false);
                                check_use(
                                    *value,
                                    &is_resource,
                                    &origin,
                                    &mut facts,
                                    &mut live,
                                    &mut violations,
                                    legal,
                                );
                            }
                        }
                        // Always an unconditional transfer (`rfcs/0011`)
                        // -- unlike a `Call` argument, whose own
                        // consumption depends on the callee's own
                        // declared `take` flag, `Move`/`DeferCapture`
                        // exist *only* to represent "this exact operand
                        // is consumed here," so there is no non-
                        // consuming shape of either to fall back to.
                        // `non_resource_moves` (below) independently
                        // rejects the malformed shape where `source`
                        // isn't even resource-typed, which `check_use`
                        // itself would otherwise just silently ignore.
                        ValueKind::Move { source } | ValueKind::DeferCapture { source } => {
                            let legal = alias_safe!(*source, true, false);
                            check_use(
                                *source,
                                &is_resource,
                                &origin,
                                &mut facts,
                                &mut live,
                                &mut violations,
                                legal,
                            );
                            // Ownership relocates to `result`, which
                            // keeps sharing `source`'s own true resource
                            // identity (so a later `Drop` reachable
                            // through *either* is recognized as the same
                            // resource) -- but only actually becomes
                            // `Owned` if this move was itself legal; a
                            // rejected attempt must never launder an
                            // `Observed` value into an owner.
                            if is_resource(*source) {
                                let ids = resolve_ids(*source, &provenance);
                                provenance.insert(
                                    *result,
                                    LocationState::Initialized((
                                        ids,
                                        if legal { Role::Owned } else { Role::Observed },
                                    )),
                                );
                            }
                        }
                        // A structural place read never consumes its own
                        // `place.root` at the whole-value level at all
                        // (`rfcs/0012`) -- unlike `Move`, `root` is not
                        // itself the value being transferred, only the
                        // aggregate reached *through*; `check_alias_
                        // safety`/`resourceck::flow`'s own separate
                        // structural pass (`verify_structural_places`)
                        // are what actually gate whether `place` itself
                        // was live to read/move at all. `result` mints a
                        // fresh identity (there is nothing at this
                        // pass's own whole-value granularity to inherit
                        // one from): `Owned`, and newly `live`, for a
                        // `Transfer` (a genuine new obligation this
                        // frame now owns); `Observed`, and never `live`,
                        // for an `Observe` -- exactly like `Load`'s own
                        // exclusion from the fresh-ownership rule below,
                        // just explicit here since a place read is
                        // neither `Load` nor `Alloc`.
                        ValueKind::PlaceRead { mode, .. } => {
                            if is_resource(*result) {
                                let role = match mode {
                                    crate::nir::OwnershipMode::Transfer => Role::Owned,
                                    crate::nir::OwnershipMode::Observe => Role::Observed,
                                };
                                provenance.insert(
                                    *result,
                                    LocationState::Initialized((BTreeSet::from([*result]), role)),
                                );
                                if *mode == crate::nir::OwnershipMode::Transfer {
                                    live.insert(*result);
                                }
                            }
                        }
                        _ => {
                            for operand in operands_of(kind) {
                                alias_safe!(operand, false, false);
                                check_use(
                                    operand,
                                    &is_resource,
                                    &origin,
                                    &mut facts,
                                    &mut live,
                                    &mut violations,
                                    false,
                                );
                            }
                        }
                    }
                    // A `Load`'s own result shares its slot's *current*
                    // state exactly -- an observing slot's own loaded
                    // alias is `Observed`, sharing the same resource
                    // identity as whatever was observingly stored there,
                    // never a fresh identity of its own (the actual fix
                    // this check exists for: without it, an alias loaded
                    // from an observing store had no recorded connection
                    // back to the value it aliases at all). The slot's
                    // own `uninitialized_uses` check already ran above
                    // (`Load(slot)`'s own operand, via the catch-all
                    // `alias_safe!` loop) -- a not-definitely-initialized
                    // load propagates nothing further, rather than
                    // fabricating an owner for its own result.
                    if let ValueKind::Load(slot) = kind
                        && let LocationState::Initialized(prov) = resolve_state(*slot, &provenance)
                    {
                        provenance.insert(*result, LocationState::Initialized(prov));
                    }
                    // `Alloc` reserves a slot with nothing stored into it
                    // yet (`rfcs/0011`) -- definitely `Uninitialized`,
                    // never a lenient fresh owner, so a `Load` reaching
                    // this exact slot before any reachable `Store`
                    // writes it is independently rejected
                    // (`RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED`).
                    if matches!(kind, ValueKind::Alloc) && is_resource(*result) {
                        provenance.insert(*result, LocationState::Uninitialized);
                    }
                    // Every resource-typed value definition other than a
                    // `Load` (which aliases its own slot's already-
                    // tracked identity, never a fresh one) or an `Alloc`
                    // (which only reserves a slot -- nothing has been
                    // stored into it yet, so there is nothing live at
                    // this point) brings a freshly owned resource into
                    // this function's own care: a direct construction,
                    // or one an ordinary (non-`Invoke`) call transferred
                    // in as its return value (`rfcs/0011`). `Move`/
                    // `DeferCapture` already recorded their own result's
                    // provenance above (propagated from `source`), so
                    // they are excluded here to avoid overwriting it
                    // with a fresh, decoupled self-identity. `Invoke`'s
                    // own `ok_slot` is deliberately excluded here -- it
                    // is never a `Value` result at all, and this block-
                    // local pass has no notion of *which* edge it is
                    // running on -- but it is not left untracked: `in_
                    // state_for`'s own `incoming_edges` seeds it as
                    // newly live specifically on the one block reached
                    // through the `Invoke`'s own `ok_target` edge, never
                    // on any block reached only through one of its
                    // `err_targets` (the same edge-sensitivity `verify_
                    // invoke_slot_initialization` already needs for
                    // V0073, for the same underlying reason: ordinary
                    // union-of-predecessors dataflow keyed only by
                    // target block cannot otherwise distinguish the two
                    // edges when they happen to share a target).
                    if is_resource(*result)
                        && !matches!(
                            kind,
                            ValueKind::Load(_) | ValueKind::Alloc | ValueKind::PlaceRead { .. }
                        )
                    {
                        live.insert(*result);
                        if !matches!(
                            kind,
                            ValueKind::Move { .. } | ValueKind::DeferCapture { .. }
                        ) {
                            provenance.insert(
                                *result,
                                LocationState::Initialized((
                                    BTreeSet::from([*result]),
                                    Role::Owned,
                                )),
                            );
                        }
                    }
                }
                Instruction::Store { slot, value, mode } => {
                    let transfers = matches!(mode, crate::nir::OwnershipMode::Transfer);
                    let legal = alias_safe!(*value, transfers, transfers);
                    check_use(
                        *value,
                        &is_resource,
                        &origin,
                        &mut facts,
                        &mut live,
                        &mut violations,
                        transfers && legal,
                    );
                    // A fresh value now occupies `slot`; whatever
                    // consumption/liveness its own prior occupant
                    // carried no longer applies (`resourceck`'s own
                    // `U0010` already rejects overwriting a still-live
                    // resource).
                    facts.remove(slot);
                    live.remove(slot);
                    provenance.remove(slot);
                    // A transferring store relocates its own value's
                    // leak-tracking identity onto the slot it now
                    // occupies -- every later `Load` of this exact slot
                    // already shares that slot's own identity (`origin`,
                    // above), so its own obligation must live there too,
                    // not stay pinned to wherever it was first defined
                    // (`check_use`, just above, already removed it from
                    // `live` as part of consuming it). An *observing*
                    // store never relocates anything: `value` remains
                    // independently live (and independently droppable)
                    // through its own original identity, and the slot
                    // itself never becomes an owner of anything -- the
                    // explicit `mode` on `Store` is `resourceck`'s own
                    // already-checked decision, never a guess `nir::
                    // verify` derives from how many times `value` is
                    // used elsewhere. Either way, `slot` shares `value`'s
                    // own true resource identity from now on -- `Owned`
                    // for a legal transfer, `Observed` for an
                    // observation (regardless of `value`'s own role: an
                    // observing store is always a merely-observing
                    // window, even onto an owned value), so a later
                    // `Load` of `slot` correctly inherits it.
                    if is_resource(*value) {
                        let ids = resolve_ids(*value, &provenance);
                        let role = if transfers && legal {
                            Role::Owned
                        } else {
                            Role::Observed
                        };
                        provenance.insert(*slot, LocationState::Initialized((ids, role)));
                    }
                    if transfers && legal && is_resource(*value) {
                        live.insert(*slot);
                    }
                }
                Instruction::Drop { value } => {
                    let legal = alias_safe!(*value, true, false);
                    check_use(
                        *value,
                        &is_resource,
                        &origin,
                        &mut facts,
                        &mut live,
                        &mut violations,
                        legal,
                    );
                    // A legally-dropped resource's own true identity is
                    // now dangling for every *other* alias that shares
                    // it, not only the one that performed this drop
                    // (`RESOURCE_ORIGIN_CONFLICT`) -- an illegal attempt
                    // (rejected just above) destroys nothing.
                    if legal && is_resource(*value) {
                        let ids = resolve_ids(*value, &provenance);
                        dropped_origins.extend(ids);
                    }
                }
                // `StorePlace` always transfers `value` into a
                // structural field (`rfcs/0012`) -- consumed here
                // exactly like an ordinary transferring `Store`'s own
                // operand is, but with no slot of its own to relocate
                // `value`'s own identity onto: a projected place is
                // never a key in this pass's own whole-value
                // `provenance` map at all (see [`verify_structural_
                // places`], the dedicated pass that tracks each place's
                // own move/reinit state instead).
                Instruction::StorePlace { value, .. } => {
                    let legal = alias_safe!(*value, true, false);
                    check_use(
                        *value,
                        &is_resource,
                        &origin,
                        &mut facts,
                        &mut live,
                        &mut violations,
                        legal,
                    );
                }
                // Reads the shell without consuming it: the payload it
                // hands over is tracked as its own value by this pass
                // already, from its own `VariantPayload` definition.
                // The structural place this moves is `verify_structural_
                // places`' own concern, not this whole-value lattice's.
                Instruction::DecomposeVariant { value, .. } => {
                    let legal = alias_safe!(*value, false, false);
                    check_use(
                        *value,
                        &is_resource,
                        &origin,
                        &mut facts,
                        &mut live,
                        &mut violations,
                        legal,
                    );
                }
            }
        }
        match &block.terminator {
            Terminator::Return(Some(value)) => {
                let legal = alias_safe!(*value, true, false);
                check_use(
                    *value,
                    &is_resource,
                    &origin,
                    &mut facts,
                    &mut live,
                    &mut violations,
                    legal,
                );
            }
            Terminator::Raise { value } => {
                let legal = alias_safe!(*value, true, false);
                check_use(
                    *value,
                    &is_resource,
                    &origin,
                    &mut facts,
                    &mut live,
                    &mut violations,
                    legal,
                );
            }
            Terminator::Invoke { callee, args, .. } => {
                let take = known_functions.get(callee).map(|f| f.take.as_slice());
                for (i, arg) in args.iter().enumerate() {
                    let consumes = consumes_arg(take, args.len(), i);
                    let legal = alias_safe!(*arg, consumes, false);
                    check_use(
                        *arg,
                        &is_resource,
                        &origin,
                        &mut facts,
                        &mut live,
                        &mut violations,
                        consumes && legal,
                    );
                }
            }
            // Matching an affine scrutinee decomposes it (`rfcs/0012`):
            // `resourceck::flow` already treats this the same way,
            // transferring the scrutinee's own place the moment a
            // `match`/`handle` runs, rather than leaving it live for its
            // own separate implicit cleanup to (wrongly) also try to
            // destroy the very payload a pattern binding already took.
            Terminator::Switch { scrutinee, .. } => {
                let legal = alias_safe!(*scrutinee, true, false);
                check_use(
                    *scrutinee,
                    &is_resource,
                    &origin,
                    &mut facts,
                    &mut live,
                    &mut violations,
                    legal,
                );
            }
            Terminator::Return(None) | Terminator::Branch(_) | Terminator::CondBranch { .. } => {}
        }
        // Every reachable `Return`/`Raise` is a real exit this function
        // takes: whatever is still `live` right here was created (or
        // transferred in) somewhere on this exact path and never
        // destroyed or transferred back out (`rfcs/0011`) -- a leak.
        // `Invoke`'s own args are already fully handled above (as
        // ownership-transferring or not); it is never itself a function
        // exit, so it contributes no leaks of its own.
        let leaks = match &block.terminator {
            Terminator::Return(_) | Terminator::Raise { .. } => {
                // Sorted, not the raw `HashSet` iteration order: two
                // resources leaked in the same block must always be
                // reported in the same order across runs, never
                // dependent on this process's own random hash seed.
                let mut leaks: Vec<ValueId> = live.iter().copied().collect();
                leaks.sort_unstable();
                leaks
            }
            _ => Vec::new(),
        };
        (
            (facts, live, dropped_origins, provenance),
            violations,
            leaks,
            role_violations,
            origin_conflicts,
            uninitialized_uses,
        )
    };

    fn in_state_for(
        block_id: BlockId,
        entry: BlockId,
        entry_seed: (&HashSet<ValueId>, &HashMap<ValueId, LocationState>),
        incoming_edges: &HashMap<BlockId, Vec<(BlockId, Option<ValueId>)>>,
        reachable: &HashSet<BlockId>,
        out: &HashMap<BlockId, State>,
        is_resource: &impl Fn(ValueId) -> bool,
    ) -> IncomingState<State> {
        if block_id == entry {
            // Every `take`-flagged resource parameter is already live the
            // moment this function begins -- an entry block that itself
            // exits directly (no successors at all) must still be
            // checked against that seed, not empty state (only `out`,
            // used to propagate *past* the entry block to its own
            // successors, needs it folded in separately -- see
            // `entry_out`, below).
            let (entry_live, entry_provenance) = entry_seed;
            return IncomingState::Entry((
                HashSet::new(),
                entry_live.clone(),
                HashSet::new(),
                entry_provenance.clone(),
            ));
        }
        let Some(edges) = incoming_edges.get(&block_id) else {
            return IncomingState::Pending;
        };
        // A predecessor the worklist has never actually run `transfer`
        // on yet contributes nothing to this merge at all -- not the
        // same thing as a *computed* predecessor definitively lacking a
        // given key (`Uninitialized`, correctly downgrading a join to
        // `MaybeUninitialized`). Conflating the two would corrupt the
        // fixpoint irrecoverably: `LocationState::MaybeUninitialized` is
        // an absorbing state `merge_location` never upgrades back out
        // of, so treating an as-yet-unprocessed loop back-edge as if it
        // had already *proven* a key uninitialized -- purely because the
        // worklist has not reached it yet -- would permanently poison
        // every block downstream of it, regardless of what that
        // predecessor's own eventually-computed state actually turns
        // out to be. Excluding an uncomputed predecessor here lets the
        // fixpoint converge on each edge's own real contribution once,
        // and only once, it is actually known.
        //
        // "Computed" is the presence of an `out` entry, and nothing
        // else: `out` holds a block only once `transfer` has actually
        // produced its state, so the two can never drift apart.
        // Yields each usable edge together with the out-state it
        // carries, so there is no second lookup that could ever need a
        // default standing in for a state.
        let mut edges = edges.iter().filter_map(|(pred, extra)| {
            if !reachable.contains(pred) {
                return None;
            }
            out.get(pred).map(|state| (state, extra))
        });
        let Some((first_state, first_extra)) = edges.next() else {
            // Nothing has been proven about this block yet. That is not
            // an empty state: an empty `provenance` map disagrees with
            // every real one, and `merge_provenance` reads disagreement
            // as the absorbing `MaybeUninitialized` it never recovers
            // from -- so recording a state here would poison an entire
            // loop permanently, and did, depending on nothing but the
            // order the block vector happened to list its blocks in.
            return IncomingState::Pending;
        };
        // Union, not intersection, matching `verify_drop_state`: a
        // resource already consumed (or still live) on *any* reachable
        // predecessor path is a live hazard the moment this path's own
        // next use -- or exit -- runs. `extra`, when present, is an
        // `Invoke`'s own `ok_slot` -- newly live (and newly `Owned`) on
        // that block's own success edge alone, never folded into any
        // sibling failure edge that happens to reach this same block
        // (`rfcs/0011`).
        let mut acc = first_state.clone();
        if let Some(slot) = first_extra
            && is_resource(*slot)
        {
            acc.1.insert(*slot);
            acc.3.insert(
                *slot,
                LocationState::Initialized((BTreeSet::from([*slot]), Role::Owned)),
            );
        }
        for (state, extra) in edges {
            let (other_facts, mut other_live, other_dropped, mut other_prov) = state.clone();
            if let Some(slot) = extra
                && is_resource(*slot)
            {
                other_live.insert(*slot);
                other_prov.insert(
                    *slot,
                    LocationState::Initialized((BTreeSet::from([*slot]), Role::Owned)),
                );
            }
            acc.0.extend(other_facts);
            acc.1.extend(other_live);
            acc.2.extend(other_dropped);
            acc.3 = merge_provenance(&acc.3, &other_prov);
        }
        IncomingState::Ready(acc)
    }

    // Every `take`-flagged resource parameter is already owned the
    // moment this function begins (`rfcs/0011`): if it is never
    // destroyed or transferred back out on some reachable exit, that
    // exit leaks it exactly like an unfreed local construction would.
    // An ordinary (non-`take`) resource parameter is already `Observed`
    // from the moment this function begins too -- a call-scoped
    // observation that never owned anything to begin with, exactly like
    // one loaded from an observing store never does.
    let mut entry_live: HashSet<ValueId> = HashSet::new();
    let mut entry_provenance: HashMap<ValueId, LocationState> = HashMap::new();
    for param in &function.params {
        if !is_resource(param.value) {
            continue;
        }
        if param.take {
            entry_live.insert(param.value);
            entry_provenance.insert(
                param.value,
                LocationState::Initialized((BTreeSet::from([param.value]), Role::Owned)),
            );
        } else {
            entry_provenance.insert(
                param.value,
                LocationState::Initialized((BTreeSet::from([param.value]), Role::Observed)),
            );
        }
    }

    let entry_block = function
        .blocks
        .iter()
        .find(|b| b.id == entry)
        .expect("presence already checked above");
    let (entry_out, ..) = transfer(
        entry_block,
        &(
            HashSet::new(),
            entry_live.clone(),
            HashSet::new(),
            entry_provenance.clone(),
        ),
    );

    // `out` holds a block *only once its own out-state has actually
    // been computed*: "not computed yet" is the absence of a key, and
    // is therefore impossible to confuse with a block genuinely
    // computed to hold no facts. Pre-seeding every block with
    // `State::default()` (as this once did) erases exactly that
    // distinction, and an empty state is not this lattice's bottom --
    // an empty `provenance` map disagrees with every real one, and
    // `merge_provenance` reads disagreement as the absorbing
    // `MaybeUninitialized` it never recovers from.
    //
    // The entry block is the one boundary condition: its in-state is
    // the parameter seed by definition, so its out-state is fixed and
    // never recomputed.
    let mut out: HashMap<BlockId, State> = HashMap::from([(entry, entry_out)]);

    let mut worklist: VecDeque<BlockId> = function
        .blocks
        .iter()
        .map(|b| b.id)
        .filter(|id| *id != entry && reachable.contains(id))
        .collect();
    let mut queued: HashSet<BlockId> = worklist.iter().copied().collect();
    while let Some(id) = worklist.pop_front() {
        queued.remove(&id);
        let Some(block) = function.blocks.iter().find(|b| b.id == id) else {
            continue;
        };
        let in_state = match in_state_for(
            id,
            entry,
            (&entry_live, &entry_provenance),
            &incoming_edges,
            &reachable,
            &out,
            &is_resource,
        ) {
            IncomingState::Entry(state) | IncomingState::Ready(state) => state,
            // Nothing has proven anything about this block yet, so it
            // runs no transfer and records no out-state. A predecessor
            // landing later re-enqueues it, and every reachable block
            // is reached from the entry, whose out-state is fixed
            // before this loop starts.
            IncomingState::Pending => continue,
        };
        let (new_out, ..) = transfer(block, &in_state);
        // An `out` entry appearing for the first time is itself a
        // change: `out.get(&id)` is `None` until then, so successors
        // are re-queued exactly when this block first becomes joinable.
        if out.get(&id) != Some(&new_out) {
            out.insert(id, new_out);
            for &succ in successors.get(&id).into_iter().flatten() {
                if succ != entry && reachable.contains(&succ) && queued.insert(succ) {
                    worklist.push_back(succ);
                }
            }
        }
    }

    for block in &function.blocks {
        let in_state = if reachable.contains(&block.id) {
            match in_state_for(
                block.id,
                entry,
                (&entry_live, &entry_provenance),
                &incoming_edges,
                &reachable,
                &out,
                &is_resource,
            ) {
                IncomingState::Entry(state) | IncomingState::Ready(state) => state,
                // The fixpoint above has converged, so every reachable
                // block has a computed predecessor by now. Judging
                // ownership from a state nothing proved would be
                // guesswork, so the block is skipped rather than
                // fabricated.
                IncomingState::Pending => continue,
            }
        } else {
            State::default()
        };
        let (_, violations, leaks, role_violations, origin_conflicts, uninitialized_uses) =
            transfer(block, &in_state);
        for origin_value in violations {
            diagnostics.push(Diagnostic::error(
                codes::RESOURCE_USE_AFTER_CONSUME,
                source,
                Span::dummy(),
                format!(
                    "function `{function_name}` uses a resource in bb{} whose underlying value (%{}) was already consumed on some path reaching it",
                    block.id.0, origin_value.0
                ),
            ));
        }
        for origin_value in leaks {
            diagnostics.push(Diagnostic::error(
                codes::RESOURCE_LEAKED_ON_EXIT,
                source,
                Span::dummy(),
                format!(
                    "function `{function_name}` exits in bb{} while still owning a resource (%{}) that was never destroyed or transferred out",
                    block.id.0, origin_value.0
                ),
            ));
        }
        for violation in role_violations {
            let (code, value) = match violation {
                RoleViolation::Consumed(v) => (codes::RESOURCE_OBSERVER_CONSUMED, v),
                RoleViolation::StoreMode(v) => (codes::INVALID_RESOURCE_STORE_MODE, v),
            };
            diagnostics.push(Diagnostic::error(
                code,
                source,
                Span::dummy(),
                format!(
                    "function `{function_name}` uses a merely-observing resource value (%{}) in bb{} where only an owner may be used",
                    value.0, block.id.0
                ),
            ));
        }
        for value in origin_conflicts {
            diagnostics.push(Diagnostic::error(
                codes::RESOURCE_ORIGIN_CONFLICT,
                source,
                Span::dummy(),
                format!(
                    "function `{function_name}` uses a resource (%{}) in bb{} whose underlying identity was already destroyed through a different alias on some path reaching it",
                    value.0, block.id.0
                ),
            ));
        }
        for value in uninitialized_uses {
            diagnostics.push(Diagnostic::error(
                codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED,
                source,
                Span::dummy(),
                format!(
                    "function `{function_name}` uses a resource (%{}) in bb{} that is not definitely initialized on every path reaching it",
                    value.0, block.id.0
                ),
            ));
        }
    }

    for (result, label) in non_resource_moves {
        diagnostics.push(Diagnostic::error(
            codes::MOVE_SOURCE_NOT_RESOURCE,
            source,
            Span::dummy(),
            format!(
                "function `{function_name}`: %{} is a `{label}` of a value that is not resource-typed; only a resource may be moved",
                result.0
            ),
        ));
    }
}

/// One structural place's own current "does it still hold its own
/// value" status (`rfcs/0012`) -- see [`verify_structural_places`]'s own
/// doc comment for the full three-state lattice this forms.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum FieldState {
    Full,
    Empty,
    Maybe,
}

/// The pairwise lattice meet two reachable predecessors' own
/// [`FieldState`] for the identical structural place join to: agreement
/// keeps that state, disagreement (including either side already being
/// the absorbing [`FieldState::Maybe`]) always joins to `Maybe` -- never
/// silently favors one side over the other, matching `LocationState`'s
/// own identical three-state shape (this one just has no separate
/// origin/role payload to carry along).
fn merge_field(a: FieldState, b: FieldState) -> FieldState {
    match (a, b) {
        (FieldState::Full, FieldState::Full) => FieldState::Full,
        (FieldState::Empty, FieldState::Empty) => FieldState::Empty,
        _ => FieldState::Maybe,
    }
}

/// Every structural place fact one program point holds, keyed by the
/// exact [`Place`] (`rfcs/0012`). A key absent here is *not* a missing
/// answer: it is the initial, untouched [`FieldState::Full`], which is
/// exactly what a freshly constructed aggregate's own fields all start
/// as. Facts are always read back through [`resolve_place_state`]/
/// [`place_is_whole`], never a bare `get`, so an ancestor's own state
/// always dominates its descendants' and a consumed descendant always
/// makes its ancestors partial.
type PlaceFacts = HashMap<Place<ValueId>, FieldState>;

/// This place's own effective state within one structural ownership
/// lattice (`rfcs/0012`): the *shortest* ancestor prefix (including
/// itself) recorded as anything other than `Full`, or `Full` when no
/// prefix was ever touched at all.
///
/// This is what makes moving or dropping a parent consume its entire
/// descendant subtree, whether or not each descendant ever got a key of
/// its own -- a child read after its parent was transferred or dropped
/// is rejected by exactly the same check a child read after its *own*
/// transfer is. Walks a bounded prefix chain in a fixed order, so no
/// `HashMap` iteration order can affect the answer.
fn resolve_place_state(facts: &PlaceFacts, place: &Place<ValueId>) -> FieldState {
    for len in 0..=place.projections.len() {
        let prefix = Place {
            root: place.root,
            projections: place.projections[..len].to_vec(),
        };
        match facts.get(&prefix) {
            Some(FieldState::Full) | None => {}
            Some(state) => return *state,
        }
    }
    FieldState::Full
}

/// `true` iff `place` itself *and* every place reachable through it
/// still hold their own values -- what a *whole-value* use requires
/// (`rfcs/0012`): observed, transferred, returned, raised, or consumed
/// into an aggregate. A parent with a moved-out child fails this while
/// still passing [`resolve_place_state`], which is precisely the
/// difference between "you may not use this as a value" and "you may
/// still reach an unaffected sibling through it, reinitialize an empty
/// child, or structurally drop what remains". A boolean `any`, so
/// `facts`' own iteration order cannot affect the answer.
fn place_is_whole(facts: &PlaceFacts, place: &Place<ValueId>) -> bool {
    if resolve_place_state(facts, place) != FieldState::Full {
        return false;
    }
    !facts
        .iter()
        .any(|(key, state)| key != place && place.is_ancestor_of(key) && *state != FieldState::Full)
}

/// Records `place`'s own new leaf state, first clearing every strictly
/// deeper key it now supersedes -- consuming or restoring a place
/// settles everything reachable through it, so a stale finer-grained
/// fact recorded before this point must never be consulted again.
/// Reinitializing an empty child through this is exactly what restores
/// its ancestors' own completeness.
fn set_place_state(facts: &mut PlaceFacts, place: &Place<ValueId>, state: FieldState) {
    facts.retain(|key, _| key == place || !place.is_ancestor_of(key));
    facts.insert(place.clone(), state);
}

/// One structural ownership violation, recorded during a block's own
/// transfer and reported once afterwards, so the dataflow fixpoint
/// never reports the same instruction twice (`rfcs/0012`).
#[derive(Clone, Copy)]
enum OwnershipViolation {
    /// A place read or moved where it is not definitely still holding
    /// its own value -- including a child reached through an ancestor
    /// already transferred or dropped.
    UseAfterMove(ValueId),
    /// A `StorePlace` targeting a place that is not definitely empty.
    OverwriteLive(ValueId),
    /// A place used as a *whole* value while one of its own affine
    /// descendants is already consumed.
    PartialWhole(ValueId),
    /// A whole-value destruction or transfer of something already
    /// consumed on a path reaching it: structural double cleanup.
    DoubleCleanup(ValueId),
    /// A variant decomposition that leaves at least one affine payload
    /// position of its own live case unclaimed -- a resource the shell
    /// no longer owns and nothing else does either.
    IncompleteDecomposition(ValueId),
}

/// Path-sensitive structural ownership verification (`rfcs/0012`),
/// independent of `resourceck` and reconstructed from NIR alone -- so
/// hand-built NIR that never passed source checking is rejected on
/// exactly the same terms as lowered NIR.
///
/// Complements [`verify_resource_ownership`], which tracks every *whole*
/// nominally-resource value's own provenance, role and aliasing. This
/// pass owns the two things that lattice deliberately does not model:
/// the place *tree* (see [`resolve_place_state`]/[`place_is_whole`]),
/// and the cleanup obligation of a *transitively* affine record, which
/// is never itself a nominal resource and so is never a key there at
/// all. The two never report the same value: the missing-cleanup check
/// below deliberately skips every root the other pass already owns.
///
/// Uses the identical reachable-union worklist shape, with the identical
/// `computed`-set fixpoint discipline `RESOURCE_LOCATION_NOT_DEFINITELY_
/// INITIALIZED`'s own fix required: an as-yet-unprocessed loop back-edge
/// predecessor contributes nothing to a join, and is never mistaken for
/// a *computed* predecessor that has definitively proven a place
/// consumed. A join takes the union of both sides' keys -- so a place
/// touched on only one predecessor still joins to `Maybe` against the
/// other's implicit `Full` -- which is what makes the result
/// independent of predecessor discovery order, block vector order and
/// `HashMap` order alike.
#[allow(clippy::too_many_arguments)]
fn verify_structural_places(
    function: &Function,
    value_types: &HashMap<ValueId, Ty>,
    known_functions: &HashMap<ItemId, KnownFunction>,
    agg: &AggregateContext,
    source: SourceId,
    function_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let entry = BlockId(0);
    if !function.blocks.iter().any(|b| b.id == entry) {
        return;
    }

    let mut successors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    let mut incoming_edges: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for block in &function.blocks {
        match &block.terminator {
            Terminator::Branch(target) => {
                successors.entry(block.id).or_default().push(*target);
                incoming_edges.entry(*target).or_default().push(block.id);
            }
            Terminator::CondBranch {
                then_block,
                else_block,
                ..
            } => {
                successors
                    .entry(block.id)
                    .or_default()
                    .extend([*then_block, *else_block]);
                incoming_edges
                    .entry(*then_block)
                    .or_default()
                    .push(block.id);
                incoming_edges
                    .entry(*else_block)
                    .or_default()
                    .push(block.id);
            }
            Terminator::Switch { cases, .. } => {
                successors.entry(block.id).or_default().extend(cases);
                for target in cases {
                    incoming_edges.entry(*target).or_default().push(block.id);
                }
            }
            Terminator::Invoke {
                ok_target,
                err_targets,
                ..
            } => {
                successors.entry(block.id).or_default().push(*ok_target);
                successors
                    .entry(block.id)
                    .or_default()
                    .extend(err_targets.iter().map(|t| t.target));
                incoming_edges.entry(*ok_target).or_default().push(block.id);
                for target in err_targets {
                    incoming_edges
                        .entry(target.target)
                        .or_default()
                        .push(block.id);
                }
            }
            Terminator::Return(_) | Terminator::Raise { .. } => {}
        }
    }

    let mut reachable: HashSet<BlockId> = HashSet::from([entry]);
    let mut frontier = vec![entry];
    while let Some(id) = frontier.pop() {
        for &succ in successors.get(&id).into_iter().flatten() {
            if reachable.insert(succ) {
                frontier.push(succ);
            }
        }
    }

    // Every `Load`'s own result shares its own place-tracking identity
    // with the slot it loads from (`rfcs/0012`): a `mutable` local
    // reloads its own current whole value fresh, as a *new* `ValueId`,
    // every time a place projects into it (`session.input`, then later
    // `session.output`, are two entirely separate `Load(%slot)`
    // results) -- without canonicalizing back to the one shared slot
    // they both actually reach into, two places that are structurally
    // the very same field would never compare equal here at all,
    // breaking every one of this pass's own checks for it.
    let mut load_origin: HashMap<ValueId, ValueId> = HashMap::new();
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value {
                result,
                kind: ValueKind::Load(slot),
                ..
            } = instruction
            {
                load_origin.insert(*result, *slot);
            }
        }
    }
    let origin = |v: ValueId| -> ValueId { load_origin.get(&v).copied().unwrap_or(v) };
    let canonical = |place: &Place<ValueId>| -> Place<ValueId> {
        Place {
            root: origin(place.root),
            projections: place.projections.clone(),
        }
    };

    // Whether a `Call`/`Invoke` argument at index `i` transfers
    // ownership -- structural malformation is handled conservatively
    // (every argument treated as consumed), for the identical reason
    // `verify_resource_ownership`'s own copy of this is: wrongly
    // assuming a mere observation could let a value an unknown callee
    // actually took ownership of keep looking live afterwards.
    let consumes_arg = |take: Option<&[bool]>, args_len: usize, i: usize| -> bool {
        match take {
            Some(flags) if flags.len() == args_len => flags.get(i).copied().unwrap_or(true),
            _ => true,
        }
    };

    // Deliberately *transitive*, never nominal `is_resource`: an affine
    // record or variant owns real resources, and is exactly what this
    // pass exists to track. An ordinary, freely-copyable value never
    // enters this lattice at all.
    let is_affine =
        |v: ValueId| -> bool { value_types.get(&v).is_some_and(|ty| is_affine_in(ty, agg)) };

    // Every value whose *only* use anywhere in this function is as a
    // `Drop` operand (`rfcs/0012`). A structural destruction of one
    // field is expressed as a `Transfer` read of it immediately
    // followed by a `Drop` of the result -- the two primitives
    // composed, since there is no separate `drop.place` instruction --
    // so such a read is a *destruction*, not a transfer, and is
    // therefore legal on a partially moved parent: it destroys exactly
    // what is left, which is the whole point of a structural drop. A
    // `Transfer` read feeding anything else really is moving a value
    // out to be used, and does require a complete one.
    let drop_only_reads: HashSet<ValueId> = {
        let mut dropped: HashSet<ValueId> = HashSet::new();
        let mut otherwise_used: HashSet<ValueId> = HashSet::new();
        for block in &function.blocks {
            for instruction in &block.instructions {
                match instruction {
                    Instruction::Drop { value } => {
                        dropped.insert(*value);
                    }
                    Instruction::Value { kind, .. } => {
                        otherwise_used.extend(operands_of(kind));
                    }
                    Instruction::Store { slot, value, .. } => {
                        otherwise_used.insert(*slot);
                        otherwise_used.insert(*value);
                    }
                    Instruction::StorePlace { place, value } => {
                        otherwise_used.insert(place.root);
                        otherwise_used.insert(*value);
                    }
                    // Reading the shell is an ordinary use; naming the
                    // transferred value is the ownership event for it,
                    // not an additional read -- but both are recorded,
                    // since this set only ever gates `PlaceRead`
                    // results, which neither of these can be.
                    Instruction::DecomposeVariant { value, taken, .. } => {
                        otherwise_used.insert(*value);
                        otherwise_used.extend(taken.iter().map(|(_, owner)| *owner));
                    }
                }
            }
            match &block.terminator {
                Terminator::Return(Some(v)) => {
                    otherwise_used.insert(*v);
                }
                Terminator::Raise { value, .. } => {
                    otherwise_used.insert(*value);
                }
                Terminator::CondBranch { condition, .. } => {
                    otherwise_used.insert(*condition);
                }
                Terminator::Switch { scrutinee, .. } => {
                    otherwise_used.insert(*scrutinee);
                }
                Terminator::Invoke { args, .. } => {
                    otherwise_used.extend(args.iter().copied());
                }
                Terminator::Return(None) | Terminator::Branch(_) => {}
            }
        }
        dropped.difference(&otherwise_used).copied().collect()
    };

    let transfer = |block: &BasicBlock,
                    in_state: &PlaceFacts|
     -> (PlaceFacts, Vec<OwnershipViolation>) {
        let mut facts = in_state.clone();
        let mut violations: Vec<OwnershipViolation> = Vec::new();

        for instruction in &block.instructions {
            // A value-producing instruction *defines* its own result
            // afresh every time it executes, so any fact about that
            // same id left over from a previous iteration -- carried
            // back around a loop's own back edge -- is stale and must
            // not survive into this definition (`rfcs/0012`). Without
            // this, a resource constructed inside a loop body and
            // destroyed at the end of that same iteration would look
            // like a double cleanup on the second iteration. Skipped
            // for a `Load`, whose canonical root is the slot it reads
            // (defined by its own `Alloc`/`Store`), not this result.
            if let Instruction::Value { result, kind, .. } = instruction
                && is_affine(*result)
                && origin(*result) == *result
            {
                // A payload *read* owns nothing. The shell still owns
                // what it read until a `DecomposeVariant` claims that
                // exact extraction, so the result starts `Empty` and
                // becomes this frame's own only at the claim.
                let state = if matches!(kind, ValueKind::VariantPayload { .. }) {
                    FieldState::Empty
                } else {
                    FieldState::Full
                };
                set_place_state(&mut facts, &Place::root(*result), state);
            }
            match instruction {
                Instruction::Value {
                    result,
                    kind: ValueKind::PlaceRead { place, mode },
                    ..
                } => {
                    let place = canonical(place);
                    if resolve_place_state(&facts, &place) != FieldState::Full {
                        violations.push(OwnershipViolation::UseAfterMove(*result));
                        continue;
                    }
                    // Reading or moving a place *as a whole* requires
                    // every affine descendant of it to still be there
                    // -- unless this read exists purely to destroy it
                    // (see `drop_only_reads`), which is exactly the
                    // shape a structural drop of a partially moved
                    // parent takes.
                    if !drop_only_reads.contains(result) && !place_is_whole(&facts, &place) {
                        violations.push(OwnershipViolation::PartialWhole(*result));
                        continue;
                    }
                    if *mode == crate::nir::OwnershipMode::Transfer {
                        set_place_state(&mut facts, &place, FieldState::Empty);
                    }
                }
                // Taking a variant apart into one specific case, on
                // this path alone (`rfcs/0012`). The shell is consumed
                // here and each claimed payload becomes its own owned
                // value from here on -- so a whole-value `Drop` or
                // transfer of the same variant on a *disjoint* path is
                // completely independent: neither can suppress or
                // discharge the other, which is exactly what a
                // function-global "was this consumed anywhere" test got
                // wrong.
                Instruction::DecomposeVariant {
                    value,
                    variant,
                    case,
                    taken,
                } => {
                    let shell = Place::root(origin(*value));
                    if resolve_place_state(&facts, &shell) != FieldState::Full {
                        violations.push(OwnershipViolation::DoubleCleanup(*value));
                        continue;
                    }
                    if !place_is_whole(&facts, &shell) {
                        violations.push(OwnershipViolation::PartialWhole(*value));
                        continue;
                    }
                    // Every *affine* payload position of this case must
                    // be claimed exactly once: one left out would be a
                    // resource the shell no longer owns and nothing else
                    // does either.
                    let args: Vec<Ty> = match value_types.get(value) {
                        Some(Ty::Applied(_, args)) => args.clone(),
                        _ => Vec::new(),
                    };
                    let payload_tys: Vec<Ty> =
                        match agg.variants.get(variant).and_then(|v| v.cases.get(*case)) {
                            Some(layout) => layout.payload.clone(),
                            // There is no declaration to check claims
                            // against. This pass's own validation arm
                            // already rejects a `DecomposeVariant` naming
                            // an unknown variant or a case out of range and
                            // owns that diagnostic, so demanding claims
                            // here would only report the same defect twice.
                            // Nothing is silently discharged: the program
                            // is rejected either way.
                            None => Vec::new(),
                        };
                    let subst = item_substitution(*variant, &args, agg);
                    let mut incomplete = false;
                    if let Ok(subst) = &subst {
                        for (index, payload_ty) in payload_tys.iter().enumerate() {
                            if !is_affine_in(&substitute(payload_ty, subst), agg) {
                                continue;
                            }
                            let claims = taken.iter().filter(|(i, _)| *i == index).count();
                            if claims != 1 {
                                incomplete = true;
                            }
                        }
                    } else {
                        incomplete = true;
                    }
                    if incomplete {
                        violations.push(OwnershipViolation::IncompleteDecomposition(*value));
                        continue;
                    }
                    set_place_state(&mut facts, &shell, FieldState::Empty);
                    // Each claimed payload is this frame's own from
                    // here: seeded `Full` so a later consumption of it
                    // is checked against a real state, never a default.
                    for (_, owner) in taken {
                        if is_affine(*owner) && origin(*owner) == *owner {
                            set_place_state(&mut facts, &Place::root(*owner), FieldState::Full);
                        }
                    }
                }
                Instruction::StorePlace { place, value } => {
                    let place = canonical(place);
                    if resolve_place_state(&facts, &place) != FieldState::Empty {
                        violations.push(OwnershipViolation::OverwriteLive(*value));
                        continue;
                    }
                    // Storing a nested affine value creates exactly the
                    // descendant obligations that value itself carries:
                    // the place becomes `Full` and every stale deeper
                    // fact recorded before it was emptied is cleared, so
                    // an ancestor emptied only by this child's own move
                    // becomes complete again.
                    set_place_state(&mut facts, &place, FieldState::Full);
                    consume_root(
                        &mut facts,
                        &mut violations,
                        &is_affine,
                        &origin,
                        *value,
                        true,
                        *value,
                    );
                }
                Instruction::Drop { value } => {
                    // A structural `Drop` destroys this value *and*
                    // every remaining descendant under it (`rfcs/0012`'s
                    // chosen coherent model), which is exactly what
                    // clearing every deeper key expresses -- so a
                    // parent dropped after one of its own children was
                    // already moved out is valid, and destroys only
                    // what is left.
                    consume_root(
                        &mut facts,
                        &mut violations,
                        &is_affine,
                        &origin,
                        *value,
                        false,
                        *value,
                    );
                }
                Instruction::Store { slot, value, mode } => match mode {
                    crate::nir::OwnershipMode::Transfer => {
                        consume_root(
                            &mut facts,
                            &mut violations,
                            &is_affine,
                            &origin,
                            *value,
                            true,
                            *value,
                        );
                        if is_affine(*slot) {
                            set_place_state(
                                &mut facts,
                                &Place::root(origin(*slot)),
                                FieldState::Full,
                            );
                        }
                    }
                    crate::nir::OwnershipMode::Observe => {
                        observe_root(&facts, &mut violations, &is_affine, &origin, *value, *value);
                    }
                },
                Instruction::Value { result, kind, .. } => match kind {
                    ValueKind::Move { source } | ValueKind::DeferCapture { source } => {
                        consume_root(
                            &mut facts,
                            &mut violations,
                            &is_affine,
                            &origin,
                            *source,
                            true,
                            *result,
                        );
                    }
                    ValueKind::RecordCreate(_, _, fields) => {
                        for field in fields {
                            consume_root(
                                &mut facts,
                                &mut violations,
                                &is_affine,
                                &origin,
                                *field,
                                true,
                                *result,
                            );
                        }
                    }
                    ValueKind::VariantCreate { payload, .. } => {
                        for field in payload {
                            consume_root(
                                &mut facts,
                                &mut violations,
                                &is_affine,
                                &origin,
                                *field,
                                true,
                                *result,
                            );
                        }
                    }
                    ValueKind::Call(callee, _, args, _) => {
                        let take = known_functions.get(callee).map(|f| f.take.as_slice());
                        for (i, arg) in args.iter().enumerate() {
                            if consumes_arg(take, args.len(), i) {
                                consume_root(
                                    &mut facts,
                                    &mut violations,
                                    &is_affine,
                                    &origin,
                                    *arg,
                                    true,
                                    *result,
                                );
                            } else {
                                observe_root(
                                    &facts,
                                    &mut violations,
                                    &is_affine,
                                    &origin,
                                    *arg,
                                    *result,
                                );
                            }
                        }
                    }
                    ValueKind::RecordField {
                        base,
                        record,
                        field,
                    } if is_affine(*base) => {
                        // Observes one *specific* field, so it requires
                        // only that field to still hold its own value
                        // -- never the whole aggregate. Reading an
                        // unaffected (or non-affine) field of a
                        // partially moved parent stays legal, which is
                        // exactly what makes a partial move usable at
                        // all; reading any field after the parent
                        // itself was consumed is still rejected,
                        // because the ancestor's own state dominates.
                        let place = Place::root(origin(*base))
                            .field(*record, crate::place::FieldId(*field as u32));
                        if resolve_place_state(&facts, &place) != FieldState::Full {
                            violations.push(OwnershipViolation::UseAfterMove(*result));
                        }
                    }
                    _ => {}
                },
            }
        }

        match &block.terminator {
            Terminator::Return(Some(value)) => {
                consume_root(
                    &mut facts,
                    &mut violations,
                    &is_affine,
                    &origin,
                    *value,
                    true,
                    *value,
                );
            }
            Terminator::Raise { value, .. } => {
                consume_root(
                    &mut facts,
                    &mut violations,
                    &is_affine,
                    &origin,
                    *value,
                    true,
                    *value,
                );
            }
            Terminator::Invoke { callee, args, .. } => {
                let take = known_functions.get(callee).map(|f| f.take.as_slice());
                for (i, arg) in args.iter().enumerate() {
                    if consumes_arg(take, args.len(), i) {
                        consume_root(
                            &mut facts,
                            &mut violations,
                            &is_affine,
                            &origin,
                            *arg,
                            true,
                            *arg,
                        );
                    } else {
                        observe_root(&facts, &mut violations, &is_affine, &origin, *arg, *arg);
                    }
                }
            }
            _ => {}
        }

        (facts, violations)
    };

    let entry_block = function
        .blocks
        .iter()
        .find(|b| b.id == entry)
        .expect("presence already checked above");
    // Every root an instruction creates starts *absent*: nothing has
    // created it yet on any path through the entry. Without this the
    // absence of a key reads as `Full`, so a value built on one arm of
    // a branch is indistinguishable at the join from one that was never
    // created on the other arm at all -- and a bypass path silently
    // excuses a real leak, or is itself blamed for a value it never
    // received. Parameters are deliberately not seeded: a `take`
    // parameter really is live from the entry.
    let mut entry_facts = PlaceFacts::new();
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value { result, .. } = instruction
                && is_affine(*result)
                && origin(*result) == *result
            {
                entry_facts.insert(Place::root(*result), FieldState::Empty);
            }
        }
    }
    let (entry_out, _) = transfer(entry_block, &entry_facts);

    // `out` holds an entry for a block *only once that block's own
    // out-state has actually been computed* -- "not computed yet" is the
    // absence of a key, and is therefore impossible to confuse with a
    // block genuinely computed to hold no facts at all. Pre-seeding
    // every block with an empty map (as this once did) erases exactly
    // that distinction, and lets an unprocessed loop back-edge
    // predecessor contribute a fact set nothing ever proved.
    //
    // The entry block is the one boundary condition: its in-state is
    // empty by definition, so its out-state is fixed and never
    // recomputed.
    let mut out: HashMap<BlockId, PlaceFacts> = HashMap::from([(entry, entry_out)]);

    // Standard worklist ("chaotic iteration") over reachable non-entry
    // blocks, seeded in declaration order so the exact same CFG is
    // always explored in the same order. A block is re-enqueued only
    // when one of its own predecessors' out-states actually changed.
    //
    // Termination, with no pass limit of any kind: every transfer
    // either records a fixed state for a place or -- when its own guard
    // fails on a worse in-state -- records nothing and leaves the joined
    // state standing. So a worse in-state can only ever produce an
    // equal-or-worse out-state, which makes the transfer monotone in
    // the order `Full`/`Empty` below the absorbing `Maybe`. The set of
    // tracked places is bounded by the places the instructions actually
    // name, and each one's state can rise at most twice, so the
    // iteration reaches a fixed point.
    let mut worklist: VecDeque<BlockId> = function
        .blocks
        .iter()
        .map(|b| b.id)
        .filter(|id| *id != entry && reachable.contains(id))
        .collect();
    let mut queued: HashSet<BlockId> = worklist.iter().copied().collect();
    while let Some(id) = worklist.pop_front() {
        queued.remove(&id);
        let Some(block) = function.blocks.iter().find(|b| b.id == id) else {
            continue;
        };
        let in_state =
            match in_state_for_places(id, entry, &incoming_edges, &reachable, &out, &entry_facts) {
                IncomingState::Entry(facts) | IncomingState::Ready(facts) => facts,
                // Nothing has proven anything about this block yet, so it
                // runs no transfer and records no out-state: the absence of
                // a key is exactly what keeps "not computed" apart from
                // "computed to nothing". Popping a block before its own
                // predecessors is ordinary -- the worklist is seeded in
                // declaration order, which says nothing about control flow
                // -- and a predecessor's out-state landing later re-enqueues
                // it. Every reachable block is reached from the entry,
                // whose out-state is fixed before this loop starts, so no
                // reachable block can stay `Pending` once this drains.
                IncomingState::Pending => continue,
            };
        let (new_out, _) = transfer(block, &in_state);
        let changed = out.get(&id) != Some(&new_out);
        if changed {
            out.insert(id, new_out);
            for &succ in successors.get(&id).into_iter().flatten() {
                if succ != entry && reachable.contains(&succ) && queued.insert(succ) {
                    worklist.push_back(succ);
                }
            }
        }
    }

    let owned_roots = structural_cleanup_obligations(function, value_types, agg);
    let payloads = extracted_payloads(function);
    let refinements = case_refinements(function);
    let extractions = payload_extractions(function);
    // Every extraction some decomposition claims *somewhere*. A value
    // claimed on no path at all was never this frame's to consume; one
    // claimed on some path and consumed twice is an ordinary double
    // cleanup, and keeps that diagnostic.
    let claimed_extractions: HashSet<ValueId> = function
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter())
        .filter_map(|instruction| match instruction {
            Instruction::DecomposeVariant { taken, .. } => Some(taken),
            _ => None,
        })
        .flat_map(|taken| taken.iter().map(|(_, owner)| *owner))
        .collect();

    for block in &function.blocks {
        let in_state = if reachable.contains(&block.id) {
            match in_state_for_places(
                block.id,
                entry,
                &incoming_edges,
                &reachable,
                &out,
                &entry_facts,
            ) {
                IncomingState::Entry(facts) | IncomingState::Ready(facts) => facts,
                // The fixpoint above has converged, so every reachable
                // block has a computed predecessor by now and this
                // cannot be observed. Were it ever observed, judging
                // ownership from a state nothing proved would be
                // guesswork, so the block is skipped rather than
                // fabricated -- which is the whole point of keeping
                // `Pending` out of `PlaceFacts`.
                IncomingState::Pending => continue,
            }
        } else {
            // An unreachable block is walked purely so its own
            // instructions are still shape-checked; it starts from
            // nothing, and its facts never reach a reachable block.
            PlaceFacts::new()
        };
        let (exit_facts, violations) = transfer(block, &in_state);
        for violation in violations {
            // A payload extraction no decomposition anywhere in this
            // function claims was never this frame's to consume or
            // transfer at all, so it gets the diagnostic that says so
            // rather than one about a value having moved.
            if let OwnershipViolation::UseAfterMove(v) | OwnershipViolation::DoubleCleanup(v) =
                violation
                && extractions.is_extraction(v)
                && !claimed_extractions.contains(&v)
            {
                diagnostics.push(Diagnostic::error(
                    codes::UNCLAIMED_PAYLOAD_OWNERSHIP,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} reads one payload position of a variant, \
                         and is destroyed or transferred without any decomposition having \
                         transferred ownership of it",
                        v.0
                    ),
                ));
                continue;
            }
            let (code, value, detail) = match violation {
                OwnershipViolation::UseAfterMove(v) => (
                    codes::PLACE_USE_AFTER_MOVE,
                    v,
                    "reads or moves a structural place that is not definitely still holding its \
                     own value on every path reaching it",
                ),
                OwnershipViolation::OverwriteLive(v) => (
                    codes::PLACE_OVERWRITE_OF_LIVE_FIELD,
                    v,
                    "reinitializes a structural place that is not definitely empty on every path \
                     reaching it",
                ),
                OwnershipViolation::PartialWhole(v) => (
                    codes::PARTIAL_PLACE_USED_AS_WHOLE,
                    v,
                    "uses a place as a whole value while one of its own affine descendants is \
                     already moved or dropped",
                ),
                OwnershipViolation::DoubleCleanup(v) => (
                    codes::DUPLICATE_STRUCTURAL_CLEANUP,
                    v,
                    "destroys or transfers a place that was already consumed on a path reaching it",
                ),
                OwnershipViolation::IncompleteDecomposition(v) => (
                    codes::MISSING_STRUCTURAL_CLEANUP,
                    v,
                    "is taken apart into a case whose own affine payload positions are not each \n                     claimed exactly once",
                ),
            };
            diagnostics.push(Diagnostic::error(
                code,
                source,
                Span::dummy(),
                format!("function `{function_name}`: %{} {detail}", value.0),
            ));
        }
        if !reachable.contains(&block.id) {
            continue;
        }
        let returned = match &block.terminator {
            Terminator::Return(Some(v)) => Some(origin(*v)),
            Terminator::Raise { value, .. } => Some(origin(*value)),
            Terminator::Return(None) => None,
            _ => continue,
        };
        let block_refinements = refinements.at_exit(block);
        let cases = VariantCaseContext {
            refinements: &block_refinements,
            payloads: &payloads,
            claimed: &claimed_extractions,
        };
        for (root, ty) in &owned_roots {
            let root_origin = origin(*root);
            if returned == Some(root_origin) {
                continue;
            }
            // Whether this exit owes cleanup is answered by the facts
            // that actually reach it, not by dominance. Dominance asks
            // "does *every* path here pass through the creation?"; the
            // obligation asks "does *any* path here pass through it and
            // still hold the value?". A branch-local aggregate reaching
            // a shared exit answers no to the first and yes to the
            // second, and used to be exempted -- a silent leak. The
            // state below is `Empty` exactly when every path here either
            // never created it or already consumed it.
            let mut obligations = Vec::new();
            remaining_obligations(
                &exit_facts,
                &Place::root(root_origin),
                ty,
                agg,
                &cases,
                0,
                &mut obligations,
            );
            if !obligations.is_empty() {
                diagnostics.push(Diagnostic::error(
                    codes::MISSING_STRUCTURAL_CLEANUP,
                    source,
                    Span::dummy(),
                    format!(
                        "function `{function_name}`: %{} still owns {} affine descendant(s) that \
                         were never destroyed or transferred out when this exit is reached",
                        root.0,
                        obligations.len()
                    ),
                ));
            }
        }
    }
}

/// Consumes `value`'s own whole root place -- a `Drop`, a
/// `Move`/`DeferCapture` source, an aggregate construction operand, a
/// `take` argument, or a returned/raised operand (`rfcs/0012`).
///
/// `require_whole` separates a *transfer* (which needs a complete
/// value, and so rejects a partially moved parent) from a structural
/// `Drop` (which is explicitly allowed on a partially moved parent, and
/// destroys exactly what is left). A consumption of something already
/// consumed on this path is duplicate structural cleanup, reported
/// against `reporter` -- the instruction result, where there is one, so
/// the diagnostic names the operation rather than its operand.
#[allow(clippy::too_many_arguments)]
fn consume_root(
    facts: &mut PlaceFacts,
    violations: &mut Vec<OwnershipViolation>,
    is_affine: &impl Fn(ValueId) -> bool,
    origin: &impl Fn(ValueId) -> ValueId,
    value: ValueId,
    require_whole: bool,
    reporter: ValueId,
) {
    if !is_affine(value) {
        return;
    }
    let place = Place::root(origin(value));
    if resolve_place_state(facts, &place) != FieldState::Full {
        violations.push(OwnershipViolation::DoubleCleanup(reporter));
        return;
    }
    if require_whole && !place_is_whole(facts, &place) {
        violations.push(OwnershipViolation::PartialWhole(reporter));
        return;
    }
    set_place_state(facts, &place, FieldState::Empty);
}

/// Observes `value`'s own whole root place without consuming it -- still
/// requires it to be intact, since a partially moved aggregate has no
/// whole value left to observe (`rfcs/0012`).
fn observe_root(
    facts: &PlaceFacts,
    violations: &mut Vec<OwnershipViolation>,
    is_affine: &impl Fn(ValueId) -> bool,
    origin: &impl Fn(ValueId) -> ValueId,
    value: ValueId,
    reporter: ValueId,
) {
    if !is_affine(value) {
        return;
    }
    let place = Place::root(origin(value));
    if resolve_place_state(facts, &place) != FieldState::Full {
        violations.push(OwnershipViolation::UseAfterMove(reporter));
    } else if !place_is_whole(facts, &place) {
        violations.push(OwnershipViolation::PartialWhole(reporter));
    }
}

/// Every root this function itself owns and must therefore have fully
/// cleaned up by any reachable exit (`rfcs/0012`), paired with its own
/// type: a `take` parameter, and every instruction result that
/// *produces* a new owned affine value.
///
/// Deliberately excludes a nominal `resource` root --
/// [`verify_resource_ownership`] already owns that obligation end to
/// end, and reporting it here too would double-report the identical
/// leak under a second code. What is left is exactly the gap that
/// lattice cannot see: a transitively affine *record*, which is never a
/// key there at all.
///
/// Also excludes any root a `Terminator::Switch` or a
/// `ValueKind::VariantPayload` reaches into: a `match`'s own decision
/// tree takes ownership of the scrutinee and hands it to the extracted
/// payloads, each of which is tracked in its own right from that point
/// on, so demanding a separate destruction of the scrutinee too would
/// double-count the very same obligation.
/// Every root this function itself owns and must therefore have fully
/// cleaned up by any reachable exit, paired with its own type and with
/// the block ownership *begins* in (`rfcs/0012`).
///
/// Ownership is read straight off the instruction that establishes it,
/// with no function-global reasoning whatsoever: a `take` parameter owns
/// from entry, a construction/move/call/place-transfer owns from its own
/// block, and a variant payload owns from the block its
/// `TakeVariantPayload` appears in -- never from the shared extraction
/// that merely read it. That last distinction is the whole point: the
/// extraction is common to every arm reachable through a case, while the
/// transfer is emitted only on the one path that actually claims the
/// payload. An earlier design instead scanned the whole function for
/// "is this value consumed anywhere", which let a whole-value drop in
/// one branch silently cancel a sibling branch's payload obligations.
///
/// Deliberately excludes a nominal `resource` root --
/// [`verify_resource_ownership`] already owns that obligation end to
/// end, and reporting it here too would double-report the identical leak
/// under a second code.
fn structural_cleanup_obligations(
    function: &Function,
    value_types: &HashMap<ValueId, Ty>,
    agg: &AggregateContext,
) -> Vec<(ValueId, Ty)> {
    let owns = |v: ValueId| -> Option<Ty> {
        let ty = value_types.get(&v)?;
        if !is_affine_in(ty, agg) {
            return None;
        }
        if matches!(ty, Ty::Named(item, _) if agg.records.get(item).is_some_and(|r| r.affine)) {
            return None;
        }
        Some(ty.clone())
    };

    let mut roots: Vec<(ValueId, Ty)> = Vec::new();
    for param in &function.params {
        if param.take
            && let Some(ty) = owns(param.value)
        {
            roots.push((param.value, ty));
        }
    }
    for block in &function.blocks {
        for instruction in &block.instructions {
            match instruction {
                Instruction::Value { result, kind, .. } => {
                    let produces_owner = matches!(
                        kind,
                        ValueKind::RecordCreate(..)
                            | ValueKind::VariantCreate { .. }
                            | ValueKind::Move { .. }
                            | ValueKind::DeferCapture { .. }
                            // A callee that returns an affine value
                            // transfers ownership of it out to this
                            // frame, exactly like a construction does.
                            | ValueKind::Call(..)
                            | ValueKind::PlaceRead {
                                mode: crate::nir::OwnershipMode::Transfer,
                                ..
                            }
                    );
                    if produces_owner && let Some(ty) = owns(*result) {
                        roots.push((*result, ty));
                    }
                }
                // Ownership of an extracted payload begins *here*, at
                // the transfer, not at the extraction that read it.
                Instruction::DecomposeVariant { taken, .. } => {
                    for (_, owner) in taken {
                        if let Some(ty) = owns(*owner) {
                            roots.push((*owner, ty));
                        }
                    }
                }
                _ => {}
            }
        }
    }
    roots.sort_by_key(|(v, _)| *v);
    roots.dedup_by_key(|(v, _)| *v);
    roots
}

/// Every payload position this function extracts, keyed by the
/// `(base, case, index)` it was read out of and mapping to the value the
/// extraction produced (`rfcs/0012`).
///
/// Read back when a variant's remaining obligations are computed: a
/// payload the shell still owns is only "nothing owed" if the value
/// standing for it owes nothing in turn, and answering that needs the
/// payload's own value to consult its own case refinement from.
fn extracted_payloads(function: &Function) -> HashMap<(ValueId, usize, usize), ValueId> {
    let mut out = HashMap::new();
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value {
                result,
                kind:
                    ValueKind::VariantPayload {
                        base, case, index, ..
                    },
                ..
            } = instruction
            {
                out.entry((*base, *case, *index)).or_insert(*result);
            }
        }
    }
    out
}

/// Every remaining *owned* affine obligation reachable through `place`,
/// given its own current type (`rfcs/0012`): a declared `resource` is
/// one obligation in its own right, an ordinary affine record
/// decomposes into its own affine fields (in reverse declaration order,
/// matching the destruction order the rest of the pipeline uses), and a
/// variant -- whose live case is a runtime fact -- or an item with
/// malformed generic metadata stays one opaque obligation. Mirrors
/// `resourceck::flow::structural_drop_targets`, recomputed here from
/// NIR alone rather than trusted from it.
fn remaining_obligations(
    facts: &PlaceFacts,
    place: &Place<ValueId>,
    ty: &Ty,
    agg: &AggregateContext,
    cases: &VariantCaseContext,
    depth: usize,
    out: &mut Vec<Place<ValueId>>,
) {
    if depth >= MAX_GENERIC_DEPTH {
        return;
    }
    // `Empty` is the only state that owes nothing: every path reaching
    // here either never created this place or already consumed it.
    // `Maybe` means at least one path still holds it, and that path
    // leaks -- treating disagreement as "nothing owed" is exactly how a
    // value live on one predecessor and consumed on another escaped.
    if resolve_place_state(facts, place) == FieldState::Empty {
        return;
    }
    if !is_affine_in(ty, agg) {
        return;
    }
    let (item, args): (ItemId, Vec<Ty>) = match ty {
        Ty::Named(item, _) => (*item, Vec::new()),
        Ty::Applied(item, args) => (*item, args.clone()),
        _ => return,
    };
    if let Some(variant) = agg.variants.get(&item) {
        // A variant only owns the payload of the case that is actually
        // live. Which case that is, is a *path* fact: on a case-refined
        // edge the switch already proved it, and this exit is on exactly
        // one such path. Decomposing by it is what lets one branch hand
        // its payload to an arm while a disjoint branch destroys the
        // whole value, with neither affecting the other.
        //
        // Without a refinement there is nothing to decompose by, so the
        // variant stays one opaque obligation -- never silently
        // discharged.
        let Some(case) = cases.refined_case(place) else {
            out.push(place.clone());
            return;
        };
        let Some(layout) = variant.cases.get(case) else {
            out.push(place.clone());
            return;
        };
        let Ok(subst) = item_substitution(item, &args, agg) else {
            out.push(place.clone());
            return;
        };
        for (index, payload_ty) in layout.payload.iter().enumerate().rev() {
            let payload_ty = substitute(payload_ty, &subst);
            if !is_affine_in(&payload_ty, agg) {
                continue;
            }
            let payload_place = place.variant_field(
                item,
                crate::place::CaseId(case as u32),
                crate::place::FieldId(index as u32),
            );
            if resolve_place_state(facts, &payload_place) != FieldState::Full {
                // Already transferred out on this path: whoever took it
                // owns it now, and owes its cleanup in its own right.
                continue;
            }
            // Still held by the shell. What it owes in turn is answered
            // through the value the extraction produced for it, which
            // carries its own case refinement; with no such value there
            // is nothing finer to say, so it is one opaque obligation.
            match cases.extracted_value(place, case, index) {
                Some(payload_value) => remaining_obligations(
                    facts,
                    &Place::root(payload_value),
                    &payload_ty,
                    agg,
                    cases,
                    depth + 1,
                    out,
                ),
                None => out.push(payload_place),
            }
        }
        return;
    }
    let Some(layout) = agg.records.get(&item) else {
        // An item with no layout at all: one opaque obligation, never
        // decomposed.
        out.push(place.clone());
        return;
    };
    let declared_resource = layout.affine;
    let Ok(subst) = item_substitution(item, &args, agg) else {
        out.push(place.clone());
        return;
    };
    for (index, (_, field_ty)) in layout.fields.iter().enumerate().rev() {
        let field_ty = substitute(field_ty, &subst);
        if !is_affine_in(&field_ty, agg) {
            continue;
        }
        remaining_obligations(
            facts,
            &place.field(item, crate::place::FieldId(index as u32)),
            &field_ty,
            agg,
            cases,
            depth + 1,
            out,
        );
    }
    if declared_resource {
        out.push(place.clone());
    }
}

/// Everything a variant obligation needs in order to decompose by the
/// case that is actually live at one exit (`rfcs/0012`): the case
/// refinements this exit's own block is on the receiving end of, and the
/// values this function extracted for each payload position.
///
/// Both are path facts read back at a specific block, never
/// function-global ownership conclusions: the refinement is whatever
/// every incoming edge of that block independently guarantees, and the
/// extraction map is mechanical instruction data.
struct VariantCaseContext<'a> {
    refinements: &'a HashSet<RefinementFact>,
    payloads: &'a HashMap<(ValueId, usize, usize), ValueId>,
    /// Extractions some decomposition actually claims. An unclaimed
    /// extraction is only a read, so the shell still owns what it read
    /// and the payload's obligation stays with the shell.
    claimed: &'a HashSet<ValueId>,
}

impl VariantCaseContext<'_> {
    /// The case this place's own root value is refined to at this exit,
    /// when it is a bare root and exactly one refinement names it. A
    /// projected place has no value to refine, and a value refined to
    /// more than one case is not refined at all.
    fn refined_case(&self, place: &Place<ValueId>) -> Option<usize> {
        if !place.projections.is_empty() {
            return None;
        }
        let mut found: Option<usize> = None;
        for (value, _, case) in self.refinements {
            if *value != place.root {
                continue;
            }
            match found {
                None => found = Some(*case),
                Some(previous) if previous == *case => {}
                Some(_) => return None,
            }
        }
        found
    }

    /// The value this function's own extraction produced for one payload
    /// position of one case, if it extracted it at all.
    fn extracted_value(
        &self,
        place: &Place<ValueId>,
        case: usize,
        index: usize,
    ) -> Option<ValueId> {
        if !place.projections.is_empty() {
            return None;
        }
        self.payloads
            .get(&(place.root, case, index))
            .copied()
            .filter(|owner| self.claimed.contains(owner))
    }
}

/// The pairwise join of two reachable predecessors' own place facts --
/// over the *union* of both sides' keys, so a place touched on only one
/// of them still joins to `Maybe` against the other's implicit `Full`.
/// Collected through a `BTreeSet`, so the result never depends on
/// either map's own iteration order.
fn merge_place_facts(a: &PlaceFacts, b: &PlaceFacts) -> PlaceFacts {
    let keys: BTreeSet<Place<ValueId>> = a.keys().chain(b.keys()).cloned().collect();
    keys.into_iter()
        .map(|key| {
            let left = a.get(&key).copied().unwrap_or(FieldState::Full);
            let right = b.get(&key).copied().unwrap_or(FieldState::Full);
            (key, merge_field(left, right))
        })
        .collect()
}

/// What a block's own incoming ownership state actually *is*
/// (`rfcs/0012`).
///
/// Kept as its own type precisely because one of these answers is not a
/// state at all, and every value that could stand in for it -- an empty
/// map, `Default::default()`, `Option::unwrap_or_default()` -- is also
/// a perfectly valid analysis state. Collapsing the two is what lets a
/// fixed point be seeded with facts nothing ever proved.
#[derive(Debug, Clone, PartialEq, Eq)]
enum IncomingState<F> {
    /// The entry block: no predecessors by definition, and a fact set
    /// that is the analysis's one real boundary condition -- a *proven*
    /// state, not a placeholder.
    Entry(F),
    /// At least one reachable predecessor has produced an out-state,
    /// and this is the join of every such predecessor's.
    Ready(F),
    /// No reachable predecessor has produced an out-state yet. Not a
    /// fact set: no transfer runs on it, and no out-state is recorded
    /// from it, so nothing downstream can read facts nothing proved.
    Pending,
}

/// This block's own in-state: the join of every *reachable, already
/// computed* predecessor's out-state (`rfcs/0012`).
///
/// The three answers are deliberately kept apart, because collapsing
/// any of them into a `PlaceFacts` is what lets a fixed point be seeded
/// with facts nothing proved:
///
/// * the **entry** block has no predecessors by definition, and its
///   empty in-state is the analysis's one real boundary condition;
/// * a **reachable but not yet computed** predecessor (an unprocessed
///   loop back edge) contributes *nothing* -- it is skipped, not
///   treated as having proven an empty fact set;
/// * an **unreachable** predecessor contributes nothing either, so a
///   dead CFG fragment can never seed reachable ownership.
///
/// A block none of whose predecessors has landed yet is therefore
/// `Pending`, never an empty state. It is always revisited: every
/// reachable block is reached from the entry, whose own out-state is
/// fixed before the worklist starts, and a predecessor's out-state
/// appearing re-enqueues it.
///
/// There is deliberately no "malformed edge" answer. Every predecessor
/// in `incoming_edges` is, by construction, the id of a block this
/// function declares -- the map is built by walking exactly those
/// blocks' own terminators -- so an undeclared *predecessor* is not a
/// question this can be asked. A terminator naming an undeclared
/// *successor* is real, and is reported once, at the terminator layer,
/// as `UNKNOWN_BRANCH_TARGET`; this pass simply never reaches past it,
/// and never invents ownership state for it.
fn in_state_for_places(
    block_id: BlockId,
    entry: BlockId,
    incoming_edges: &HashMap<BlockId, Vec<BlockId>>,
    reachable: &HashSet<BlockId>,
    out: &HashMap<BlockId, PlaceFacts>,
    entry_facts: &PlaceFacts,
) -> IncomingState<PlaceFacts> {
    if block_id == entry {
        return IncomingState::Entry(entry_facts.clone());
    }
    let mut acc: Option<PlaceFacts> = None;
    for pred in incoming_edges.get(&block_id).into_iter().flatten() {
        if !reachable.contains(pred) {
            continue;
        }
        // Absence from `out` means "not computed yet", never "computed
        // to nothing" -- the two are distinguishable precisely because
        // `out` is populated only as blocks are actually processed.
        let Some(facts) = out.get(pred) else {
            continue;
        };
        acc = Some(match acc {
            None => facts.clone(),
            Some(previous) => merge_place_facts(&previous, facts),
        });
    }
    match acc {
        Some(facts) => IncomingState::Ready(facts),
        None => IncomingState::Pending,
    }
}

fn verify_invoke_slot_initialization(
    function: &Function,
    source: SourceId,
    function_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Every `ValueId` some `Terminator::Invoke` in this function writes
    // conditionally on one of its own edges -- an ordinary mutable
    // binding (always written unconditionally immediately after its own
    // `alloc`, `rfcs/0002`) never needs this analysis at all, and
    // restricting the fact domain to exactly this finite set is what
    // keeps the fixpoint below guaranteed to terminate.
    let mut guarded_slots: HashSet<ValueId> = HashSet::new();
    for block in &function.blocks {
        if let Terminator::Invoke {
            ok_slot,
            err_targets,
            ..
        } = &block.terminator
        {
            guarded_slots.insert(*ok_slot);
            for target in err_targets {
                guarded_slots.insert(target.slot);
            }
        }
    }
    if guarded_slots.is_empty() {
        return;
    }

    let entry = BlockId(0);
    if !function.blocks.iter().any(|b| b.id == entry) {
        // Already reported elsewhere (missing entry block); nothing
        // meaningful to analyze without one.
        return;
    }

    // Built by matching each block's own terminator exactly once and
    // pushing one entry per *logical* edge directly, each carrying its
    // own gen fact -- never by first collecting a plain list of target
    // `BlockId`s and re-deriving each edge's own gen from the target
    // alone afterward, which would conflate two distinct edges into the
    // same target block (an Invoke's own `ok_target` coinciding with one
    // of its `err_targets`' own `target`, as in
    // `a_success_slot_loaded_from_a_block_also_reached_through_a_failure_edge_is_rejected`)
    // into a single, wrongly-shared gen fact.
    let mut incoming_edges: HashMap<BlockId, Vec<(BlockId, Option<ValueId>)>> = HashMap::new();
    // The same edges as `incoming_edges`, indexed by *source* instead of
    // target, purely to drive worklist propagation below (`invoke_slot_
    // in_facts` never reads this -- it always recomputes a block's own
    // incoming facts from `incoming_edges`, which alone carries each
    // edge's own gen fact).
    let mut successors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for block in &function.blocks {
        match &block.terminator {
            Terminator::Branch(target) => {
                incoming_edges
                    .entry(*target)
                    .or_default()
                    .push((block.id, None));
                successors.entry(block.id).or_default().push(*target);
            }
            Terminator::CondBranch {
                then_block,
                else_block,
                ..
            } => {
                incoming_edges
                    .entry(*then_block)
                    .or_default()
                    .push((block.id, None));
                incoming_edges
                    .entry(*else_block)
                    .or_default()
                    .push((block.id, None));
                successors
                    .entry(block.id)
                    .or_default()
                    .extend([*then_block, *else_block]);
            }
            Terminator::Switch { cases, .. } => {
                for target in cases {
                    incoming_edges
                        .entry(*target)
                        .or_default()
                        .push((block.id, None));
                }
                successors.entry(block.id).or_default().extend(cases);
            }
            Terminator::Invoke {
                ok_slot,
                ok_target,
                err_targets,
                ..
            } => {
                incoming_edges
                    .entry(*ok_target)
                    .or_default()
                    .push((block.id, Some(*ok_slot)));
                successors.entry(block.id).or_default().push(*ok_target);
                for target in err_targets {
                    incoming_edges
                        .entry(target.target)
                        .or_default()
                        .push((block.id, Some(target.slot)));
                    successors.entry(block.id).or_default().push(target.target);
                }
            }
            Terminator::Return(_) | Terminator::Raise { .. } => {}
        }
    }

    // Reachability from the entry block, computed the same way
    // `compute_dominators` computes its own -- needed so an unreachable
    // block is never seeded with an optimistic "everything already
    // initialized" starting fact, which is not merely imprecise but
    // actively unsound: a cycle purely among unreachable blocks (each
    // one only ever reached from another block in the same cycle) would
    // otherwise never have any real predecessor information flow in at
    // all, so an optimistic start would just sit at "fully initialized"
    // forever and could hide a genuine violation inside dead code that
    // happens to also be an `Invoke` target.
    let mut reachable: HashSet<BlockId> = HashSet::from([entry]);
    let mut frontier = vec![entry];
    while let Some(id) = frontier.pop() {
        for &succ in successors.get(&id).into_iter().flatten() {
            if reachable.insert(succ) {
                frontier.push(succ);
            }
        }
    }

    // The entry's own boundary value: its IN is always empty, by
    // definition, so its OUT is exactly its own local transfer applied
    // to nothing -- computed once, here, before the fixpoint below ever
    // starts, and never revisited by it.
    let entry_block = function
        .blocks
        .iter()
        .find(|b| b.id == entry)
        .expect("presence already checked above");
    let (entry_out, _) = invoke_slot_block_transfer(entry_block, &guarded_slots, &HashSet::new());

    // `OUT[b]` starts optimistic (the complete guarded set) for every
    // *reachable* block other than the entry; the entry itself is
    // seeded directly at its own precomputed, fixed `entry_out`; an
    // unreachable block starts at (and, since it is never touched by
    // the worklist below, permanently stays at) the empty set.
    let mut out: HashMap<BlockId, HashSet<ValueId>> = function
        .blocks
        .iter()
        .map(|b| {
            let initial = if b.id == entry {
                entry_out.clone()
            } else if reachable.contains(&b.id) {
                guarded_slots.clone()
            } else {
                HashSet::new()
            };
            (b.id, initial)
        })
        .collect();

    // Standard worklist ("chaotic iteration") fixpoint over reachable
    // non-entry blocks only -- the entry is a fixed boundary condition,
    // never re-processed, so nothing can ever read a stale, not-yet-
    // computed value for it regardless of `function.blocks`' own
    // storage order. Every other reachable block is processed at least
    // once (seeded here, in declaration order, so a rerun of the exact
    // same CFG always explores it in the same order); whenever a
    // block's own `OUT` actually changes, only *its own* reachable,
    // non-entry successors -- read directly from the CFG, never a fixed
    // count -- are re-enqueued, since only they could possibly be
    // affected. Termination follows from monotonicity: each processed
    // change strictly shrinks that block's `OUT` from the lattice's own
    // top, and the sum of every block's `OUT` size is a natural number
    // bounded below by zero, so it cannot decrease forever.
    let mut worklist: VecDeque<BlockId> = function
        .blocks
        .iter()
        .map(|b| b.id)
        .filter(|id| *id != entry && reachable.contains(id))
        .collect();
    let mut queued: HashSet<BlockId> = worklist.iter().copied().collect();
    while let Some(id) = worklist.pop_front() {
        queued.remove(&id);
        let Some(block) = function.blocks.iter().find(|b| b.id == id) else {
            continue;
        };
        let in_facts = invoke_slot_in_facts(id, entry, &incoming_edges, &reachable, &out);
        let (new_out, _) = invoke_slot_block_transfer(block, &guarded_slots, &in_facts);
        if out.get(&id) != Some(&new_out) {
            out.insert(id, new_out);
            for &succ in successors.get(&id).into_iter().flatten() {
                if succ != entry && reachable.contains(&succ) && queued.insert(succ) {
                    worklist.push_back(succ);
                }
            }
        }
    }

    // One diagnostic per malformed `Load`, read off the now-stable
    // fixpoint -- never during an intermediate, not-yet-converged pass.
    // A reachable block (entry included) reads its IN from the
    // fixpoint's own `out` map; an unreachable block is always checked
    // independently, from an empty IN, ignoring any (dead) incoming
    // edge `incoming_edges` recorded for it.
    for block in &function.blocks {
        let in_facts = if reachable.contains(&block.id) {
            invoke_slot_in_facts(block.id, entry, &incoming_edges, &reachable, &out)
        } else {
            HashSet::new()
        };
        let (_, violations) = invoke_slot_block_transfer(block, &guarded_slots, &in_facts);
        for slot in violations {
            diagnostics.push(Diagnostic::error(
                codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED,
                source,
                Span::dummy(),
                format!(
                    "function `{function_name}` loads %{} in bb{}, which is not definitely initialized on every path reaching it",
                    slot.0, block.id.0
                ),
            ));
        }
    }
}

fn check_same_as_result(
    a: ValueId,
    b: ValueId,
    result_ty: &Ty,
    value_types: &HashMap<ValueId, Ty>,
    operand_mismatch: &impl Fn(&mut Vec<Diagnostic>, String),
    diagnostics: &mut Vec<Diagnostic>,
) {
    for (label, v) in [("left", a), ("right", b)] {
        if let Some(ty) = value_types.get(&v)
            && ty != result_ty
        {
            operand_mismatch(
                diagnostics,
                format!("has a {label} operand of a different type than its own declared type"),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nir::{BasicBlock, CaseLayout, InvokeErrTarget, Param, ProtocolMethodLayout};
    use crate::source::SourceMap;
    use crate::symbol::Symbol;

    // -- `merge_location`/`merge_provenance` lattice laws (`rfcs/0011`) --

    #[test]
    fn a_key_initialized_only_on_the_left_becomes_maybe_uninitialized() {
        let mut a: HashMap<ValueId, LocationState> = HashMap::new();
        a.insert(
            ValueId(0),
            LocationState::Initialized((BTreeSet::from([ValueId(0)]), Role::Owned)),
        );
        let b: HashMap<ValueId, LocationState> = HashMap::new();
        let merged = merge_provenance(&a, &b);
        assert_eq!(
            merged.get(&ValueId(0)),
            Some(&LocationState::MaybeUninitialized),
            "unexpected merge result: {merged:?}"
        );
    }

    #[test]
    fn a_key_initialized_only_on_the_right_becomes_maybe_uninitialized() {
        let a: HashMap<ValueId, LocationState> = HashMap::new();
        let mut b: HashMap<ValueId, LocationState> = HashMap::new();
        b.insert(
            ValueId(0),
            LocationState::Initialized((BTreeSet::from([ValueId(0)]), Role::Owned)),
        );
        let merged = merge_provenance(&a, &b);
        assert_eq!(
            merged.get(&ValueId(0)),
            Some(&LocationState::MaybeUninitialized),
            "unexpected merge result: {merged:?}"
        );
    }

    // -- `merge_field` lattice laws (`rfcs/0012`) --------------------

    #[test]
    fn merge_field_is_commutative() {
        for a in [FieldState::Full, FieldState::Empty, FieldState::Maybe] {
            for b in [FieldState::Full, FieldState::Empty, FieldState::Maybe] {
                assert_eq!(
                    merge_field(a, b),
                    merge_field(b, a),
                    "merge_field({a:?}, {b:?}) != merge_field({b:?}, {a:?})"
                );
            }
        }
    }

    #[test]
    fn merge_field_is_idempotent() {
        for a in [FieldState::Full, FieldState::Empty, FieldState::Maybe] {
            assert_eq!(
                merge_field(a, a),
                a,
                "merging {a:?} with itself must not change it"
            );
        }
    }

    #[test]
    fn merge_field_is_associative() {
        let states = [FieldState::Full, FieldState::Empty, FieldState::Maybe];
        for a in states {
            for b in states {
                for c in states {
                    assert_eq!(
                        merge_field(merge_field(a, b), c),
                        merge_field(a, merge_field(b, c)),
                        "(a merge b) merge c != a merge (b merge c) for {a:?}, {b:?}, {c:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn merge_field_disagreement_is_the_absorbing_maybe_state() {
        assert_eq!(
            merge_field(FieldState::Full, FieldState::Empty),
            FieldState::Maybe
        );
        assert_eq!(
            merge_field(FieldState::Maybe, FieldState::Full),
            FieldState::Maybe
        );
        assert_eq!(
            merge_field(FieldState::Empty, FieldState::Maybe),
            FieldState::Maybe
        );
    }

    #[test]
    fn merge_provenance_is_commutative() {
        let mut a: HashMap<ValueId, LocationState> = HashMap::new();
        a.insert(
            ValueId(0),
            LocationState::Initialized((BTreeSet::from([ValueId(0)]), Role::Owned)),
        );
        a.insert(ValueId(1), LocationState::Uninitialized);
        let mut b: HashMap<ValueId, LocationState> = HashMap::new();
        b.insert(
            ValueId(1),
            LocationState::Initialized((BTreeSet::from([ValueId(1)]), Role::Observed)),
        );
        b.insert(
            ValueId(2),
            LocationState::Initialized((BTreeSet::from([ValueId(2)]), Role::Owned)),
        );
        let ab = merge_provenance(&a, &b);
        let ba = merge_provenance(&b, &a);
        assert_eq!(ab, ba, "merge_provenance(a, b) != merge_provenance(b, a)");
    }

    #[test]
    fn merge_provenance_is_idempotent() {
        let mut a: HashMap<ValueId, LocationState> = HashMap::new();
        a.insert(
            ValueId(0),
            LocationState::Initialized((BTreeSet::from([ValueId(0)]), Role::Owned)),
        );
        a.insert(ValueId(1), LocationState::Uninitialized);
        a.insert(ValueId(2), LocationState::MaybeUninitialized);
        let merged = merge_provenance(&a, &a);
        assert_eq!(merged, a, "merging a state with itself must not change it");
    }

    #[test]
    fn merge_provenance_is_associative() {
        let mut a: HashMap<ValueId, LocationState> = HashMap::new();
        a.insert(
            ValueId(0),
            LocationState::Initialized((BTreeSet::from([ValueId(0)]), Role::Owned)),
        );
        let mut b: HashMap<ValueId, LocationState> = HashMap::new();
        b.insert(ValueId(0), LocationState::Uninitialized);
        b.insert(
            ValueId(1),
            LocationState::Initialized((BTreeSet::from([ValueId(1)]), Role::Owned)),
        );
        let mut c: HashMap<ValueId, LocationState> = HashMap::new();
        c.insert(
            ValueId(1),
            LocationState::Initialized((BTreeSet::from([ValueId(9)]), Role::Observed)),
        );
        c.insert(
            ValueId(2),
            LocationState::Initialized((BTreeSet::from([ValueId(2)]), Role::Owned)),
        );
        let ab_c = merge_provenance(&merge_provenance(&a, &b), &c);
        let a_bc = merge_provenance(&a, &merge_provenance(&b, &c));
        assert_eq!(ab_c, a_bc, "(a merge b) merge c != a merge (b merge c)");
    }

    #[test]
    fn differing_initialized_identities_are_unioned_deterministically() {
        let mut a: HashMap<ValueId, LocationState> = HashMap::new();
        a.insert(
            ValueId(0),
            LocationState::Initialized((BTreeSet::from([ValueId(10)]), Role::Owned)),
        );
        let mut b: HashMap<ValueId, LocationState> = HashMap::new();
        b.insert(
            ValueId(0),
            LocationState::Initialized((BTreeSet::from([ValueId(20)]), Role::Owned)),
        );
        let merged = merge_provenance(&a, &b);
        assert_eq!(
            merged.get(&ValueId(0)),
            Some(&LocationState::Initialized((
                BTreeSet::from([ValueId(10), ValueId(20)]),
                Role::Owned
            ))),
            "unexpected merge result: {merged:?}"
        );
        // Order-independent: merging the other way round produces the
        // identical union.
        let merged_swapped = merge_provenance(&b, &a);
        assert_eq!(merged, merged_swapped);
    }

    #[test]
    fn an_owned_observed_disagreement_merges_to_the_conservative_observed_role() {
        let mut a: HashMap<ValueId, LocationState> = HashMap::new();
        a.insert(
            ValueId(0),
            LocationState::Initialized((BTreeSet::from([ValueId(0)]), Role::Owned)),
        );
        let mut b: HashMap<ValueId, LocationState> = HashMap::new();
        b.insert(
            ValueId(0),
            LocationState::Initialized((BTreeSet::from([ValueId(0)]), Role::Observed)),
        );
        let merged = merge_provenance(&a, &b);
        assert_eq!(
            merged.get(&ValueId(0)),
            Some(&LocationState::Initialized((
                BTreeSet::from([ValueId(0)]),
                Role::Observed
            ))),
            "an Owned/Observed disagreement must resolve to the conservative Observed role: {merged:?}"
        );
    }

    /// `func f() -> i64 { return 1 }`, built directly (bypassing
    /// `nir::lower`) so each test can mutate exactly one thing about an
    /// otherwise-valid module and confirm the verifier catches it.
    fn valid_function(id: ItemId, name: Symbol) -> Function {
        Function {
            id,
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::I64,
                    kind: ValueKind::Const(Const::Int(1)),
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        }
    }

    fn codes_of(diagnostics: &[Diagnostic]) -> Vec<&str> {
        diagnostics.iter().map(|d| d.code).collect()
    }

    #[test]
    fn a_valid_module_has_no_diagnostics() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![valid_function(ItemId(0), name)],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn duplicate_function_ids_are_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let a = interner.intern("a");
        let b = interner.intern("b");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![valid_function(ItemId(0), a), valid_function(ItemId(0), b)],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_FUNCTION_ID));
    }

    #[test]
    fn duplicate_block_ids_are_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks.push(BasicBlock {
            id: BlockId(0),
            instructions: Vec::new(),
            terminator: Terminator::Return(None),
        });
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_BLOCK_ID));
    }

    #[test]
    fn a_function_with_no_blocks_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks.clear();
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert_eq!(codes_of(&diagnostics), vec![codes::EMPTY_FUNCTION]);
    }

    #[test]
    fn branching_to_a_nonexistent_block_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].terminator = Terminator::Branch(BlockId(99));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_BRANCH_TARGET));
    }

    #[test]
    fn calling_a_nonexistent_function_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            kind: ValueKind::Call(ItemId(42), Vec::new(), Vec::new(), Vec::new()),
        });
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_FUNCTION_REF));
    }

    #[test]
    fn referencing_an_undefined_value_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        // %99 is never defined anywhere in this function.
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(99)));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_VALUE));
    }

    #[test]
    fn loading_a_value_never_allocated_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        // %0 is a Const, not an Alloc; loading from it is invalid.
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            kind: ValueKind::Load(ValueId(0)),
        });
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_SLOT));
    }

    #[test]
    fn storing_a_mismatched_type_into_a_slot_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Bool,
                kind: ValueKind::Const(Const::Bool(true)),
            },
            Instruction::Store {
                slot: ValueId(0),
                value: ValueId(1),
                mode: crate::nir::OwnershipMode::Observe,
            },
        ];
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(1)));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::STORE_TYPE_MISMATCH));
    }

    #[test]
    fn a_non_bool_condition_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].terminator = Terminator::CondBranch {
            condition: ValueId(0), // declared i64, not bool
            then_block: BlockId(0),
            else_block: BlockId(0),
        };
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::NON_BOOL_CONDITION));
    }

    #[test]
    fn a_return_value_not_matching_the_declared_return_type_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Bool; // body still returns an i64
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::RETURN_TYPE_MISMATCH));
    }

    #[test]
    fn mismatched_operand_types_are_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Bool,
                kind: ValueKind::Const(Const::Bool(true)),
            },
            // Declared i64, but the right operand is a bool.
            Instruction::Value {
                result: ValueId(2),
                ty: Ty::I64,
                kind: ValueKind::Add(ValueId(0), ValueId(1)),
            },
        ];
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(2)));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::OPERAND_TYPE_MISMATCH));
    }

    #[test]
    fn an_unresolved_type_variable_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Var(crate::types::TyVar(0));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNRESOLVED_TYPE_VARIABLE));
    }

    #[test]
    fn an_error_type_in_executable_nir_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Error;
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::UNEXPECTED_ERROR_TYPE));
    }

    #[test]
    fn a_call_with_the_wrong_argument_count_is_rejected() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            // `g` takes zero parameters; this call passes one.
            kind: ValueKind::Call(ItemId(0), Vec::new(), vec![ValueId(0)], Vec::new()),
        });
        let callee = valid_function(ItemId(0), g_name);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(codes_of(&diagnostics).contains(&codes::ARITY_MISMATCH));
    }

    fn verify_one(function: Function, interner: &Interner) -> Vec<Diagnostic> {
        verify_one_with_aggregates(function, Vec::new(), Vec::new(), interner)
    }

    fn verify_one_with_aggregates(
        function: Function,
        records: Vec<(ItemId, RecordLayout)>,
        variants: Vec<(ItemId, VariantLayout)>,
        interner: &Interner,
    ) -> Vec<Diagnostic> {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records,
            variants,
        };
        verify_module(&module, source, interner, &ItemRegistry::default())
    }

    /// A `record Point { x: i64 }` layout, and a matching `func f() ->
    /// i64 { %0 = record.create @Point(%c); %1 = record.field
    /// @Point.0 %0; ret %1 }`-shaped valid function, for tests that
    /// mutate exactly one thing about it.
    fn record_point(interner: &mut Interner) -> (ItemId, RecordLayout, Symbol) {
        let point = interner.intern("Point");
        let x = interner.intern("x");
        (
            ItemId(100),
            RecordLayout {
                name: point,
                type_params: Vec::new(),
                fields: vec![(x, Ty::I64)],
                affine: false,
            },
            point,
        )
    }

    fn valid_record_function(
        id: ItemId,
        name: Symbol,
        record: ItemId,
        ty_name: Symbol,
    ) -> Function {
        Function {
            id,
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(1)),
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::Named(record, ty_name),
                        kind: ValueKind::RecordCreate(record, Vec::new(), vec![ValueId(0)]),
                    },
                    Instruction::Value {
                        result: ValueId(2),
                        ty: Ty::I64,
                        kind: ValueKind::RecordField {
                            base: ValueId(1),
                            record,
                            field: 0,
                        },
                    },
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        }
    }

    #[test]
    fn valid_record_create_and_field_access_has_no_diagnostics() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout, ty_name) = record_point(&mut interner);
        let function = valid_record_function(ItemId(0), name, record, ty_name);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn record_create_referencing_an_unknown_record_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let unknown_record = ItemId(999);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Named(unknown_record, interner.intern("Ghost")),
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(1)),
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::Named(unknown_record, interner.intern("Ghost")),
                        kind: ValueKind::RecordCreate(unknown_record, Vec::new(), vec![ValueId(0)]),
                    },
                ],
                terminator: Terminator::Return(Some(ValueId(1))),
            }],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_RECORD));
    }

    #[test]
    fn record_create_with_the_wrong_field_count_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout, ty_name) = record_point(&mut interner);
        let mut function = valid_record_function(ItemId(0), name, record, ty_name);
        // Point has one field, but this supplies two values.
        function.blocks[0].instructions[1] = Instruction::Value {
            result: ValueId(1),
            ty: Ty::Named(record, ty_name),
            kind: ValueKind::RecordCreate(record, Vec::new(), vec![ValueId(0), ValueId(0)]),
        };
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::RECORD_FIELDS_NOT_INITIALIZED_ONCE_EACH));
    }

    #[test]
    fn record_create_with_a_mismatched_field_type_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout, ty_name) = record_point(&mut interner);
        let mut function = valid_record_function(ItemId(0), name, record, ty_name);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::Bool,
            kind: ValueKind::Const(Const::Bool(true)),
        };
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::OPERAND_TYPE_MISMATCH));
    }

    #[test]
    fn record_field_with_an_out_of_range_index_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout, ty_name) = record_point(&mut interner);
        let mut function = valid_record_function(ItemId(0), name, record, ty_name);
        function.blocks[0].instructions[2] = Instruction::Value {
            result: ValueId(2),
            ty: Ty::I64,
            kind: ValueKind::RecordField {
                base: ValueId(1),
                record,
                field: 5,
            },
        };
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_FIELD));
    }

    /// A `variant Shape { Circle(i64), Empty }` layout.
    fn variant_shape(interner: &mut Interner) -> (ItemId, VariantLayout, Symbol) {
        let shape = interner.intern("Shape");
        let circle = interner.intern("Circle");
        let empty = interner.intern("Empty");
        (
            ItemId(200),
            VariantLayout {
                name: shape,
                type_params: Vec::new(),
                cases: vec![
                    CaseLayout {
                        name: circle,
                        payload: vec![Ty::I64],
                    },
                    CaseLayout {
                        name: empty,
                        payload: vec![],
                    },
                ],
            },
            shape,
        )
    }

    fn valid_variant_switch_function(
        id: ItemId,
        name: Symbol,
        variant: ItemId,
        ty_name: Symbol,
    ) -> Function {
        Function {
            id,
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(1)),
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::Named(variant, ty_name),
                            kind: ValueKind::VariantCreate {
                                variant,
                                case: 0,
                                type_args: Vec::new(),
                                payload: vec![ValueId(0)],
                            },
                        },
                    ],
                    terminator: Terminator::Switch {
                        scrutinee: ValueId(1),
                        variant,
                        cases: vec![BlockId(1), BlockId(2)],
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![Instruction::Value {
                        result: ValueId(2),
                        ty: Ty::I64,
                        kind: ValueKind::VariantPayload {
                            base: ValueId(1),
                            variant,
                            case: 0,
                            index: 0,
                        },
                    }],
                    terminator: Terminator::Return(Some(ValueId(2))),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![Instruction::Value {
                        result: ValueId(3),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(0)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(3))),
                },
            ],
        }
    }

    #[test]
    fn valid_variant_switch_and_payload_extraction_has_no_diagnostics() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn variant_create_referencing_an_unknown_variant_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let unknown_variant = ItemId(999);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Named(unknown_variant, interner.intern("Ghost")),
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::Named(unknown_variant, interner.intern("Ghost")),
                    kind: ValueKind::VariantCreate {
                        variant: unknown_variant,
                        case: 0,
                        type_args: Vec::new(),
                        payload: vec![],
                    },
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_VARIANT_OR_CASE));
    }

    #[test]
    fn variant_create_with_an_out_of_range_case_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Named(variant, ty_name),
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::Named(variant, ty_name),
                    kind: ValueKind::VariantCreate {
                        variant,
                        case: 9,
                        type_args: Vec::new(),
                        payload: vec![],
                    },
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_VARIANT_OR_CASE));
    }

    #[test]
    fn variant_create_with_the_wrong_payload_count_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Named(variant, ty_name),
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::Named(variant, ty_name),
                    kind: ValueKind::VariantCreate {
                        variant,
                        case: 0,
                        type_args: Vec::new(),
                        payload: vec![],
                    },
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::ARITY_MISMATCH));
    }

    #[test]
    fn switch_with_too_few_case_targets_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        function.blocks[0].terminator = Terminator::Switch {
            scrutinee: ValueId(1),
            variant,
            cases: vec![BlockId(1)],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::SWITCH_CASE_COVERAGE));
    }

    #[test]
    fn switch_targeting_a_nonexistent_block_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        function.blocks[0].terminator = Terminator::Switch {
            scrutinee: ValueId(1),
            variant,
            cases: vec![BlockId(1), BlockId(99)],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_BRANCH_TARGET));
    }

    #[test]
    fn payload_extraction_outside_its_case_refinement_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        // bb2 (the `Empty` case's own block) illegally extracts the
        // `Circle` case's payload -- never reached via that case's
        // switch edge.
        function.blocks[2].instructions.push(Instruction::Value {
            result: ValueId(4),
            ty: Ty::I64,
            kind: ValueKind::VariantPayload {
                base: ValueId(1),
                variant,
                case: 0,
                index: 0,
            },
        });
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::PAYLOAD_OUTSIDE_REFINEMENT));
    }

    #[test]
    fn two_switch_cases_sharing_one_block_reject_case_specific_payload_extraction() {
        // Both cases of the switch target bb1 -- reachable via either
        // case 0 or case 1, so nothing case-specific can be assumed
        // just from having reached it. A case-0 payload extraction
        // there must be rejected even though it's the very block the
        // switch's own case-0 edge points to.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        function.blocks[0].terminator = Terminator::Switch {
            scrutinee: ValueId(1),
            variant,
            cases: vec![BlockId(1), BlockId(1)],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::PAYLOAD_OUTSIDE_REFINEMENT));
    }

    #[test]
    fn a_case_refined_target_with_an_additional_ordinary_predecessor_is_rejected() {
        // bb1 (the `Circle` case's own block, legally extracting its
        // own payload under the switch alone) also gets a plain branch
        // predecessor -- a *reachable* one, via bb2 -- and that edge
        // guarantees nothing, so the intersection across bb1's
        // predecessors is empty and the extraction must be rejected.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        function.blocks[2].terminator = Terminator::Branch(BlockId(3));
        function.blocks.push(BasicBlock {
            id: BlockId(3),
            instructions: Vec::new(),
            terminator: Terminator::Branch(BlockId(1)),
        });
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::PAYLOAD_OUTSIDE_REFINEMENT));
    }

    #[test]
    fn an_unreachable_ordinary_predecessor_does_not_erase_a_refinement() {
        // The same third block, left unreachable. A dead edge proves
        // nothing, but it also disproves nothing: intersecting its
        // empty fact set in would wipe out a guarantee every genuinely
        // live path into bb1 really did establish.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        function.blocks.push(BasicBlock {
            id: BlockId(3),
            instructions: Vec::new(),
            terminator: Terminator::Branch(BlockId(1)),
        });
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(
            !codes_of(&diagnostics).contains(&codes::PAYLOAD_OUTSIDE_REFINEMENT),
            "an unreachable predecessor must contribute nothing: {diagnostics:?}"
        );
    }

    #[test]
    fn two_predecessors_carrying_the_same_refinement_are_accepted() {
        // bb2 (the `Empty` case's own block, dominated by bb0's
        // definition of the scrutinee like every block here) also
        // switches on the same scrutinee value instead of returning
        // directly -- a second, different edge into bb1, but one that
        // guarantees the exact same fact as the original switch's
        // case-0 edge. The intersection across both is still that one
        // fact, so bb1's existing case-0 payload extraction remains
        // legal.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        function.blocks[2].terminator = Terminator::Switch {
            scrutinee: ValueId(1),
            variant,
            cases: vec![BlockId(1), BlockId(2)],
        };
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn variant_payload_used_by_a_sibling_case_block_violates_dominance() {
        // Even if a payload extraction happened to be legal under its
        // own case's refinement, using its *result* in an unrelated
        // sibling block must still be caught by ordinary dominance --
        // this exercises that the aggregate-instruction additions
        // didn't bypass the existing dominance analysis.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (variant, layout, ty_name) = variant_shape(&mut interner);
        let mut function = valid_variant_switch_function(ItemId(0), name, variant, ty_name);
        // bb2 returns %2, which is only defined in bb1.
        function.blocks[2].terminator = Terminator::Return(Some(ValueId(2)));
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::NON_DOMINATING_DEFINITION));
    }

    #[test]
    fn missing_entry_block_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        // Only block is bb1, not bb0.
        function.blocks[0].id = BlockId(1);
        function.blocks[0].terminator = Terminator::Return(None);
        function.blocks[0].instructions.clear();
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::MISSING_ENTRY_BLOCK));
    }

    #[test]
    fn a_reordered_bb0_is_still_a_valid_entry_block() {
        // bb0 exists but isn't first in the vector; entry status must
        // come from the id, never from vector position.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(0)),
                },
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(1)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(0))),
                },
            ],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn duplicate_parameter_value_ids_are_rejected() {
        use crate::nir::Param;
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.params = vec![
            Param {
                value: ValueId(0),
                ty: Ty::I64,
                take: false,
            },
            Param {
                value: ValueId(0),
                ty: Ty::Bool,
                take: false,
            },
        ];
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_VALUE_DEFINITION));
    }

    #[test]
    fn duplicate_instruction_result_ids_are_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        // %0 is already defined by `valid_function`'s single instruction;
        // add a second instruction that reuses it.
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(2)),
        });
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_VALUE_DEFINITION));
    }

    #[test]
    fn a_parameter_colliding_with_an_instruction_result_is_rejected() {
        use crate::nir::Param;
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        // `valid_function`'s single instruction already produces %0;
        // adding a parameter that also claims %0 is a collision across
        // the two different kinds of definition.
        function.params = vec![Param {
            value: ValueId(0),
            ty: Ty::I64,
            take: false,
        }];
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_VALUE_DEFINITION));
    }

    #[test]
    fn a_forward_reference_within_one_block_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions = vec![
            // %0 used here, before it is defined below.
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::I64,
                kind: ValueKind::Neg(ValueId(0)),
            },
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            },
        ];
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(1)));
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::USE_BEFORE_DEFINITION));
    }

    #[test]
    fn a_value_defined_in_a_sibling_branch_is_rejected() {
        // bb0 branches to bb1 or bb2; bb1 defines %1, bb2 uses it via
        // its return terminator despite never having executed bb1.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::Bool,
                        kind: ValueKind::Const(Const::Bool(true)),
                    }],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(1)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(1))),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    // %1 was only ever defined in the sibling bb1.
                    terminator: Terminator::Return(Some(ValueId(1))),
                },
            ],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::NON_DOMINATING_DEFINITION));
    }

    #[test]
    fn loading_a_slot_only_allocated_in_one_branch_is_rejected() {
        // bb1 allocates and stores a slot; bb2 (the sibling) never
        // does; bb3 (their merge) loads it regardless.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::Bool,
                        kind: ValueKind::Const(Const::Bool(true)),
                    }],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::I64,
                            kind: ValueKind::Alloc,
                        },
                        Instruction::Value {
                            result: ValueId(2),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(1)),
                        },
                        Instruction::Store {
                            slot: ValueId(1),
                            value: ValueId(2),
                            mode: crate::nir::OwnershipMode::Observe,
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    // %1 (the alloc) does not dominate bb3: the else
                    // path (bb2) reaches it without ever allocating it.
                    instructions: vec![Instruction::Value {
                        result: ValueId(3),
                        ty: Ty::I64,
                        kind: ValueKind::Load(ValueId(1)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(3))),
                },
            ],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(codes_of(&diagnostics).contains(&codes::NON_DOMINATING_DEFINITION));
    }

    #[test]
    fn a_drop_on_only_one_branch_still_double_drops_at_an_unconditional_merge() {
        // bb1 (the then-branch) drops %1; bb2 (the sibling else-branch)
        // never does; bb3 (their merge) drops %1 again unconditionally
        // regardless of which branch actually ran. A *must* analysis
        // (dropped on every incoming path) would intersect bb1's and
        // bb2's own out-facts down to the empty set and miss this
        // entirely; this must be caught because the bb1-then-bb3 path
        // genuinely drops %1 twice.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: resource_ty.clone(),
                            kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::Bool,
                            kind: ValueKind::Const(Const::Bool(true)),
                        },
                    ],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(1),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![Instruction::Drop { value: ValueId(0) }],
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![Instruction::Drop { value: ValueId(0) }],
                    terminator: Terminator::Return(None),
                },
            ],
        };
        let records = vec![(
            resource,
            RecordLayout {
                name: resource_name,
                type_params: Vec::new(),
                fields: Vec::new(),
                affine: true,
            },
        )];
        let diagnostics = verify_one_with_aggregates(function, records, Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::DOUBLE_DROP));
    }

    #[test]
    fn dropping_a_resource_through_two_aliased_loads_of_the_same_slot_is_rejected() {
        // %2 and %3 are two distinct `ValueId`s, but both are `Load`s of
        // the identical slot (%0) -- `DOUBLE_DROP` alone (keyed by exact
        // `ValueId`) cannot see this at all, since %2 != %3; this is
        // exactly the "alias-based duplicate destruction through
        // different `ValueId`s" case `RESOURCE_USE_AFTER_CONSUME` exists
        // to independently catch.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: resource_ty.clone(),
                        kind: ValueKind::Alloc,
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: resource_ty.clone(),
                        kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                    },
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(1),
                        mode: crate::nir::OwnershipMode::Transfer,
                    },
                    Instruction::Value {
                        result: ValueId(2),
                        ty: resource_ty.clone(),
                        kind: ValueKind::Load(ValueId(0)),
                    },
                    Instruction::Drop { value: ValueId(2) },
                    Instruction::Value {
                        result: ValueId(3),
                        ty: resource_ty.clone(),
                        kind: ValueKind::Load(ValueId(0)),
                    },
                    Instruction::Drop { value: ValueId(3) },
                ],
                terminator: Terminator::Return(None),
            }],
        };
        let records = vec![(
            resource,
            RecordLayout {
                name: resource_name,
                type_params: Vec::new(),
                fields: Vec::new(),
                affine: true,
            },
        )];
        let diagnostics = verify_one_with_aggregates(function, records, Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_USE_AFTER_CONSUME),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn dropping_a_resource_already_moved_into_a_take_argument_is_rejected() {
        // `sink`'s own `file` parameter is declared `take`; the caller's
        // %0 is passed to it and then dropped again -- a genuine
        // use-after-move `resourceck` would also reject at the source
        // level, but reconstructed here purely from NIR, independent of
        // whether the source ever passed through `resourceck` at all.
        let mut interner = Interner::new();
        let caller_name = interner.intern("f");
        let sink_name = interner.intern("sink");
        let resource_name = interner.intern("File");
        let resource = ItemId(2);
        let resource_ty = Ty::Named(resource, resource_name);
        let sink = Function {
            id: ItemId(1),
            name: sink_name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: resource_ty.clone(),
                take: true,
            }],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Drop { value: ValueId(0) }],
                terminator: Terminator::Return(None),
            }],
        };
        let caller = Function {
            id: ItemId(0),
            name: caller_name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: resource_ty.clone(),
                        kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::Unit,
                        kind: ValueKind::Call(ItemId(1), Vec::new(), vec![ValueId(0)], Vec::new()),
                    },
                    Instruction::Drop { value: ValueId(0) },
                ],
                terminator: Terminator::Return(None),
            }],
        };
        let records = vec![(
            resource,
            RecordLayout {
                name: resource_name,
                type_params: Vec::new(),
                fields: Vec::new(),
                affine: true,
            },
        )];
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![caller, sink],
            records,
            variants: Vec::new(),
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_USE_AFTER_CONSUME),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_valid_loop_cfg_has_no_diagnostics() {
        // Standard header/body/exit shape: a mutable counter allocated
        // in the entry, loaded/compared/incremented in the header and
        // body, with a back-edge from body to header.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: Ty::I64,
                            kind: ValueKind::Alloc,
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(0)),
                        },
                        Instruction::Store {
                            slot: ValueId(0),
                            mode: crate::nir::OwnershipMode::Observe,
                            value: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(2),
                            ty: Ty::I64,
                            kind: ValueKind::Load(ValueId(0)),
                        },
                        Instruction::Value {
                            result: ValueId(3),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(10)),
                        },
                        Instruction::Value {
                            result: ValueId(4),
                            ty: Ty::Bool,
                            kind: ValueKind::Lt(ValueId(2), ValueId(3)),
                        },
                    ],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(4),
                        then_block: BlockId(2),
                        else_block: BlockId(3),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(5),
                            ty: Ty::I64,
                            kind: ValueKind::Load(ValueId(0)),
                        },
                        Instruction::Value {
                            result: ValueId(6),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(1)),
                        },
                        Instruction::Value {
                            result: ValueId(7),
                            ty: Ty::I64,
                            kind: ValueKind::Add(ValueId(5), ValueId(6)),
                        },
                        Instruction::Store {
                            slot: ValueId(0),
                            mode: crate::nir::OwnershipMode::Observe,
                            value: ValueId(7),
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![Instruction::Value {
                        result: ValueId(8),
                        ty: Ty::I64,
                        kind: ValueKind::Load(ValueId(0)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(8))),
                },
            ],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_valid_conditional_cfg_with_an_entry_allocation_used_in_both_branches_has_no_diagnostics() {
        // The slot is allocated once in the entry block (which
        // dominates every other block), then both the then- and
        // else-branches store into it before a shared merge block loads
        // it back -- exactly the shape if/else lowering actually
        // produces.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: Ty::Bool,
                            kind: ValueKind::Const(Const::Bool(true)),
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::I64,
                            kind: ValueKind::Alloc,
                        },
                    ],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(2),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(1)),
                        },
                        Instruction::Store {
                            slot: ValueId(1),
                            mode: crate::nir::OwnershipMode::Observe,
                            value: ValueId(2),
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(3),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(2)),
                        },
                        Instruction::Store {
                            slot: ValueId(1),
                            mode: crate::nir::OwnershipMode::Observe,
                            value: ValueId(3),
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![Instruction::Value {
                        result: ValueId(4),
                        ty: Ty::I64,
                        kind: ValueKind::Load(ValueId(1)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(4))),
                },
            ],
        };
        let diagnostics = verify_one(function, &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    // -- Generic type-argument validation (`rfcs/0008`) -----------------

    #[test]
    fn a_type_parameter_escaping_a_non_generic_function_is_rejected() {
        // A `Ty::Param` belonging to *no* declaration this function
        // itself declares -- no valid lowering ever produces this; only
        // a hand-built (malformed) NIR module can.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let foreign_t = interner.intern("T");
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Param(TypeParamId(999), foreign_t);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::Param(TypeParamId(999), foreign_t),
            kind: ValueKind::Const(Const::Int(1)),
        };
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(0)));
        let diagnostics = verify_one(function, &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::ESCAPING_TYPE_PARAMETER),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_type_parameter_matching_the_functions_own_declaration_is_accepted() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let t = interner.intern("T");
        let mut function = valid_function(ItemId(0), name);
        function.type_params = vec![(TypeParamId(0), t)];
        function.return_type = Ty::Param(TypeParamId(0), t);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::Param(TypeParamId(0), t),
            kind: ValueKind::Const(Const::Int(1)),
        };
        // A `Ty::Param`-typed constant is itself a defense-in-depth
        // impossibility (no valid lowering emits one), but this test
        // only cares about the parameter-scope check specifically; the
        // const/type mismatch it also happens to trip is not what is
        // being asserted here.
        let diagnostics = verify_one(function, &interner);
        assert!(
            !codes_of(&diagnostics).contains(&codes::ESCAPING_TYPE_PARAMETER),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_duplicate_type_parameter_in_a_function_declaration_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let t = interner.intern("T");
        let mut function = valid_function(ItemId(0), name);
        function.type_params = vec![(TypeParamId(0), t), (TypeParamId(0), t)];
        let diagnostics = verify_one(function, &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::DUPLICATE_TYPE_PARAMETER),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_duplicate_type_parameter_in_a_record_declaration_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let point = interner.intern("Point");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: point,
            type_params: vec![(TypeParamId(0), t), (TypeParamId(0), t)],
            fields: vec![],
            affine: false,
        };
        let function = valid_function(ItemId(0), name);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::DUPLICATE_TYPE_PARAMETER),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_duplicate_type_parameter_in_a_variant_declaration_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let shape = interner.intern("Shape");
        let t = interner.intern("T");
        let variant = ItemId(200);
        let layout = VariantLayout {
            name: shape,
            type_params: vec![(TypeParamId(0), t), (TypeParamId(0), t)],
            cases: vec![],
        };
        let function = valid_function(ItemId(0), name);
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::DUPLICATE_TYPE_PARAMETER),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_unresolved_type_variable_nested_inside_an_applied_type_is_rejected() {
        // `Ty::Var` buried *inside* a `Ty::Applied`'s own argument list
        // (`Box[Var(0)]`), not just at the top level -- a hand-built NIR
        // module bypassing typeck's own resolution is the only way this
        // is ever reachable.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: boxed,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![],
            affine: false,
        };
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Applied(record, vec![Ty::Var(crate::types::TyVar(0))]);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::UNRESOLVED_TYPE_VARIABLE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_error_type_nested_inside_an_applied_type_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: boxed,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![],
            affine: false,
        };
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Applied(record, vec![Ty::Error]);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::UNEXPECTED_ERROR_TYPE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn generic_arity_mismatch_nested_inside_an_applied_types_own_argument_is_rejected() {
        // `Outer[Pair[i64]]`, where `Pair` itself declares two type
        // parameters -- the arity problem is one level *inside* the
        // outer application's own argument, not at `Outer` itself, so
        // recursive validation (not just a top-level check) is required
        // to catch it.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let outer_name = interner.intern("Outer");
        let pair_name = interner.intern("Pair");
        let t = interner.intern("T");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let outer = ItemId(100);
        let pair = ItemId(101);
        let outer_layout = RecordLayout {
            name: outer_name,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![],
            affine: false,
        };
        let pair_layout = RecordLayout {
            name: pair_name,
            type_params: vec![(TypeParamId(1), a), (TypeParamId(2), b)],
            fields: vec![],
            affine: false,
        };
        let mut function = valid_function(ItemId(0), name);
        function.return_type = Ty::Applied(outer, vec![Ty::Applied(pair, vec![Ty::I64])]);
        let diagnostics = verify_one_with_aggregates(
            function,
            vec![(outer, outer_layout), (pair, pair_layout)],
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_ARITY_MISMATCH),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_call_supplying_the_wrong_number_of_type_arguments_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let mut callee = valid_function(ItemId(0), g_name);
        callee.type_params = vec![(TypeParamId(0), t)];
        callee.return_type = Ty::Param(TypeParamId(0), t);
        callee.params = vec![crate::nir::Param {
            value: ValueId(0),
            ty: Ty::Param(TypeParamId(0), t),
            take: false,
        }];
        callee.blocks[0].instructions.clear();
        callee.blocks[0].terminator = Terminator::Return(Some(ValueId(0)));

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            // `g` declares one type parameter; this call supplies none.
            kind: ValueKind::Call(ItemId(0), Vec::new(), vec![ValueId(0)], Vec::new()),
        });
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_ARITY_MISMATCH),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_valid_generic_call_with_matching_type_argument_count_has_no_diagnostics() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let mut callee = valid_function(ItemId(0), g_name);
        callee.type_params = vec![(TypeParamId(0), t)];
        callee.return_type = Ty::Param(TypeParamId(0), t);
        callee.params = vec![crate::nir::Param {
            value: ValueId(0),
            ty: Ty::Param(TypeParamId(0), t),
            take: false,
        }];
        callee.blocks[0].instructions.clear();
        callee.blocks[0].terminator = Terminator::Return(Some(ValueId(0)));

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(1)),
        };
        caller.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            kind: ValueKind::Call(ItemId(0), vec![Ty::I64], vec![ValueId(0)], Vec::new()),
        });
        caller.blocks[0].terminator = Terminator::Return(Some(ValueId(1)));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_phantom_type_parameter_never_occurring_in_params_or_return_is_accepted() {
        // `T` appears in the function's own declared type parameters but
        // nowhere in its params or return type -- a legitimate
        // compile-time-only marker, not a malformed declaration; the
        // verifier must not require every declared parameter to actually
        // occur anywhere.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let t = interner.intern("T");
        let mut function = valid_function(ItemId(0), name);
        function.type_params = vec![(TypeParamId(0), t)];
        let diagnostics = verify_one(function, &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_phantom_type_parameter_on_a_record_never_occurring_in_any_field_is_accepted() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let marker = interner.intern("Marker");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: marker,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![(interner.intern("tag"), Ty::I64)],
            affine: false,
        };
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(1)),
        };
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::Applied(record, vec![Ty::Bool]),
            kind: ValueKind::RecordCreate(record, vec![Ty::Bool], vec![ValueId(0)]),
        });
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(0)));
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    /// Built programmatically: a `Ty::Applied` nested well past
    /// `crate::limits::MAX_GENERIC_DEPTH`, used as a function's own
    /// return type. `check_type_root`'s depth check runs before every
    /// recursive check this verifier would otherwise run over a type
    /// (`check_no_bad_type`, `check_named_type_identity`,
    /// `check_type_param_scope`), each of which would otherwise descend
    /// into it once per level. Must terminate (this test finishing at
    /// all is the no-hang assertion), never overflow the native call
    /// stack, and must produce exactly the dedicated `V0035` diagnostic
    /// -- not silently pass, and not one diagnostic per nested level.
    #[test]
    fn a_pathologically_deep_applied_type_does_not_overflow_the_verifier() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: boxed,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![],
            affine: false,
        };
        let depth = crate::limits::MAX_GENERIC_DEPTH + 200;
        let mut ty = Ty::I64;
        for _ in 0..depth {
            ty = Ty::Applied(record, vec![ty]);
        }
        let mut function = valid_function(ItemId(0), name);
        function.return_type = ty;
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    // -- `check_type_root` over every type root `verify_module` inspects --

    /// A `record Box[T] { payload: i64 }`-shaped layout (`payload` is
    /// deliberately non-generic; only its *use* as a type root under
    /// test needs to be generic-shaped) reused by every over-depth test
    /// below to build a `Ty::Applied` nested `depth` levels deep.
    fn deeply_applied_type(record: ItemId, depth: usize) -> Ty {
        let mut ty = Ty::I64;
        for _ in 0..depth {
            ty = Ty::Applied(record, vec![ty]);
        }
        ty
    }

    fn box_layout(interner: &mut Interner) -> (ItemId, RecordLayout) {
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        (
            ItemId(100),
            RecordLayout {
                name: boxed,
                type_params: vec![(TypeParamId(0), t)],
                fields: vec![],
                affine: false,
            },
        )
    }

    #[test]
    fn an_over_depth_function_parameter_produces_generic_depth_exceeded() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout) = box_layout(&mut interner);
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let mut function = valid_function(ItemId(0), name);
        function.params.push(crate::nir::Param {
            value: ValueId(1),
            ty: deeply_applied_type(record, depth),
            take: false,
        });
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    #[test]
    fn an_over_depth_function_return_type_produces_generic_depth_exceeded() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout) = box_layout(&mut interner);
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let mut function = valid_function(ItemId(0), name);
        function.return_type = deeply_applied_type(record, depth);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    #[test]
    fn an_over_depth_record_field_produces_generic_depth_exceeded() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, mut layout) = box_layout(&mut interner);
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let deep = interner.intern("deep");
        layout
            .fields
            .push((deep, deeply_applied_type(record, depth)));
        let function = valid_function(ItemId(0), name);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    #[test]
    fn an_over_depth_variant_payload_produces_generic_depth_exceeded() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, record_layout) = box_layout(&mut interner);
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let maybe = interner.intern("Maybe");
        let some = interner.intern("Some");
        let variant = ItemId(101);
        let variant_layout = VariantLayout {
            name: maybe,
            type_params: Vec::new(),
            cases: vec![CaseLayout {
                name: some,
                payload: vec![deeply_applied_type(record, depth)],
            }],
        };
        let function = valid_function(ItemId(0), name);
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: vec![(record, record_layout)],
            variants: vec![(variant, variant_layout)],
        };
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    #[test]
    fn an_over_depth_instruction_result_type_produces_generic_depth_exceeded() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout) = box_layout(&mut interner);
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: deeply_applied_type(record, depth),
            kind: ValueKind::Const(Const::Int(1)),
        });
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    /// A type nested *exactly* `MAX_GENERIC_DEPTH` levels deep is still
    /// within bounds -- `exceeds_generic_depth` must reject strictly
    /// past the limit, not at it, so this must produce no `V0035`.
    #[test]
    fn a_type_nested_exactly_at_the_generic_depth_limit_is_accepted() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let (record, layout) = box_layout(&mut interner);
        let mut function = valid_function(ItemId(0), name);
        function.return_type = deeply_applied_type(record, crate::limits::MAX_GENERIC_DEPTH);
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            !codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    // -- Shared type-root validation (`check_type_root`) at use-site generic arguments --

    /// `func g[T](x: i64) -> i64 { return x }` -- `T` occurs in neither
    /// its parameter nor its return type, so the declaration itself is
    /// legitimate (a compile-time-only marker); every *call* to it must
    /// still supply a valid type argument for its own sake.
    fn phantom_generic_callee(id: ItemId, name: Symbol, t: Symbol) -> Function {
        Function {
            id,
            name,
            type_params: vec![(TypeParamId(0), t)],
            requirements: Vec::new(),
            params: vec![crate::nir::Param {
                value: ValueId(0),
                ty: Ty::I64,
                take: false,
            }],
            return_type: Ty::I64,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        }
    }

    /// `func f() -> i64 { ...; return %1 }` calling `g` (id 0) with
    /// `type_arg` as its sole type argument and a single `const.i64 1`
    /// as its sole value argument.
    fn caller_calling_g_with_type_arg(f_name: Symbol, type_arg: Ty) -> Function {
        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            kind: ValueKind::Call(ItemId(0), vec![type_arg], vec![ValueId(0)], Vec::new()),
        });
        caller.blocks[0].terminator = Terminator::Return(Some(ValueId(1)));
        caller
    }

    #[test]
    fn a_call_with_ty_error_as_a_phantom_type_argument_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let caller = caller_calling_g_with_type_arg(f_name, Ty::Error);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::UNEXPECTED_ERROR_TYPE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_call_with_an_unresolved_type_variable_as_a_phantom_type_argument_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let caller = caller_calling_g_with_type_arg(f_name, Ty::Var(crate::types::TyVar(0)));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::UNRESOLVED_TYPE_VARIABLE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_call_with_an_applied_type_naming_an_unknown_declaration_as_a_type_argument_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let unknown = ItemId(9999);
        let caller = caller_calling_g_with_type_arg(f_name, Ty::Applied(unknown, vec![Ty::I64]));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::UNKNOWN_NAMED_TYPE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_call_with_a_nested_wrong_arity_application_as_a_type_argument_is_rejected() {
        // The call's own type argument is `Pair[i64]` -- valid on its
        // own shape, but `Pair` actually declares *two* type parameters,
        // so this arity problem is one level inside the call's own type
        // argument, not at the call itself.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let pair_name = interner.intern("Pair");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let pair = ItemId(100);
        let pair_layout = RecordLayout {
            name: pair_name,
            type_params: vec![(TypeParamId(1), a), (TypeParamId(2), b)],
            fields: vec![],
            affine: false,
        };
        let caller = caller_calling_g_with_type_arg(f_name, Ty::Applied(pair, vec![Ty::I64]));
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: vec![(pair, pair_layout)],
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_ARITY_MISMATCH),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_call_with_a_type_argument_deeper_than_the_generic_depth_limit_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let boxed = interner.intern("Box");
        let box_t = interner.intern("T");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let box_item = ItemId(100);
        let box_layout = RecordLayout {
            name: boxed,
            type_params: vec![(TypeParamId(1), box_t)],
            fields: vec![],
            affine: false,
        };
        let depth = crate::limits::MAX_GENERIC_DEPTH + 50;
        let mut deep_ty = Ty::I64;
        for _ in 0..depth {
            deep_ty = Ty::Applied(box_item, vec![deep_ty]);
        }
        let caller = caller_calling_g_with_type_arg(f_name, deep_ty);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: vec![(box_item, box_layout)],
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED),
            "unexpected diagnostics: {diagnostics:?}"
        );
        // A controlled number of diagnostics, not one per nested level.
        assert!(
            diagnostics.len() < depth,
            "expected a single depth diagnostic, not one per nested level: {} diagnostics",
            diagnostics.len()
        );
    }

    #[test]
    fn a_valid_phantom_generic_call_still_verifies() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let t = interner.intern("T");
        let callee = phantom_generic_callee(ItemId(0), g_name, t);
        let caller = caller_calling_g_with_type_arg(f_name, Ty::Bool);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_valid_generic_record_construction_with_a_real_field_still_verifies() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let boxed = interner.intern("Box");
        let t = interner.intern("T");
        let record = ItemId(100);
        let layout = RecordLayout {
            name: boxed,
            type_params: vec![(TypeParamId(0), t)],
            fields: vec![(interner.intern("value"), Ty::Param(TypeParamId(0), t))],
            affine: false,
        };
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(1)),
        };
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::Applied(record, vec![Ty::I64]),
            kind: ValueKind::RecordCreate(record, vec![Ty::I64], vec![ValueId(0)]),
        });
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(2),
            ty: Ty::I64,
            kind: ValueKind::RecordField {
                base: ValueId(1),
                record,
                field: 0,
            },
        });
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(2)));
        let diagnostics =
            verify_one_with_aggregates(function, vec![(record, layout)], Vec::new(), &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_valid_generic_variant_construction_still_verifies() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let maybe = interner.intern("Maybe");
        let some_case = interner.intern("Some");
        let t = interner.intern("T");
        let variant = ItemId(200);
        let layout = VariantLayout {
            name: maybe,
            type_params: vec![(TypeParamId(0), t)],
            cases: vec![CaseLayout {
                name: some_case,
                payload: vec![Ty::Param(TypeParamId(0), t)],
            }],
        };
        let mut function = valid_function(ItemId(0), name);
        function.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(1)),
        };
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::Applied(variant, vec![Ty::I64]),
            kind: ValueKind::VariantCreate {
                variant,
                case: 0,
                type_args: vec![Ty::I64],
                payload: vec![ValueId(0)],
            },
        });
        // Not projecting the payload back out here: doing so validly
        // requires a case-refinement edge (a `switch`), which is its own
        // separate, already-covered concern
        // (`valid_variant_switch_and_payload_extraction_has_no_diagnostics`)
        // -- this test is only about construction itself verifying.
        function.blocks[0].terminator = Terminator::Return(Some(ValueId(0)));
        let diagnostics =
            verify_one_with_aggregates(function, Vec::new(), vec![(variant, layout)], &interner);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    // -- Fix 3: protocol layout validation (`rfcs/0009`) -----------------

    fn verify_module_with(
        protocols: Vec<(ItemId, ProtocolLayout)>,
        extends: Vec<(ItemId, ExtendLayout)>,
        functions: Vec<Function>,
        interner: &Interner,
    ) -> Vec<Diagnostic> {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let module = Module {
            protocols,
            extends,
            functions,
            records: Vec::new(),
            variants: Vec::new(),
        };
        verify_module(&module, source, interner, &ItemRegistry::default())
    }

    /// A one-method `protocol Equal[T] { func equal(left: T, right: T)
    /// -> bool; }` layout, for tests that mutate exactly one thing about
    /// an otherwise-valid protocol declaration.
    fn valid_equal_protocol(interner: &mut Interner) -> (ItemId, ProtocolLayout) {
        let t = TypeParamId(0);
        let t_symbol = interner.intern("T");
        let equal = interner.intern("equal");
        (
            ItemId(0),
            ProtocolLayout {
                name: interner.intern("Equal"),
                type_params: vec![(t, t_symbol)],
                methods: vec![ProtocolMethodLayout {
                    name: equal,
                    params: vec![Ty::Param(t, t_symbol), Ty::Param(t, t_symbol)],
                    return_type: Ty::Bool,
                }],
            },
        )
    }

    #[test]
    fn a_valid_protocol_layout_has_no_diagnostics() {
        let mut interner = Interner::new();
        let (id, protocol) = valid_equal_protocol(&mut interner);
        let diagnostics =
            verify_module_with(vec![(id, protocol)], Vec::new(), Vec::new(), &interner);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn a_protocol_declaring_the_same_type_parameter_twice_is_rejected() {
        let mut interner = Interner::new();
        let (id, mut protocol) = valid_equal_protocol(&mut interner);
        let t = protocol.type_params[0];
        protocol.type_params.push(t);
        let diagnostics =
            verify_module_with(vec![(id, protocol)], Vec::new(), Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_TYPE_PARAMETER));
    }

    #[test]
    fn a_protocol_method_using_a_foreign_type_parameter_is_rejected() {
        let mut interner = Interner::new();
        let (id, mut protocol) = valid_equal_protocol(&mut interner);
        let foreign_symbol = interner.intern("U");
        protocol.methods[0].params[0] = Ty::Param(TypeParamId(99), foreign_symbol);
        let diagnostics =
            verify_module_with(vec![(id, protocol)], Vec::new(), Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::ESCAPING_TYPE_PARAMETER));
    }

    #[test]
    fn a_protocol_method_returning_an_error_type_is_rejected() {
        let mut interner = Interner::new();
        let (id, mut protocol) = valid_equal_protocol(&mut interner);
        protocol.methods[0].return_type = Ty::Error;
        let diagnostics =
            verify_module_with(vec![(id, protocol)], Vec::new(), Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNEXPECTED_ERROR_TYPE));
    }

    #[test]
    fn a_protocol_method_parameter_naming_an_unknown_type_is_rejected() {
        let mut interner = Interner::new();
        let (id, mut protocol) = valid_equal_protocol(&mut interner);
        let bogus = interner.intern("Bogus");
        protocol.methods[0].params[0] = Ty::Named(ItemId(999), bogus);
        let diagnostics =
            verify_module_with(vec![(id, protocol)], Vec::new(), Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_NAMED_TYPE));
    }

    #[test]
    fn a_protocol_method_parameter_nested_deeper_than_the_generic_depth_limit_is_rejected() {
        let mut interner = Interner::new();
        let (id, mut protocol) = valid_equal_protocol(&mut interner);
        let box_item = ItemId(50);
        let t = protocol.type_params[0];
        let mut deep = Ty::Param(t.0, t.1);
        for _ in 0..(MAX_GENERIC_DEPTH + 2) {
            deep = Ty::Applied(box_item, vec![deep]);
        }
        protocol.methods[0].params[0] = deep;
        let diagnostics =
            verify_module_with(vec![(id, protocol)], Vec::new(), Vec::new(), &interner);
        assert!(codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED));
    }

    // -- Fix 3: extend layout validation (`rfcs/0009`) -------------------

    /// `func equal_i64(left: i64, right: i64) -> bool { return left ==
    /// right }`, the implementing function for `extend Equal[i64]`
    /// below.
    fn equal_i64_method(interner: &mut Interner) -> Function {
        Function {
            id: ItemId(1),
            name: interner.intern("equal_i64"),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![
                crate::nir::Param {
                    value: ValueId(0),
                    ty: Ty::I64,
                    take: false,
                },
                crate::nir::Param {
                    value: ValueId(1),
                    ty: Ty::I64,
                    take: false,
                },
            ],
            return_type: Ty::Bool,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(2),
                    ty: Ty::Bool,
                    kind: ValueKind::Eq(ValueId(0), ValueId(1)),
                }],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        }
    }

    /// `extend Equal[i64] { func equal(left: i64, right: i64) -> bool
    /// {..} }` -- a concrete extend of [`valid_equal_protocol`], for
    /// tests that mutate exactly one thing about an otherwise-valid
    /// extend declaration.
    fn valid_equal_i64_extend() -> (ItemId, ExtendLayout) {
        (
            ItemId(10),
            ExtendLayout {
                protocol: ItemId(0),
                type_params: Vec::new(),
                protocol_arguments: vec![Ty::I64],
                requirements: Vec::new(),
                methods: vec![ItemId(1)],
            },
        )
    }

    #[test]
    fn a_valid_extend_layout_has_no_diagnostics() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let method = equal_i64_method(&mut interner);
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn an_extend_method_declaring_raises_is_rejected() {
        // hir::lower/typeck both already reject this for ordinary source
        // (R0031/T0034); this verifier never trusts hand-built NIR to
        // already satisfy it -- a fallible implementation could
        // otherwise satisfy an apparently infallible protocol method.
        // (`ItemId(20)` need not itself be a declared variant for this
        // specific check -- it may also trigger the independent
        // UNKNOWN_RAISES_TYPE check, which does not interfere with the
        // assertion below.)
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let mut method = equal_i64_method(&mut interner);
        method.raises = vec![ItemId(20)];
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTEND_METHOD_MUST_BE_INFALLIBLE));
    }

    #[test]
    fn an_extend_naming_an_unknown_protocol_is_rejected() {
        let mut interner = Interner::new();
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.protocol = ItemId(999);
        let method = equal_i64_method(&mut interner);
        let diagnostics = verify_module_with(
            Vec::new(),
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_EXTEND_PROTOCOL));
    }

    #[test]
    fn an_extend_supplying_the_wrong_number_of_protocol_arguments_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.protocol_arguments = vec![Ty::I64, Ty::I64];
        let method = equal_i64_method(&mut interner);
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTEND_PROTOCOL_ARITY_MISMATCH));
    }

    #[test]
    fn an_extend_requirement_naming_an_unknown_protocol_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.requirements = vec![CapabilityRequirement::new(ItemId(999), vec![Ty::I64])];
        let method = equal_i64_method(&mut interner);
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_REQUIREMENT_PROTOCOL));
    }

    #[test]
    fn an_extend_requirement_with_the_wrong_arity_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.requirements = vec![CapabilityRequirement::new(protocol_id, Vec::new())];
        let method = equal_i64_method(&mut interner);
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::REQUIREMENT_ARITY_MISMATCH));
    }

    #[test]
    fn an_extend_with_the_wrong_method_table_length_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.methods = Vec::new();
        let method = equal_i64_method(&mut interner);
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTEND_METHOD_COUNT_MISMATCH));
    }

    #[test]
    fn an_extend_method_referencing_an_unknown_function_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.methods = vec![ItemId(999)];
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            Vec::new(),
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTEND_METHOD_UNKNOWN_FUNCTION));
    }

    #[test]
    fn an_extend_method_function_not_sharing_its_extends_type_parameter_scope_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let mut method = equal_i64_method(&mut interner);
        method.type_params = vec![(TypeParamId(77), interner.intern("U"))];
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTEND_METHOD_TYPE_PARAM_MISMATCH));
    }

    #[test]
    fn an_extend_method_with_a_signature_not_matching_its_protocol_method_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let mut method = equal_i64_method(&mut interner);
        // Declares `(i64, i64) -> i64` where the protocol (substituted
        // for `Equal[i64]`) requires `(i64, i64) -> bool`.
        method.return_type = Ty::I64;
        method.blocks[0].instructions[0] = Instruction::Value {
            result: ValueId(2),
            ty: Ty::I64,
            kind: ValueKind::Add(ValueId(0), ValueId(1)),
        };
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTEND_METHOD_SIGNATURE_MISMATCH));
    }

    #[test]
    fn an_extend_using_the_same_function_for_two_method_slots_is_rejected() {
        let mut interner = Interner::new();
        let t = TypeParamId(0);
        let t_symbol = interner.intern("T");
        let protocol_id = ItemId(0);
        let protocol = ProtocolLayout {
            name: interner.intern("Equal"),
            type_params: vec![(t, t_symbol)],
            methods: vec![
                ProtocolMethodLayout {
                    name: interner.intern("equal"),
                    params: vec![Ty::Param(t, t_symbol), Ty::Param(t, t_symbol)],
                    return_type: Ty::Bool,
                },
                ProtocolMethodLayout {
                    name: interner.intern("not_equal"),
                    params: vec![Ty::Param(t, t_symbol), Ty::Param(t, t_symbol)],
                    return_type: Ty::Bool,
                },
            ],
        };
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.methods = vec![ItemId(1), ItemId(1)];
        let method = equal_i64_method(&mut interner);
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::DUPLICATE_EXTEND_METHOD_REFERENCE));
    }

    // -- Fix 2 (0.1.5 follow-up): an extend method's own `requirements`
    //    must be exactly its owning extend's `requirements`, in order --

    #[test]
    fn an_extend_method_with_a_different_requirement_count_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let mut method = equal_i64_method(&mut interner);
        method.requirements = vec![CapabilityRequirement::new(protocol_id, vec![Ty::I64])];
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTEND_METHOD_REQUIREMENTS_MISMATCH));
    }

    #[test]
    fn an_extend_method_with_the_same_count_but_a_different_protocol_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.requirements = vec![CapabilityRequirement::new(protocol_id, vec![Ty::I64])];
        let mut method = equal_i64_method(&mut interner);
        method.requirements = vec![CapabilityRequirement::new(ItemId(999), vec![Ty::I64])];
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTEND_METHOD_REQUIREMENTS_MISMATCH));
    }

    #[test]
    fn an_extend_method_with_the_same_protocol_but_different_arguments_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.requirements = vec![CapabilityRequirement::new(protocol_id, vec![Ty::I64])];
        let mut method = equal_i64_method(&mut interner);
        method.requirements = vec![CapabilityRequirement::new(protocol_id, vec![Ty::Bool])];
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTEND_METHOD_REQUIREMENTS_MISMATCH));
    }

    #[test]
    fn an_extend_method_with_requirements_in_a_different_order_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let other_protocol_id = ItemId(21);
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.requirements = vec![
            CapabilityRequirement::new(protocol_id, vec![Ty::I64]),
            CapabilityRequirement::new(other_protocol_id, vec![Ty::Bool]),
        ];
        let mut method = equal_i64_method(&mut interner);
        method.requirements = vec![
            CapabilityRequirement::new(other_protocol_id, vec![Ty::Bool]),
            CapabilityRequirement::new(protocol_id, vec![Ty::I64]),
        ];
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTEND_METHOD_REQUIREMENTS_MISMATCH));
    }

    #[test]
    fn an_extend_method_with_exactly_matching_requirements_is_accepted() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.requirements = vec![CapabilityRequirement::new(protocol_id, vec![Ty::I64])];
        let mut method = equal_i64_method(&mut interner);
        method.requirements = vec![CapabilityRequirement::new(protocol_id, vec![Ty::I64])];
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(
            !codes_of(&diagnostics).contains(&codes::EXTEND_METHOD_REQUIREMENTS_MISMATCH),
            "{diagnostics:?}"
        );
    }

    // -- Fix 3 (0.1.5 follow-up): exact-forwarding-only symbolic
    //    semantics, independently re-checked in NIR (`rfcs/0009`) -------

    #[test]
    fn an_extend_with_an_unconstrained_type_parameter_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let t = TypeParamId(40);
        let t_symbol = interner.intern("T");
        let extend_id = ItemId(10);
        let extend = ExtendLayout {
            protocol: protocol_id,
            type_params: vec![(t, t_symbol)],
            protocol_arguments: vec![Ty::I64],
            requirements: Vec::new(),
            methods: vec![ItemId(1)],
        };
        let method = equal_i64_method(&mut interner);
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::UNCONSTRAINED_EXTEND_PARAMETER));
    }

    #[test]
    fn two_unconstrained_extend_parameters_each_get_their_own_named_diagnostic_in_order() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let t = TypeParamId(40);
        let u = TypeParamId(41);
        let t_symbol = interner.intern("T");
        let u_symbol = interner.intern("U");
        let extend_id = ItemId(10);
        let extend = ExtendLayout {
            protocol: protocol_id,
            type_params: vec![(t, t_symbol), (u, u_symbol)],
            protocol_arguments: vec![Ty::I64],
            requirements: Vec::new(),
            methods: vec![ItemId(1)],
        };
        let method = equal_i64_method(&mut interner);
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method],
            &interner,
        );
        let v0059: Vec<&Diagnostic> = diagnostics
            .iter()
            .filter(|d| d.code == codes::UNCONSTRAINED_EXTEND_PARAMETER)
            .collect();
        assert_eq!(v0059.len(), 2, "{diagnostics:?}");
        assert!(v0059[0].message.contains("`T`"), "{}", v0059[0].message);
        assert!(v0059[1].message.contains("`U`"), "{}", v0059[1].message);
    }

    #[test]
    fn an_extend_type_parameter_occurring_in_a_nested_application_is_accepted() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let t = TypeParamId(41);
        let t_symbol = interner.intern("T");
        let box_item = ItemId(51);
        let extend_id = ItemId(11);
        let extend = ExtendLayout {
            protocol: protocol_id,
            type_params: vec![(t, t_symbol)],
            protocol_arguments: vec![Ty::Applied(box_item, vec![Ty::Param(t, t_symbol)])],
            requirements: Vec::new(),
            methods: Vec::new(),
        };
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            Vec::new(),
            &interner,
        );
        assert!(!codes_of(&diagnostics).contains(&codes::UNCONSTRAINED_EXTEND_PARAMETER));
    }

    #[test]
    fn every_extend_type_parameter_occurring_in_a_multi_argument_protocol_head_is_accepted() {
        let mut interner = Interner::new();
        let a = TypeParamId(0);
        let b = TypeParamId(1);
        let a_symbol = interner.intern("A");
        let b_symbol = interner.intern("B");
        let protocol_id = ItemId(0);
        let protocol = ProtocolLayout {
            name: interner.intern("P"),
            type_params: vec![(a, a_symbol), (b, b_symbol)],
            methods: vec![ProtocolMethodLayout {
                name: interner.intern("test"),
                params: vec![Ty::Param(a, a_symbol), Ty::Param(b, b_symbol)],
                return_type: Ty::Bool,
            }],
        };
        let t = TypeParamId(42);
        let u = TypeParamId(43);
        let t_symbol = interner.intern("T");
        let u_symbol = interner.intern("U");
        let extend_id = ItemId(12);
        let extend = ExtendLayout {
            protocol: protocol_id,
            type_params: vec![(t, t_symbol), (u, u_symbol)],
            protocol_arguments: vec![Ty::Param(t, t_symbol), Ty::Param(u, u_symbol)],
            requirements: Vec::new(),
            methods: Vec::new(),
        };
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            Vec::new(),
            &interner,
        );
        assert!(!codes_of(&diagnostics).contains(&codes::UNCONSTRAINED_EXTEND_PARAMETER));
    }

    #[test]
    fn evidence_selecting_an_extension_for_a_still_symbolic_requirement_is_rejected() {
        let extend_id = ItemId(1);
        let protocol_id = ItemId(0);
        let t = TypeParamId(0);
        let t_symbol = Symbol(0);
        let layout = ExtendLayout {
            protocol: protocol_id,
            type_params: Vec::new(),
            protocol_arguments: vec![Ty::Param(t, t_symbol)],
            requirements: Vec::new(),
            methods: Vec::new(),
        };
        let mut extends = HashMap::new();
        extends.insert(extend_id, &layout);
        let agg = AggregateContext {
            records: HashMap::new(),
            variants: HashMap::new(),
            protocols: HashMap::new(),
            extends,
        };
        let evidence = Evidence::Extension {
            extend: extend_id,
            nested: Vec::new(),
        };
        let mut budget = MAX_CAPABILITY_RESOLUTION_STEPS;
        let result = check_evidence(
            &evidence,
            protocol_id,
            &[Ty::Param(t, t_symbol)],
            true,
            &[],
            &agg,
            0,
            &mut budget,
        );
        assert!(matches!(
            result,
            Err(EvidenceProblem::ExtensionForSymbolicRequirement)
        ));
    }

    #[test]
    fn the_equivalent_exact_forwarded_evidence_for_a_symbolic_requirement_is_accepted() {
        let protocol_id = ItemId(0);
        let t = TypeParamId(0);
        let t_symbol = Symbol(0);
        let agg = AggregateContext {
            records: HashMap::new(),
            variants: HashMap::new(),
            protocols: HashMap::new(),
            extends: HashMap::new(),
        };
        let caller_requirements = vec![CapabilityRequirement::new(
            protocol_id,
            vec![Ty::Param(t, t_symbol)],
        )];
        let mut budget = MAX_CAPABILITY_RESOLUTION_STEPS;
        let result = check_evidence(
            &Evidence::Forwarded(0),
            protocol_id,
            &[Ty::Param(t, t_symbol)],
            true,
            &caller_requirements,
            &agg,
            0,
            &mut budget,
        );
        assert!(result.is_ok(), "{result:?}");
    }

    // -- Fix 3: ordinary `Call` evidence validation (`rfcs/0009`) -------

    /// `func g() -> bool uses Equal[i64] { return true }` -- a callee
    /// declaring one capability requirement, for tests that call it with
    /// exactly one evidence entry and mutate that entry.
    fn callee_requiring_equal_i64(interner: &mut Interner) -> Function {
        Function {
            id: ItemId(2),
            name: interner.intern("g"),
            type_params: Vec::new(),
            requirements: vec![CapabilityRequirement::new(ItemId(0), vec![Ty::I64])],
            params: Vec::new(),
            return_type: Ty::Bool,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::Bool,
                    kind: ValueKind::Const(Const::Bool(true)),
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        }
    }

    /// `func f() -> bool uses Equal[i64] { return g() }`, calling
    /// [`callee_requiring_equal_i64`] with whatever `evidence` a test
    /// wants to check, and declaring its own requirement so a
    /// `Forwarded(0)` test has something valid to forward.
    fn caller_forwarding_to_callee(
        interner: &mut Interner,
        requirements: Vec<CapabilityRequirement>,
        evidence: Vec<Evidence>,
    ) -> Function {
        Function {
            id: ItemId(3),
            name: interner.intern("f"),
            type_params: Vec::new(),
            requirements,
            params: Vec::new(),
            return_type: Ty::Bool,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::Bool,
                    kind: ValueKind::Call(ItemId(2), Vec::new(), Vec::new(), evidence),
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        }
    }

    #[test]
    fn forwarding_the_callers_own_matching_requirement_has_no_diagnostics() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let caller = caller_forwarding_to_callee(
            &mut interner,
            vec![CapabilityRequirement::new(ItemId(0), vec![Ty::I64])],
            vec![Evidence::Forwarded(0)],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            Vec::new(),
            vec![callee_requiring_equal_i64(&mut interner), caller],
            &interner,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn dispatching_through_a_valid_concrete_extension_has_no_diagnostics() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let method = equal_i64_method(&mut interner);
        let caller = caller_forwarding_to_callee(
            &mut interner,
            Vec::new(),
            vec![Evidence::Extension {
                extend: extend_id,
                nested: Vec::new(),
            }],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![callee_requiring_equal_i64(&mut interner), method, caller],
            &interner,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn a_call_with_the_wrong_number_of_evidence_entries_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let caller = caller_forwarding_to_callee(
            &mut interner,
            vec![CapabilityRequirement::new(ItemId(0), vec![Ty::I64])],
            Vec::new(),
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            Vec::new(),
            vec![callee_requiring_equal_i64(&mut interner), caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EVIDENCE_COUNT_MISMATCH));
    }

    #[test]
    fn a_forwarded_index_out_of_range_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let caller = caller_forwarding_to_callee(
            &mut interner,
            vec![CapabilityRequirement::new(ItemId(0), vec![Ty::I64])],
            vec![Evidence::Forwarded(5)],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            Vec::new(),
            vec![callee_requiring_equal_i64(&mut interner), caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::FORWARDED_INDEX_OUT_OF_RANGE));
    }

    #[test]
    fn a_forwarded_requirement_not_matching_the_call_site_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        // The caller's own requirement at index 0 is `Equal[bool]`, not
        // the `Equal[i64]` the callee actually requires.
        let caller = caller_forwarding_to_callee(
            &mut interner,
            vec![CapabilityRequirement::new(ItemId(0), vec![Ty::Bool])],
            vec![Evidence::Forwarded(0)],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            Vec::new(),
            vec![callee_requiring_equal_i64(&mut interner), caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::FORWARDED_REQUIREMENT_MISMATCH));
    }

    #[test]
    fn evidence_referencing_an_unknown_extend_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let caller = caller_forwarding_to_callee(
            &mut interner,
            Vec::new(),
            vec![Evidence::Extension {
                extend: ItemId(999),
                nested: Vec::new(),
            }],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            Vec::new(),
            vec![callee_requiring_equal_i64(&mut interner), caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_EXTENSION_REFERENCE));
    }

    #[test]
    fn evidence_selecting_an_extension_for_the_wrong_protocol_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        // A second, unrelated protocol with the same shape as `Equal`,
        // so the extend below is a completely valid extension -- just
        // not of the protocol the callee actually requires.
        let ord_t = TypeParamId(1);
        let ord_t_symbol = interner.intern("U");
        let ord_protocol_id = ItemId(20);
        let ord_protocol = ProtocolLayout {
            name: interner.intern("Ord"),
            type_params: vec![(ord_t, ord_t_symbol)],
            methods: vec![ProtocolMethodLayout {
                name: interner.intern("less"),
                params: vec![
                    Ty::Param(ord_t, ord_t_symbol),
                    Ty::Param(ord_t, ord_t_symbol),
                ],
                return_type: Ty::Bool,
            }],
        };
        let ord_extend_id = ItemId(11);
        let ord_extend = ExtendLayout {
            protocol: ord_protocol_id,
            type_params: Vec::new(),
            protocol_arguments: vec![Ty::I64],
            requirements: Vec::new(),
            methods: vec![ItemId(1)],
        };
        let method = equal_i64_method(&mut interner);
        let caller = caller_forwarding_to_callee(
            &mut interner,
            Vec::new(),
            vec![Evidence::Extension {
                extend: ord_extend_id,
                nested: Vec::new(),
            }],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol), (ord_protocol_id, ord_protocol)],
            vec![(ord_extend_id, ord_extend)],
            vec![callee_requiring_equal_i64(&mut interner), method, caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTENSION_PROTOCOL_MISMATCH));
    }

    #[test]
    fn evidence_selecting_an_extension_whose_head_does_not_match_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        // Targets the right protocol, but for `bool`, not the `i64` the
        // callee actually requires.
        let mismatched_extend_id = ItemId(12);
        let mismatched_extend = ExtendLayout {
            protocol: protocol_id,
            type_params: Vec::new(),
            protocol_arguments: vec![Ty::Bool],
            requirements: Vec::new(),
            methods: vec![ItemId(1)],
        };
        let caller = caller_forwarding_to_callee(
            &mut interner,
            Vec::new(),
            vec![Evidence::Extension {
                extend: mismatched_extend_id,
                nested: Vec::new(),
            }],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(mismatched_extend_id, mismatched_extend)],
            vec![callee_requiring_equal_i64(&mut interner), caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTENSION_HEAD_MISMATCH));
    }

    #[test]
    fn evidence_with_the_wrong_number_of_nested_entries_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, mut extend) = valid_equal_i64_extend();
        // A conditional extend requiring one capability of its own --
        // the evidence below supplies zero nested entries for it.
        extend.requirements = vec![CapabilityRequirement::new(protocol_id, vec![Ty::I64])];
        let method = equal_i64_method(&mut interner);
        let caller = caller_forwarding_to_callee(
            &mut interner,
            Vec::new(),
            vec![Evidence::Extension {
                extend: extend_id,
                nested: Vec::new(),
            }],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![callee_requiring_equal_i64(&mut interner), method, caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::NESTED_EVIDENCE_COUNT_MISMATCH));
    }

    #[test]
    fn a_forwarded_entry_nested_inside_an_extension_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, mut extend) = valid_equal_i64_extend();
        extend.requirements = vec![CapabilityRequirement::new(protocol_id, vec![Ty::I64])];
        let method = equal_i64_method(&mut interner);
        let caller = caller_forwarding_to_callee(
            &mut interner,
            vec![CapabilityRequirement::new(protocol_id, vec![Ty::I64])],
            vec![Evidence::Extension {
                extend: extend_id,
                nested: vec![Evidence::Forwarded(0)],
            }],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![callee_requiring_equal_i64(&mut interner), method, caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::FORWARDED_INSIDE_NESTED_EVIDENCE));
    }

    // -- `check_evidence`/`match_extend_head` unit tests: depth/work
    //    budgets on a hostile hand-built evidence tree, exercised
    //    directly rather than through `verify_module` since building an
    //    equally deep *valid* chain of distinct extends would obscure
    //    what each test is actually bounding.

    #[test]
    fn evidence_nested_deeper_than_the_capability_depth_limit_is_rejected() {
        // A chain of `Extension { extend: SAME_ID, nested: [...] }`,
        // self-referentially "requiring itself" at every level -- purely
        // structural (no real solver would ever produce this), built
        // only to exercise `check_evidence`'s own recursion depth bound
        // directly, independent of `verify_module`'s plumbing.
        let extend_id = ItemId(1);
        let protocol_id = ItemId(0);
        let layout = ExtendLayout {
            protocol: protocol_id,
            type_params: Vec::new(),
            protocol_arguments: vec![Ty::I64],
            requirements: vec![CapabilityRequirement::new(protocol_id, vec![Ty::I64])],
            methods: Vec::new(),
        };
        let mut extends = HashMap::new();
        extends.insert(extend_id, &layout);
        let agg = AggregateContext {
            records: HashMap::new(),
            variants: HashMap::new(),
            protocols: HashMap::new(),
            extends,
        };
        let mut evidence = Evidence::Extension {
            extend: extend_id,
            nested: Vec::new(),
        };
        for _ in 0..(MAX_CAPABILITY_DEPTH + 2) {
            evidence = Evidence::Extension {
                extend: extend_id,
                nested: vec![evidence],
            };
        }
        let mut budget = MAX_CAPABILITY_RESOLUTION_STEPS;
        let result = check_evidence(
            &evidence,
            protocol_id,
            &[Ty::I64],
            true,
            &[],
            &agg,
            0,
            &mut budget,
        );
        assert!(matches!(result, Err(EvidenceProblem::DepthExceeded)));
    }

    #[test]
    fn evidence_exceeding_the_work_budget_is_rejected_without_a_diagnostic_per_node() {
        let protocol_id = ItemId(0);
        // Two extends sharing one shape: `branch` requires `WIDTH`
        // copies of itself (so a structurally valid tree stays exactly
        // `WIDTH`-ary at every internal node), `leaf` requires nothing
        // (a valid terminal, so the tree can actually bottom out without
        // needing to recurse forever to stay well-formed).
        const WIDTH: usize = 4;
        let branch_id = ItemId(1);
        let leaf_id = ItemId(2);
        let branch = ExtendLayout {
            protocol: protocol_id,
            type_params: Vec::new(),
            protocol_arguments: vec![Ty::I64],
            requirements: vec![CapabilityRequirement::new(protocol_id, vec![Ty::I64]); WIDTH],
            methods: Vec::new(),
        };
        let leaf = ExtendLayout {
            protocol: protocol_id,
            type_params: Vec::new(),
            protocol_arguments: vec![Ty::I64],
            requirements: Vec::new(),
            methods: Vec::new(),
        };
        let mut extends = HashMap::new();
        extends.insert(branch_id, &branch);
        extends.insert(leaf_id, &leaf);
        let agg = AggregateContext {
            records: HashMap::new(),
            variants: HashMap::new(),
            protocols: HashMap::new(),
            extends,
        };
        // Shallow (well within the depth limit) but wide enough at every
        // level to blow well past a small work budget: `WIDTH^levels`
        // leaves alone is already far more than `budget` below, while
        // `levels` itself stays nowhere near `MAX_CAPABILITY_DEPTH`.
        fn build(branch_id: ItemId, leaf_id: ItemId, levels: usize) -> Evidence {
            if levels == 0 {
                return Evidence::Extension {
                    extend: leaf_id,
                    nested: Vec::new(),
                };
            }
            Evidence::Extension {
                extend: branch_id,
                nested: (0..WIDTH)
                    .map(|_| build(branch_id, leaf_id, levels - 1))
                    .collect(),
            }
        }
        let evidence = build(branch_id, leaf_id, 10);
        let mut budget = 50;
        let result = check_evidence(
            &evidence,
            protocol_id,
            &[Ty::I64],
            true,
            &[],
            &agg,
            0,
            &mut budget,
        );
        assert!(matches!(result, Err(EvidenceProblem::WorkBudgetExceeded)));
    }

    // -- Fix 3: `protocol.call` validation (`rfcs/0009`) -----------------

    /// `func f() -> <result_ty> { return <protocol>[<arguments>].method[<method>](1, 1, ..) }`
    /// with `arg_count` integer-literal arguments, for tests that mutate
    /// exactly one thing about an otherwise-valid `protocol.call`.
    #[allow(clippy::too_many_arguments)]
    fn caller_with_protocol_call(
        interner: &mut Interner,
        protocol: ItemId,
        arguments: Vec<Ty>,
        method: usize,
        evidence: Evidence,
        result_ty: Ty,
        arg_count: usize,
    ) -> Function {
        let mut instructions: Vec<Instruction> = (0..arg_count)
            .map(|i| Instruction::Value {
                result: ValueId(i as u32),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            })
            .collect();
        let call_result = ValueId(arg_count as u32);
        instructions.push(Instruction::Value {
            result: call_result,
            ty: result_ty.clone(),
            kind: ValueKind::ProtocolCall {
                protocol,
                arguments,
                method,
                evidence,
                args: (0..arg_count).map(|i| ValueId(i as u32)).collect(),
            },
        });
        Function {
            id: ItemId(3),
            name: interner.intern("f"),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: result_ty,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions,
                terminator: Terminator::Return(Some(call_result)),
            }],
        }
    }

    fn valid_evidence_for_equal_i64(extend_id: ItemId) -> Evidence {
        Evidence::Extension {
            extend: extend_id,
            nested: Vec::new(),
        }
    }

    #[test]
    fn a_valid_protocol_call_has_no_diagnostics() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let method_fn = equal_i64_method(&mut interner);
        let caller = caller_with_protocol_call(
            &mut interner,
            protocol_id,
            vec![Ty::I64],
            0,
            valid_evidence_for_equal_i64(extend_id),
            Ty::Bool,
            2,
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method_fn, caller],
            &interner,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn a_protocol_call_naming_an_unknown_protocol_is_rejected() {
        let mut interner = Interner::new();
        let (extend_id, extend) = valid_equal_i64_extend();
        let method_fn = equal_i64_method(&mut interner);
        let caller = caller_with_protocol_call(
            &mut interner,
            ItemId(999),
            vec![Ty::I64],
            0,
            valid_evidence_for_equal_i64(extend_id),
            Ty::Bool,
            2,
        );
        let diagnostics = verify_module_with(
            Vec::new(),
            vec![(extend_id, extend)],
            vec![method_fn, caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_PROTOCOL_CALL_TARGET));
    }

    #[test]
    fn a_protocol_call_with_the_wrong_number_of_type_arguments_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let method_fn = equal_i64_method(&mut interner);
        let caller = caller_with_protocol_call(
            &mut interner,
            protocol_id,
            vec![Ty::I64, Ty::I64],
            0,
            valid_evidence_for_equal_i64(extend_id),
            Ty::Bool,
            2,
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method_fn, caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::GENERIC_ARITY_MISMATCH));
    }

    #[test]
    fn a_protocol_call_with_an_out_of_range_method_index_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let method_fn = equal_i64_method(&mut interner);
        let caller = caller_with_protocol_call(
            &mut interner,
            protocol_id,
            vec![Ty::I64],
            5,
            valid_evidence_for_equal_i64(extend_id),
            Ty::Bool,
            2,
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method_fn, caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_PROTOCOL_CALL_TARGET));
    }

    #[test]
    fn a_protocol_call_with_the_wrong_number_of_value_arguments_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let method_fn = equal_i64_method(&mut interner);
        let caller = caller_with_protocol_call(
            &mut interner,
            protocol_id,
            vec![Ty::I64],
            0,
            valid_evidence_for_equal_i64(extend_id),
            Ty::Bool,
            3,
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method_fn, caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::ARITY_MISMATCH));
    }

    #[test]
    fn a_protocol_call_declared_with_the_wrong_result_type_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let method_fn = equal_i64_method(&mut interner);
        // `Equal[i64].equal(..)` actually returns `bool`, not `i64`.
        let caller = caller_with_protocol_call(
            &mut interner,
            protocol_id,
            vec![Ty::I64],
            0,
            valid_evidence_for_equal_i64(extend_id),
            Ty::I64,
            2,
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method_fn, caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::OPERAND_TYPE_MISMATCH));
    }

    #[test]
    fn a_protocol_call_passing_an_argument_of_the_wrong_type_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let (extend_id, extend) = valid_equal_i64_extend();
        let method_fn = equal_i64_method(&mut interner);
        // `Equal[i64].equal(left: i64, right: i64)` expects two `i64`s;
        // this call passes a `bool` as its first argument instead.
        let caller = Function {
            id: ItemId(3),
            name: interner.intern("f"),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Bool,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::Bool,
                        kind: ValueKind::Const(Const::Bool(true)),
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(1)),
                    },
                    Instruction::Value {
                        result: ValueId(2),
                        ty: Ty::Bool,
                        kind: ValueKind::ProtocolCall {
                            protocol: protocol_id,
                            arguments: vec![Ty::I64],
                            method: 0,
                            evidence: valid_evidence_for_equal_i64(extend_id),
                            args: vec![ValueId(0), ValueId(1)],
                        },
                    },
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        };
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(extend_id, extend)],
            vec![method_fn, caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::OPERAND_TYPE_MISMATCH));
    }

    #[test]
    fn a_protocol_call_whose_evidence_cannot_satisfy_the_exact_requirement_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        // Targets the right protocol, but for `bool`, not the `i64` this
        // call site actually requires.
        let mismatched_extend_id = ItemId(12);
        let mismatched_extend = ExtendLayout {
            protocol: protocol_id,
            type_params: Vec::new(),
            protocol_arguments: vec![Ty::Bool],
            requirements: Vec::new(),
            methods: vec![ItemId(1)],
        };
        let caller = caller_with_protocol_call(
            &mut interner,
            protocol_id,
            vec![Ty::I64],
            0,
            valid_evidence_for_equal_i64(mismatched_extend_id),
            Ty::Bool,
            2,
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            vec![(mismatched_extend_id, mismatched_extend)],
            vec![caller],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::EXTENSION_HEAD_MISMATCH));
    }

    // -- Fix 1 (0.1.5 follow-up): every Function::requirements entry is
    //    independently validated ---------------------------------------

    fn function_with_requirement(
        interner: &mut Interner,
        type_params: Vec<(TypeParamId, Symbol)>,
        requirements: Vec<CapabilityRequirement>,
    ) -> Function {
        Function {
            id: ItemId(20),
            name: interner.intern("f"),
            type_params,
            requirements,
            params: Vec::new(),
            return_type: Ty::Bool,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::Bool,
                    kind: ValueKind::Const(Const::Bool(true)),
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        }
    }

    #[test]
    fn a_function_requirement_naming_an_unknown_protocol_is_rejected() {
        let mut interner = Interner::new();
        let function = function_with_requirement(
            &mut interner,
            Vec::new(),
            vec![CapabilityRequirement::new(ItemId(999), vec![Ty::I64])],
        );
        let diagnostics = verify_module_with(Vec::new(), Vec::new(), vec![function], &interner);
        assert!(codes_of(&diagnostics).contains(&codes::UNKNOWN_REQUIREMENT_PROTOCOL));
    }

    #[test]
    fn a_function_requirement_with_the_wrong_arity_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let function = function_with_requirement(
            &mut interner,
            Vec::new(),
            vec![CapabilityRequirement::new(protocol_id, Vec::new())],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            Vec::new(),
            vec![function],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::REQUIREMENT_ARITY_MISMATCH));
    }

    #[test]
    fn a_function_requirement_with_an_error_type_argument_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let function = function_with_requirement(
            &mut interner,
            Vec::new(),
            vec![CapabilityRequirement::new(protocol_id, vec![Ty::Error])],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            Vec::new(),
            vec![function],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::UNEXPECTED_ERROR_TYPE));
    }

    #[test]
    fn a_function_requirement_with_an_unresolved_type_variable_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let function = function_with_requirement(
            &mut interner,
            Vec::new(),
            vec![CapabilityRequirement::new(
                protocol_id,
                vec![Ty::Var(crate::types::TyVar(0))],
            )],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            Vec::new(),
            vec![function],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::UNRESOLVED_TYPE_VARIABLE));
    }

    #[test]
    fn a_function_requirement_using_a_foreign_type_parameter_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let foreign = interner.intern("U");
        let function = function_with_requirement(
            &mut interner,
            Vec::new(),
            vec![CapabilityRequirement::new(
                protocol_id,
                vec![Ty::Param(TypeParamId(999), foreign)],
            )],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            Vec::new(),
            vec![function],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::ESCAPING_TYPE_PARAMETER));
    }

    #[test]
    fn a_function_requirement_nested_past_the_generic_depth_limit_is_rejected() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let box_item = ItemId(50);
        let mut deep = Ty::I64;
        for _ in 0..(MAX_GENERIC_DEPTH + 2) {
            deep = Ty::Applied(box_item, vec![deep]);
        }
        let function = function_with_requirement(
            &mut interner,
            Vec::new(),
            vec![CapabilityRequirement::new(protocol_id, vec![deep])],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            Vec::new(),
            vec![function],
            &interner,
        );
        assert!(codes_of(&diagnostics).contains(&codes::GENERIC_DEPTH_EXCEEDED));
    }

    #[test]
    fn a_valid_symbolic_function_requirement_has_no_diagnostics() {
        let mut interner = Interner::new();
        let (protocol_id, protocol) = valid_equal_protocol(&mut interner);
        let t = TypeParamId(30);
        let t_symbol = interner.intern("T");
        let function = function_with_requirement(
            &mut interner,
            vec![(t, t_symbol)],
            vec![CapabilityRequirement::new(
                protocol_id,
                vec![Ty::Param(t, t_symbol)],
            )],
        );
        let diagnostics = verify_module_with(
            vec![(protocol_id, protocol)],
            Vec::new(),
            vec![function],
            &interner,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    // -- Typed outcomes: Invoke/Raise (`rfcs/0010`) ---------------------

    #[test]
    fn an_ordinary_call_to_a_fallible_function_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let (shape_id, shape_layout, _shape_name) = variant_shape(&mut interner);

        let mut callee = valid_function(ItemId(0), g_name);
        callee.raises = vec![shape_id];

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            kind: ValueKind::Call(ItemId(0), Vec::new(), Vec::new(), Vec::new()),
        });
        caller.blocks[0].terminator = Terminator::Return(Some(ValueId(1)));

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::CALL_TO_FALLIBLE_FUNCTION),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_invoke_of_an_infallible_function_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let callee = valid_function(ItemId(0), g_name);

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            kind: ValueKind::Alloc,
        });
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(1),
            ok_target: BlockId(1),
            err_targets: Vec::new(),
        };
        caller.blocks.push(BasicBlock {
            id: BlockId(1),
            instructions: vec![Instruction::Value {
                result: ValueId(2),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(1)),
            }],
            terminator: Terminator::Return(Some(ValueId(2))),
        });

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::INVOKE_OF_INFALLIBLE_FUNCTION),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_invoke_of_an_unknown_callee_still_validates_its_own_slots_and_targets() {
        // An unknown callee means there is no signature to check
        // type/arity/evidence against -- but the `Invoke`'s own
        // structure (its argument values, its success/failure slots,
        // its branch targets) is independent of the callee entirely,
        // and must still be validated rather than short-circuited by
        // the callee lookup failing.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, _shape_layout, _shape_name) = variant_shape(&mut interner);

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(999), // does not exist in this module
            type_args: Vec::new(),
            args: vec![ValueId(77)], // never defined anywhere
            evidence: Vec::new(),
            ok_slot: ValueId(2),   // never allocated
            ok_target: BlockId(9), // does not exist
            err_targets: vec![InvokeErrTarget {
                variant: shape_id,
                slot: ValueId(3),    // never allocated
                target: BlockId(10), // does not exist
            }],
        };

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![caller],
            records: Vec::new(),
            variants: vec![(shape_id, _shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        let codes = codes_of(&diagnostics);
        assert!(
            codes.contains(&codes::UNKNOWN_FUNCTION_REF),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            codes.contains(&codes::UNKNOWN_VALUE),
            "an unknown callee must not skip argument value validation: {diagnostics:?}"
        );
        assert!(
            codes.contains(&codes::INVOKE_SUCCESS_SLOT_UNALLOCATED),
            "an unknown callee must not skip success slot allocation validation: {diagnostics:?}"
        );
        assert!(
            codes.contains(&codes::INVOKE_FAILURE_SLOT_UNALLOCATED),
            "an unknown callee must not skip failure slot allocation validation: {diagnostics:?}"
        );
        assert_eq!(
            codes
                .iter()
                .filter(|c| **c == codes::UNKNOWN_BRANCH_TARGET)
                .count(),
            2,
            "an unknown callee must not skip either branch target's validation: {diagnostics:?}"
        );
    }

    #[test]
    fn an_invoke_missing_a_failure_target_for_a_declared_raise_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let (shape_id, shape_layout, _shape_name) = variant_shape(&mut interner);

        let mut callee = valid_function(ItemId(0), g_name);
        callee.raises = vec![shape_id];

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::I64,
            kind: ValueKind::Alloc,
        });
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(1),
            ok_target: BlockId(1),
            // Missing a failure target for `shape_id`, which the callee
            // declares -- an unhandled effect at this Invoke's own
            // failure edge.
            err_targets: Vec::new(),
        };
        caller.blocks.push(BasicBlock {
            id: BlockId(1),
            instructions: vec![Instruction::Value {
                result: ValueId(2),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(1)),
            }],
            terminator: Terminator::Return(Some(ValueId(2))),
        });

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::INVOKE_ERR_TARGET_COVERAGE_MISMATCH),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_raise_of_a_type_not_in_the_functions_own_raises_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);

        // `function.raises` stays empty -- this function never declared
        // it may raise `Shape` at all.
        let mut function = valid_function(ItemId(0), f_name);
        function.blocks[0].instructions.push(Instruction::Value {
            result: ValueId(1),
            ty: Ty::Named(shape_id, shape_name),
            kind: ValueKind::VariantCreate {
                variant: shape_id,
                case: 1,
                type_args: Vec::new(),
                payload: Vec::new(),
            },
        });
        function.blocks[0].terminator = Terminator::Raise { value: ValueId(1) };

        let diagnostics = verify_one_with_aggregates(
            function,
            Vec::new(),
            vec![(shape_id, shape_layout)],
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::UNDECLARED_RAISE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_function_declaring_raises_of_a_generic_variant_is_rejected() {
        // `hir::lower`'s own `resolve_raises` already rejects this for
        // ordinary source (R0030); this verifier never trusts hand-built
        // NIR to already satisfy it.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let failure_name = interner.intern("Failure");
        let t = interner.intern("T");
        let value_name = interner.intern("Value");
        let failure_id = ItemId(200);
        let failure_layout = VariantLayout {
            name: failure_name,
            type_params: vec![(TypeParamId(0), t)],
            cases: vec![CaseLayout {
                name: value_name,
                payload: vec![Ty::Param(TypeParamId(0), t)],
            }],
        };

        let mut function = valid_function(ItemId(0), f_name);
        function.raises = vec![failure_id];

        let diagnostics = verify_one_with_aggregates(
            function,
            Vec::new(),
            vec![(failure_id, failure_layout)],
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::GENERIC_RAISES_TYPE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_valid_invoke_and_raise_round_trip_has_no_diagnostics() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let shape_ty = Ty::Named(shape_id, shape_name);

        // `func g() -> i64 raises Shape { raise Shape.Empty }`
        let mut callee = valid_function(ItemId(0), g_name);
        callee.raises = vec![shape_id];
        callee.blocks[0].instructions = vec![Instruction::Value {
            result: ValueId(0),
            ty: shape_ty.clone(),
            kind: ValueKind::VariantCreate {
                variant: shape_id,
                case: 1,
                type_args: Vec::new(),
                payload: Vec::new(),
            },
        }];
        callee.blocks[0].terminator = Terminator::Raise { value: ValueId(0) };

        // `func f() -> i64 { handle g() { success v => v, failure
        // Shape.Circle(v) => v, failure Shape.Empty => -1 } }`, lowered
        // by hand into the same Invoke/Switch shape `nir::lower` builds.
        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: shape_ty.clone(),
                kind: ValueKind::Alloc,
            },
        ];
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(0),
            ok_target: BlockId(1),
            err_targets: vec![InvokeErrTarget {
                variant: shape_id,
                slot: ValueId(1),
                target: BlockId(2),
            }],
        };
        caller.blocks.push(BasicBlock {
            id: BlockId(1),
            instructions: vec![Instruction::Value {
                result: ValueId(2),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(2))),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(2),
            instructions: vec![Instruction::Value {
                result: ValueId(3),
                ty: shape_ty,
                kind: ValueKind::Load(ValueId(1)),
            }],
            terminator: Terminator::Switch {
                scrutinee: ValueId(3),
                variant: shape_id,
                cases: vec![BlockId(3), BlockId(4)],
            },
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(3),
            instructions: vec![Instruction::Value {
                result: ValueId(4),
                ty: Ty::I64,
                kind: ValueKind::VariantPayload {
                    base: ValueId(3),
                    variant: shape_id,
                    case: 0,
                    index: 0,
                },
            }],
            terminator: Terminator::Return(Some(ValueId(4))),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(4),
            instructions: vec![Instruction::Value {
                result: ValueId(5),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            }],
            terminator: Terminator::Return(Some(ValueId(5))),
        });

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    // -- Fix 7: Invoke slot definite initialization (`rfcs/0010`) -------

    #[test]
    fn a_success_slot_loaded_from_a_block_also_reached_through_a_failure_edge_is_rejected() {
        // `ok_target` and the (single) failure target are the *same*
        // block, which loads `ok_slot` -- but the failure edge never
        // writes `ok_slot` at all, only its own `err_slot`. Dominance
        // alone (the alloc precedes the Invoke) would wrongly accept
        // this; only proving the load's own block is reached *solely*
        // through the writing edge catches it.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let g_name = interner.intern("g");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);

        let mut callee = valid_function(ItemId(0), g_name);
        callee.raises = vec![shape_id];
        callee.blocks[0].instructions = vec![Instruction::Value {
            result: ValueId(0),
            ty: Ty::Named(shape_id, shape_name),
            kind: ValueKind::VariantCreate {
                variant: shape_id,
                case: 1,
                type_args: Vec::new(),
                payload: Vec::new(),
            },
        }];
        callee.blocks[0].terminator = Terminator::Raise { value: ValueId(0) };

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Named(shape_id, shape_name),
                kind: ValueKind::Alloc,
            },
        ];
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(0),
            // Both edges land on bb1 -- the failure edge never wrote
            // %0 (`ok_slot`), only %1 (its own failure slot).
            ok_target: BlockId(1),
            err_targets: vec![InvokeErrTarget {
                variant: shape_id,
                slot: ValueId(1),
                target: BlockId(1),
            }],
        };
        caller.blocks.push(BasicBlock {
            id: BlockId(1),
            instructions: vec![Instruction::Value {
                result: ValueId(2),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(2))),
        });

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    /// `func g() -> i64 raises Shape { raise Shape.Empty }` at `ItemId(0)`
    /// -- the shared fallible callee every real-dataflow test below
    /// invokes.
    fn raising_shape_callee(
        interner: &mut Interner,
        shape_id: ItemId,
        shape_name: Symbol,
    ) -> Function {
        let g_name = interner.intern("g");
        let mut callee = valid_function(ItemId(0), g_name);
        callee.raises = vec![shape_id];
        callee.blocks[0].instructions = vec![Instruction::Value {
            result: ValueId(0),
            ty: Ty::Named(shape_id, shape_name),
            kind: ValueKind::VariantCreate {
                variant: shape_id,
                case: 1,
                type_args: Vec::new(),
                payload: Vec::new(),
            },
        }];
        callee.blocks[0].terminator = Terminator::Raise { value: ValueId(0) };
        callee
    }

    #[test]
    fn a_success_slot_loaded_several_ordinary_hops_after_ok_target_is_accepted() {
        // ok_target (bb1) branches through two plain, instruction-less
        // blocks before finally loading ok_slot in bb3 -- a single-hop
        // check would wrongly reject this (bb3's own immediate
        // predecessor, bb2, guarantees nothing on its own); the real
        // dataflow correctly propagates the fact across every ordinary
        // hop in between.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let callee = raising_shape_callee(&mut interner, shape_id, shape_name);

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Named(shape_id, shape_name),
                kind: ValueKind::Alloc,
            },
        ];
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(0),
            ok_target: BlockId(1),
            err_targets: vec![InvokeErrTarget {
                variant: shape_id,
                slot: ValueId(1),
                target: BlockId(4),
            }],
        };
        caller.blocks.push(BasicBlock {
            id: BlockId(1),
            instructions: Vec::new(),
            terminator: Terminator::Branch(BlockId(2)),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(2),
            instructions: Vec::new(),
            terminator: Terminator::Branch(BlockId(3)),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(3),
            instructions: vec![Instruction::Value {
                result: ValueId(2),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(2))),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(4),
            instructions: vec![Instruction::Value {
                result: ValueId(3),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            }],
            terminator: Terminator::Return(Some(ValueId(3))),
        });

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            !codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_success_slot_joined_from_an_ok_path_and_a_store_initialized_failure_path_is_accepted() {
        // ok_target (bb1) branches straight to the merge block bb3
        // (ok_slot already set by the Invoke's own edge); the failure
        // target (bb2) independently overwrites ok_slot with its own
        // unconditional `Store` before also branching to bb3 -- both
        // predecessors of the join genuinely guarantee the fact, so the
        // load in bb3 is accepted. Also exercises an unconditional
        // `Store` establishing the fact across a block boundary on its
        // own, unrelated to any Invoke edge.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let callee = raising_shape_callee(&mut interner, shape_id, shape_name);

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Named(shape_id, shape_name),
                kind: ValueKind::Alloc,
            },
        ];
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(0),
            ok_target: BlockId(1),
            err_targets: vec![InvokeErrTarget {
                variant: shape_id,
                slot: ValueId(1),
                target: BlockId(2),
            }],
        };
        caller.blocks.push(BasicBlock {
            id: BlockId(1),
            instructions: Vec::new(),
            terminator: Terminator::Branch(BlockId(3)),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(2),
            instructions: vec![
                Instruction::Value {
                    result: ValueId(2),
                    ty: Ty::I64,
                    kind: ValueKind::Const(Const::Int(1)),
                },
                Instruction::Store {
                    slot: ValueId(0),
                    mode: crate::nir::OwnershipMode::Observe,
                    value: ValueId(2),
                },
            ],
            terminator: Terminator::Branch(BlockId(3)),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(3),
            instructions: vec![Instruction::Value {
                result: ValueId(3),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(3))),
        });

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            !codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_success_slot_read_after_a_same_block_store_needs_no_invoke_edge_at_all() {
        // The failure block never reaches ok_slot through any Invoke
        // edge at all -- but it unconditionally `Store`s into it before
        // loading it back later in that very same block, which alone
        // is enough to prove initialization for every following
        // instruction.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let callee = raising_shape_callee(&mut interner, shape_id, shape_name);

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Named(shape_id, shape_name),
                kind: ValueKind::Alloc,
            },
        ];
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(0),
            ok_target: BlockId(1),
            err_targets: vec![InvokeErrTarget {
                variant: shape_id,
                slot: ValueId(1),
                target: BlockId(2),
            }],
        };
        caller.blocks.push(BasicBlock {
            id: BlockId(1),
            instructions: vec![Instruction::Value {
                result: ValueId(2),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(2))),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(2),
            instructions: vec![
                Instruction::Value {
                    result: ValueId(3),
                    ty: Ty::I64,
                    kind: ValueKind::Const(Const::Int(1)),
                },
                Instruction::Store {
                    slot: ValueId(0),
                    mode: crate::nir::OwnershipMode::Observe,
                    value: ValueId(3),
                },
                Instruction::Value {
                    result: ValueId(4),
                    ty: Ty::I64,
                    kind: ValueKind::Load(ValueId(0)),
                },
            ],
            terminator: Terminator::Return(Some(ValueId(4))),
        });

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            !codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_success_slot_loaded_after_a_self_loop_converges_with_no_diagnostics() {
        // ok_target (bb1) conditionally branches back to itself before
        // eventually exiting to bb2, which loads ok_slot -- the
        // fixpoint must converge deterministically through the back
        // edge rather than looping forever or wrongly losing the fact.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let callee = raising_shape_callee(&mut interner, shape_id, shape_name);

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Named(shape_id, shape_name),
                kind: ValueKind::Alloc,
            },
        ];
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(0),
            ok_target: BlockId(1),
            err_targets: vec![InvokeErrTarget {
                variant: shape_id,
                slot: ValueId(1),
                target: BlockId(3),
            }],
        };
        caller.blocks.push(BasicBlock {
            id: BlockId(1),
            instructions: vec![Instruction::Value {
                result: ValueId(2),
                ty: Ty::Bool,
                kind: ValueKind::Const(Const::Bool(true)),
            }],
            terminator: Terminator::CondBranch {
                condition: ValueId(2),
                then_block: BlockId(1),
                else_block: BlockId(2),
            },
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(2),
            instructions: vec![Instruction::Value {
                result: ValueId(4),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(4))),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(3),
            instructions: vec![Instruction::Value {
                result: ValueId(5),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            }],
            terminator: Terminator::Return(Some(ValueId(5))),
        });

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            !codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    /// Builds a 10-block straight-line chain bb1 -> bb2 -> ... -> bb10,
    /// pushed onto `caller.blocks` in *reverse* declaration order
    /// (bb10 first, bb1 last) -- deliberately adversarial for any
    /// analysis that sweeps blocks in declaration order once per pass
    /// instead of following the CFG, since propagating a fact (or its
    /// absence) from bb1 to bb10 then needs one full pass per hop. Ten
    /// hops comfortably exceeds `guarded_slots.len() + 2` (2 + 2 = 4
    /// here: `ok_slot` and the one failure slot), the old, incorrect
    /// pass bound. bb10 ends with a `Load` of `ok_slot`; the caller
    /// decides whether that load is genuinely justified.
    fn reverse_order_chain_to_bb10(caller: &mut Function) {
        for id in (1..=9u32).rev() {
            caller.blocks.push(BasicBlock {
                id: BlockId(id),
                instructions: Vec::new(),
                terminator: Terminator::Branch(BlockId(id + 1)),
            });
        }
        caller.blocks.push(BasicBlock {
            id: BlockId(10),
            instructions: vec![Instruction::Value {
                result: ValueId(10),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(10))),
        });
    }

    #[test]
    fn a_deep_reverse_order_chain_with_a_genuinely_initialized_join_is_accepted() {
        // bb11 (reached only through the Invoke's own failure edge)
        // independently `Store`s ok_slot itself before joining bb1, so
        // both of bb1's predecessors genuinely guarantee it; the fact
        // must then survive propagating forward across all ten
        // reverse-declared hops down to bb10's own `Load`.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let callee = raising_shape_callee(&mut interner, shape_id, shape_name);

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Named(shape_id, shape_name),
                kind: ValueKind::Alloc,
            },
        ];
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(0),
            ok_target: BlockId(1),
            err_targets: vec![InvokeErrTarget {
                variant: shape_id,
                slot: ValueId(1),
                target: BlockId(11),
            }],
        };
        reverse_order_chain_to_bb10(&mut caller);
        caller.blocks.push(BasicBlock {
            id: BlockId(11),
            instructions: vec![
                Instruction::Value {
                    result: ValueId(11),
                    ty: Ty::I64,
                    kind: ValueKind::Const(Const::Int(1)),
                },
                Instruction::Store {
                    slot: ValueId(0),
                    mode: crate::nir::OwnershipMode::Observe,
                    value: ValueId(11),
                },
            ],
            terminator: Terminator::Branch(BlockId(1)),
        });

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            !codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_deep_reverse_order_chain_with_an_uninitialized_join_is_rejected() {
        // bb11 (reached only through the Invoke's own failure edge,
        // which guarantees the *failure* slot, never ok_slot) branches
        // straight into bb1 with no `Store` of its own -- bb1's true
        // in-facts for ok_slot must resolve to "not guaranteed" (the
        // intersection of the ok edge's guarantee and bb11's lack of
        // one), and that absence must then correctly persist forward
        // across all ten reverse-declared hops down to bb10's own
        // `Load`, which must be rejected. A bound as low as
        // `guarded_slots.len() + 2` cannot propagate this far in
        // adversarial declaration order, so this is exactly the case
        // the old fixed pass count would have silently missed.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let callee = raising_shape_callee(&mut interner, shape_id, shape_name);

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Named(shape_id, shape_name),
                kind: ValueKind::Alloc,
            },
        ];
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(0),
            ok_target: BlockId(1),
            err_targets: vec![InvokeErrTarget {
                variant: shape_id,
                slot: ValueId(1),
                target: BlockId(11),
            }],
        };
        reverse_order_chain_to_bb10(&mut caller);
        caller.blocks.push(BasicBlock {
            id: BlockId(11),
            instructions: Vec::new(),
            terminator: Terminator::Branch(BlockId(1)),
        });

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "expected the uninitialized join to be rejected: {diagnostics:?}"
        );
    }

    #[test]
    fn a_cycle_of_unreachable_blocks_never_inherits_optimistic_initialization() {
        // bb20/bb21 only ever branch to each other -- neither is a
        // target of anything reachable from the entry block, so the
        // cycle as a whole is unreachable. Each has an "incoming edge"
        // (from the other), so it is not caught by the simpler
        // no-incoming-edge shortcut; if such a cycle were seeded with
        // the same optimistic "everything already initialized" start
        // every reachable block gets, the intersection within the
        // cycle would never have any real information flow in and
        // would just stay at "initialized" forever, silently hiding
        // bb20's genuine, never-stored `Load` of ok_slot.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let callee = raising_shape_callee(&mut interner, shape_id, shape_name);

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: Ty::I64,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Named(shape_id, shape_name),
                kind: ValueKind::Alloc,
            },
        ];
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(0),
            ok_target: BlockId(1),
            err_targets: vec![InvokeErrTarget {
                variant: shape_id,
                slot: ValueId(1),
                target: BlockId(2),
            }],
        };
        caller.blocks.push(BasicBlock {
            id: BlockId(1),
            instructions: vec![Instruction::Value {
                result: ValueId(2),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(2))),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(2),
            instructions: vec![
                Instruction::Value {
                    result: ValueId(3),
                    ty: Ty::I64,
                    kind: ValueKind::Const(Const::Int(1)),
                },
                Instruction::Store {
                    slot: ValueId(0),
                    mode: crate::nir::OwnershipMode::Observe,
                    value: ValueId(3),
                },
            ],
            terminator: Terminator::Return(None),
        });
        // Unreachable cycle: nothing reachable from the entry ever
        // branches to bb20 or bb21.
        caller.blocks.push(BasicBlock {
            id: BlockId(20),
            instructions: vec![Instruction::Value {
                result: ValueId(20),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Branch(BlockId(21)),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(21),
            instructions: Vec::new(),
            terminator: Terminator::Branch(BlockId(20)),
        });

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "expected the unreachable cycle's own unstored load to be rejected: {diagnostics:?}"
        );
    }

    /// Builds the caller for the entry-boundary tests below. `%0` is
    /// allocated in the entry block, which then `CondBranch`es to a
    /// self-looping block (bb1, which exits to bb2 and loads `%0`) or to
    /// bb5, a separate, always-structurally-reachable block whose own
    /// `Invoke` uses `%0` as its own `ok_slot` -- which is what makes
    /// `%0` a guarded slot at all, entirely independent of bb1's own
    /// loop, which never goes through that `Invoke`'s own edges at all.
    /// When `entry_stores` is true, the entry also unconditionally
    /// `Store`s `%0` itself before branching anywhere, which must make
    /// bb2's load valid on *every* path (including straight through
    /// bb1's loop, which bb5's `Invoke` edges never reach). When false,
    /// the only initialization of `%0` is bb5's own `Invoke` edge into
    /// bb6, which bb1's loop never passes through, so bb2's load must be
    /// rejected.
    fn entry_boundary_caller(
        f_name: Symbol,
        shape_id: ItemId,
        shape_name: Symbol,
        entry_stores: bool,
    ) -> Function {
        let mut entry_instructions = vec![Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Alloc,
        }];
        if entry_stores {
            entry_instructions.push(Instruction::Value {
                result: ValueId(8),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            });
            entry_instructions.push(Instruction::Store {
                slot: ValueId(0),
                value: ValueId(8),
                mode: crate::nir::OwnershipMode::Observe,
            });
        }
        entry_instructions.push(Instruction::Value {
            result: ValueId(9),
            ty: Ty::Bool,
            kind: ValueKind::Const(Const::Bool(true)),
        });
        let entry = BasicBlock {
            id: BlockId(0),
            instructions: entry_instructions,
            terminator: Terminator::CondBranch {
                condition: ValueId(9),
                then_block: BlockId(1),
                else_block: BlockId(5),
            },
        };
        let bb1 = BasicBlock {
            id: BlockId(1),
            instructions: vec![Instruction::Value {
                result: ValueId(10),
                ty: Ty::Bool,
                kind: ValueKind::Const(Const::Bool(true)),
            }],
            terminator: Terminator::CondBranch {
                condition: ValueId(10),
                then_block: BlockId(1),
                else_block: BlockId(2),
            },
        };
        let bb2 = BasicBlock {
            id: BlockId(2),
            instructions: vec![Instruction::Value {
                result: ValueId(11),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(11))),
        };
        let bb5 = BasicBlock {
            id: BlockId(5),
            instructions: vec![Instruction::Value {
                result: ValueId(1),
                ty: Ty::Named(shape_id, shape_name),
                kind: ValueKind::Alloc,
            }],
            terminator: Terminator::Invoke {
                callee: ItemId(0),
                type_args: Vec::new(),
                args: Vec::new(),
                evidence: Vec::new(),
                ok_slot: ValueId(0),
                ok_target: BlockId(6),
                err_targets: vec![InvokeErrTarget {
                    variant: shape_id,
                    slot: ValueId(1),
                    target: BlockId(7),
                }],
            },
        };
        let bb6 = BasicBlock {
            id: BlockId(6),
            instructions: vec![Instruction::Value {
                result: ValueId(12),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(12))),
        };
        let bb7 = BasicBlock {
            id: BlockId(7),
            instructions: vec![Instruction::Value {
                result: ValueId(13),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            }],
            terminator: Terminator::Return(Some(ValueId(13))),
        };

        let mut caller = valid_function(ItemId(1), f_name);
        // BlockId(0) deliberately last: correctness must not depend on
        // the entry being visited before any other block.
        caller.blocks = vec![bb7, bb6, bb5, bb2, bb1, entry];
        caller
    }

    #[test]
    fn an_entry_boundary_stored_only_via_its_own_unconditional_store_is_accepted() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let callee = raising_shape_callee(&mut interner, shape_id, shape_name);
        let caller = entry_boundary_caller(f_name, shape_id, shape_name, true);

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            !codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_entry_boundary_without_its_own_store_and_a_loop_bypassing_the_invoke_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let callee = raising_shape_callee(&mut interner, shape_id, shape_name);
        let caller = entry_boundary_caller(f_name, shape_id, shape_name, false);

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "expected the loop bypassing the Invoke's own edges to be rejected: {diagnostics:?}"
        );
    }

    #[test]
    fn permuting_the_block_vector_never_changes_the_v0073_result() {
        // The same rejected CFG as above, re-verified under several
        // different `function.blocks` storage orders (including entry
        // first, entry last, and reversed) -- the result must be
        // identical every time, since correctness must never depend on
        // Vec order, only on the CFG itself.
        fn diagnoses_v0073(order: &[BlockId]) -> bool {
            let mut interner = Interner::new();
            let f_name = interner.intern("f");
            let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
            let callee = raising_shape_callee(&mut interner, shape_id, shape_name);
            let mut caller = entry_boundary_caller(f_name, shape_id, shape_name, false);
            let by_id: HashMap<BlockId, BasicBlock> =
                caller.blocks.drain(..).map(|b| (b.id, b)).collect();
            caller.blocks = order.iter().map(|id| by_id[id].clone()).collect();

            let module = Module {
                protocols: Vec::new(),
                extends: Vec::new(),
                functions: vec![callee, caller],
                records: Vec::new(),
                variants: vec![(shape_id, shape_layout)],
            };
            let mut map = SourceMap::new();
            let source = map.add_file("t.npt", "");
            let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
            codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED)
        }

        let entry_last = [1u32, 2, 5, 6, 7, 0];
        let entry_first = [0u32, 1, 2, 5, 6, 7];
        let reversed = [7u32, 6, 5, 2, 1, 0];
        let shuffled = [5u32, 0, 7, 1, 6, 2];

        for order in [entry_last, entry_first, reversed, shuffled] {
            let order: Vec<BlockId> = order.into_iter().map(BlockId).collect();
            assert!(
                diagnoses_v0073(&order),
                "expected V0073 regardless of block order {order:?}"
            );
        }
    }

    /// bb1 is the join/load block, reached by two recorded predecessors:
    /// entry (via its own `CondBranch` then-edge -- always reachable)
    /// and bb20 (via a plain `Branch` -- never reachable from entry at
    /// all, since nothing live ever targets it). bb5's own `Invoke`
    /// (targeting the throwaway bb6/bb7) is what registers `%0` as a
    /// guarded slot in the first place, entirely independent of bb1's
    /// own join. When `entry_stores` is true, entry itself
    /// unconditionally `Store`s `%0` before branching anywhere, and
    /// bb20 does nothing; the join must accept bb1's load regardless of
    /// bb20's mere presence as a recorded (but dead) predecessor. When
    /// false, entry never stores `%0` at all, and instead bb20 -- the
    /// unreachable predecessor -- performs its own unconditional
    /// `Store`; that store must never be treated as initializing bb1's
    /// join, since bb20 itself is never actually reached.
    fn join_with_dead_predecessor_caller(
        f_name: Symbol,
        shape_id: ItemId,
        shape_name: Symbol,
        entry_stores: bool,
    ) -> Function {
        let mut entry_instructions = vec![Instruction::Value {
            result: ValueId(0),
            ty: Ty::I64,
            kind: ValueKind::Alloc,
        }];
        if entry_stores {
            entry_instructions.push(Instruction::Value {
                result: ValueId(8),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            });
            entry_instructions.push(Instruction::Store {
                slot: ValueId(0),
                value: ValueId(8),
                mode: crate::nir::OwnershipMode::Observe,
            });
        }
        entry_instructions.push(Instruction::Value {
            result: ValueId(9),
            ty: Ty::Bool,
            kind: ValueKind::Const(Const::Bool(true)),
        });
        let entry = BasicBlock {
            id: BlockId(0),
            instructions: entry_instructions,
            terminator: Terminator::CondBranch {
                condition: ValueId(9),
                then_block: BlockId(1),
                else_block: BlockId(5),
            },
        };
        let bb1 = BasicBlock {
            id: BlockId(1),
            instructions: vec![Instruction::Value {
                result: ValueId(11),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(11))),
        };
        let bb5 = BasicBlock {
            id: BlockId(5),
            instructions: vec![Instruction::Value {
                result: ValueId(1),
                ty: Ty::Named(shape_id, shape_name),
                kind: ValueKind::Alloc,
            }],
            terminator: Terminator::Invoke {
                callee: ItemId(0),
                type_args: Vec::new(),
                args: Vec::new(),
                evidence: Vec::new(),
                ok_slot: ValueId(0),
                ok_target: BlockId(6),
                err_targets: vec![InvokeErrTarget {
                    variant: shape_id,
                    slot: ValueId(1),
                    target: BlockId(7),
                }],
            },
        };
        let bb6 = BasicBlock {
            id: BlockId(6),
            instructions: vec![Instruction::Value {
                result: ValueId(12),
                ty: Ty::I64,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(Some(ValueId(12))),
        };
        let bb7 = BasicBlock {
            id: BlockId(7),
            instructions: vec![Instruction::Value {
                result: ValueId(13),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            }],
            terminator: Terminator::Return(Some(ValueId(13))),
        };
        let mut bb20_instructions = Vec::new();
        if !entry_stores {
            bb20_instructions.push(Instruction::Value {
                result: ValueId(21),
                ty: Ty::I64,
                kind: ValueKind::Const(Const::Int(1)),
            });
            bb20_instructions.push(Instruction::Store {
                slot: ValueId(0),
                value: ValueId(21),
                mode: crate::nir::OwnershipMode::Observe,
            });
        }
        let bb20 = BasicBlock {
            id: BlockId(20),
            instructions: bb20_instructions,
            terminator: Terminator::Branch(BlockId(1)),
        };

        let mut caller = valid_function(ItemId(1), f_name);
        caller.blocks = vec![bb7, bb6, bb5, bb20, bb1, entry];
        caller
    }

    #[test]
    fn a_dead_predecessor_never_wipes_a_reachable_joins_own_fact() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let callee = raising_shape_callee(&mut interner, shape_id, shape_name);
        let caller = join_with_dead_predecessor_caller(f_name, shape_id, shape_name, true);

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            !codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "an unreachable predecessor's mere presence must not wipe a live fact: {diagnostics:?}"
        );
    }

    #[test]
    fn only_a_dead_predecessors_own_store_never_initializes_a_reachable_join() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let callee = raising_shape_callee(&mut interner, shape_id, shape_name);
        let caller = join_with_dead_predecessor_caller(f_name, shape_id, shape_name, false);

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: Vec::new(),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED),
            "a store only reachable through dead code must never initialize a live join: {diagnostics:?}"
        );
    }

    #[test]
    fn permuting_the_block_vector_never_changes_the_dead_predecessor_result() {
        fn check(entry_stores: bool, order: &[BlockId]) -> bool {
            let mut interner = Interner::new();
            let f_name = interner.intern("f");
            let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
            let callee = raising_shape_callee(&mut interner, shape_id, shape_name);
            let mut caller =
                join_with_dead_predecessor_caller(f_name, shape_id, shape_name, entry_stores);
            let by_id: HashMap<BlockId, BasicBlock> =
                caller.blocks.drain(..).map(|b| (b.id, b)).collect();
            caller.blocks = order.iter().map(|id| by_id[id].clone()).collect();

            let module = Module {
                protocols: Vec::new(),
                extends: Vec::new(),
                functions: vec![callee, caller],
                records: Vec::new(),
                variants: vec![(shape_id, shape_layout)],
            };
            let mut map = SourceMap::new();
            let source = map.add_file("t.npt", "");
            let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
            codes_of(&diagnostics).contains(&codes::INVOKE_SLOT_NOT_DEFINITELY_INITIALIZED)
        }

        let orderings: [[u32; 6]; 4] = [
            [0, 1, 5, 6, 7, 20],
            [20, 7, 6, 5, 1, 0],
            [1, 0, 20, 5, 7, 6],
            [5, 20, 0, 7, 1, 6],
        ];
        for raw in orderings {
            let order: Vec<BlockId> = raw.into_iter().map(BlockId).collect();
            assert!(
                !check(true, &order),
                "expected no V0073 (entry stores) with order {order:?}"
            );
            assert!(
                check(false, &order),
                "expected V0073 (only dead predecessor stores) with order {order:?}"
            );
        }
    }

    fn leaked_resource_records(
        resource: ItemId,
        resource_name: Symbol,
    ) -> Vec<(ItemId, RecordLayout)> {
        vec![(
            resource,
            RecordLayout {
                name: resource_name,
                type_params: Vec::new(),
                fields: Vec::new(),
                affine: true,
            },
        )]
    }

    #[test]
    fn a_created_resource_never_dropped_or_returned_is_a_leak() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: resource_ty,
                    kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                }],
                terminator: Terminator::Return(None),
            }],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_LEAKED_ON_EXIT),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_take_parameter_never_dropped_or_returned_is_a_leak() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: resource_ty,
                take: true,
            }],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Return(None),
            }],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_LEAKED_ON_EXIT),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_observing_non_take_parameter_never_dropped_is_not_a_leak() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: resource_ty,
                take: false,
            }],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Return(None),
            }],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            !codes_of(&diagnostics).contains(&codes::RESOURCE_LEAKED_ON_EXIT),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn one_reachable_exit_cleans_and_a_sibling_branch_leaks() {
        // bb1 drops the resource before returning; bb2 does not -- only
        // bb2's own `Return` may be reported, never bb1's.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: resource_ty,
                            kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::Bool,
                            kind: ValueKind::Const(Const::Bool(true)),
                        },
                    ],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(1),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![Instruction::Drop { value: ValueId(0) }],
                    terminator: Terminator::Return(None),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    terminator: Terminator::Return(None),
                },
            ],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        let leaks: Vec<&Diagnostic> = diagnostics
            .iter()
            .filter(|d| d.code == codes::RESOURCE_LEAKED_ON_EXIT)
            .collect();
        assert_eq!(leaks.len(), 1, "unexpected diagnostics: {diagnostics:?}");
        assert!(
            leaks[0].message.contains("bb2"),
            "expected the leak reported against bb2, got: {}",
            leaks[0].message
        );
    }

    /// Builds a fallible `g` returning a fresh resource on success and
    /// raising `shape_id` on failure -- paired with `invoke_of_resource_
    /// returning_callee_caller`, below, to exercise `Terminator::Invoke`'s
    /// own success-edge ownership tracking (`rfcs/0011`).
    fn resource_returning_fallible_callee(
        interner: &mut Interner,
        shape_id: ItemId,
        resource: ItemId,
        resource_name: Symbol,
    ) -> Function {
        let g_name = interner.intern("g");
        let resource_ty = Ty::Named(resource, resource_name);
        Function {
            id: ItemId(0),
            name: g_name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: resource_ty.clone(),
            raises: vec![shape_id],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: resource_ty,
                    kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        }
    }

    /// A caller invoking `resource_returning_fallible_callee`: `%0`
    /// (`ok_slot`) and `%1` (the failure slot) are each allocated at
    /// their own declared type before the `Invoke`, exactly like a real
    /// lowering would (`alloc_slots` -- checked independently of this
    /// pass -- requires it). `ok_dropped` controls whether `ok_target`
    /// (bb1) actually destroys the resource it received before
    /// returning, or abandons it -- the two cases this function's own
    /// two callers below each check.
    fn invoke_of_resource_returning_callee_caller(
        f_name: Symbol,
        shape_id: ItemId,
        shape_name: Symbol,
        resource: ItemId,
        resource_name: Symbol,
        ok_dropped: bool,
    ) -> Function {
        let resource_ty = Ty::Named(resource, resource_name);
        let mut caller = valid_function(ItemId(1), f_name);
        caller.return_type = Ty::Unit;
        caller.blocks[0].instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: resource_ty,
                kind: ValueKind::Alloc,
            },
            Instruction::Value {
                result: ValueId(1),
                ty: Ty::Named(shape_id, shape_name),
                kind: ValueKind::Alloc,
            },
        ];
        caller.blocks[0].terminator = Terminator::Invoke {
            callee: ItemId(0),
            type_args: Vec::new(),
            args: Vec::new(),
            evidence: Vec::new(),
            ok_slot: ValueId(0),
            ok_target: BlockId(1),
            err_targets: vec![InvokeErrTarget {
                variant: shape_id,
                slot: ValueId(1),
                target: BlockId(2),
            }],
        };
        let ok_instructions = if ok_dropped {
            vec![Instruction::Drop { value: ValueId(0) }]
        } else {
            Vec::new()
        };
        caller.blocks.push(BasicBlock {
            id: BlockId(1),
            instructions: ok_instructions,
            terminator: Terminator::Return(None),
        });
        caller.blocks.push(BasicBlock {
            id: BlockId(2),
            instructions: Vec::new(),
            terminator: Terminator::Return(None),
        });
        caller
    }

    #[test]
    fn an_invoke_success_slot_abandoned_on_its_own_success_edge_is_a_leak() {
        // Before ownership was tracked per `Invoke` edge, this exact
        // shape passed `nir::verify` silently: `ok_slot` was never
        // seeded as live at all, so bb1 abandoning it went undetected
        // until (at best) the interpreter's own frame-exit check.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let resource_name = interner.intern("File");
        let resource = ItemId(2);
        let callee =
            resource_returning_fallible_callee(&mut interner, shape_id, resource, resource_name);
        let caller = invoke_of_resource_returning_callee_caller(
            f_name,
            shape_id,
            shape_name,
            resource,
            resource_name,
            false,
        );

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: leaked_resource_records(resource, resource_name),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        let leaks: Vec<&Diagnostic> = diagnostics
            .iter()
            .filter(|d| d.code == codes::RESOURCE_LEAKED_ON_EXIT)
            .collect();
        assert_eq!(leaks.len(), 1, "unexpected diagnostics: {diagnostics:?}");
        assert!(
            leaks[0].message.contains("bb1"),
            "expected the leak reported against the success edge's own bb1, got: {}",
            leaks[0].message
        );
    }

    #[test]
    fn an_invoke_success_slot_dropped_on_its_own_success_edge_is_not_a_leak() {
        // The same shape as above, except bb1 destroys the resource it
        // received before returning -- must not be flagged, and the
        // sibling failure edge (bb2, which never owns anything) must
        // not be flagged either.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let resource_name = interner.intern("File");
        let resource = ItemId(2);
        let callee =
            resource_returning_fallible_callee(&mut interner, shape_id, resource, resource_name);
        let caller = invoke_of_resource_returning_callee_caller(
            f_name,
            shape_id,
            shape_name,
            resource,
            resource_name,
            true,
        );

        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee, caller],
            records: leaked_resource_records(resource, resource_name),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            !codes_of(&diagnostics).contains(&codes::RESOURCE_LEAKED_ON_EXIT),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    // -- Observing aliases can never be treated as owners (`rfcs/0011`) --

    /// `%0 = record.create @File; %1 = alloc File; store.observe %1, %0;
    /// %2 = load %1;` -- `%2` is a merely-observing alias of `%0`'s own
    /// resource, sharing its true identity but never itself an owner.
    fn observing_alias_setup(resource: ItemId, resource_ty: Ty) -> Vec<Instruction> {
        vec![
            Instruction::Value {
                result: ValueId(0),
                ty: resource_ty.clone(),
                kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
            },
            Instruction::Value {
                result: ValueId(1),
                ty: resource_ty.clone(),
                kind: ValueKind::Alloc,
            },
            Instruction::Store {
                slot: ValueId(1),
                value: ValueId(0),
                mode: crate::nir::OwnershipMode::Observe,
            },
            Instruction::Value {
                result: ValueId(2),
                ty: resource_ty,
                kind: ValueKind::Load(ValueId(1)),
            },
        ]
    }

    #[test]
    fn an_observing_alias_dropped_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let mut instructions = observing_alias_setup(resource, resource_ty.clone());
        instructions.push(Instruction::Drop { value: ValueId(2) });
        instructions.push(Instruction::Drop { value: ValueId(0) });
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions,
                terminator: Terminator::Return(None),
            }],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_OBSERVER_CONSUMED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_observing_alias_returned_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let instructions = observing_alias_setup(resource, resource_ty.clone());
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: resource_ty,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions,
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_OBSERVER_CONSUMED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_observing_alias_passed_to_take_is_rejected() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let sink_name = interner.intern("sink");
        let resource_name = interner.intern("File");
        let resource = ItemId(2);
        let f = ItemId(0);
        let sink = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let mut instructions = observing_alias_setup(resource, resource_ty.clone());
        instructions.push(Instruction::Value {
            result: ValueId(3),
            ty: Ty::Unit,
            kind: ValueKind::Call(sink, Vec::new(), vec![ValueId(2)], Vec::new()),
        });
        instructions.push(Instruction::Drop { value: ValueId(0) });
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![
                Function {
                    id: f,
                    name: f_name,
                    type_params: Vec::new(),
                    requirements: Vec::new(),
                    params: Vec::new(),
                    return_type: Ty::Unit,
                    raises: Vec::new(),
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        instructions,
                        terminator: Terminator::Return(None),
                    }],
                },
                Function {
                    id: sink,
                    name: sink_name,
                    type_params: Vec::new(),
                    requirements: Vec::new(),
                    params: vec![Param {
                        value: ValueId(0),
                        ty: resource_ty,
                        take: true,
                    }],
                    return_type: Ty::Unit,
                    raises: Vec::new(),
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Return(None),
                    }],
                },
            ],
            records: leaked_resource_records(resource, resource_name),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_OBSERVER_CONSUMED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn storing_an_observing_alias_with_transfer_mode_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let mut instructions = observing_alias_setup(resource, resource_ty.clone());
        instructions.push(Instruction::Value {
            result: ValueId(3),
            ty: resource_ty,
            kind: ValueKind::Alloc,
        });
        instructions.push(Instruction::Store {
            slot: ValueId(3),
            value: ValueId(2),
            mode: crate::nir::OwnershipMode::Transfer,
        });
        instructions.push(Instruction::Drop { value: ValueId(0) });
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions,
                terminator: Terminator::Return(None),
            }],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::INVALID_RESOURCE_STORE_MODE),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_alias_used_after_the_owner_is_dropped_through_a_different_reference_is_rejected() {
        // `%0` is dropped directly; `%2`, an observing alias of the same
        // resource created *before* that drop, is then merely passed to
        // an ordinary (non-`take`, non-consuming) parameter -- still
        // rejected, since the resource it aliases no longer exists,
        // regardless of whether this particular use would itself have
        // consumed anything.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let inspect_name = interner.intern("inspect");
        let resource_name = interner.intern("File");
        let resource = ItemId(2);
        let f = ItemId(0);
        let inspect = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let mut instructions = observing_alias_setup(resource, resource_ty.clone());
        instructions.push(Instruction::Drop { value: ValueId(0) });
        instructions.push(Instruction::Value {
            result: ValueId(3),
            ty: Ty::Unit,
            kind: ValueKind::Call(inspect, Vec::new(), vec![ValueId(2)], Vec::new()),
        });
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![
                Function {
                    id: f,
                    name: f_name,
                    type_params: Vec::new(),
                    requirements: Vec::new(),
                    params: Vec::new(),
                    return_type: Ty::Unit,
                    raises: Vec::new(),
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        instructions,
                        terminator: Terminator::Return(None),
                    }],
                },
                Function {
                    id: inspect,
                    name: inspect_name,
                    type_params: Vec::new(),
                    requirements: Vec::new(),
                    params: vec![Param {
                        value: ValueId(0),
                        ty: resource_ty,
                        take: false,
                    }],
                    return_type: Ty::Unit,
                    raises: Vec::new(),
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Return(None),
                    }],
                },
            ],
            records: leaked_resource_records(resource, resource_name),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_ORIGIN_CONFLICT),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn two_observing_aliases_of_one_owner_used_before_the_drop_are_accepted() {
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let inspect_name = interner.intern("inspect");
        let resource_name = interner.intern("File");
        let resource = ItemId(2);
        let f = ItemId(0);
        let inspect = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let mut instructions = observing_alias_setup(resource, resource_ty.clone());
        // A second, independent alias of the same slot.
        instructions.push(Instruction::Value {
            result: ValueId(3),
            ty: resource_ty.clone(),
            kind: ValueKind::Load(ValueId(1)),
        });
        instructions.push(Instruction::Value {
            result: ValueId(4),
            ty: Ty::Unit,
            kind: ValueKind::Call(inspect, Vec::new(), vec![ValueId(2)], Vec::new()),
        });
        instructions.push(Instruction::Value {
            result: ValueId(5),
            ty: Ty::Unit,
            kind: ValueKind::Call(inspect, Vec::new(), vec![ValueId(3)], Vec::new()),
        });
        instructions.push(Instruction::Drop { value: ValueId(0) });
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![
                Function {
                    id: f,
                    name: f_name,
                    type_params: Vec::new(),
                    requirements: Vec::new(),
                    params: Vec::new(),
                    return_type: Ty::Unit,
                    raises: Vec::new(),
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        instructions,
                        terminator: Terminator::Return(None),
                    }],
                },
                Function {
                    id: inspect,
                    name: inspect_name,
                    type_params: Vec::new(),
                    requirements: Vec::new(),
                    params: vec![Param {
                        value: ValueId(0),
                        ty: resource_ty,
                        take: false,
                    }],
                    return_type: Ty::Unit,
                    raises: Vec::new(),
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Return(None),
                    }],
                },
            ],
            records: leaked_resource_records(resource, resource_name),
            variants: Vec::new(),
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_move_result_dropped_after_its_own_source_shares_identity_is_not_a_false_positive() {
        // A regression guard for the alias-role fix above: `Move`'s own
        // result deliberately keeps sharing `source`'s true resource
        // identity now (so a drop reachable through either is
        // recognized as the same resource) -- this must never make a
        // legitimate later drop of the *new* owner collide with its own
        // already-`Move`d-out `source` in `RESOURCE_USE_AFTER_CONSUME`'s
        // own separate (and deliberately still-decoupled) bookkeeping.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: resource_ty.clone(),
                        kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: resource_ty,
                        kind: ValueKind::Move { source: ValueId(0) },
                    },
                    Instruction::Drop { value: ValueId(1) },
                ],
                terminator: Terminator::Return(None),
            }],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    // -- Resource slots must be definitely initialized, not just live
    // (`rfcs/0011`) ------------------------------------------------------

    /// `%0 = alloc Resource; %1 = const.bool true; condbranch %1, bb1,
    /// bb2` (entry) -- `bb1` optionally stores a fresh resource into
    /// `%0` (`left_mode`) before branching to `bb3`, `bb2` optionally
    /// does the same (`right_mode`); `None` means that branch never
    /// touches `%0` at all. `bb3` (the join) loads `%0` and returns.
    fn uninit_join_caller(
        name: Symbol,
        resource: ItemId,
        resource_ty: Ty,
        left_mode: Option<crate::nir::OwnershipMode>,
        right_mode: Option<crate::nir::OwnershipMode>,
    ) -> Function {
        let mut bb1_instructions = Vec::new();
        if let Some(mode) = left_mode {
            bb1_instructions.push(Instruction::Value {
                result: ValueId(2),
                ty: resource_ty.clone(),
                kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
            });
            bb1_instructions.push(Instruction::Store {
                slot: ValueId(0),
                value: ValueId(2),
                mode,
            });
        }
        let mut bb2_instructions = Vec::new();
        if let Some(mode) = right_mode {
            bb2_instructions.push(Instruction::Value {
                result: ValueId(3),
                ty: resource_ty.clone(),
                kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
            });
            bb2_instructions.push(Instruction::Store {
                slot: ValueId(0),
                value: ValueId(3),
                mode,
            });
        }
        Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: resource_ty.clone(),
                            kind: ValueKind::Alloc,
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::Bool,
                            kind: ValueKind::Const(Const::Bool(true)),
                        },
                    ],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(1),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: bb1_instructions,
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: bb2_instructions,
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![Instruction::Value {
                        result: ValueId(4),
                        ty: resource_ty,
                        kind: ValueKind::Load(ValueId(0)),
                    }],
                    terminator: Terminator::Return(None),
                },
            ],
        }
    }

    /// `%1 = const.bool true; condbranch %1, then_target, else_target`
    /// (entry) -- exactly one of the two successor blocks
    /// (`resource_block`) allocates *and fully initializes* a fresh `%0`
    /// before branching to the join (`BlockId(3)`); the other successor
    /// never mentions `%0` at all, so -- unlike `uninit_join_caller`,
    /// above, whose entry-block `Alloc` seeds `%0` (if only as
    /// `Uninitialized`) on *both* paths -- that other branch's own
    /// out-state genuinely has no map entry for the key at all. This is
    /// the one-sided-key shape `merge_provenance` iterating only one
    /// map's own keys could miss entirely, which an `Alloc`-in-entry
    /// join cannot exercise (`%0` is present, merely uninitialized, on
    /// both sides there). The join (`BlockId(3)`) loads `%0` and
    /// returns. `then_target`/`else_target` let a caller swap which
    /// physical block the `then` edge reaches independently of which
    /// block (`resource_block`) is the one that actually holds the
    /// resource; `block_order` lets a caller independently control both
    /// predecessor-discovery order (`incoming_edges` is populated by
    /// iterating `function.blocks` in order) and the literal block
    /// vector order.
    fn one_sided_key_join_caller(
        name: Symbol,
        resource: ItemId,
        resource_ty: Ty,
        then_target: BlockId,
        else_target: BlockId,
        resource_block: BlockId,
        block_order: &[BlockId],
    ) -> Function {
        let empty_block = if resource_block == BlockId(1) {
            BlockId(2)
        } else {
            BlockId(1)
        };
        let by_id: HashMap<BlockId, BasicBlock> = HashMap::from([
            (
                BlockId(0),
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::Bool,
                        kind: ValueKind::Const(Const::Bool(true)),
                    }],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(1),
                        then_block: then_target,
                        else_block: else_target,
                    },
                },
            ),
            (
                resource_block,
                BasicBlock {
                    id: resource_block,
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: resource_ty.clone(),
                            kind: ValueKind::Alloc,
                        },
                        Instruction::Value {
                            result: ValueId(2),
                            ty: resource_ty.clone(),
                            kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                        },
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(2),
                            mode: crate::nir::OwnershipMode::Transfer,
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(3)),
                },
            ),
            (
                empty_block,
                BasicBlock {
                    id: empty_block,
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(3)),
                },
            ),
            (
                BlockId(3),
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![Instruction::Value {
                        result: ValueId(4),
                        ty: resource_ty,
                        kind: ValueKind::Load(ValueId(0)),
                    }],
                    terminator: Terminator::Return(None),
                },
            ),
        ]);
        Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: block_order.iter().map(|id| by_id[id].clone()).collect(),
        }
    }

    #[test]
    fn a_one_sided_provenance_key_is_rejected_regardless_of_order() {
        // Every configuration below diagnoses the exact same underlying
        // program; only presentation order (which branch is "then",
        // which predecessor is discovered first, the literal block
        // vector order, where the entry block sits in that vector)
        // differs. A merge that iterates only one map's own keys (the
        // bug this fix corrects) is order-sensitive; the fix must not
        // be.
        fn diagnose(
            then_target: BlockId,
            else_target: BlockId,
            block_order: &[BlockId],
        ) -> Vec<String> {
            let mut interner = Interner::new();
            let name = interner.intern("f");
            let resource_name = interner.intern("File");
            let resource = ItemId(1);
            let resource_ty = Ty::Named(resource, resource_name);
            let function = one_sided_key_join_caller(
                name,
                resource,
                resource_ty,
                then_target,
                else_target,
                BlockId(1),
                block_order,
            );
            let diagnostics = verify_one_with_aggregates(
                function,
                leaked_resource_records(resource, resource_name),
                Vec::new(),
                &interner,
            );
            let mut codes: Vec<String> = codes_of(&diagnostics)
                .into_iter()
                .map(|c| c.to_string())
                .collect();
            codes.sort_unstable();
            codes
        }

        let block = |ids: [u32; 4]| -> Vec<BlockId> { ids.into_iter().map(BlockId).collect() };

        let entry_first = block([0, 1, 2, 3]);
        let reversed_predecessor_discovery = block([0, 2, 1, 3]);
        let reversed_block_vector = block([3, 2, 1, 0]);
        let entry_last = block([1, 2, 3, 0]);

        let baseline = diagnose(BlockId(1), BlockId(2), &entry_first);
        assert!(
            baseline
                .iter()
                .any(|c| c == codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
            "expected V0082 on the baseline one-sided-key join: {baseline:?}"
        );

        let reversed_branch_targets = diagnose(BlockId(2), BlockId(1), &entry_first);
        let reordered_predecessors =
            diagnose(BlockId(1), BlockId(2), &reversed_predecessor_discovery);
        let reversed_vector = diagnose(BlockId(1), BlockId(2), &reversed_block_vector);
        let entry_at_end = diagnose(BlockId(1), BlockId(2), &entry_last);

        for (label, codes) in [
            ("reversed branch targets", &reversed_branch_targets),
            (
                "reversed predecessor discovery order",
                &reordered_predecessors,
            ),
            ("reversed block vector", &reversed_vector),
            ("entry block last", &entry_at_end),
        ] {
            assert!(
                codes
                    .iter()
                    .any(|c| c == codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
                "expected V0082 with {label}: {codes:?}"
            );
            assert_eq!(
                &baseline, codes,
                "diagnostic multiset changed under {label}: baseline {baseline:?} vs. {codes:?}"
            );
        }
    }

    #[test]
    fn a_direct_uninitialized_resource_load_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: resource_ty.clone(),
                        kind: ValueKind::Alloc,
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: resource_ty,
                        kind: ValueKind::Load(ValueId(0)),
                    },
                ],
                terminator: Terminator::Return(None),
            }],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn initialization_on_only_one_branch_via_transfer_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = uninit_join_caller(
            name,
            resource,
            resource_ty,
            Some(crate::nir::OwnershipMode::Transfer),
            None,
        );
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn initialization_on_only_one_branch_via_observe_is_rejected() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = uninit_join_caller(
            name,
            resource,
            resource_ty,
            Some(crate::nir::OwnershipMode::Observe),
            None,
        );
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn reversed_branches_still_reject_the_uninitialized_side() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = uninit_join_caller(
            name,
            resource,
            resource_ty,
            None,
            Some(crate::nir::OwnershipMode::Transfer),
        );
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn initialization_on_every_reachable_branch_is_accepted() {
        // Both branches transfer a fresh (differently-origined) resource
        // into the slot -- initialization itself is unconditionally
        // sound here; any origin/role disagreement at the join is
        // `RESOURCE_ORIGIN_CONFLICT`'s own concern, never this check's.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = uninit_join_caller(
            name,
            resource,
            resource_ty,
            Some(crate::nir::OwnershipMode::Transfer),
            Some(crate::nir::OwnershipMode::Transfer),
        );
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            !codes_of(&diagnostics).contains(&codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn permuting_the_block_vector_never_changes_the_v0082_result() {
        fn diagnoses_v0082(order: &[BlockId]) -> bool {
            let mut interner = Interner::new();
            let name = interner.intern("f");
            let resource_name = interner.intern("File");
            let resource = ItemId(1);
            let resource_ty = Ty::Named(resource, resource_name);
            let mut function = uninit_join_caller(
                name,
                resource,
                resource_ty,
                Some(crate::nir::OwnershipMode::Transfer),
                None,
            );
            let by_id: HashMap<BlockId, BasicBlock> =
                function.blocks.drain(..).map(|b| (b.id, b)).collect();
            function.blocks = order.iter().map(|id| by_id[id].clone()).collect();
            let diagnostics = verify_one_with_aggregates(
                function,
                leaked_resource_records(resource, resource_name),
                Vec::new(),
                &interner,
            );
            codes_of(&diagnostics).contains(&codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED)
        }

        let entry_first = [0u32, 1, 2, 3];
        let reversed = [3u32, 2, 1, 0];
        let entry_last = [1u32, 2, 3, 0];
        let shuffled = [2u32, 0, 3, 1];
        for order in [entry_first, reversed, entry_last, shuffled] {
            let order: Vec<BlockId> = order.into_iter().map(BlockId).collect();
            assert!(
                diagnoses_v0082(&order),
                "expected V0082 regardless of block order {order:?}"
            );
        }
    }

    #[test]
    fn an_unreachable_predecessors_own_store_never_initializes_a_reachable_join() {
        // bb1 (the only *reachable* path into bb3) never stores into
        // `%0`; bb20 (never actually targeted by anything reachable from
        // entry) does -- its own store must not count.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(0),
                        ty: resource_ty.clone(),
                        kind: ValueKind::Alloc,
                    }],
                    terminator: Terminator::Branch(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(20),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(2),
                            ty: resource_ty.clone(),
                            kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                        },
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(2),
                            mode: crate::nir::OwnershipMode::Transfer,
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![Instruction::Value {
                        result: ValueId(4),
                        ty: resource_ty,
                        kind: ValueKind::Load(ValueId(0)),
                    }],
                    terminator: Terminator::Return(None),
                },
            ],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_unreachable_cycles_own_store_never_initializes_a_reachable_join() {
        // bb20 and bb21 only ever branch to each other -- an unreachable
        // cycle, per `compute_dominators`'s own doc comment concern --
        // and bb20 stores into `%0`, but nothing reachable ever reaches
        // either of them.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(0),
                        ty: resource_ty.clone(),
                        kind: ValueKind::Alloc,
                    }],
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(20),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(2),
                            ty: resource_ty.clone(),
                            kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                        },
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(2),
                            mode: crate::nir::OwnershipMode::Transfer,
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(21)),
                },
                BasicBlock {
                    id: BlockId(21),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(20)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![Instruction::Value {
                        result: ValueId(4),
                        ty: resource_ty,
                        kind: ValueKind::Load(ValueId(0)),
                    }],
                    terminator: Terminator::Return(None),
                },
            ],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_loop_back_edge_that_may_bypass_initialization_is_rejected() {
        // bb1 is the loop header: reached directly from entry (which
        // never initializes `%0`) *and* from bb2 (the loop body, which
        // does, then branches back) -- the exit at bb3 may be taken on
        // the very first pass, before the body ever ran.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(0),
                        ty: resource_ty.clone(),
                        kind: ValueKind::Alloc,
                    }],
                    terminator: Terminator::Branch(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::Bool,
                        kind: ValueKind::Const(Const::Bool(true)),
                    }],
                    terminator: Terminator::CondBranch {
                        condition: ValueId(1),
                        then_block: BlockId(2),
                        else_block: BlockId(3),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(2),
                            ty: resource_ty.clone(),
                            kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                        },
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(2),
                            mode: crate::nir::OwnershipMode::Transfer,
                        },
                    ],
                    terminator: Terminator::Branch(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![Instruction::Value {
                        result: ValueId(4),
                        ty: resource_ty,
                        kind: ValueKind::Load(ValueId(0)),
                    }],
                    terminator: Terminator::Return(None),
                },
            ],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_deep_chain_before_initialization_is_accepted() {
        // Five ordinary hops between the `Alloc` and the `store.transfer`
        // that actually initializes it, then one more before the `Load`
        // -- proves the analysis genuinely propagates the fact forward,
        // not merely a single-hop check of a load's own immediate
        // predecessor.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let mut blocks = vec![BasicBlock {
            id: BlockId(0),
            instructions: vec![Instruction::Value {
                result: ValueId(0),
                ty: resource_ty.clone(),
                kind: ValueKind::Alloc,
            }],
            terminator: Terminator::Branch(BlockId(1)),
        }];
        for hop in 1..5u32 {
            blocks.push(BasicBlock {
                id: BlockId(hop),
                instructions: Vec::new(),
                terminator: Terminator::Branch(BlockId(hop + 1)),
            });
        }
        blocks.push(BasicBlock {
            id: BlockId(5),
            instructions: vec![
                Instruction::Value {
                    result: ValueId(2),
                    ty: resource_ty.clone(),
                    kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                },
                Instruction::Store {
                    slot: ValueId(0),
                    value: ValueId(2),
                    mode: crate::nir::OwnershipMode::Transfer,
                },
            ],
            terminator: Terminator::Branch(BlockId(6)),
        });
        blocks.push(BasicBlock {
            id: BlockId(6),
            instructions: vec![Instruction::Value {
                result: ValueId(4),
                ty: resource_ty,
                kind: ValueKind::Load(ValueId(0)),
            }],
            terminator: Terminator::Return(None),
        });
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks,
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            !codes_of(&diagnostics).contains(&codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn an_invoke_success_and_failure_edge_reaching_the_same_target_rejects_the_load() {
        // Both `ok_target` and the sole `err_target` point at the same
        // block, which then loads `ok_slot` -- only the success edge
        // ever actually writes it, so the load must still be rejected,
        // never treated as initialized just because *some* edge into
        // this block happens to write it.
        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(2);
        let f = ItemId(0);
        let callee = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let (shape_id, shape_layout, shape_name) = variant_shape(&mut interner);
        let g_name = interner.intern("g");
        let callee_fn = Function {
            id: callee,
            name: g_name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: resource_ty.clone(),
            raises: vec![shape_id],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(0),
                    ty: resource_ty.clone(),
                    kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                }],
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        };
        let caller = Function {
            id: f,
            name: f_name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: resource_ty.clone(),
                            kind: ValueKind::Alloc,
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::Named(shape_id, shape_name),
                            kind: ValueKind::Alloc,
                        },
                    ],
                    terminator: Terminator::Invoke {
                        callee,
                        type_args: Vec::new(),
                        args: Vec::new(),
                        evidence: Vec::new(),
                        ok_slot: ValueId(0),
                        ok_target: BlockId(1),
                        err_targets: vec![InvokeErrTarget {
                            variant: shape_id,
                            slot: ValueId(1),
                            target: BlockId(1),
                        }],
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![Instruction::Value {
                        result: ValueId(2),
                        ty: resource_ty,
                        kind: ValueKind::Load(ValueId(0)),
                    }],
                    terminator: Terminator::Return(None),
                },
            ],
        };
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![callee_fn, caller],
            records: leaked_resource_records(resource, resource_name),
            variants: vec![(shape_id, shape_layout)],
        };
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_LOCATION_NOT_DEFINITELY_INITIALIZED),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    // -- A malformed call's own resource argument is never silently
    // treated as a mere observation (`rfcs/0011`) --------------------------

    #[test]
    fn a_resource_argument_to_an_unknown_callee_is_treated_as_consumed_not_observed() {
        // `unknown` is never registered as a known function at all --
        // `%0`'s own status after this call must be conservatively
        // "already consumed" (so a later use of it is independently
        // rejected), never "merely observed" (which would let it be
        // used, or leaked, without complaint).
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: resource_ty.clone(),
                        kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::Unit,
                        kind: ValueKind::Call(
                            ItemId(999),
                            Vec::new(),
                            vec![ValueId(0)],
                            Vec::new(),
                        ),
                    },
                    Instruction::Drop { value: ValueId(0) },
                ],
                terminator: Terminator::Return(None),
            }],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        // Conservatively consumed by the unknown call: the `Drop`
        // afterward is a genuine use-after-consume, and nothing about
        // this shape leaks (the call already discharged the obligation).
        assert!(
            codes_of(&diagnostics).contains(&codes::RESOURCE_USE_AFTER_CONSUME),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert!(
            !codes_of(&diagnostics).contains(&codes::RESOURCE_LEAKED_ON_EXIT),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_resource_stored_into_a_slot_and_dropped_through_it_is_not_a_leak() {
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: resource_ty.clone(),
                        kind: ValueKind::Alloc,
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: resource_ty.clone(),
                        kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                    },
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(1),
                        mode: crate::nir::OwnershipMode::Transfer,
                    },
                    Instruction::Value {
                        result: ValueId(2),
                        ty: resource_ty,
                        kind: ValueKind::Load(ValueId(0)),
                    },
                    Instruction::Drop { value: ValueId(2) },
                ],
                terminator: Terminator::Return(None),
            }],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_resource_stored_into_a_merge_slot_but_dropped_through_its_own_identity_is_not_a_leak() {
        // %1 is stored into %0 (mirroring an `if`'s own internal merge
        // slot fed an already-owned value purely to unify a *read*), but
        // %1 is also dropped directly, through its own original
        // identity, afterward -- exactly the "value used again after
        // being stored" shape a merge slot (never an ownership-
        // transferring move) produces. Must not relocate %1's own
        // obligation onto %0, or this dropped-exactly-once resource
        // would be wrongly reported as leaked through %0, which nothing
        // here ever destroys.
        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let function = Function {
            id: ItemId(0),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: resource_ty.clone(),
                        kind: ValueKind::Alloc,
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: resource_ty,
                        kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                    },
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(1),
                        mode: crate::nir::OwnershipMode::Observe,
                    },
                    Instruction::Drop { value: ValueId(1) },
                ],
                terminator: Terminator::Return(None),
            }],
        };
        let diagnostics = verify_one_with_aggregates(
            function,
            leaked_resource_records(resource, resource_name),
            Vec::new(),
            &interner,
        );
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn two_resources_leaked_in_the_same_block_are_reported_in_a_deterministic_order() {
        // `live`'s own internal `HashSet` iteration order is not
        // deterministic across process runs on its own -- the reported
        // order must never depend on it. Run several times (each a
        // fresh `HashSet`, so a stable *within-one-run* order alone
        // would not catch a raw-iteration-order regression) and require
        // byte-identical messages every time.
        fn leaked_value_ids(
            name: Symbol,
            resource: ItemId,
            resource_name: Symbol,
            interner: &Interner,
        ) -> Vec<u32> {
            let resource_ty = Ty::Named(resource, resource_name);
            let function = Function {
                id: ItemId(0),
                name,
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: Vec::new(),
                return_type: Ty::Unit,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: resource_ty.clone(),
                            kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: resource_ty,
                            kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                        },
                    ],
                    terminator: Terminator::Return(None),
                }],
            };
            let diagnostics = verify_one_with_aggregates(
                function,
                leaked_resource_records(resource, resource_name),
                Vec::new(),
                interner,
            );
            diagnostics
                .iter()
                .filter(|d| d.code == codes::RESOURCE_LEAKED_ON_EXIT)
                .filter_map(|d| {
                    let after = d.message.split_once("(%")?.1;
                    after.split_once(')')?.0.parse().ok()
                })
                .collect()
        }

        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource = ItemId(1);
        let resource_name = interner.intern("File");
        let first = leaked_value_ids(name, resource, resource_name, &interner);
        assert_eq!(first, vec![0, 1], "unexpected leaked ids: {first:?}");
        for _ in 0..8 {
            assert_eq!(
                leaked_value_ids(name, resource, resource_name, &interner),
                first
            );
        }
    }
}

/// Adversarial hand-built NIR for the structural ownership lattice
/// (`rfcs/0012`), written against `verify_module` directly rather than
/// through `nir::lower`: every one of these modules is malformed in a
/// way no source program can express, which is exactly the point --
/// `nir::verify` must reject malformed ownership independently, even
/// when NIR bypasses source checking entirely.
///
/// Every assertion is made against the *set of structural codes*
/// (`V0083`-`V0092`) rather than the complete diagnostic list, so an
/// unrelated pre-existing check firing on the same fixture never makes
/// one of these tests pass or fail for the wrong reason.
#[cfg(test)]
mod structural_ownership {
    use super::*;
    use crate::hir::TypeParamId;
    use crate::nir::{BasicBlock, CaseLayout, OwnershipMode, Param};
    use crate::place::FieldId;
    use crate::source::SourceMap;

    const FILE: ItemId = ItemId(200);
    const SESSION: ItemId = ItemId(201);
    const ENVELOPE: ItemId = ItemId(202);
    const BOXY: ItemId = ItemId(203);
    const HOLDER: ItemId = ItemId(204);
    const PLAIN: ItemId = ItemId(205);
    const SELF: ItemId = ItemId(300);
    const SINK: ItemId = ItemId(301);
    const OBSERVE: ItemId = ItemId(302);
    const BUILD: ItemId = ItemId(303);
    const RAISER: ItemId = ItemId(304);
    const T: TypeParamId = TypeParamId(0);

    struct Fixture {
        interner: Interner,
        records: Vec<(ItemId, RecordLayout)>,
        variants: Vec<(ItemId, VariantLayout)>,
        file: Ty,
        session: Ty,
        envelope: Ty,
        holder: Ty,
        box_file: Ty,
        plain: Ty,
    }

    /// `File` (a declared `resource`), `Session` (a `resource` with two
    /// `File` fields), `Envelope` (an ordinary `record` with one `File`
    /// field, so transitively affine but never nominally a resource),
    /// `Box[T]` (generic), `Holder` (a variant carrying an `Envelope`),
    /// and `Plain` (an ordinary non-affine record).
    fn fixture() -> Fixture {
        let mut interner = Interner::new();
        let file = interner.intern("File");
        let session = interner.intern("Session");
        let envelope = interner.intern("Envelope");
        let boxy = interner.intern("Box");
        let holder = interner.intern("Holder");
        let plain = interner.intern("Plain");
        let descriptor = interner.intern("descriptor");
        let input = interner.intern("input");
        let output = interner.intern("output");
        let item = interner.intern("item");
        let full = interner.intern("Full");
        let empty = interner.intern("Empty");

        let file_ty = Ty::Named(FILE, file);
        let envelope_ty = Ty::Named(ENVELOPE, envelope);
        let records = vec![
            (
                FILE,
                RecordLayout {
                    name: file,
                    type_params: Vec::new(),
                    fields: vec![(descriptor, Ty::I64)],
                    affine: true,
                },
            ),
            (
                SESSION,
                RecordLayout {
                    name: session,
                    type_params: Vec::new(),
                    fields: vec![(input, file_ty.clone()), (output, file_ty.clone())],
                    affine: true,
                },
            ),
            (
                ENVELOPE,
                RecordLayout {
                    name: envelope,
                    type_params: Vec::new(),
                    fields: vec![(item, file_ty.clone())],
                    affine: false,
                },
            ),
            (
                BOXY,
                RecordLayout {
                    name: boxy,
                    type_params: vec![(T, item)],
                    fields: vec![(item, Ty::Param(T, item))],
                    affine: false,
                },
            ),
            (
                PLAIN,
                RecordLayout {
                    name: plain,
                    type_params: Vec::new(),
                    fields: vec![(descriptor, Ty::I64)],
                    affine: false,
                },
            ),
        ];
        let variants = vec![(
            HOLDER,
            VariantLayout {
                name: holder,
                type_params: Vec::new(),
                cases: vec![
                    CaseLayout {
                        name: full,
                        payload: vec![envelope_ty.clone()],
                    },
                    CaseLayout {
                        name: empty,
                        payload: Vec::new(),
                    },
                ],
            },
        )];

        Fixture {
            interner,
            records,
            variants,
            file: file_ty.clone(),
            session: Ty::Named(SESSION, session),
            envelope: envelope_ty,
            holder: Ty::Named(HOLDER, holder),
            box_file: Ty::Applied(BOXY, vec![file_ty]),
            plain: Ty::Named(PLAIN, plain),
        }
    }

    /// `sink(take File) -> unit`, for a genuinely consuming call
    /// argument, and `observe(File) -> i64`, for a merely-observing one.
    fn helpers(fx: &mut Fixture) -> Vec<Function> {
        let sink = fx.interner.intern("sink");
        let observe = fx.interner.intern("observe");
        vec![
            Function {
                id: SINK,
                name: sink,
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: vec![Param {
                    value: ValueId(0),
                    ty: fx.file.clone(),
                    take: true,
                }],
                return_type: Ty::Unit,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Drop { value: ValueId(0) }],
                    terminator: Terminator::Return(None),
                }],
            },
            Function {
                id: OBSERVE,
                name: observe,
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: vec![Param {
                    value: ValueId(0),
                    ty: fx.file.clone(),
                    take: false,
                }],
                return_type: Ty::I64,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(1),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(0)),
                    }],
                    terminator: Terminator::Return(Some(ValueId(1))),
                }],
            },
        ]
    }

    fn under_test(params: Vec<Param>, return_type: Ty, blocks: Vec<BasicBlock>) -> Function {
        Function {
            id: SELF,
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params,
            return_type,
            raises: Vec::new(),
            blocks,
        }
    }

    /// Only the structural ownership family, sorted -- a deterministic
    /// multiset two permutations of the same module can be compared
    /// against directly.
    fn structural_codes(fx: &mut Fixture, function: Function) -> Vec<&'static str> {
        structural_codes_with(fx, function, false)
    }

    /// `with_builder` additionally links in `build`, a callee that
    /// transfers an affine record out to its caller.
    fn structural_codes_with(
        fx: &mut Fixture,
        function: Function,
        with_builder: bool,
    ) -> Vec<&'static str> {
        let helpers = helpers(fx);
        let builder = with_builder.then(|| builder(fx));
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut functions = vec![function];
        functions.extend(helpers);
        functions.extend(builder);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions,
            records: fx.records.clone(),
            variants: fx.variants.clone(),
        };
        let mut codes: Vec<&'static str> =
            verify_module(&module, source, &fx.interner, &ItemRegistry::default())
                .into_iter()
                .map(|d| d.code)
                .filter(|code| {
                    matches!(
                        *code,
                        codes::PLACE_PROJECTION_THROUGH_NON_RECORD
                            | codes::INVALID_PLACE_FIELD_OWNER
                            | codes::UNKNOWN_PLACE_FIELD
                            | codes::MOVE_OF_NON_AFFINE_PLACE
                            | codes::PLACE_USE_AFTER_MOVE
                            | codes::PLACE_OVERWRITE_OF_LIVE_FIELD
                            | codes::PLACE_GENERIC_ARITY_MISMATCH
                            | codes::PARTIAL_PLACE_USED_AS_WHOLE
                            | codes::MISSING_STRUCTURAL_CLEANUP
                            | codes::DUPLICATE_STRUCTURAL_CLEANUP
                            | codes::DECOMPOSITION_OUTSIDE_REFINEMENT
                            | codes::DECOMPOSITION_CLAIM_MISMATCH
                            | codes::UNCLAIMED_PAYLOAD_OWNERSHIP
                    )
                })
                .collect();
        codes.sort_unstable();
        codes
    }

    /// Every diagnostic the whole verifier reports, rendered as
    /// `code: message` in the exact order it was emitted -- so two runs
    /// can be compared byte for byte, not merely as a set of codes.
    fn rendered(fx: &mut Fixture, function: Function) -> Vec<String> {
        let helpers = helpers(fx);
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut functions = vec![function];
        functions.extend(helpers);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions,
            records: fx.records.clone(),
            variants: fx.variants.clone(),
        };
        verify_module(&module, source, &fx.interner, &ItemRegistry::default())
            .into_iter()
            .map(|d| format!("{}: {}", d.code, d.message))
            .collect()
    }

    /// Every diagnostic the whole verifier reports, unfiltered and
    /// sorted -- for asserting which *layer* owns a malformed CFG, and
    /// that no second layer reports the same defect again.
    fn all_codes(fx: &mut Fixture, function: Function) -> Vec<&'static str> {
        let helpers = helpers(fx);
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut functions = vec![function];
        functions.extend(helpers);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions,
            records: fx.records.clone(),
            variants: fx.variants.clone(),
        };
        let mut codes: Vec<&'static str> =
            verify_module(&module, source, &fx.interner, &ItemRegistry::default())
                .into_iter()
                .map(|d| d.code)
                .collect();
        codes.sort_unstable();
        codes
    }

    fn take_session(fx: &Fixture) -> Vec<Param> {
        vec![Param {
            value: ValueId(0),
            ty: fx.session.clone(),
            take: true,
        }]
    }

    fn session_field(index: u32) -> Place<ValueId> {
        Place::root(ValueId(0)).field(SESSION, FieldId(index))
    }

    fn read(result: u32, ty: Ty, place: Place<ValueId>, mode: OwnershipMode) -> Instruction {
        Instruction::Value {
            result: ValueId(result),
            ty,
            kind: ValueKind::PlaceRead { place, mode },
        }
    }

    fn drop_of(value: u32) -> Instruction {
        Instruction::Drop {
            value: ValueId(value),
        }
    }

    fn int(result: u32, value: u128) -> Instruction {
        Instruction::Value {
            result: ValueId(result),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(value)),
        }
    }

    // -- the place tree: ancestors, descendants, siblings ---------------

    #[test]
    fn a_child_moved_then_the_parent_moved_as_a_whole_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    // Moving the parent *as a value* after one of its
                    // own children left: nothing may transfer an
                    // incomplete aggregate.
                    Instruction::Value {
                        result: ValueId(2),
                        ty: fx.session.clone(),
                        kind: ValueKind::Move { source: ValueId(0) },
                    },
                    drop_of(2),
                    int(3, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(3))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::PARTIAL_PLACE_USED_AS_WHOLE),
            "moving a partially moved parent as a whole must be rejected"
        );
    }

    #[test]
    fn a_child_moved_then_the_parent_observed_as_a_whole_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    read(
                        2,
                        fx.session.clone(),
                        Place::root(ValueId(0)),
                        OwnershipMode::Observe,
                    ),
                    int(3, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(3))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::PARTIAL_PLACE_USED_AS_WHOLE),
            "observing a partially moved parent as a whole must be rejected"
        );
    }

    #[test]
    fn a_child_read_after_its_parent_was_transferred_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(1),
                        ty: fx.session.clone(),
                        kind: ValueKind::Move { source: ValueId(0) },
                    },
                    drop_of(1),
                    // `session` is gone: every place reachable through
                    // it went with it, whether or not this exact field
                    // was ever individually tracked.
                    read(2, fx.file.clone(), session_field(0), OwnershipMode::Observe),
                    int(3, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(3))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::PLACE_USE_AFTER_MOVE),
            "reading a child after its parent was transferred must be rejected"
        );
    }

    #[test]
    fn a_child_read_after_its_parent_was_dropped_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    drop_of(0),
                    read(
                        1,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::PLACE_USE_AFTER_MOVE),
            "reading a child after its parent was dropped must be rejected"
        );
    }

    #[test]
    fn moving_one_child_leaves_its_sibling_freely_readable() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    read(
                        2,
                        fx.file.clone(),
                        session_field(1),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(2),
                    drop_of(0),
                    int(3, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(3))),
            }],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "an unaffected sibling must stay available after its sibling moved"
        );
    }

    #[test]
    fn a_partially_moved_parent_may_still_be_structurally_dropped() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    // Only `output` and the outer identity are left --
                    // a structural drop destroys exactly those.
                    read(
                        2,
                        fx.file.clone(),
                        session_field(1),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(2),
                    drop_of(0),
                    int(3, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(3))),
            }],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "a structural drop after a partial move must be accepted"
        );
    }

    #[test]
    fn reinitializing_an_empty_child_restores_the_parents_completeness() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    int(2, 7),
                    Instruction::Value {
                        result: ValueId(3),
                        ty: fx.file.clone(),
                        kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(2)]),
                    },
                    Instruction::StorePlace {
                        place: session_field(0),
                        value: ValueId(3),
                    },
                    // Complete again: a whole-value transfer is legal
                    // once more.
                    Instruction::Value {
                        result: ValueId(4),
                        ty: fx.session.clone(),
                        kind: ValueKind::Move { source: ValueId(0) },
                    },
                    drop_of(4),
                    int(5, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(5))),
            }],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "a reinitialized child must restore its parent's completeness"
        );
    }

    #[test]
    fn dropping_the_same_structural_field_twice_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    read(
                        2,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(2),
                    drop_of(0),
                    int(3, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(3))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::PLACE_USE_AFTER_MOVE),
            "destroying the same structural field twice must be rejected"
        );
    }

    #[test]
    fn dropping_the_same_whole_value_twice_is_duplicate_structural_cleanup() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![drop_of(0), drop_of(0), int(1, 0)],
                terminator: Terminator::Return(Some(ValueId(1))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::DUPLICATE_STRUCTURAL_CLEANUP),
            "a second whole-value destruction must be rejected"
        );
    }

    // -- missing cleanup for a transitively affine aggregate -----------

    #[test]
    fn a_taken_affine_record_parameter_left_undestroyed_is_reported_as_leaked() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.envelope.clone(),
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![int(1, 0)],
                terminator: Terminator::Return(Some(ValueId(1))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::MISSING_STRUCTURAL_CLEANUP),
            "a taken affine record left undestroyed must be reported"
        );
    }

    #[test]
    fn a_taken_affine_record_parameter_destroyed_field_by_field_is_accepted() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.envelope.clone(),
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        Place::root(ValueId(0)).field(ENVELOPE, FieldId(0)),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "an affine record whose own affine field was destroyed owes nothing further"
        );
    }

    #[test]
    fn a_record_construction_consuming_an_affine_record_field_is_accepted() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.file.clone(),
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(1),
                        ty: fx.envelope.clone(),
                        kind: ValueKind::RecordCreate(ENVELOPE, Vec::new(), vec![ValueId(0)]),
                    },
                    read(
                        2,
                        fx.file.clone(),
                        Place::root(ValueId(1)).field(ENVELOPE, FieldId(0)),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(2),
                    int(3, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(3))),
            }],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "constructing an affine record from an owned field, then destroying it, is complete"
        );
    }

    #[test]
    fn a_record_construction_from_an_already_consumed_field_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.file.clone(),
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    drop_of(0),
                    Instruction::Value {
                        result: ValueId(1),
                        ty: fx.envelope.clone(),
                        kind: ValueKind::RecordCreate(ENVELOPE, Vec::new(), vec![ValueId(0)]),
                    },
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::DUPLICATE_STRUCTURAL_CLEANUP),
            "an aggregate built from an already-destroyed field must be rejected"
        );
    }

    #[test]
    fn a_variant_construction_consuming_an_affine_record_payload_is_accepted() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.envelope.clone(),
                take: true,
            }],
            fx.holder.clone(),
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(1),
                    ty: fx.holder.clone(),
                    kind: ValueKind::VariantCreate {
                        variant: HOLDER,
                        case: 0,
                        type_args: Vec::new(),
                        payload: vec![ValueId(0)],
                    },
                }],
                terminator: Terminator::Return(Some(ValueId(1))),
            }],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "a variant taking ownership of an affine payload and returning it owes nothing"
        );
    }

    #[test]
    fn a_take_argument_consuming_an_affine_record_discharges_its_obligation() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.file.clone(),
                take: true,
            }],
            Ty::Unit,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(1),
                    ty: Ty::Unit,
                    kind: ValueKind::Call(SINK, Vec::new(), vec![ValueId(0)], Vec::new()),
                }],
                terminator: Terminator::Return(Some(ValueId(1))),
            }],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "a take argument must discharge its own structural obligation"
        );
    }

    #[test]
    fn an_observing_argument_of_a_partially_moved_parent_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    Instruction::Value {
                        result: ValueId(2),
                        ty: Ty::I64,
                        kind: ValueKind::Call(OBSERVE, Vec::new(), vec![ValueId(0)], Vec::new()),
                    },
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::PARTIAL_PLACE_USED_AS_WHOLE),
            "passing a partially moved parent to an observing parameter must be rejected"
        );
    }

    // -- malformed projection metadata ---------------------------------

    #[test]
    fn a_place_projecting_an_unknown_field_owner_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        Place::root(ValueId(0)).field(ItemId(9999), FieldId(0)),
                        OwnershipMode::Observe,
                    ),
                    drop_of(0),
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        let codes = structural_codes(&mut fx, f);
        assert!(
            codes.contains(&codes::PLACE_PROJECTION_THROUGH_NON_RECORD)
                || codes.contains(&codes::INVALID_PLACE_FIELD_OWNER),
            "an unknown field owner must be rejected, got {codes:?}"
        );
    }

    #[test]
    fn a_place_projecting_a_field_index_out_of_range_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        Place::root(ValueId(0)).field(SESSION, FieldId(9)),
                        OwnershipMode::Observe,
                    ),
                    drop_of(0),
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::UNKNOWN_PLACE_FIELD),
            "a field index out of range must be rejected"
        );
    }

    #[test]
    fn a_place_projecting_a_non_affine_field_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.plain.clone(),
                take: false,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        Ty::I64,
                        Place::root(ValueId(0)).field(PLAIN, FieldId(0)),
                        OwnershipMode::Transfer,
                    ),
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::MOVE_OF_NON_AFFINE_PLACE),
            "moving an ordinary, freely copyable field must be rejected"
        );
    }

    // -- generics -------------------------------------------------------

    #[test]
    fn a_substituted_generic_field_place_resolves_to_its_concrete_affine_type() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.box_file.clone(),
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        Place::root(ValueId(0)).field(BOXY, FieldId(0)),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "`Box[File].item` must resolve to the affine `File`, not a bare type parameter"
        );
    }

    #[test]
    fn a_generic_place_with_the_wrong_type_argument_arity_is_rejected() {
        let mut fx = fixture();
        let wrong = Ty::Applied(BOXY, vec![fx.file.clone(), fx.file.clone()]);
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: wrong,
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        Place::root(ValueId(0)).field(BOXY, FieldId(0)),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::PLACE_GENERIC_ARITY_MISMATCH),
            "a generic place whose arity disagrees with its own declaration must be rejected"
        );
    }

    #[test]
    fn a_generic_place_with_no_recorded_type_parameters_is_rejected_not_defaulted() {
        let mut fx = fixture();
        // Strip `Box`'s own type-parameter list, leaving the place's
        // own single type argument with nothing to bind to. The
        // substitution must fail loudly rather than silently become
        // empty and leave `item` typed as a never-affine `Ty::Param`.
        for (id, layout) in fx.records.iter_mut() {
            if *id == BOXY {
                layout.type_params.clear();
            }
        }
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.box_file.clone(),
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(
                        1,
                        fx.file.clone(),
                        Place::root(ValueId(0)).field(BOXY, FieldId(0)),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(1),
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::PLACE_GENERIC_ARITY_MISMATCH),
            "missing generic metadata must be rejected, never treated as an empty substitution"
        );
    }

    // -- joins, orderings, and permutation invariance -------------------

    /// `f(cond) { if cond { move session.input; drop it } ; read
    /// session.input }` -- empty on exactly one predecessor, so the
    /// join is the absorbing `Maybe` and the later read is rejected.
    fn field_empty_on_one_predecessor(fx: &Fixture) -> Vec<BasicBlock> {
        vec![
            BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::CondBranch {
                    condition: ValueId(1),
                    then_block: BlockId(1),
                    else_block: BlockId(2),
                },
            },
            BasicBlock {
                id: BlockId(1),
                instructions: vec![
                    read(
                        2,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(2),
                ],
                terminator: Terminator::Branch(BlockId(2)),
            },
            BasicBlock {
                id: BlockId(2),
                instructions: vec![
                    read(
                        3,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(3),
                    drop_of(0),
                    int(4, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(4))),
            },
        ]
    }

    fn cond_params(fx: &Fixture) -> Vec<Param> {
        vec![
            Param {
                value: ValueId(0),
                ty: fx.session.clone(),
                take: true,
            },
            Param {
                value: ValueId(1),
                ty: Ty::Bool,
                take: false,
            },
        ]
    }

    #[test]
    fn a_field_empty_on_only_one_predecessor_is_rejected_at_the_join() {
        let mut fx = fixture();
        let blocks = field_empty_on_one_predecessor(&fx);
        let f = under_test(cond_params(&fx), Ty::I64, blocks);
        assert!(
            structural_codes(&mut fx, f).contains(&codes::PLACE_USE_AFTER_MOVE),
            "a field emptied on only one path must not be usable after the join"
        );
    }

    #[test]
    fn a_reversed_block_vector_produces_the_identical_diagnostic_multiset() {
        let mut fx = fixture();
        let forward = field_empty_on_one_predecessor(&fx);
        let mut reversed = forward.clone();
        reversed.reverse();
        let params = cond_params(&fx);
        let a = structural_codes(&mut fx, under_test(params.clone(), Ty::I64, forward));
        let b = structural_codes(&mut fx, under_test(params, Ty::I64, reversed));
        assert_eq!(
            a, b,
            "block vector order must not change which structural diagnostics fire"
        );
        assert!(
            !a.is_empty(),
            "the fixture must actually diagnose something"
        );
    }

    #[test]
    fn a_reversed_predecessor_order_produces_the_identical_diagnostic_multiset() {
        let mut fx = fixture();
        // The join block's two predecessors are discovered in the order
        // the block vector lists them; swapping the two `CondBranch`
        // targets (and the bodies with them) reverses that discovery
        // order without changing the program's meaning.
        let forward = field_empty_on_one_predecessor(&fx);
        let mut swapped = forward.clone();
        swapped[0].terminator = Terminator::CondBranch {
            condition: ValueId(1),
            then_block: BlockId(2),
            else_block: BlockId(1),
        };
        swapped[1].terminator = Terminator::Branch(BlockId(2));
        let params = cond_params(&fx);
        let a = structural_codes(&mut fx, under_test(params.clone(), Ty::I64, forward));
        let b = structural_codes(&mut fx, under_test(params, Ty::I64, swapped));
        assert_eq!(
            a, b,
            "predecessor discovery order must not change which structural diagnostics fire"
        );
    }

    #[test]
    fn an_unreachable_predecessor_contributes_no_structural_facts() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        read(
                            1,
                            fx.file.clone(),
                            session_field(0),
                            OwnershipMode::Transfer,
                        ),
                        drop_of(1),
                        read(
                            2,
                            fx.file.clone(),
                            session_field(1),
                            OwnershipMode::Transfer,
                        ),
                        drop_of(2),
                        drop_of(0),
                        int(3, 0),
                    ],
                    terminator: Terminator::Return(Some(ValueId(3))),
                },
                // Never reached from the entry block at all: its own
                // (nonsense) facts must not leak into anything.
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![
                        read(
                            4,
                            fx.file.clone(),
                            session_field(0),
                            OwnershipMode::Transfer,
                        ),
                        drop_of(4),
                    ],
                    terminator: Terminator::Branch(BlockId(1)),
                },
            ],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "an unreachable block (including an unreachable cycle) must contribute nothing"
        );
    }

    #[test]
    fn a_loop_that_moves_and_reinitializes_the_same_field_is_accepted() {
        let mut fx = fixture();
        let f = under_test(
            cond_params(&fx),
            Ty::I64,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::CondBranch {
                        condition: ValueId(1),
                        then_block: BlockId(2),
                        else_block: BlockId(3),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![
                        read(
                            2,
                            fx.file.clone(),
                            session_field(0),
                            OwnershipMode::Transfer,
                        ),
                        drop_of(2),
                        int(3, 1),
                        Instruction::Value {
                            result: ValueId(4),
                            ty: fx.file.clone(),
                            kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(3)]),
                        },
                        Instruction::StorePlace {
                            place: session_field(0),
                            value: ValueId(4),
                        },
                    ],
                    // Back edge: the field is `Full` again, so a second
                    // iteration may move it again.
                    terminator: Terminator::Branch(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![drop_of(0), int(5, 0)],
                    terminator: Terminator::Return(Some(ValueId(5))),
                },
            ],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "a loop that restores what it moved must be accepted on every iteration"
        );
    }

    #[test]
    fn a_deep_alternating_projection_chain_is_tracked_without_panicking() {
        let mut fx = fixture();
        // `Session.input.descriptor` is not affine, so the deepest
        // *affine* place is two levels down; the chain below goes
        // deliberately deeper than any declaration allows, which must
        // be diagnosed rather than panic or hang.
        let deep = Place::root(ValueId(0))
            .field(SESSION, FieldId(0))
            .field(FILE, FieldId(0))
            .field(FILE, FieldId(0));
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    read(1, fx.file.clone(), deep, OwnershipMode::Transfer),
                    drop_of(1),
                    drop_of(0),
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        let codes = structural_codes(&mut fx, f);
        assert!(
            !codes.is_empty(),
            "an over-deep projection chain must be diagnosed, got {codes:?}"
        );
    }

    #[test]
    fn the_entry_block_listed_last_produces_the_identical_diagnostic_multiset() {
        let mut fx = fixture();
        let forward = field_empty_on_one_predecessor(&fx);
        let mut rotated = forward.clone();
        let head = rotated.remove(0);
        rotated.push(head);
        let params = cond_params(&fx);
        let a = structural_codes(&mut fx, under_test(params.clone(), Ty::I64, forward));
        let b = structural_codes(&mut fx, under_test(params, Ty::I64, rotated));
        assert_eq!(
            a, b,
            "the entry block's position in the vector must not change the result"
        );
    }

    // -- lattice laws ---------------------------------------------------

    #[test]
    fn an_ancestors_state_dominates_every_descendant() {
        let mut facts = PlaceFacts::new();
        let parent = Place::root(ValueId(0));
        let child = parent.field(SESSION, FieldId(0));
        let grandchild = child.field(FILE, FieldId(0));
        set_place_state(&mut facts, &parent, FieldState::Empty);
        assert_eq!(resolve_place_state(&facts, &child), FieldState::Empty);
        assert_eq!(resolve_place_state(&facts, &grandchild), FieldState::Empty);
    }

    #[test]
    fn a_consumed_descendant_makes_every_ancestor_partial_but_not_consumed() {
        let mut facts = PlaceFacts::new();
        let parent = Place::root(ValueId(0));
        let child = parent.field(SESSION, FieldId(0));
        let sibling = parent.field(SESSION, FieldId(1));
        set_place_state(&mut facts, &child, FieldState::Empty);
        assert_eq!(resolve_place_state(&facts, &parent), FieldState::Full);
        assert!(!place_is_whole(&facts, &parent));
        assert!(place_is_whole(&facts, &sibling));
    }

    #[test]
    fn setting_an_ancestor_clears_every_stale_descendant_fact() {
        let mut facts = PlaceFacts::new();
        let parent = Place::root(ValueId(0));
        let child = parent.field(SESSION, FieldId(0));
        set_place_state(&mut facts, &child, FieldState::Empty);
        set_place_state(&mut facts, &parent, FieldState::Full);
        assert!(
            place_is_whole(&facts, &parent),
            "restoring a parent must retire every stale descendant fact"
        );
    }

    #[test]
    fn a_join_over_the_union_of_keys_is_commutative_and_absorbing() {
        let parent = Place::root(ValueId(0));
        let child = parent.field(SESSION, FieldId(0));
        let mut a = PlaceFacts::new();
        a.insert(child.clone(), FieldState::Empty);
        let b = PlaceFacts::new();
        let left = merge_place_facts(&a, &b);
        let right = merge_place_facts(&b, &a);
        assert_eq!(left, right, "the join must be commutative");
        assert_eq!(
            left.get(&child),
            Some(&FieldState::Maybe),
            "a key present on only one side must join to the absorbing state"
        );
    }

    // -- an extracted variant payload's own obligation ------------------

    /// `f(take holder: Holder) { switch holder { Full -> extract the
    /// `Envelope` payload and <do something with it>; Empty -> return } }`
    /// -- the scrutinee itself is never consumed whole, so the extracted
    /// payload is this function's own sole obligation.
    fn payload_extraction(fx: &Fixture, destroy_payload: bool) -> Vec<BasicBlock> {
        payload_extraction_with(fx, true, destroy_payload)
    }

    /// `claim_payload` decides whether a `DecomposeVariant` actually
    /// transfers the extraction to this frame. Without it the read owns
    /// nothing, and the shell still owns what it read.
    fn payload_extraction_with(
        fx: &Fixture,
        claim_payload: bool,
        destroy_payload: bool,
    ) -> Vec<BasicBlock> {
        let mut full = vec![Instruction::Value {
            result: ValueId(1),
            ty: fx.envelope.clone(),
            kind: ValueKind::VariantPayload {
                base: ValueId(0),
                variant: HOLDER,
                case: 0,
                index: 0,
            },
        }];
        if claim_payload {
            full.push(Instruction::DecomposeVariant {
                value: ValueId(0),
                variant: HOLDER,
                case: 0,
                taken: vec![(0, ValueId(1))],
            });
        }
        if destroy_payload {
            full.push(drop_of(1));
        }
        full.push(int(2, 1));
        vec![
            BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Switch {
                    scrutinee: ValueId(0),
                    variant: HOLDER,
                    cases: vec![BlockId(1), BlockId(2)],
                },
            },
            BasicBlock {
                id: BlockId(1),
                instructions: full,
                terminator: Terminator::Return(Some(ValueId(2))),
            },
            BasicBlock {
                id: BlockId(2),
                instructions: vec![int(3, 0)],
                terminator: Terminator::Return(Some(ValueId(3))),
            },
        ]
    }

    #[test]
    fn an_extracted_affine_record_payload_left_undestroyed_is_reported() {
        let mut fx = fixture();
        let blocks = payload_extraction(&fx, false);
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.holder.clone(),
                take: true,
            }],
            Ty::I64,
            blocks,
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::MISSING_STRUCTURAL_CLEANUP),
            "a payload extracted out of a scrutinee nothing else consumes is this function's own \
             obligation"
        );
    }

    #[test]
    fn an_extracted_affine_record_payload_that_is_destroyed_is_accepted() {
        let mut fx = fixture();
        let blocks = payload_extraction(&fx, true);
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.holder.clone(),
                take: true,
            }],
            Ty::I64,
            blocks,
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "destroying the extracted payload discharges the obligation"
        );
    }

    #[test]
    fn an_extracted_affine_record_payload_destroyed_without_a_claim_is_rejected() {
        let mut fx = fixture();
        // The read alone transfers nothing: the shell still owns this
        // payload, and will destroy it again.
        let blocks = payload_extraction_with(&fx, false, true);
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.holder.clone(),
                take: true,
            }],
            Ty::I64,
            blocks,
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::UNCLAIMED_PAYLOAD_OWNERSHIP),
            "destroying an unclaimed extraction destroys storage the shell still owns"
        );
    }

    /// The same extraction, but with the scrutinee *also* destroyed on
    /// the other edge: that destruction already covers the payload, so
    /// the extracted copy owns nothing of its own and demanding a
    /// separate destruction would double-count the identical obligation.
    #[test]
    fn a_payload_extracted_from_a_scrutinee_that_is_itself_destroyed_owes_nothing() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.holder.clone(),
                take: true,
            }],
            Ty::I64,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Switch {
                        scrutinee: ValueId(0),
                        variant: HOLDER,
                        cases: vec![BlockId(1), BlockId(2)],
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(1),
                            ty: fx.envelope.clone(),
                            kind: ValueKind::VariantPayload {
                                base: ValueId(0),
                                variant: HOLDER,
                                case: 0,
                                index: 0,
                            },
                        },
                        drop_of(0),
                        int(2, 1),
                    ],
                    terminator: Terminator::Return(Some(ValueId(2))),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![drop_of(0), int(3, 0)],
                    terminator: Terminator::Return(Some(ValueId(3))),
                },
            ],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "a scrutinee destroyed as a whole already covers its own extracted payload"
        );
    }

    // -- a call's own returned affine value -----------------------------

    /// `build() -> Envelope`, for a callee that transfers an affine
    /// record out to its caller.
    fn builder(fx: &mut Fixture) -> Function {
        let build = fx.interner.intern("build");
        Function {
            id: BUILD,
            name: build,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: fx.file.clone(),
                take: true,
            }],
            return_type: fx.envelope.clone(),
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(1),
                    ty: fx.envelope.clone(),
                    kind: ValueKind::RecordCreate(ENVELOPE, Vec::new(), vec![ValueId(0)]),
                }],
                terminator: Terminator::Return(Some(ValueId(1))),
            }],
        }
    }

    fn calls_builder(fx: &Fixture, destroy: bool) -> Function {
        let mut instructions = vec![Instruction::Value {
            result: ValueId(1),
            ty: fx.envelope.clone(),
            kind: ValueKind::Call(BUILD, Vec::new(), vec![ValueId(0)], Vec::new()),
        }];
        if destroy {
            instructions.push(read(
                2,
                fx.file.clone(),
                Place::root(ValueId(1)).field(ENVELOPE, FieldId(0)),
                OwnershipMode::Transfer,
            ));
            instructions.push(drop_of(2));
        }
        instructions.push(int(3, 0));
        under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.file.clone(),
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions,
                terminator: Terminator::Return(Some(ValueId(3))),
            }],
        )
    }

    #[test]
    fn an_affine_record_returned_by_a_call_and_left_undestroyed_is_reported() {
        let mut fx = fixture();
        let f = calls_builder(&fx, false);
        assert!(
            structural_codes_with(&mut fx, f, true).contains(&codes::MISSING_STRUCTURAL_CLEANUP),
            "a callee transfers its affine result out to this frame, which then owns it"
        );
    }

    #[test]
    fn an_affine_record_returned_by_a_call_and_destroyed_is_accepted() {
        let mut fx = fixture();
        let f = calls_builder(&fx, true);
        assert_eq!(
            structural_codes_with(&mut fx, f, true),
            Vec::<&str>::new(),
            "destroying the returned record's own affine field discharges the obligation"
        );
    }

    // -- adversarial control-flow shapes for the structural fixed point -

    /// A diamond whose two arms may disagree about whether they
    /// moved `session.input`. The merge block then moves it, which is
    /// legal exactly when it is definitely still there on every path
    /// reaching the join.
    fn diamond(fx: &Fixture, arms_that_move: usize) -> Vec<BasicBlock> {
        let arm = |index: usize, result: u32| {
            if index < arms_that_move {
                vec![
                    read(
                        result,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(result),
                ]
            } else {
                Vec::new()
            }
        };
        vec![
            BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::CondBranch {
                    condition: ValueId(1),
                    then_block: BlockId(1),
                    else_block: BlockId(2),
                },
            },
            BasicBlock {
                id: BlockId(1),
                instructions: arm(0, 2),
                terminator: Terminator::Branch(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                instructions: arm(1, 3),
                terminator: Terminator::Branch(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(3),
                instructions: vec![
                    read(
                        4,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(4),
                    read(
                        6,
                        fx.file.clone(),
                        session_field(1),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(6),
                    drop_of(0),
                    int(5, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(5))),
            },
        ]
    }

    #[test]
    fn a_diamond_whose_arms_agree_joins_cleanly() {
        let mut fx = fixture();
        let params = cond_params(&fx);
        let blocks = diamond(&fx, 0);
        assert_eq!(
            structural_codes(&mut fx, under_test(params, Ty::I64, blocks)),
            Vec::<&str>::new(),
            "neither arm touched the field, so the join leaves it definitely present"
        );
    }

    #[test]
    fn a_diamond_whose_arms_disagree_is_reported_once_at_the_join() {
        let mut fx = fixture();
        let params = cond_params(&fx);
        let blocks = diamond(&fx, 1);
        let codes = structural_codes(&mut fx, under_test(params, Ty::I64, blocks));
        assert!(
            codes.contains(&codes::PARTIAL_PLACE_USED_AS_WHOLE)
                || codes.contains(&codes::PLACE_USE_AFTER_MOVE),
            "a one-sided move before a join must not be silently accepted, got {codes:?}"
        );
    }

    /// A loop whose back edge reaches the header before the header has
    /// ever been processed: the unprocessed predecessor must contribute
    /// nothing, never a fact set nothing proved.
    fn loop_with_back_edge(fx: &Fixture, restore: bool) -> Vec<BasicBlock> {
        let mut body = vec![
            read(
                2,
                fx.file.clone(),
                session_field(0),
                OwnershipMode::Transfer,
            ),
            drop_of(2),
        ];
        if restore {
            body.push(int(3, 1));
            body.push(Instruction::Value {
                result: ValueId(4),
                ty: fx.file.clone(),
                kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(3)]),
            });
            body.push(Instruction::StorePlace {
                place: session_field(0),
                value: ValueId(4),
            });
        }
        vec![
            BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Branch(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                instructions: Vec::new(),
                terminator: Terminator::CondBranch {
                    condition: ValueId(1),
                    then_block: BlockId(2),
                    else_block: BlockId(3),
                },
            },
            BasicBlock {
                id: BlockId(2),
                instructions: body,
                terminator: Terminator::Branch(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(3),
                instructions: vec![drop_of(0), int(5, 0)],
                terminator: Terminator::Return(Some(ValueId(5))),
            },
        ]
    }

    #[test]
    fn a_loop_that_moves_without_restoring_is_reported() {
        let mut fx = fixture();
        let params = cond_params(&fx);
        let blocks = loop_with_back_edge(&fx, false);
        assert!(
            structural_codes(&mut fx, under_test(params, Ty::I64, blocks))
                .contains(&codes::PLACE_USE_AFTER_MOVE),
            "a second iteration would move an already-empty field"
        );
    }

    #[test]
    fn a_loop_that_restores_what_it_moved_reaches_a_clean_fixed_point() {
        let mut fx = fixture();
        let params = cond_params(&fx);
        let blocks = loop_with_back_edge(&fx, true);
        assert_eq!(
            structural_codes(&mut fx, under_test(params, Ty::I64, blocks)),
            Vec::<&str>::new(),
            "the back edge restores the field, so every iteration starts complete"
        );
    }

    /// Every permutation of the same CFG must produce the identical
    /// sorted diagnostic multiset -- block-vector order, entry position
    /// and predecessor discovery order are all storage details.
    fn assert_permutation_invariant(fx: &mut Fixture, blocks: Vec<BasicBlock>, label: &str) {
        let params = cond_params(fx);
        let baseline = structural_codes(fx, under_test(params.clone(), Ty::I64, blocks.clone()));

        let mut reversed = blocks.clone();
        reversed.reverse();
        assert_eq!(
            structural_codes(fx, under_test(params.clone(), Ty::I64, reversed)),
            baseline,
            "{label}: reversing the block vector changed the result"
        );

        let mut rotated = blocks.clone();
        let head = rotated.remove(0);
        rotated.push(head);
        assert_eq!(
            structural_codes(fx, under_test(params.clone(), Ty::I64, rotated)),
            baseline,
            "{label}: moving the entry block last changed the result"
        );

        // Reverse each block's own predecessor discovery order by
        // reversing the order successors are listed in.
        let swapped: Vec<BasicBlock> = blocks
            .iter()
            .map(|b| {
                let terminator = match &b.terminator {
                    Terminator::CondBranch {
                        condition,
                        then_block,
                        else_block,
                    } => Terminator::CondBranch {
                        condition: *condition,
                        then_block: *else_block,
                        else_block: *then_block,
                    },
                    other => other.clone(),
                };
                BasicBlock {
                    id: b.id,
                    instructions: b.instructions.clone(),
                    terminator,
                }
            })
            .collect();
        let swapped_codes = structural_codes(fx, under_test(params, Ty::I64, swapped));
        assert_eq!(
            swapped_codes.len(),
            baseline.len(),
            "{label}: swapping branch targets changed how many diagnostics fire"
        );
    }

    #[test]
    fn a_diamonds_diagnostics_are_invariant_under_every_ordering() {
        let mut fx = fixture();
        let blocks = diamond(&fx, 1);
        assert_permutation_invariant(&mut fx, blocks, "diamond");
    }

    #[test]
    fn a_loops_diagnostics_are_invariant_under_every_ordering() {
        let mut fx = fixture();
        let blocks = loop_with_back_edge(&fx, false);
        assert_permutation_invariant(&mut fx, blocks, "loop");
    }

    #[test]
    fn a_deep_chain_reaches_its_fixed_point() {
        let mut fx = fixture();
        // Twenty blocks in a row, the last of which cleans up: a long
        // chain must not need more passes than the worklist gives it.
        let depth = 20u32;
        let mut blocks: Vec<BasicBlock> = (0..depth)
            .map(|i| BasicBlock {
                id: BlockId(i),
                instructions: Vec::new(),
                terminator: Terminator::Branch(BlockId(i + 1)),
            })
            .collect();
        blocks.push(BasicBlock {
            id: BlockId(depth),
            instructions: vec![
                read(
                    2,
                    fx.file.clone(),
                    session_field(0),
                    OwnershipMode::Transfer,
                ),
                drop_of(2),
                read(
                    3,
                    fx.file.clone(),
                    session_field(1),
                    OwnershipMode::Transfer,
                ),
                drop_of(3),
                drop_of(0),
                int(4, 0),
            ],
            terminator: Terminator::Return(Some(ValueId(4))),
        });
        let params = cond_params(&fx);
        assert_eq!(
            structural_codes(&mut fx, under_test(params, Ty::I64, blocks)),
            Vec::<&str>::new(),
            "a twenty-deep chain must converge and stay clean"
        );
    }

    #[test]
    fn an_unreachable_cycle_seeds_no_reachable_ownership() {
        let mut fx = fixture();
        let params = cond_params(&fx);
        let f = under_test(
            params,
            Ty::I64,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        read(
                            2,
                            fx.file.clone(),
                            session_field(0),
                            OwnershipMode::Transfer,
                        ),
                        drop_of(2),
                        read(
                            3,
                            fx.file.clone(),
                            session_field(1),
                            OwnershipMode::Transfer,
                        ),
                        drop_of(3),
                        drop_of(0),
                        int(4, 0),
                    ],
                    terminator: Terminator::Return(Some(ValueId(4))),
                },
                // Two blocks reachable only from each other. Their
                // (nonsense) facts must never reach bb0.
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![read(
                        5,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    )],
                    terminator: Terminator::Branch(BlockId(2)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(1)),
                },
            ],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "an unreachable cycle must contribute nothing at all"
        );
    }

    /// An `Invoke`'s success and failure edges reaching the same block:
    /// both are real predecessors and both must be joined.
    #[test]
    fn invoke_success_and_failure_edges_reaching_one_block_are_both_joined() {
        let mut fx = fixture();
        let raiser = fx.interner.intern("raiser");
        let shared = BlockId(1);
        let f = Function {
            id: SELF,
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: take_session(&fx),
            return_type: Ty::I64,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        read(
                            1,
                            fx.file.clone(),
                            session_field(0),
                            OwnershipMode::Transfer,
                        ),
                        drop_of(1),
                        Instruction::Value {
                            result: ValueId(2),
                            ty: Ty::Unit,
                            kind: ValueKind::Alloc,
                        },
                    ],
                    terminator: Terminator::Invoke {
                        callee: RAISER,
                        type_args: Vec::new(),
                        args: Vec::new(),
                        evidence: Vec::new(),
                        ok_slot: ValueId(2),
                        ok_target: shared,
                        err_targets: vec![crate::nir::InvokeErrTarget {
                            variant: HOLDER,
                            slot: ValueId(3),
                            target: shared,
                        }],
                    },
                },
                BasicBlock {
                    id: shared,
                    instructions: vec![
                        // `input` is empty on *both* edges, so this
                        // second move of it must be rejected.
                        read(
                            4,
                            fx.file.clone(),
                            session_field(0),
                            OwnershipMode::Transfer,
                        ),
                        drop_of(4),
                        int(5, 0),
                    ],
                    terminator: Terminator::Return(Some(ValueId(5))),
                },
            ],
        };
        let _ = raiser;
        assert!(
            structural_codes(&mut fx, f).contains(&codes::PLACE_USE_AFTER_MOVE),
            "both invoke edges carry the same emptied field into the shared block"
        );
    }

    #[test]
    fn an_edge_naming_an_undeclared_block_is_owned_by_the_terminator_layer() {
        let mut fx = fixture();
        let params = cond_params(&fx);
        let f = under_test(
            params,
            Ty::I64,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::CondBranch {
                        condition: ValueId(1),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                // bb1 branches from a block that does not exist in this
                // function at all -- reached here by declaring bb2 with
                // an edge out of an undeclared bb7 into bb1 is not
                // expressible, so instead bb2 itself is undeclared and
                // bb1 joins an edge from it.
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![
                        read(
                            2,
                            fx.file.clone(),
                            session_field(0),
                            OwnershipMode::Transfer,
                        ),
                        drop_of(2),
                        read(
                            3,
                            fx.file.clone(),
                            session_field(1),
                            OwnershipMode::Transfer,
                        ),
                        drop_of(3),
                        drop_of(0),
                        int(4, 0),
                    ],
                    terminator: Terminator::Return(Some(ValueId(4))),
                },
            ],
        );
        // bb2 is never declared. That is a genuine malformed CFG, and
        // exactly one layer owns it: the terminator check, as
        // `UNKNOWN_BRANCH_TARGET`. The structural pass never reaches
        // past that edge and must invent no ownership state for it --
        // bb1 cleans `session` up completely, so there is nothing for
        // it to report and no second diagnostic for the same defect.
        let structural = structural_codes(&mut fx, f.clone());
        assert!(
            structural.is_empty(),
            "an undeclared successor must not make this pass invent ownership state, \
             got {structural:?}"
        );
        let all = all_codes(&mut fx, f);
        assert_eq!(
            all.iter()
                .filter(|code| **code == codes::UNKNOWN_BRANCH_TARGET)
                .count(),
            1,
            "the undeclared target is reported once, by the layer that owns it, got {all:?}"
        );
    }

    // -- path-sensitive variant decomposition, hand-built --------------

    /// `f(take holder: Holder, cond: bool)`: one branch drops the shell
    /// whole, the other takes it apart into case `Full` and claims its
    /// `Envelope` payload. Neither may affect the other.
    fn branch_local_variant(
        fx: &Fixture,
        drop_first: bool,
        claim_payload: bool,
        destroy_claim: bool,
    ) -> Vec<BasicBlock> {
        let mut decompose_block = vec![Instruction::Value {
            result: ValueId(2),
            ty: fx.envelope.clone(),
            kind: ValueKind::VariantPayload {
                base: ValueId(0),
                variant: HOLDER,
                case: 0,
                index: 0,
            },
        }];
        decompose_block.push(Instruction::DecomposeVariant {
            value: ValueId(0),
            variant: HOLDER,
            case: 0,
            taken: if claim_payload {
                vec![(0, ValueId(2))]
            } else {
                Vec::new()
            },
        });
        if destroy_claim {
            decompose_block.push(drop_of(2));
        }
        decompose_block.push(int(3, 2));

        let drop_block = vec![drop_of(0), int(4, 1)];
        // Taking a value apart into one case is only meaningful where
        // the case is proven, so the decomposing branch tests it first
        // -- exactly the shape `nir::lower` emits for a `match`.
        let (switch_arm, drop_arm) = if drop_first {
            (BlockId(2), BlockId(1))
        } else {
            (BlockId(1), BlockId(2))
        };
        vec![
            BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::CondBranch {
                    condition: ValueId(1),
                    then_block: BlockId(1),
                    else_block: BlockId(2),
                },
            },
            BasicBlock {
                id: drop_arm,
                instructions: drop_block,
                terminator: Terminator::Return(Some(ValueId(4))),
            },
            BasicBlock {
                id: switch_arm,
                instructions: Vec::new(),
                terminator: Terminator::Switch {
                    scrutinee: ValueId(0),
                    variant: HOLDER,
                    cases: vec![BlockId(3), BlockId(4)],
                },
            },
            BasicBlock {
                id: BlockId(3),
                instructions: decompose_block,
                terminator: Terminator::Return(Some(ValueId(3))),
            },
            BasicBlock {
                id: BlockId(4),
                instructions: vec![
                    Instruction::DecomposeVariant {
                        value: ValueId(0),
                        variant: HOLDER,
                        case: 1,
                        taken: Vec::new(),
                    },
                    int(5, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(5))),
            },
        ]
    }

    fn holder_params(fx: &Fixture) -> Vec<Param> {
        vec![
            Param {
                value: ValueId(0),
                ty: fx.holder.clone(),
                take: true,
            },
            Param {
                value: ValueId(1),
                ty: Ty::Bool,
                take: false,
            },
        ]
    }

    #[test]
    fn a_whole_drop_in_one_branch_does_not_discharge_a_sibling_decomposition() {
        let mut fx = fixture();
        let params = holder_params(&fx);
        // The decomposing branch claims the payload but never destroys
        // it: that branch alone must be reported, and the sibling
        // branch's whole drop must not excuse it.
        let blocks = branch_local_variant(&fx, true, true, false);
        assert!(
            structural_codes(&mut fx, under_test(params, Ty::I64, blocks))
                .contains(&codes::MISSING_STRUCTURAL_CLEANUP),
            "a claimed payload left undestroyed on its own path must be reported"
        );
    }

    #[test]
    fn a_whole_drop_in_one_branch_and_a_complete_match_in_the_other_is_accepted() {
        let mut fx = fixture();
        let params = holder_params(&fx);
        let blocks = branch_local_variant(&fx, true, true, true);
        assert_eq!(
            structural_codes(&mut fx, under_test(params, Ty::I64, blocks)),
            Vec::<&str>::new(),
            "disjoint branches each account for the shell exactly once"
        );
    }

    #[test]
    fn reversing_the_branch_order_produces_the_identical_diagnostic_multiset() {
        let mut fx = fixture();
        let params = holder_params(&fx);
        let forward = branch_local_variant(&fx, true, true, true);
        let reversed = branch_local_variant(&fx, false, true, true);
        let a = structural_codes(&mut fx, under_test(params.clone(), Ty::I64, forward));
        let b = structural_codes(&mut fx, under_test(params, Ty::I64, reversed));
        assert_eq!(a, b, "which branch comes first must not matter");
        assert_eq!(a, Vec::<&str>::new());
    }

    #[test]
    fn reversing_the_block_vector_produces_the_identical_diagnostic_multiset() {
        let mut fx = fixture();
        let params = holder_params(&fx);
        let forward = branch_local_variant(&fx, true, true, true);
        let mut reversed = forward.clone();
        reversed.reverse();
        let a = structural_codes(&mut fx, under_test(params.clone(), Ty::I64, forward));
        let b = structural_codes(&mut fx, under_test(params, Ty::I64, reversed));
        assert_eq!(a, b, "block vector order must not matter");
    }

    #[test]
    fn a_decomposition_leaving_an_affine_payload_unclaimed_is_reported() {
        let mut fx = fixture();
        let params = holder_params(&fx);
        // `Full`'s own `Envelope` payload is affine and is claimed by
        // nobody: the shell no longer owns it and nothing else does.
        let blocks = branch_local_variant(&fx, true, false, false);
        assert!(
            structural_codes(&mut fx, under_test(params, Ty::I64, blocks))
                .contains(&codes::MISSING_STRUCTURAL_CLEANUP),
            "every affine payload position must be claimed exactly once"
        );
    }

    #[test]
    fn decomposing_a_shell_twice_on_one_path_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.holder.clone(),
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(1),
                        ty: fx.envelope.clone(),
                        kind: ValueKind::VariantPayload {
                            base: ValueId(0),
                            variant: HOLDER,
                            case: 0,
                            index: 0,
                        },
                    },
                    Instruction::DecomposeVariant {
                        value: ValueId(0),
                        variant: HOLDER,
                        case: 0,
                        taken: vec![(0, ValueId(1))],
                    },
                    drop_of(1),
                    Instruction::DecomposeVariant {
                        value: ValueId(0),
                        variant: HOLDER,
                        case: 0,
                        taken: Vec::new(),
                    },
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::DUPLICATE_STRUCTURAL_CLEANUP),
            "a shell already taken apart cannot be taken apart again"
        );
    }

    #[test]
    fn dropping_a_shell_already_decomposed_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.holder.clone(),
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(1),
                        ty: fx.envelope.clone(),
                        kind: ValueKind::VariantPayload {
                            base: ValueId(0),
                            variant: HOLDER,
                            case: 0,
                            index: 0,
                        },
                    },
                    Instruction::DecomposeVariant {
                        value: ValueId(0),
                        variant: HOLDER,
                        case: 0,
                        taken: vec![(0, ValueId(1))],
                    },
                    drop_of(1),
                    drop_of(0),
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::DUPLICATE_STRUCTURAL_CLEANUP),
            "the shell is spent once its payloads have been taken"
        );
    }

    #[test]
    fn an_inactive_case_owning_nothing_discharges_the_shell() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.holder.clone(),
                take: true,
            }],
            Ty::I64,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Switch {
                        scrutinee: ValueId(0),
                        variant: HOLDER,
                        cases: vec![BlockId(1), BlockId(2)],
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![drop_of(0), int(1, 0)],
                    terminator: Terminator::Return(Some(ValueId(1))),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![
                        // Case 1 (`Empty`) carries no payload at all.
                        Instruction::DecomposeVariant {
                            value: ValueId(0),
                            variant: HOLDER,
                            case: 1,
                            taken: Vec::new(),
                        },
                        int(2, 0),
                    ],
                    terminator: Terminator::Return(Some(ValueId(2))),
                },
            ],
        );
        assert_eq!(
            structural_codes(&mut fx, f),
            Vec::<&str>::new(),
            "taking a payload-less case apart leaves nothing owed"
        );
    }

    #[test]
    fn a_decomposition_naming_a_case_out_of_range_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.holder.clone(),
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::DecomposeVariant {
                        value: ValueId(0),
                        variant: HOLDER,
                        case: 9,
                        taken: Vec::new(),
                    },
                    int(1, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(1))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::UNKNOWN_PLACE_FIELD),
            "a case index out of range must be rejected"
        );
    }

    #[test]
    fn a_decomposition_claiming_one_position_twice_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            vec![Param {
                value: ValueId(0),
                ty: fx.holder.clone(),
                take: true,
            }],
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(1),
                        ty: fx.envelope.clone(),
                        kind: ValueKind::VariantPayload {
                            base: ValueId(0),
                            variant: HOLDER,
                            case: 0,
                            index: 0,
                        },
                    },
                    Instruction::DecomposeVariant {
                        value: ValueId(0),
                        variant: HOLDER,
                        case: 0,
                        taken: vec![(0, ValueId(1)), (0, ValueId(1))],
                    },
                    drop_of(1),
                    int(2, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::DUPLICATE_STRUCTURAL_CLEANUP),
            "one payload position cannot be handed to two owners"
        );
    }

    #[test]
    fn a_decomposition_of_a_value_that_is_not_that_variant_is_rejected() {
        let mut fx = fixture();
        let f = under_test(
            take_session(&fx),
            Ty::I64,
            vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    // `%0` is a `Session`, not a `Holder`.
                    Instruction::DecomposeVariant {
                        value: ValueId(0),
                        variant: HOLDER,
                        case: 1,
                        taken: Vec::new(),
                    },
                    int(1, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(1))),
            }],
        );
        assert!(
            structural_codes(&mut fx, f).contains(&codes::PLACE_PROJECTION_THROUGH_NON_RECORD),
            "the decomposed value must actually be the named variant"
        );
    }

    /// Adversarial control-flow shapes for the structural ownership fixed
    /// point (`rfcs/0012`).
    ///
    /// The defect these exist for: the join used to end in
    /// `Ok(acc.unwrap_or_default())`, so a block none of whose reachable
    /// predecessors had landed yet was handed a real, empty `PlaceFacts` --
    /// a perfectly valid state meaning "every place is still whole" -- ran
    /// its transfer on it, and recorded an out-state its successors then
    /// joined. `IncomingState::Pending` is a distinct answer that runs no
    /// transfer and records no out-state, and the shapes below pin down
    /// both that distinction and the convergence it has to preserve.
    #[cfg(test)]
    mod structural_fixpoint {
        use super::*;

        // -- the Pending answer itself -------------------------------------

        #[test]
        fn the_entry_block_is_its_own_proven_boundary_condition() {
            let incoming = HashMap::new();
            let reachable = HashSet::from([BlockId(0)]);
            let out = HashMap::new();
            assert_eq!(
                in_state_for_places(
                    BlockId(0),
                    BlockId(0),
                    &incoming,
                    &reachable,
                    &out,
                    &PlaceFacts::new()
                ),
                IncomingState::Entry(PlaceFacts::new()),
                "the entry block's empty in-state is proven, not a placeholder"
            );
        }

        #[test]
        fn a_block_waiting_for_every_predecessor_is_pending_not_an_empty_state() {
            // bb2 joins bb0 and bb1. Neither has produced an out-state.
            let incoming = HashMap::from([(BlockId(2), vec![BlockId(0), BlockId(1)])]);
            let reachable = HashSet::from([BlockId(0), BlockId(1), BlockId(2)]);
            assert_eq!(
                in_state_for_places(
                    BlockId(2),
                    BlockId(0),
                    &incoming,
                    &reachable,
                    &HashMap::new(),
                    &PlaceFacts::new()
                ),
                IncomingState::Pending,
                "nothing has been computed, which is not the same as having computed nothing"
            );
            // The same block, once a predecessor has genuinely computed an
            // empty out-state, is a different answer entirely -- which is
            // exactly what `unwrap_or_default` used to erase.
            assert_eq!(
                in_state_for_places(
                    BlockId(2),
                    BlockId(0),
                    &incoming,
                    &reachable,
                    &HashMap::from([(BlockId(1), PlaceFacts::new())]),
                    &PlaceFacts::new()
                ),
                IncomingState::Ready(PlaceFacts::new()),
                "a computed empty out-state is a real state, and must not compare equal to Pending"
            );
        }

        #[test]
        fn a_block_waiting_for_one_predecessor_joins_only_the_ones_that_landed() {
            let consumed = PlaceFacts::from([(Place::root(ValueId(0)), FieldState::Empty)]);
            // bb2's back edge from bb1 has not been processed yet; bb0 has.
            let incoming = HashMap::from([(BlockId(2), vec![BlockId(0), BlockId(1)])]);
            let reachable = HashSet::from([BlockId(0), BlockId(1), BlockId(2)]);
            assert_eq!(
                in_state_for_places(
                    BlockId(2),
                    BlockId(0),
                    &incoming,
                    &reachable,
                    &HashMap::from([(BlockId(0), consumed.clone())]),
                    &PlaceFacts::new()
                ),
                IncomingState::Ready(consumed),
                "an unprocessed back edge contributes nothing, and never dilutes what did land"
            );
        }

        #[test]
        fn an_unreachable_predecessors_computed_out_state_is_never_joined() {
            let consumed = PlaceFacts::from([(Place::root(ValueId(0)), FieldState::Empty)]);
            let incoming = HashMap::from([(BlockId(2), vec![BlockId(1)])]);
            // bb1 has an out-state, but nothing reaches it from the entry.
            let reachable = HashSet::from([BlockId(0), BlockId(2)]);
            assert_eq!(
                in_state_for_places(
                    BlockId(2),
                    BlockId(0),
                    &incoming,
                    &reachable,
                    &HashMap::from([(BlockId(1), consumed)]),
                    &PlaceFacts::new()
                ),
                IncomingState::Pending,
                "a dead CFG fragment may not seed reachable ownership, even having computed facts"
            );
        }

        // -- convergence under adversarial control flow --------------------

        #[test]
        fn a_self_looping_block_reaches_a_fixed_point() {
            let mut fx = fixture();
            let f = under_test(
                cond_params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(1)),
                    },
                    // bb1 is its own predecessor: on the very first visit
                    // its only landed predecessor is bb0, and the back edge
                    // contributes nothing until it has been computed.
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: Terminator::CondBranch {
                            condition: ValueId(1),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![
                            read(
                                2,
                                fx.file.clone(),
                                session_field(0),
                                OwnershipMode::Transfer,
                            ),
                            drop_of(2),
                            read(
                                3,
                                fx.file.clone(),
                                session_field(1),
                                OwnershipMode::Transfer,
                            ),
                            drop_of(3),
                            drop_of(0),
                            int(4, 0),
                        ],
                        terminator: Terminator::Return(Some(ValueId(4))),
                    },
                ],
            );
            assert_eq!(
                structural_codes(&mut fx, f),
                Vec::<&str>::new(),
                "a self-loop that owns nothing must converge and stay clean"
            );
        }

        #[test]
        fn a_self_looping_block_that_consumes_a_field_is_still_reported() {
            let mut fx = fixture();
            let f = under_test(
                cond_params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(1)),
                    },
                    // The second iteration reaches this same move with the
                    // field already emptied by the first.
                    BasicBlock {
                        id: BlockId(1),
                        instructions: vec![
                            read(
                                2,
                                fx.file.clone(),
                                session_field(0),
                                OwnershipMode::Transfer,
                            ),
                            drop_of(2),
                        ],
                        terminator: Terminator::CondBranch {
                            condition: ValueId(1),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![drop_of(0), int(4, 0)],
                        terminator: Terminator::Return(Some(ValueId(4))),
                    },
                ],
            );
            assert!(
                structural_codes(&mut fx, f).contains(&codes::PLACE_USE_AFTER_MOVE),
                "the self-loop's own back edge must carry its consumption back to its head"
            );
        }

        /// bb1 loops through bb2 and back, so bb1 is its own indirect
        /// predecessor and neither block can be computed before the other.
        fn mutually_recursive_loop(fx: &Fixture, consume_in_the_loop: bool) -> Vec<BasicBlock> {
            let body = if consume_in_the_loop {
                vec![
                    read(
                        2,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(2),
                ]
            } else {
                Vec::new()
            };
            vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: body,
                    terminator: Terminator::CondBranch {
                        condition: ValueId(1),
                        then_block: BlockId(2),
                        else_block: BlockId(3),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![
                        read(
                            3,
                            fx.file.clone(),
                            session_field(1),
                            OwnershipMode::Transfer,
                        ),
                        drop_of(3),
                        drop_of(0),
                        int(4, 0),
                    ],
                    terminator: Terminator::Return(Some(ValueId(4))),
                },
            ]
        }

        #[test]
        fn mutually_recursive_loop_blocks_reach_a_fixed_point() {
            let mut fx = fixture();
            let blocks = mutually_recursive_loop(&fx, false);
            let f = under_test(cond_params(&fx), Ty::I64, blocks);
            assert_eq!(
                structural_codes(&mut fx, f),
                Vec::<&str>::new(),
                "a loop that consumes nothing must converge and stay clean"
            );
        }

        #[test]
        fn a_consumption_inside_a_mutually_recursive_loop_reaches_its_own_head() {
            let mut fx = fixture();
            let blocks = mutually_recursive_loop(&fx, true);
            let f = under_test(cond_params(&fx), Ty::I64, blocks);
            assert!(
                structural_codes(&mut fx, f).contains(&codes::PLACE_USE_AFTER_MOVE),
                "the move must be seen again on the iteration that re-enters through bb2"
            );
        }

        #[test]
        fn a_deep_reverse_ordered_chain_reaches_the_same_fixed_point() {
            let mut fx = fixture();
            let depth = 20u32;
            let mut forward: Vec<BasicBlock> = (0..depth)
                .map(|i| BasicBlock {
                    id: BlockId(i),
                    // The entry empties `input`; that fact then has to
                    // travel the whole chain to the exit below.
                    instructions: if i == 0 {
                        vec![
                            read(
                                2,
                                fx.file.clone(),
                                session_field(0),
                                OwnershipMode::Transfer,
                            ),
                            drop_of(2),
                        ]
                    } else {
                        Vec::new()
                    },
                    terminator: Terminator::Branch(BlockId(i + 1)),
                })
                .collect();
            forward.push(BasicBlock {
                id: BlockId(depth),
                // Twenty blocks later, `input` is moved a second time. Only
                // a fact that actually travelled the chain can catch it.
                instructions: vec![
                    read(
                        3,
                        fx.file.clone(),
                        session_field(0),
                        OwnershipMode::Transfer,
                    ),
                    drop_of(3),
                    drop_of(0),
                    int(4, 0),
                ],
                terminator: Terminator::Return(Some(ValueId(4))),
            });
            // Declared last-to-first, so every block in the chain is popped
            // before the predecessor it depends on.
            let mut reversed = forward.clone();
            reversed.reverse();
            let params = cond_params(&fx);
            let a = structural_codes(&mut fx, under_test(params.clone(), Ty::I64, forward));
            let b = structural_codes(&mut fx, under_test(params, Ty::I64, reversed));
            assert_eq!(
                a, b,
                "a chain explored entirely backwards must reach the same fixed point"
            );
            assert!(
                a.contains(&codes::PLACE_USE_AFTER_MOVE),
                "the move in the entry block must still be visible twenty blocks later, got {a:?}"
            );
        }

        #[test]
        fn a_diverging_arm_owes_nothing_at_the_other_arms_exit() {
            let mut fx = fixture();
            let f = under_test(
                cond_params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::CondBranch {
                            condition: ValueId(1),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    // This arm diverges: it is reachable, it is part of the
                    // fixed point, and it never reaches any exit at all, so
                    // it owes nothing and must impose nothing.
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![
                            read(
                                5,
                                fx.file.clone(),
                                session_field(0),
                                OwnershipMode::Transfer,
                            ),
                            drop_of(5),
                            read(
                                6,
                                fx.file.clone(),
                                session_field(1),
                                OwnershipMode::Transfer,
                            ),
                            drop_of(6),
                            drop_of(0),
                            int(7, 0),
                        ],
                        terminator: Terminator::Return(Some(ValueId(7))),
                    },
                ],
            );
            assert_eq!(
                structural_codes(&mut fx, f),
                Vec::<&str>::new(),
                "a diverging arm must not disturb the arm that actually reaches the exit"
            );
        }

        // -- determinism ---------------------------------------------------

        #[test]
        fn verifying_one_adversarial_module_twice_reports_byte_identical_diagnostics() {
            let mut fx = fixture();
            let blocks = mutually_recursive_loop(&fx, true);
            let params = cond_params(&fx);
            let first = rendered(&mut fx, under_test(params.clone(), Ty::I64, blocks.clone()));
            let second = rendered(&mut fx, under_test(params, Ty::I64, blocks));
            assert_eq!(
                first, second,
                "the same module must produce byte-identical diagnostics on every run"
            );
            assert!(
                !first.is_empty(),
                "the fixture must actually diagnose something"
            );
        }

        /// Every rotation of `blocks`, plus the full reversal: the entry
        /// block ends up first, last and everywhere between, and each block
        /// is popped both before and after the predecessors it depends on.
        ///
        /// Compares *every* diagnostic the verifier reports, rendered in
        /// emission order -- not just the structural family -- because the
        /// fixed points in this file share one discipline and a regression
        /// in any of them is a regression in all of them.
        fn assert_order_independent(fx: &mut Fixture, blocks: Vec<BasicBlock>, label: &str) {
            let params = cond_params(fx);
            let expected = rendered(fx, under_test(params.clone(), Ty::I64, blocks.clone()));
            for rotation in 1..blocks.len() {
                let mut rotated = blocks.clone();
                rotated.rotate_left(rotation);
                assert_eq!(
                    rendered(fx, under_test(params.clone(), Ty::I64, rotated)),
                    expected,
                    "{label}: rotating the block vector by {rotation} changed the diagnostics"
                );
            }
            let mut reversed = blocks;
            reversed.reverse();
            assert_eq!(
                rendered(fx, under_test(params, Ty::I64, reversed)),
                expected,
                "{label}: reversing the block vector changed the diagnostics"
            );
        }

        #[test]
        fn every_block_vector_permutation_reports_byte_identical_diagnostics() {
            let mut fx = fixture();
            // A loop whose body consumes a field used to poison itself
            // permanently when the block vector happened to list the loop
            // before the entry: the loop's own uncomputed head was read as
            // a *computed* empty state, and `merge_provenance`'s absorbing
            // `MaybeUninitialized` never recovers from that.
            let loops = mutually_recursive_loop(&fx, true);
            assert_order_independent(&mut fx, loops, "a mutually recursive loop that consumes");
            let clean_loop = mutually_recursive_loop(&fx, false);
            assert_order_independent(
                &mut fx,
                clean_loop,
                "a mutually recursive loop that does not",
            );
            let joined = field_empty_on_one_predecessor(&fx);
            assert_order_independent(&mut fx, joined, "a join whose predecessors disagree");
            for arms in 0..=2 {
                let shape = diamond(&fx, arms);
                assert_order_independent(&mut fx, shape, "a diamond");
            }
            for restore in [false, true] {
                let shape = loop_with_back_edge(&fx, restore);
                assert_order_independent(&mut fx, shape, "a loop with a back edge");
            }
        }
    }

    /// A `DecomposeVariant` is only meaningful where the active case is
    /// *proven*: taking a value apart into a case it might not hold
    /// moves ownership of storage that may not exist (`rfcs/0012`).
    ///
    /// The proof is a real CFG fixed point, so these cover it
    /// end-to-end through `verify_module`, never a private helper.
    #[cfg(test)]
    mod decomposition_refinement {
        use super::*;

        /// `f(take holder: Holder, cond: bool, take other: Holder)`.
        fn params(fx: &Fixture) -> Vec<Param> {
            vec![
                Param {
                    value: ValueId(0),
                    ty: fx.holder.clone(),
                    take: true,
                },
                Param {
                    value: ValueId(1),
                    ty: Ty::Bool,
                    take: false,
                },
                Param {
                    value: ValueId(2),
                    ty: fx.holder.clone(),
                    take: true,
                },
            ]
        }

        fn switch_on(value: u32, targets: Vec<BlockId>) -> Terminator {
            Terminator::Switch {
                scrutinee: ValueId(value),
                variant: HOLDER,
                cases: targets,
            }
        }

        fn payload(result: u32, base: u32, case: usize, fx: &Fixture) -> Instruction {
            Instruction::Value {
                result: ValueId(result),
                ty: fx.envelope.clone(),
                kind: ValueKind::VariantPayload {
                    base: ValueId(base),
                    variant: HOLDER,
                    case,
                    index: 0,
                },
            }
        }

        fn decompose(value: u32, case: usize, taken: Vec<(usize, u32)>) -> Instruction {
            Instruction::DecomposeVariant {
                value: ValueId(value),
                variant: HOLDER,
                case,
                taken: taken
                    .into_iter()
                    .map(|(index, owner)| (index, ValueId(owner)))
                    .collect(),
            }
        }

        /// `Full`: extract, claim and destroy the payload, then return.
        fn take_full(first: u32, result: u32, base: u32, fx: &Fixture) -> Vec<Instruction> {
            vec![
                payload(first, base, 0, fx),
                decompose(base, 0, vec![(0, first)]),
                drop_of(first),
                int(result, 0),
            ]
        }

        /// The second `take` parameter is destroyed wherever it is not
        /// the value under test, so no test is ever judged on a leak it
        /// did not mean to create.
        fn dispose_other() -> Instruction {
            drop_of(2)
        }

        #[test]
        fn a_decomposition_at_the_entry_block_is_rejected() {
            let mut fx = fixture();
            // Nothing whatsoever proved `%0` holds `Empty`. It might be
            // `Full`, whose payload this silently abandons.
            let f = under_test(
                params(&fx),
                Ty::I64,
                vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![decompose(0, 1, Vec::new()), dispose_other(), int(3, 0)],
                    terminator: Terminator::Return(Some(ValueId(3))),
                }],
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_OUTSIDE_REFINEMENT),
                "a decomposition with no proof of its own case must be rejected"
            );
        }

        #[test]
        fn a_decomposition_in_its_own_case_block_is_accepted() {
            let mut fx = fixture();
            let f = under_test(
                params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![dispose_other()],
                        terminator: switch_on(0, vec![BlockId(1), BlockId(2)]),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: take_full(4, 5, 0, &fx),
                        terminator: Terminator::Return(Some(ValueId(5))),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![decompose(0, 1, Vec::new()), int(6, 0)],
                        terminator: Terminator::Return(Some(ValueId(6))),
                    },
                ],
            );
            assert_eq!(
                all_codes(&mut fx, f),
                Vec::<&str>::new(),
                "each arm decomposes exactly the case its own switch edge proved"
            );
        }

        #[test]
        fn a_decomposition_after_several_ordinary_branches_is_accepted() {
            let mut fx = fixture();
            // The refinement has to survive two plain hops to reach the
            // block that uses it -- a single-hop rule cannot see it.
            let f = under_test(
                params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![dispose_other()],
                        terminator: switch_on(0, vec![BlockId(1), BlockId(2)]),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![decompose(0, 1, Vec::new()), int(6, 0)],
                        terminator: Terminator::Return(Some(ValueId(6))),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(4)),
                    },
                    BasicBlock {
                        id: BlockId(4),
                        instructions: take_full(4, 5, 0, &fx),
                        terminator: Terminator::Return(Some(ValueId(5))),
                    },
                ],
            );
            assert_eq!(
                all_codes(&mut fx, f),
                Vec::<&str>::new(),
                "a refinement must propagate through ordinary branches"
            );
        }

        #[test]
        fn a_decomposition_naming_the_sibling_case_is_rejected() {
            let mut fx = fixture();
            let f = under_test(
                params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![dispose_other()],
                        terminator: switch_on(0, vec![BlockId(1), BlockId(2)]),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: take_full(4, 5, 0, &fx),
                        terminator: Terminator::Return(Some(ValueId(5))),
                    },
                    // Reached only through the `Empty` edge, but takes
                    // the value apart as `Full`.
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![decompose(0, 0, Vec::new()), int(6, 0)],
                        terminator: Terminator::Return(Some(ValueId(6))),
                    },
                ],
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_OUTSIDE_REFINEMENT),
                "a sibling case's edge proves nothing about this case"
            );
        }

        #[test]
        fn a_join_of_two_different_cases_loses_the_refinement() {
            let mut fx = fixture();
            let f = under_test(
                params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![dispose_other()],
                        terminator: switch_on(0, vec![BlockId(1), BlockId(2)]),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(3)),
                    },
                    // Reachable through either case: neither is proven.
                    BasicBlock {
                        id: BlockId(3),
                        instructions: take_full(4, 5, 0, &fx),
                        terminator: Terminator::Return(Some(ValueId(5))),
                    },
                ],
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_OUTSIDE_REFINEMENT),
                "a block reachable through two different cases has proven neither"
            );
        }

        #[test]
        fn a_join_where_only_one_path_refines_loses_the_refinement() {
            let mut fx = fixture();
            let f = under_test(
                params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![dispose_other()],
                        terminator: Terminator::CondBranch {
                            condition: ValueId(1),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: switch_on(0, vec![BlockId(3), BlockId(4)]),
                    },
                    // Reaches the same block having tested nothing.
                    BasicBlock {
                        id: BlockId(2),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: take_full(4, 5, 0, &fx),
                        terminator: Terminator::Return(Some(ValueId(5))),
                    },
                    BasicBlock {
                        id: BlockId(4),
                        instructions: vec![decompose(0, 1, Vec::new()), int(6, 0)],
                        terminator: Terminator::Return(Some(ValueId(6))),
                    },
                ],
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_OUTSIDE_REFINEMENT),
                "one unrefined predecessor is enough to lose the guarantee"
            );
        }

        #[test]
        fn an_unreachable_switch_edge_contributes_no_refinement() {
            let mut fx = fixture();
            // bb9 is unreachable and names bb3 on its `Empty` edge.
            // Intersecting that in would wipe the guarantee bb1 really
            // proved; skipping it entirely is the only sound answer.
            let f = under_test(
                params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![dispose_other()],
                        terminator: switch_on(0, vec![BlockId(1), BlockId(2)]),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![decompose(0, 1, Vec::new()), int(6, 0)],
                        terminator: Terminator::Return(Some(ValueId(6))),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: take_full(4, 5, 0, &fx),
                        terminator: Terminator::Return(Some(ValueId(5))),
                    },
                    BasicBlock {
                        id: BlockId(9),
                        instructions: Vec::new(),
                        terminator: switch_on(0, vec![BlockId(9), BlockId(3)]),
                    },
                ],
            );
            assert!(
                !all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_OUTSIDE_REFINEMENT),
                "a dead switch edge may not erase a guarantee every live path proved"
            );
        }

        #[test]
        fn nested_switches_refine_their_own_scrutinees_independently() {
            let mut fx = fixture();
            let f = under_test(
                params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: switch_on(0, vec![BlockId(1), BlockId(2)]),
                    },
                    // Inside `%0 == Full`, test `%2` as well.
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: switch_on(2, vec![BlockId(3), BlockId(4)]),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![decompose(0, 1, Vec::new()), dispose_other(), int(6, 0)],
                        terminator: Terminator::Return(Some(ValueId(6))),
                    },
                    // Both refinements hold here, and each applies only
                    // to its own scrutinee.
                    BasicBlock {
                        id: BlockId(3),
                        instructions: {
                            let mut v = take_full(4, 5, 0, &fx);
                            v.pop();
                            v.extend(take_full(7, 8, 2, &fx));
                            v
                        },
                        terminator: Terminator::Return(Some(ValueId(8))),
                    },
                    BasicBlock {
                        id: BlockId(4),
                        instructions: {
                            let mut v = take_full(10, 11, 0, &fx);
                            v.pop();
                            v.push(decompose(2, 1, Vec::new()));
                            v.push(int(12, 0));
                            v
                        },
                        terminator: Terminator::Return(Some(ValueId(12))),
                    },
                ],
            );
            assert_eq!(
                all_codes(&mut fx, f),
                Vec::<&str>::new(),
                "two independent scrutinees each keep their own refinement"
            );
        }

        #[test]
        fn a_nested_switch_may_not_borrow_its_parents_refinement() {
            let mut fx = fixture();
            let f = under_test(
                params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: switch_on(0, vec![BlockId(1), BlockId(2)]),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: switch_on(2, vec![BlockId(3), BlockId(4)]),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![decompose(0, 1, Vec::new()), dispose_other(), int(6, 0)],
                        terminator: Terminator::Return(Some(ValueId(6))),
                    },
                    // `%2` was proven `Full` here; `%0` was too. Taking
                    // `%2` apart as `Empty` is still unproven.
                    BasicBlock {
                        id: BlockId(3),
                        instructions: {
                            let mut v = take_full(4, 5, 0, &fx);
                            v.pop();
                            v.push(decompose(2, 1, Vec::new()));
                            v.push(int(9, 0));
                            v
                        },
                        terminator: Terminator::Return(Some(ValueId(9))),
                    },
                    BasicBlock {
                        id: BlockId(4),
                        instructions: {
                            let mut v = take_full(10, 11, 0, &fx);
                            v.pop();
                            v.push(decompose(2, 1, Vec::new()));
                            v.push(int(12, 0));
                            v
                        },
                        terminator: Terminator::Return(Some(ValueId(12))),
                    },
                ],
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_OUTSIDE_REFINEMENT),
                "the inner scrutinee's own `Full` edge proves nothing about `Empty`"
            );
        }

        #[test]
        fn a_refinement_does_not_survive_a_store_to_its_own_scrutinee() {
            let mut fx = fixture();
            // `%4` is a fresh `Holder` written into the slot the
            // scrutinee was loaded from, so the switch's guarantee no
            // longer describes what a later load of it holds.
            let f = under_test(
                vec![Param {
                    value: ValueId(1),
                    ty: Ty::Bool,
                    take: false,
                }],
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![
                            Instruction::Value {
                                result: ValueId(0),
                                ty: fx.holder.clone(),
                                kind: ValueKind::Alloc,
                            },
                            Instruction::Value {
                                result: ValueId(3),
                                ty: fx.holder.clone(),
                                kind: ValueKind::VariantCreate {
                                    variant: HOLDER,
                                    case: 1,
                                    type_args: Vec::new(),
                                    payload: Vec::new(),
                                },
                            },
                            Instruction::Store {
                                slot: ValueId(0),
                                value: ValueId(3),
                                mode: OwnershipMode::Transfer,
                            },
                            Instruction::Value {
                                result: ValueId(5),
                                ty: fx.holder.clone(),
                                kind: ValueKind::Load(ValueId(0)),
                            },
                        ],
                        terminator: switch_on(5, vec![BlockId(1), BlockId(2)]),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: vec![
                            Instruction::Value {
                                result: ValueId(6),
                                ty: fx.holder.clone(),
                                kind: ValueKind::VariantCreate {
                                    variant: HOLDER,
                                    case: 1,
                                    type_args: Vec::new(),
                                    payload: Vec::new(),
                                },
                            },
                            Instruction::Store {
                                slot: ValueId(0),
                                value: ValueId(6),
                                mode: OwnershipMode::Transfer,
                            },
                            Instruction::Value {
                                result: ValueId(7),
                                ty: fx.holder.clone(),
                                kind: ValueKind::Load(ValueId(0)),
                            },
                            decompose(7, 1, Vec::new()),
                            int(8, 0),
                        ],
                        terminator: Terminator::Return(Some(ValueId(8))),
                    },
                ],
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_OUTSIDE_REFINEMENT),
                "writing the scrutinee's own storage invalidates what the switch proved"
            );
        }

        #[test]
        fn an_invoke_edge_fabricates_no_refinement() {
            let mut fx = fixture();
            let builder = builder(&mut fx);
            let _ = builder;
            let f = under_test(
                params(&fx),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![dispose_other()],
                        terminator: Terminator::Branch(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: vec![decompose(0, 0, Vec::new()), int(6, 0)],
                        terminator: Terminator::Return(Some(ValueId(6))),
                    },
                ],
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_OUTSIDE_REFINEMENT),
                "an ordinary edge proves no case at all"
            );
        }

        #[test]
        fn reversing_the_block_vector_reports_the_identical_diagnostics() {
            let mut fx = fixture();
            let blocks = vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![dispose_other()],
                    terminator: switch_on(0, vec![BlockId(1), BlockId(2)]),
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: take_full(4, 5, 0, &fx),
                    terminator: Terminator::Return(Some(ValueId(5))),
                },
            ];
            let ps = params(&fx);
            let forward = all_codes(&mut fx, under_test(ps.clone(), Ty::I64, blocks.clone()));
            for rotation in 1..blocks.len() {
                let mut rotated = blocks.clone();
                rotated.rotate_left(rotation);
                assert_eq!(
                    all_codes(&mut fx, under_test(ps.clone(), Ty::I64, rotated)),
                    forward,
                    "rotating the block vector by {rotation} changed the diagnostics"
                );
            }
            let mut reversed = blocks;
            reversed.reverse();
            assert_eq!(
                all_codes(&mut fx, under_test(ps, Ty::I64, reversed)),
                forward,
                "reversing the block vector changed the diagnostics"
            );
            assert!(
                !forward.is_empty(),
                "the fixture must actually diagnose something"
            );
        }
    }

    /// A decomposition transfers ownership of *specific storage*, so
    /// each claimed owner must be the very value that extraction
    /// produced -- having the right declared type proves nothing
    /// (`rfcs/0012`).
    ///
    /// And a `ValueKind::VariantPayload` is only a read: ownership of a
    /// payload begins when a decomposition claims that exact extraction,
    /// never merely because it was read.
    #[cfg(test)]
    mod payload_binding {
        use super::*;

        fn params(fx: &Fixture) -> Vec<Param> {
            vec![Param {
                value: ValueId(0),
                ty: fx.holder.clone(),
                take: true,
            }]
        }

        fn payload(result: u32, base: u32, case: usize, index: usize, fx: &Fixture) -> Instruction {
            Instruction::Value {
                result: ValueId(result),
                ty: fx.envelope.clone(),
                kind: ValueKind::VariantPayload {
                    base: ValueId(base),
                    variant: HOLDER,
                    case,
                    index,
                },
            }
        }

        fn decompose(value: u32, case: usize, taken: Vec<(usize, u32)>) -> Instruction {
            Instruction::DecomposeVariant {
                value: ValueId(value),
                variant: HOLDER,
                case,
                taken: taken
                    .into_iter()
                    .map(|(index, owner)| (index, ValueId(owner)))
                    .collect(),
            }
        }

        /// `switch %0 { bb1 => full, bb2 => empty }`, where `full` is
        /// whatever the test wants to try in the `Full` case block.
        fn under_switch(full: Vec<Instruction>, result: u32) -> Vec<BasicBlock> {
            vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Switch {
                        scrutinee: ValueId(0),
                        variant: HOLDER,
                        cases: vec![BlockId(1), BlockId(2)],
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: full,
                    terminator: Terminator::Return(Some(ValueId(result))),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![decompose(0, 1, Vec::new()), int(20, 0)],
                    terminator: Terminator::Return(Some(ValueId(20))),
                },
            ]
        }

        #[test]
        fn an_unrelated_value_of_the_right_type_may_not_be_claimed() {
            let mut fx = fixture();
            // `%3` is a brand new `Envelope`, not the shell's payload.
            // Claiming it would leave the real payload owned by nothing
            // and hand this frame a second obligation it never received.
            let f = under_test(
                params(&fx),
                Ty::I64,
                under_switch(
                    vec![
                        payload(2, 0, 0, 0, &fx),
                        Instruction::Value {
                            result: ValueId(4),
                            ty: fx.file.clone(),
                            kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(9)]),
                        },
                        Instruction::Value {
                            result: ValueId(3),
                            ty: fx.envelope.clone(),
                            kind: ValueKind::RecordCreate(ENVELOPE, Vec::new(), vec![ValueId(4)]),
                        },
                        decompose(0, 0, vec![(0, 3)]),
                        drop_of(3),
                        int(5, 0),
                    ],
                    5,
                ),
            );
            let mut blocks = f.blocks.clone();
            blocks[0].instructions.push(int(9, 0));
            let f = under_test(params(&fx), Ty::I64, blocks);
            assert!(
                all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_CLAIM_MISMATCH),
                "a same-typed value that is not the extraction must be rejected"
            );
        }

        #[test]
        fn the_exact_extraction_is_accepted() {
            let mut fx = fixture();
            let f = under_test(
                params(&fx),
                Ty::I64,
                under_switch(
                    vec![
                        payload(2, 0, 0, 0, &fx),
                        decompose(0, 0, vec![(0, 2)]),
                        drop_of(2),
                        int(5, 0),
                    ],
                    5,
                ),
            );
            assert_eq!(
                all_codes(&mut fx, f),
                Vec::<&str>::new(),
                "claiming the extraction this decomposition's own base produced is the whole point"
            );
        }

        #[test]
        fn an_extraction_from_another_base_may_not_be_claimed() {
            let mut fx = fixture();
            let mut blocks = under_switch(
                vec![
                    payload(2, 6, 0, 0, &fx),
                    decompose(0, 0, vec![(0, 2)]),
                    drop_of(2),
                    int(5, 0),
                ],
                5,
            );
            // A second, independent `Holder`, extracted from in the same
            // block but belonging to nothing this decomposition names.
            blocks[0].instructions.push(Instruction::Value {
                result: ValueId(6),
                ty: fx.holder.clone(),
                kind: ValueKind::VariantCreate {
                    variant: HOLDER,
                    case: 1,
                    type_args: Vec::new(),
                    payload: Vec::new(),
                },
            });
            let f = under_test(params(&fx), Ty::I64, blocks);
            assert!(
                all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_CLAIM_MISMATCH),
                "an extraction out of a different value is not this shell's payload"
            );
        }

        #[test]
        fn an_extraction_of_another_position_may_not_be_claimed() {
            let mut fx = fixture();
            // `Full` declares one payload position, so index 1 does not
            // exist -- but the claim names position 0 with a value read
            // from position 1.
            let f = under_test(
                params(&fx),
                Ty::I64,
                under_switch(
                    vec![
                        payload(2, 0, 0, 1, &fx),
                        decompose(0, 0, vec![(0, 2)]),
                        drop_of(2),
                        int(5, 0),
                    ],
                    5,
                ),
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_CLAIM_MISMATCH),
                "the claimed position must be the position the extraction read"
            );
        }

        #[test]
        fn an_extraction_of_another_case_may_not_be_claimed() {
            let mut fx = fixture();
            let f = under_test(
                params(&fx),
                Ty::I64,
                under_switch(
                    vec![
                        payload(2, 0, 1, 0, &fx),
                        decompose(0, 0, vec![(0, 2)]),
                        drop_of(2),
                        int(5, 0),
                    ],
                    5,
                ),
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::DECOMPOSITION_CLAIM_MISMATCH),
                "the claimed case must be the case the extraction read"
            );
        }

        #[test]
        fn one_extraction_may_not_be_claimed_by_two_decompositions_on_one_path() {
            let mut fx = fixture();
            let f = under_test(
                params(&fx),
                Ty::I64,
                under_switch(
                    vec![
                        payload(2, 0, 0, 0, &fx),
                        decompose(0, 0, vec![(0, 2)]),
                        decompose(0, 0, vec![(0, 2)]),
                        drop_of(2),
                        int(5, 0),
                    ],
                    5,
                ),
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::DUPLICATE_STRUCTURAL_CLEANUP),
                "the shell is already emptied, so a second decomposition of it has nothing to take"
            );
        }

        #[test]
        fn an_extraction_destroyed_without_any_decomposition_is_rejected() {
            let mut fx = fixture();
            // Reading a payload position is a read. Destroying what it
            // read, then destroying the shell that still owns it, is a
            // double destruction of the same storage.
            let f = under_test(
                params(&fx),
                Ty::I64,
                under_switch(
                    vec![payload(2, 0, 0, 0, &fx), drop_of(2), drop_of(0), int(5, 0)],
                    5,
                ),
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::UNCLAIMED_PAYLOAD_OWNERSHIP),
                "a payload read confers no ownership at all"
            );
        }

        #[test]
        fn an_extraction_transferred_without_any_decomposition_is_rejected() {
            let mut fx = fixture();
            let mut blocks = under_switch(vec![payload(2, 0, 0, 0, &fx), drop_of(0)], 2);
            blocks[1].terminator = Terminator::Return(Some(ValueId(2)));
            let f = under_test(params(&fx), fx.envelope.clone(), blocks);
            let codes = all_codes(&mut fx, f);
            assert!(
                codes.contains(&codes::UNCLAIMED_PAYLOAD_OWNERSHIP)
                    || codes.contains(&codes::MISSING_STRUCTURAL_CLEANUP),
                "returning an unclaimed extraction transfers storage this frame never owned, \
                 got {codes:?}"
            );
        }

        #[test]
        fn a_claimed_payload_may_be_returned_instead_of_destroyed() {
            let mut fx = fixture();
            let mut blocks = under_switch(
                vec![payload(2, 0, 0, 0, &fx), decompose(0, 0, vec![(0, 2)])],
                2,
            );
            blocks[1].terminator = Terminator::Return(Some(ValueId(2)));
            blocks[2].instructions = vec![
                decompose(0, 1, Vec::new()),
                Instruction::Value {
                    result: ValueId(7),
                    ty: fx.file.clone(),
                    kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(8)]),
                },
                Instruction::Value {
                    result: ValueId(20),
                    ty: fx.envelope.clone(),
                    kind: ValueKind::RecordCreate(ENVELOPE, Vec::new(), vec![ValueId(7)]),
                },
            ];
            blocks[0].instructions.push(int(8, 0));
            let f = under_test(params(&fx), fx.envelope.clone(), blocks);
            assert_eq!(
                all_codes(&mut fx, f),
                Vec::<&str>::new(),
                "an arm that returns its claimed payload transfers it instead of destroying it"
            );
        }

        #[test]
        fn a_wildcard_payload_is_claimed_and_destroyed_in_the_same_block() {
            let mut fx = fixture();
            let f = under_test(
                params(&fx),
                Ty::I64,
                under_switch(
                    vec![
                        payload(2, 0, 0, 0, &fx),
                        decompose(0, 0, vec![(0, 2)]),
                        drop_of(2),
                        int(5, 0),
                    ],
                    5,
                ),
            );
            assert_eq!(
                all_codes(&mut fx, f),
                Vec::<&str>::new(),
                "a discarded payload is claimed and destroyed the instant the arm commits"
            );
        }

        #[test]
        fn the_shell_may_not_be_dropped_after_it_was_decomposed() {
            let mut fx = fixture();
            let f = under_test(
                params(&fx),
                Ty::I64,
                under_switch(
                    vec![
                        payload(2, 0, 0, 0, &fx),
                        decompose(0, 0, vec![(0, 2)]),
                        drop_of(2),
                        drop_of(0),
                        int(5, 0),
                    ],
                    5,
                ),
            );
            assert!(
                all_codes(&mut fx, f).contains(&codes::DUPLICATE_STRUCTURAL_CLEANUP),
                "the shell was emptied by the decomposition and owns nothing to destroy"
            );
        }

        #[test]
        fn two_arms_of_one_case_may_each_claim_the_shared_extraction() {
            let mut fx = fixture();
            // One extraction is genuinely shared by every arm reachable
            // through a case; each arm commits on its own disjoint path,
            // so both claims are correct and neither may be rejected.
            let f = under_test(
                vec![
                    Param {
                        value: ValueId(0),
                        ty: fx.holder.clone(),
                        take: true,
                    },
                    Param {
                        value: ValueId(1),
                        ty: Ty::Bool,
                        take: false,
                    },
                ],
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Switch {
                            scrutinee: ValueId(0),
                            variant: HOLDER,
                            cases: vec![BlockId(1), BlockId(2)],
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: vec![payload(2, 0, 0, 0, &fx)],
                        terminator: Terminator::CondBranch {
                            condition: ValueId(1),
                            then_block: BlockId(3),
                            else_block: BlockId(4),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![decompose(0, 1, Vec::new()), int(20, 0)],
                        terminator: Terminator::Return(Some(ValueId(20))),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: vec![decompose(0, 0, vec![(0, 2)]), drop_of(2), int(5, 1)],
                        terminator: Terminator::Return(Some(ValueId(5))),
                    },
                    BasicBlock {
                        id: BlockId(4),
                        instructions: vec![decompose(0, 0, vec![(0, 2)]), drop_of(2), int(6, 2)],
                        terminator: Terminator::Return(Some(ValueId(6))),
                    },
                ],
            );
            assert_eq!(
                all_codes(&mut fx, f),
                Vec::<&str>::new(),
                "two disjoint arms under one case each legitimately claim the shared extraction"
            );
        }
    }

    /// Whether an exit owes cleanup for a value is a question about the
    /// *paths reaching it*, not about dominance (`rfcs/0012`).
    ///
    /// Dominance asks "does every path to this exit pass through the
    /// creation?". The obligation asks "does *any* path to this exit
    /// pass through it and still hold the value?". A branch-local
    /// aggregate reaching a shared exit answers no to the first and yes
    /// to the second, and was silently exempted.
    #[cfg(test)]
    mod ownership_presence {
        use super::*;

        fn cond_param() -> Vec<Param> {
            vec![Param {
                value: ValueId(0),
                ty: Ty::Bool,
                take: false,
            }]
        }

        /// `%file = File { n }` then `%box = Box[File](%file)`.
        fn build_box(file: u32, boxed: u32, n: u32, fx: &Fixture) -> Vec<Instruction> {
            vec![
                int(n, 1),
                Instruction::Value {
                    result: ValueId(file),
                    ty: fx.file.clone(),
                    kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(n)]),
                },
                Instruction::Value {
                    result: ValueId(boxed),
                    ty: fx.box_file.clone(),
                    kind: ValueKind::RecordCreate(BOXY, vec![fx.file.clone()], vec![ValueId(file)]),
                },
            ]
        }

        /// bb0 branches to bb1 (which builds a `Box[File]`) and bb2
        /// (which does not); both meet at bb3, which returns.
        fn diamond_creating_on_one_arm(fx: &Fixture, destroy: bool) -> Vec<BasicBlock> {
            let mut arm = build_box(1, 2, 3, fx);
            if destroy {
                arm.push(drop_of(2));
            }
            vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::CondBranch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: arm,
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![int(4, 0)],
                    terminator: Terminator::Return(Some(ValueId(4))),
                },
            ]
        }

        #[test]
        fn a_branch_local_aggregate_leaked_at_a_shared_exit_is_reported() {
            let mut fx = fixture();
            // bb1 does not dominate bb3, but the path bb1 -> bb3 leaks
            // the `Box[File]` it built.
            let blocks = diamond_creating_on_one_arm(&fx, false);
            let f = under_test(cond_param(), Ty::I64, blocks);
            assert!(
                structural_codes(&mut fx, f).contains(&codes::MISSING_STRUCTURAL_CLEANUP),
                "a value created on one arm and still live at the shared exit is leaked"
            );
        }

        #[test]
        fn a_branch_local_aggregate_cleaned_before_the_merge_is_accepted() {
            let mut fx = fixture();
            let blocks = diamond_creating_on_one_arm(&fx, true);
            let f = under_test(cond_param(), Ty::I64, blocks);
            assert_eq!(
                structural_codes(&mut fx, f),
                Vec::<&str>::new(),
                "destroying it on the only arm that created it discharges the obligation"
            );
        }

        #[test]
        fn the_bypassing_arm_alone_is_never_diagnosed() {
            let mut fx = fixture();
            // bb2 creates nothing, and returns on its own. Nothing may
            // be demanded of it for a value it never received.
            let mut blocks = diamond_creating_on_one_arm(&fx, true);
            blocks[2].instructions = vec![int(5, 0)];
            blocks[2].terminator = Terminator::Return(Some(ValueId(5)));
            let f = under_test(cond_param(), Ty::I64, blocks);
            assert_eq!(
                structural_codes(&mut fx, f),
                Vec::<&str>::new(),
                "an exit on a path that never created the value owes nothing"
            );
        }

        #[test]
        fn both_arms_creating_their_own_value_must_each_clean_it() {
            let mut fx = fixture();
            let mut first = build_box(1, 2, 3, &fx);
            first.push(drop_of(2));
            // The second arm builds its own and abandons it.
            let second = build_box(5, 6, 7, &fx);
            let f = under_test(
                cond_param(),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::CondBranch {
                            condition: ValueId(0),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: first,
                        terminator: Terminator::Branch(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: second,
                        terminator: Terminator::Branch(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: vec![int(4, 0)],
                        terminator: Terminator::Return(Some(ValueId(4))),
                    },
                ],
            );
            let codes = structural_codes(&mut fx, f);
            assert!(
                codes.contains(&codes::MISSING_STRUCTURAL_CLEANUP),
                "the arm that abandoned its own value must be reported, got {codes:?}"
            );
        }

        #[test]
        fn both_arms_cleaning_their_own_value_are_accepted() {
            let mut fx = fixture();
            let mut first = build_box(1, 2, 3, &fx);
            first.push(drop_of(2));
            let mut second = build_box(5, 6, 7, &fx);
            second.push(drop_of(6));
            let f = under_test(
                cond_param(),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::CondBranch {
                            condition: ValueId(0),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: first,
                        terminator: Terminator::Branch(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: second,
                        terminator: Terminator::Branch(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: vec![int(4, 0)],
                        terminator: Terminator::Return(Some(ValueId(4))),
                    },
                ],
            );
            assert_eq!(
                structural_codes(&mut fx, f),
                Vec::<&str>::new(),
                "each arm discharges its own obligation on its own path"
            );
        }

        #[test]
        fn an_arm_that_diverges_imposes_nothing_on_the_other() {
            let mut fx = fixture();
            let mut blocks = diamond_creating_on_one_arm(&fx, true);
            // The creating arm never reaches the exit at all.
            blocks[1].instructions = build_box(1, 2, 3, &fx);
            blocks[1].terminator = Terminator::Branch(BlockId(1));
            let f = under_test(cond_param(), Ty::I64, blocks);
            let codes = structural_codes(&mut fx, f);
            assert_eq!(
                codes,
                Vec::<&str>::new(),
                "a diverging arm reaches no exit, so it owes nothing there, got {codes:?}"
            );
        }

        #[test]
        fn a_loop_creating_and_cleaning_each_iteration_is_accepted() {
            let mut fx = fixture();
            let mut body = build_box(1, 2, 3, &fx);
            body.push(drop_of(2));
            let f = under_test(
                cond_param(),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: body,
                        terminator: Terminator::CondBranch {
                            condition: ValueId(0),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![int(4, 0)],
                        terminator: Terminator::Return(Some(ValueId(4))),
                    },
                ],
            );
            assert_eq!(
                structural_codes(&mut fx, f),
                Vec::<&str>::new(),
                "a loop that destroys what it built each iteration owes nothing at the exit"
            );
        }

        #[test]
        fn a_loop_leaking_on_its_exit_path_is_reported() {
            let mut fx = fixture();
            let body = build_box(1, 2, 3, &fx);
            let f = under_test(
                cond_param(),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: body,
                        terminator: Terminator::CondBranch {
                            condition: ValueId(0),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![int(4, 0)],
                        terminator: Terminator::Return(Some(ValueId(4))),
                    },
                ],
            );
            assert!(
                structural_codes(&mut fx, f).contains(&codes::MISSING_STRUCTURAL_CLEANUP),
                "a loop body that never destroys what it built leaks on the way out"
            );
        }

        #[test]
        fn a_nested_branch_creating_deep_inside_still_owes_at_the_outer_exit() {
            let mut fx = fixture();
            let f = under_test(
                cond_param(),
                Ty::I64,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::CondBranch {
                            condition: ValueId(0),
                            then_block: BlockId(1),
                            else_block: BlockId(4),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: Terminator::CondBranch {
                            condition: ValueId(0),
                            then_block: BlockId(2),
                            else_block: BlockId(3),
                        },
                    },
                    // Two levels in, and still reaching the one exit.
                    BasicBlock {
                        id: BlockId(2),
                        instructions: build_box(1, 2, 3, &fx),
                        terminator: Terminator::Branch(BlockId(5)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(5)),
                    },
                    BasicBlock {
                        id: BlockId(4),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch(BlockId(5)),
                    },
                    BasicBlock {
                        id: BlockId(5),
                        instructions: vec![int(4, 0)],
                        terminator: Terminator::Return(Some(ValueId(4))),
                    },
                ],
            );
            assert!(
                structural_codes(&mut fx, f).contains(&codes::MISSING_STRUCTURAL_CLEANUP),
                "depth of nesting changes nothing about which paths reach the exit"
            );
        }

        #[test]
        fn every_block_and_predecessor_order_reports_the_identical_diagnostics() {
            let mut fx = fixture();
            let blocks = diamond_creating_on_one_arm(&fx, false);
            let expected = rendered(&mut fx, under_test(cond_param(), Ty::I64, blocks.clone()));
            for rotation in 1..blocks.len() {
                let mut rotated = blocks.clone();
                rotated.rotate_left(rotation);
                assert_eq!(
                    rendered(&mut fx, under_test(cond_param(), Ty::I64, rotated)),
                    expected,
                    "rotating the block vector by {rotation} changed the diagnostics"
                );
            }
            let mut reversed = blocks.clone();
            reversed.reverse();
            assert_eq!(
                rendered(&mut fx, under_test(cond_param(), Ty::I64, reversed)),
                expected,
                "reversing the block vector changed the diagnostics"
            );
            // The same diamond with its two arms swapped: the join's
            // predecessors are discovered in the other order.
            let mut swapped = blocks;
            swapped[0].terminator = Terminator::CondBranch {
                condition: ValueId(0),
                then_block: BlockId(2),
                else_block: BlockId(1),
            };
            assert_eq!(
                rendered(&mut fx, under_test(cond_param(), Ty::I64, swapped)),
                expected,
                "reversing predecessor discovery order changed the diagnostics"
            );
            assert!(
                !expected.is_empty(),
                "the fixture must actually diagnose something"
            );
        }
    }
}
