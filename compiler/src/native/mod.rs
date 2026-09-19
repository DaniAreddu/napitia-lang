//! The native ahead-of-time backend (`rfcs/0014`): a deterministic
//! Cranelift path from already-verified NIR to an
//! `x86_64-unknown-linux-gnu` executable.
//!
//! This is a *preview*, and the shape of that preview is the whole
//! design. Napitia's full semantics live in the interpreter, and this
//! milestone does not move any of them: resources, observations,
//! `defer`, typed failure, records, variants, strings, generics and
//! capability protocols are all still executed exactly as before by
//! `napitia run`, and none of them is lowered here -- not
//! approximately, not erased, and never by quietly handing the program
//! back to the interpreter. The backend compiles one small, honestly
//! described subset and refuses everything else with a diagnostic that
//! names what it refused.
//!
//! The pipeline `napitia build` runs is:
//!
//! ```text
//! source -> .. -> nir -> nir::verify -> native::capability -> native::lower -> system linker
//! ```
//!
//! Two of those stages are load-bearing in a way worth stating
//! explicitly:
//!
//! * [`crate::nir::verify_module`] is mandatory and runs first. Code
//!   generation never sees NIR the verifier has not accepted, so
//!   nothing here re-derives structural invariants the verifier already
//!   owns -- and where this module does notice such a violation anyway
//!   (it is a public API, and a caller can hand it anything), it refuses
//!   with [`codes::UNVERIFIED_NIR`] rather than guessing.
//! * [`capability`] runs after verification and before Cranelift ever
//!   sees a function. It decides, exhaustively, whether the whole
//!   reachable program is inside the supported subset. Everything after
//!   it may therefore assume that subset, which is why [`lower`] has no
//!   "unsupported, give up" path buried inside code generation.
//!
//! # Diagnostic layers
//!
//! Malformed NIR is the verifier's business (`V...` codes). *Valid* NIR
//! this backend cannot compile is this module's business (`A...`
//! codes). The two are never mixed: a program that uses a resource is
//! not malformed, and a program with a dangling block target is not
//! merely unsupported.

use crate::types::Ty;

/// The one target triple `napitia build` produces, and the only one
/// [`capability::validate`] accepts. Alpha 0.2.0 adds a single target
/// on purpose: a second one would need its own ABI decisions, its own
/// linker contract and its own end-to-end test matrix, none of which
/// this milestone has.
pub const TARGET_TRIPLE: &str = "x86_64-unknown-linux-gnu";

/// The symbol the generated object exports for the system C runtime to
/// call. Napitia's own `main` is *not* emitted under this name -- every
/// Napitia function gets an internal, mangled symbol, and this is a
/// small wrapper the backend synthesizes around it. Only this name is a
/// documented interface; the mangled ones are not.
pub const ENTRY_SYMBOL: &str = "main";

/// Stable diagnostic codes for the native backend.
///
/// `A0001`-`A0019` are the capability layer: reasons this backend will
/// not compile a program that is otherwise perfectly valid Napitia.
/// `A0020`-`A0024` are the backend layer: something went wrong while
/// actually producing the executable.
///
/// The `A` prefix is a new namespace, allocated the same way `V`
/// (verifier) and `U` (ownership) each got one when those layers
/// appeared. No existing code is renumbered.
pub mod codes {
    /// A target triple other than [`super::TARGET_TRIPLE`].
    pub const UNSUPPORTED_TARGET: &str = "A0001";
    /// The module declares no function named `main`.
    pub const MISSING_ENTRY: &str = "A0002";
    /// The module declares more than one function named `main`.
    pub const DUPLICATE_ENTRY: &str = "A0003";
    /// `main` declares parameters. The native entry point is invoked by
    /// the C runtime with no Napitia arguments at all.
    pub const ENTRY_PARAMETERS: &str = "A0004";
    /// `main` returns something other than `unit` or `i64`.
    pub const ENTRY_RETURN_TYPE: &str = "A0005";
    /// A type outside `{i64, bool, unit}` appears in a reachable
    /// signature, slot, constant or result -- including nested inside a
    /// generic application.
    pub const UNSUPPORTED_TYPE: &str = "A0006";
    /// A reachable instruction the native subset does not include:
    /// anything to do with resources, observations, `defer`, records or
    /// variants.
    pub const UNSUPPORTED_INSTRUCTION: &str = "A0007";
    /// A reachable terminator the native subset does not include:
    /// `switch`, `invoke` or `raise`.
    pub const UNSUPPORTED_TERMINATOR: &str = "A0008";
    /// A reachable operator whose *exceptional* behavior this backend
    /// cannot reproduce without a runtime facility Alpha 0.2.0 does not
    /// have -- [`capability`] documents exactly which operators those
    /// are, and why each one is on that list.
    pub const UNSUPPORTED_OPERATOR: &str = "A0009";
    /// A reachable function declares type parameters, or a reachable
    /// call supplies type arguments. There is no monomorphization here.
    pub const GENERIC_CODE: &str = "A0010";
    /// A reachable function declares a `uses` requirement, or a
    /// reachable call dispatches through capability evidence. This is
    /// NIR's only non-direct call form, and it is not lowered.
    pub const CAPABILITY_DISPATCH: &str = "A0011";
    /// A reachable function declares `raises`. There is no native
    /// typed-failure runtime.
    pub const FALLIBLE_FUNCTION: &str = "A0012";
    /// A reachable call names a function this module does not define.
    /// There is no FFI: every callee must be a Napitia function
    /// compiled alongside its caller.
    pub const UNKNOWN_CALLEE: &str = "A0013";
    /// A reachable direct call disagrees with its callee's own
    /// signature on argument count, argument type or result type.
    pub const CALL_SIGNATURE_MISMATCH: &str = "A0014";
    /// The reachable direct-call graph contains a cycle -- self
    /// recursion or mutual recursion.
    pub const RECURSIVE_CALL_GRAPH: &str = "A0015";
    /// The build spans more than one module: the source declared an
    /// `import`, or the NIR carries items declared in another file.
    pub const MULTI_MODULE_BUILD: &str = "A0016";
    /// A reachable `load` is not preceded by a `store` to that slot on
    /// every path that reaches it.
    pub const UNINITIALIZED_SLOT_LOAD: &str = "A0017";
    /// An `alloc` result is used somewhere other than as the slot of a
    /// `store` or the operand of a `load`.
    pub const SLOT_USED_AS_VALUE: &str = "A0018";
    /// Structure [`crate::nir::verify_module`] would already have
    /// rejected reached this backend: a dangling block target, an
    /// undefined value, a duplicate id, a type inconsistency. Reported
    /// instead of guessed at, and never produced for NIR that actually
    /// went through the verifier.
    pub const UNVERIFIED_NIR: &str = "A0019";

    /// Cranelift rejected, or failed to emit, something this backend
    /// built. A defect in this backend rather than in the program, and
    /// reported as a diagnostic rather than a panic.
    pub const CODEGEN_FAILED: &str = "A0020";
    /// The host cannot link an executable for [`super::TARGET_TRIPLE`].
    pub const UNSUPPORTED_HOST: &str = "A0021";
    /// The system linker could not be launched at all.
    pub const LINKER_LAUNCH_FAILED: &str = "A0022";
    /// The system linker ran and reported failure.
    pub const LINKER_FAILED: &str = "A0023";
    /// The build could not create its scratch directory, write the
    /// object, or move the finished executable into place.
    pub const BUILD_IO_FAILED: &str = "A0024";
}

/// Every Napitia type the native subset can represent, and nothing
/// else.
///
/// The mapping to machine representation is recorded here, once, rather
/// than rediscovered at each use:
///
/// * [`Scalar::Int`] (`i64`) is represented by Cranelift's `I128`. That
///   is not an oversight and not future-proofing. The interpreter holds
///   every Napitia integer in an `i128` and performs *128-bit* wrapping
///   arithmetic on it (`Value::Int(i128)`, `i128::wrapping_add` and
///   friends), so 64-bit machine arithmetic would disagree with the
///   reference implementation for every operation whose mathematical
///   result leaves `i64`'s range. Matching the interpreter exactly, over
///   the whole input domain, is worth two registers. `rfcs/0014` records
///   this as the limitation it is: Napitia's declared `i64` width and
///   its interpreter's actual integer width are not yet the same thing,
///   and reconciling them (`spec/0005` wants overflow to be a panic) is
///   a language decision, not a backend one.
/// * [`Scalar::Bool`] is represented by `I8`, always normalized to `0`
///   or `1` -- never "whatever nonzero value a comparison happened to
///   leave behind".
/// * [`Scalar::Unit`] is represented by *nothing*. It has exactly one
///   inhabitant, so it needs no bits, no register and no stack slot; a
///   `unit` parameter or result simply does not appear in a native
///   signature. It is never given a fabricated runtime value.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Scalar {
    Int,
    Bool,
    Unit,
}

impl Scalar {
    /// This scalar's Napitia spelling, for diagnostics.
    pub fn as_str(self) -> &'static str {
        match self {
            Scalar::Int => "i64",
            Scalar::Bool => "bool",
            Scalar::Unit => "unit",
        }
    }
}

/// Classifies `ty` as a natively representable scalar, or `None` when
/// the native subset has no representation for it.
///
/// Exhaustive by construction: every [`Ty`] variant is named, so a type
/// added to the language later cannot be silently classified as
/// supported through a wildcard arm.
pub fn scalar_of(ty: &Ty) -> Option<Scalar> {
    match ty {
        Ty::I64 => Some(Scalar::Int),
        Ty::Bool => Some(Scalar::Bool),
        Ty::Unit => Some(Scalar::Unit),
        // Other integer widths are genuinely absent, not merely
        // untested: the interpreter gives every integer the same `i128`
        // representation and never narrows to a declared width, so an
        // `i32` would need semantics this milestone has not decided.
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::Isize
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::Usize
        | Ty::F32
        | Ty::F64
        | Ty::Char
        | Ty::Str
        // A type no value ever has; a slot, parameter or result
        // declared with it is not storage to lay out.
        | Ty::Never
        // A record, variant or resource declaration: aggregates are not
        // laid out natively at all.
        | Ty::Named(_, _)
        // A still-generic parameter, or a generic instantiation. Either
        // way there is no monomorphization here to make it concrete.
        | Ty::Param(_, _)
        | Ty::Applied(_, _)
        // Only ever produced alongside a diagnostic that was already
        // reported; compilation never reaches this backend carrying one.
        | Ty::Error
        // Unification never left one of these behind in a module that
        // passed type-checking.
        | Ty::Var(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::ItemId;
    use crate::symbol::Interner;
    use crate::types::TyVar;

    #[test]
    fn the_three_supported_scalars_are_exactly_i64_bool_and_unit() {
        assert_eq!(scalar_of(&Ty::I64), Some(Scalar::Int));
        assert_eq!(scalar_of(&Ty::Bool), Some(Scalar::Bool));
        assert_eq!(scalar_of(&Ty::Unit), Some(Scalar::Unit));
    }

    #[test]
    fn every_other_type_is_rejected_including_nested_generic_applications() {
        let mut interner = Interner::new();
        let name = interner.intern("Box");
        for ty in [
            Ty::I8,
            Ty::I16,
            Ty::I32,
            Ty::Isize,
            Ty::U8,
            Ty::U16,
            Ty::U32,
            Ty::U64,
            Ty::Usize,
            Ty::F32,
            Ty::F64,
            Ty::Char,
            Ty::Str,
            Ty::Never,
            Ty::Error,
            Ty::Var(TyVar(0)),
            Ty::Named(ItemId(0), name),
            Ty::Applied(ItemId(0), vec![Ty::I64]),
        ] {
            assert_eq!(scalar_of(&ty), None, "{ty:?} must not be natively supported");
        }
    }

    #[test]
    fn scalar_names_match_their_napitia_spelling() {
        assert_eq!(Scalar::Int.as_str(), "i64");
        assert_eq!(Scalar::Bool.as_str(), "bool");
        assert_eq!(Scalar::Unit.as_str(), "unit");
    }

    #[test]
    fn the_only_supported_target_is_the_one_the_cli_documents() {
        assert_eq!(TARGET_TRIPLE, "x86_64-unknown-linux-gnu");
    }
}
