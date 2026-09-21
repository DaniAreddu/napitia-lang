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
//! * [`crate::nir::verify()`] is mandatory and runs first, and its seal
//!   is what this backend takes: `build_executable` and
//!   [`capability::validate`] accept a [`crate::nir::VerifiedModule`],
//!   never a bare module, so code generation cannot be reached with NIR
//!   the verifier has not accepted. Nothing here re-derives structural
//!   invariants the verifier already owns -- and where this module does
//!   notice such a violation anyway (a `#[cfg(test)]` unchecked seal is
//!   still a seal), it refuses with [`codes::UNVERIFIED_NIR`] rather
//!   than guessing.
//! * `capability` runs after verification and before Cranelift ever
//!   sees a function. It decides, exhaustively, whether the whole
//!   reachable program is inside the supported subset. Everything after
//!   it may therefore assume that subset, which is why `lower` has no
//!   "unsupported, give up" path buried inside code generation.
//!
//! # Diagnostic layers
//!
//! Malformed NIR is the verifier's business (`V...` codes). *Valid* NIR
//! this backend cannot compile is this module's business (`A...`
//! codes). The two are never mixed: a program that uses a resource is
//! not malformed, and a program with a dangling block target is not
//! merely unsupported.

// Both are crate-private on purpose: the only supported way into the
// native backend is `crate::driver::build_native`, which runs the whole
// frontend and the NIR verifier first. Nothing outside this crate can
// name the capability validator, name the lowering module, or mint the
// plan that lowering requires.
pub(crate) mod capability;
pub(crate) mod lower;

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use target_lexicon::Triple;

use crate::diagnostics::Diagnostic;
use crate::hir::ItemRegistry;
use crate::nir::VerifiedModule;
use crate::source::{SourceId, Span};
use crate::symbol::Interner;
use crate::types::Ty;

/// The one target triple `napitia build` produces, and the only one
/// the capability validator accepts. Alpha 0.2.0 adds a single target
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
/// `A0020`-`A0025` are the backend layer: something went wrong while
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
    /// have -- the capability validator documents exactly which
    /// operators those are, and why each one is on that list.
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
    /// The system linker is installed and runnable, but targets
    /// something other than [`super::TARGET_TRIPLE`] -- a musl
    /// environment, another architecture, another operating system --
    /// or would not say what it targets at all.
    pub const LINKER_TARGET_MISMATCH: &str = "A0025";
}

/// Every Napitia type the native subset can represent, and nothing
/// else.
///
/// The mapping to machine representation is recorded here, once, rather
/// than rediscovered at each use:
///
/// * [`Scalar::Int`] (`i64`) is represented by Cranelift's `I64`: the
///   declared width and the machine width are the same width
///   (`rfcs/0015`). Alpha 0.2.0 used `I128` here, because the
///   interpreter of that release held every Napitia integer in an
///   `i128` and wrapped at 128 bits, and matching the reference
///   implementation mattered more than matching the type's own name.
///   Both sides are 64 bits now, and the operation that used to
///   disagree -- one whose mathematical result leaves `i64` -- has no
///   result at all in either.
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
        // untested: nothing in the language executes them at all
        // (`rfcs/0015`), so the checker refuses one in source and the
        // verifier refuses one in NIR long before this is asked.
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

/// The linker `napitia build` runs: a C compiler driver, which is what
/// knows where this system's startup objects and C runtime live. It is
/// invoked as a program, never as a shell command line.
pub const DEFAULT_LINKER: &str = "cc";

/// Whether this host can link an executable for [`TARGET_TRIPLE`].
///
/// Object generation is host-independent -- Cranelift writes an ELF
/// object for the target from anywhere -- but linking one needs a
/// toolchain that targets it. All three components of the target have
/// to hold, *including the environment*: a musl host is Linux on
/// x86-64 and its `cc` still produces executables against a different
/// C runtime than the one `x86_64-unknown-linux-gnu` names.
///
/// Passing this gate is necessary and not sufficient. It says the host
/// could plausibly have such a toolchain; the `-dumpmachine` probe then asks
/// the toolchain itself.
pub const fn host_can_link() -> bool {
    cfg!(target_os = "linux") && cfg!(target_arch = "x86_64") && cfg!(target_env = "gnu")
}

/// What a `-dumpmachine` probe established about a linker.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LinkerTarget {
    /// It targets [`TARGET_TRIPLE`]'s architecture, operating system
    /// and environment.
    Native,
    /// It targets something else, spelled the way it spelled it.
    Other(String),
    /// It would not say, or said something that is not a target triple.
    Unreadable(String),
}

/// Classifies one `-dumpmachine` probe from its observable result.
///
/// Pure on purpose: the spellings a real toolchain reports are a table,
/// and a table is worth testing without needing every toolchain
/// installed to do it.
///
/// Comparison is by *component*, through `target_lexicon`, never by
/// substring. `-dumpmachine` answers in whichever spelling its
/// environment prefers -- `x86_64-linux-gnu` on Debian,
/// `x86_64-pc-linux-gnu` elsewhere, `x86_64-unknown-linux-gnu` from a
/// Rust-shaped toolchain -- and those differ in exactly the component
/// that carries no meaning here, the vendor. Architecture, operating
/// system and environment are the three that do.
pub(crate) fn classify_linker_target(succeeded: bool, reported: &str) -> LinkerTarget {
    let reported = reported.trim();
    if !succeeded {
        return LinkerTarget::Unreadable(format!(
            "`-dumpmachine` failed{}",
            if reported.is_empty() {
                String::new()
            } else {
                format!(": {reported}")
            }
        ));
    }
    let Ok(probed) = Triple::from_str(reported) else {
        return LinkerTarget::Unreadable(format!("`{reported}` is not a target triple"));
    };
    let Ok(wanted) = Triple::from_str(TARGET_TRIPLE) else {
        return LinkerTarget::Unreadable(format!("`{TARGET_TRIPLE}` is not a target triple"));
    };
    if probed.architecture == wanted.architecture
        && probed.operating_system == wanted.operating_system
        && probed.environment == wanted.environment
    {
        LinkerTarget::Native
    } else {
        LinkerTarget::Other(reported.to_string())
    }
}

/// Asks `linker` what it targets.
///
/// `Err` only when the linker could not be launched at all; a linker
/// that ran and answered unusably is a [`LinkerTarget::Unreadable`],
/// which is a different problem with a different diagnostic.
fn probe_linker_target(linker: &OsStr) -> Result<LinkerTarget, std::io::Error> {
    let probe = std::process::Command::new(linker)
        .arg("-dumpmachine")
        .output()?;
    let reported = String::from_utf8_lossy(&probe.stdout);
    let reported = if reported.trim().is_empty() {
        String::from_utf8_lossy(&probe.stderr).into_owned()
    } else {
        reported.into_owned()
    };
    Ok(classify_linker_target(probe.status.success(), &reported))
}

/// Runs the whole native pipeline for one already-verified module:
/// capability validation, Cranelift object generation, and the system
/// linker.
///
/// Returns every reason it could not, or an empty list on success.
/// There is no partial outcome and no fallback: if this returns
/// diagnostics, `output` is exactly as it was before the call.
///
/// `imports` carries the span of every `import` the source declared
/// (see [`capability::validate`]).
pub(crate) fn build_executable(
    module: &VerifiedModule,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
    imports: &[Span],
    output: &Path,
) -> Vec<Diagnostic> {
    let plan =
        match capability::validate(module, source, interner, registry, TARGET_TRIPLE, imports) {
            Ok(plan) => plan,
            Err(diagnostics) => return diagnostics,
        };

    // Deliberately before the host check: a program outside the native
    // subset gets the same diagnostic wherever it is compiled, and
    // whether this host could have linked the result is a separate
    // question from whether the program was compilable at all.
    let object = match lower::emit_object(module.module(), interner, &plan, TARGET_TRIPLE) {
        Ok(object) => object,
        Err(reason) => {
            return vec![
                Diagnostic::error(
                    codes::CODEGEN_FAILED,
                    source,
                    Span::dummy(),
                    format!("the native backend could not generate code: {reason}"),
                )
                .with_note(
                    "capability validation accepted this program, so this is a defect in the backend rather than in the program",
                ),
            ];
        }
    };

    if !host_can_link() {
        return vec![
            Diagnostic::error(
                codes::UNSUPPORTED_HOST,
                source,
                Span::dummy(),
                format!(
                    "this host ({}/{}) cannot link an executable for `{TARGET_TRIPLE}`",
                    std::env::consts::OS,
                    std::env::consts::ARCH
                ),
            )
            .with_note("the object was generated; only linking it is unavailable here")
            .with_help(format!(
                "build on an x86_64 Linux host, where `{DEFAULT_LINKER}` targets `{TARGET_TRIPLE}`"
            )),
        ];
    }

    // Asked before anything is written, and asked of the toolchain
    // rather than assumed from the host: a GNU x86-64 Linux machine can
    // still have a `cc` that cross-compiles somewhere else, and an
    // executable for somewhere else is not the executable that was
    // requested.
    let linker = OsStr::new(DEFAULT_LINKER);
    match probe_linker_target(linker) {
        Err(error) => {
            return vec![linker_launch_failure(linker, &error, source)];
        }
        Ok(LinkerTarget::Native) => {}
        Ok(LinkerTarget::Other(reported)) => {
            return vec![
                Diagnostic::error(
                    codes::LINKER_TARGET_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "the system linker `{}` targets `{reported}`, not `{TARGET_TRIPLE}`",
                        linker.to_string_lossy()
                    ),
                )
                .with_note("`cc -dumpmachine` was asked, and its answer compared by architecture, operating system and environment")
                .with_help("install a C toolchain that targets `x86_64-unknown-linux-gnu`, or put one earlier on PATH"),
            ];
        }
        Ok(LinkerTarget::Unreadable(detail)) => {
            return vec![
                Diagnostic::error(
                    codes::LINKER_TARGET_MISMATCH,
                    source,
                    Span::dummy(),
                    format!(
                        "the system linker `{}` would not say what it targets: {detail}",
                        linker.to_string_lossy()
                    ),
                )
                .with_note(
                    "a linker whose target cannot be established is not one this backend will publish an executable from",
                ),
            ];
        }
    }

    match link_object(&object, output, linker, source) {
        Ok(()) => Vec::new(),
        Err(diagnostic) => vec![*diagnostic],
    }
}

/// The one diagnostic for "this linker could not be launched", shared
/// by the target probe and the link itself so both say the same thing.
fn linker_launch_failure(linker: &OsStr, error: &std::io::Error, source: SourceId) -> Diagnostic {
    Diagnostic::error(
        codes::LINKER_LAUNCH_FAILED,
        source,
        Span::dummy(),
        format!(
            "could not run the system linker `{}`: {error}",
            linker.to_string_lossy()
        ),
    )
    .with_help(format!(
        "`napitia build` links with `{DEFAULT_LINKER}`; install a C toolchain, or put one on PATH"
    ))
}

/// Writes `object` out and links it into `output` with `linker`.
///
/// Public, and not a way around the sealed codegen path: this takes
/// opaque bytes, never NIR, and the only thing that produces those
/// bytes -- `lower::emit_object` -- is internal to the crate. A caller
/// can link bytes it already had; it cannot obtain bytes from this
/// compiler without having gone through verification and capability
/// validation first.
///
/// The scratch directory this needs is created *beside* `output`, with
/// [`std::fs::create_dir`], which fails rather than succeeding on a
/// path that already exists -- so this only ever writes to, and only
/// ever removes, a directory it created itself. Nothing else on the
/// filesystem is touched, and `output` itself is only written at the
/// very end, by renaming a finished executable over it. A link that
/// fails therefore cannot leave a truncated file that looks like a
/// build, and cannot disturb an executable an earlier build left
/// there: if this returns a diagnostic, `output` is byte-for-byte what
/// it was before the call. See `resolve_outcome` for the one place
/// that guarantee is decided, including why a cleanup failure *after*
/// the executable is in place is not allowed to undo it.
///
/// The linker is launched as a program with a fixed argument list, via
/// [`std::process::Command`] -- there is no shell, no quoting, and no
/// command string to get wrong. It runs *inside* the scratch
/// directory and is handed two constant relative names, so no path the
/// user chose (however it is spelled, spaces included) ever reaches its
/// argument vector, and the vector itself is identical from one build
/// to the next.
pub fn link_object(
    object: &[u8],
    output: &Path,
    linker: &OsStr,
    source: SourceId,
) -> Result<(), Box<Diagnostic>> {
    let io_failure = |context: String, error: &std::io::Error| {
        Box::new(Diagnostic::error(
            codes::BUILD_IO_FAILED,
            source,
            Span::dummy(),
            format!("{context}: {error}"),
        ))
    };

    let scratch = scratch_directory(output)
        .map_err(|error| io_failure("could not create a build directory".to_string(), &error))?;
    let linked = link_in(object, output, linker, source, &scratch);
    // Attempted on both paths, before either is reported.
    let cleaned = std::fs::remove_dir_all(&scratch);
    resolve_outcome(linked, cleaned)
}

/// Decides what a caller is told, given how the link went and how the
/// scratch cleanup went.
///
/// Two rules, and together they are the whole of this backend's
/// atomicity guarantee:
///
/// * **The build's own failure wins.** A cleanup error never replaces
///   the reason a build failed, because the reason a build failed is
///   the thing the user needs.
/// * **Publication is final.** Once the executable has been renamed
///   into place, nothing that happens afterwards can un-publish it, so
///   a failure to remove the scratch directory is not a build failure.
///   Reporting one would mean the command said "failed" about an output
///   it had already replaced, which is exactly what `NativeOutput` and
///   the documentation promise cannot happen.
///
/// Cleanup after successful publication is therefore best-effort: on
/// the vanishingly rare path where it fails, a `.napitia-build-*`
/// directory is left beside the output and the build still succeeds.
/// `rfcs/0014` says so too.
///
/// Extracted from [`link_object`] so both outcomes can be injected
/// directly in a test, rather than needing a filesystem that fails on
/// demand.
fn resolve_outcome(
    linked: Result<(), Box<Diagnostic>>,
    cleaned: Result<(), std::io::Error>,
) -> Result<(), Box<Diagnostic>> {
    match linked {
        Err(refusal) => Err(refusal),
        Ok(()) => {
            let _ = cleaned;
            Ok(())
        }
    }
}

/// The body of [`link_object`], with the scratch directory already
/// created so its caller can remove it on every path out.
fn link_in(
    object: &[u8],
    output: &Path,
    linker: &OsStr,
    source: SourceId,
    scratch: &Path,
) -> Result<(), Box<Diagnostic>> {
    const OBJECT_FILE: &str = "program.o";
    const LINKED_FILE: &str = "program";

    let object_path = scratch.join(OBJECT_FILE);
    std::fs::write(&object_path, object).map_err(|error| {
        Box::new(Diagnostic::error(
            codes::BUILD_IO_FAILED,
            source,
            Span::dummy(),
            format!("could not write `{}`: {error}", object_path.display()),
        ))
    })?;

    let linked = std::process::Command::new(linker)
        .current_dir(scratch)
        .arg("-o")
        .arg(LINKED_FILE)
        .arg(OBJECT_FILE)
        // A build id is a hash the linker stamps into the executable;
        // leaving it on would make two identical builds differ in
        // exactly the bytes a determinism test looks at.
        .arg("-Wl,--build-id=none")
        .output();

    let linked = match linked {
        Ok(linked) => linked,
        Err(error) => {
            return Err(Box::new(linker_launch_failure(linker, &error, source)));
        }
    };

    if !linked.status.success() {
        let status = match linked.status.code() {
            Some(code) => format!("exit status {code}"),
            None => "a signal".to_string(),
        };
        let mut diagnostic = Diagnostic::error(
            codes::LINKER_FAILED,
            source,
            Span::dummy(),
            format!(
                "the system linker `{}` failed with {status}",
                linker.to_string_lossy()
            ),
        );
        let output_text = linker_output(&linked.stdout, &linked.stderr);
        if !output_text.is_empty() {
            diagnostic = diagnostic.with_note(output_text);
        }
        return Err(Box::new(diagnostic));
    }

    // `output` is written exactly once, at the end, by moving a
    // finished file onto it. The scratch directory sits beside it, so
    // this is a same-filesystem rename rather than a copy that could
    // fail halfway.
    std::fs::rename(scratch.join(LINKED_FILE), output).map_err(|error| {
        Box::new(Diagnostic::error(
            codes::BUILD_IO_FAILED,
            source,
            Span::dummy(),
            format!(
                "could not move the linked executable to `{}`: {error}",
                output.display()
            ),
        ))
    })?;
    Ok(())
}

/// Whatever the linker said, as one block of text for a diagnostic's
/// note. Lossy on purpose: a linker's output is bytes, and refusing to
/// show it because it is not valid UTF-8 would hide the only
/// explanation there is.
fn linker_output(stdout: &[u8], stderr: &[u8]) -> String {
    let mut text = String::new();
    for stream in [stderr, stdout] {
        let rendered = String::from_utf8_lossy(stream);
        let rendered = rendered.trim();
        if rendered.is_empty() {
            continue;
        }
        if !text.is_empty() {
            text.push('\n');
        }
        text.push_str(rendered);
    }
    text
}

/// A fresh directory beside `output`, created exclusively.
///
/// [`std::fs::create_dir`] reports `AlreadyExists` rather than
/// succeeding on an existing path, which is what makes this
/// exclusive: every directory this returns is one nothing else owns,
/// so removing it later cannot take anything with it.
fn scratch_directory(output: &Path) -> Result<PathBuf, std::io::Error> {
    let parent = build_directory_parent(output);
    let process = std::process::id();
    for attempt in 0..MAX_SCRATCH_ATTEMPTS {
        let candidate = parent.join(format!(".napitia-build-{process}-{attempt}"));
        match std::fs::create_dir(&candidate) {
            Ok(()) => return Ok(candidate),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    Err(std::io::Error::other(format!(
        "no unused build directory beside `{}` after {MAX_SCRATCH_ATTEMPTS} attempts",
        parent.display()
    )))
}

/// Where a build directory for `output` belongs: beside it.
///
/// A bare file name has no parent component, and joining onto `""`
/// would put the build directory at the filesystem root rather than in
/// the working directory `output` itself is relative to.
fn build_directory_parent(output: &Path) -> &Path {
    match output.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent,
        _ => Path::new("."),
    }
}

/// How many names [`scratch_directory`] will try before giving up.
/// Bounded so a directory full of leftovers from a killed build fails
/// the build with a diagnostic instead of spinning.
const MAX_SCRATCH_ATTEMPTS: u32 = 1024;
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
            assert_eq!(
                scalar_of(&ty),
                None,
                "{ty:?} must not be natively supported"
            );
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

#[cfg(test)]
mod link_tests {
    use super::*;
    use crate::driver::{self, IrOutput};
    use crate::nir::Module;
    use crate::source::SourceMap;

    /// A directory of this test's own, under the system temporary
    /// directory, created exclusively. The name carries a space on
    /// purpose: every path the build touches has to survive one.
    struct TempDir {
        path: PathBuf,
    }

    impl TempDir {
        fn new(tag: &str) -> TempDir {
            let base = std::env::temp_dir();
            for attempt in 0..1024u32 {
                let candidate = base.join(format!(
                    "napitia build {tag} {} {attempt}",
                    std::process::id()
                ));
                match std::fs::create_dir(&candidate) {
                    Ok(()) => return TempDir { path: candidate },
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("could not create a temporary directory: {error}"),
                }
            }
            panic!("no unused temporary directory name")
        }

        fn join(&self, name: &str) -> PathBuf {
            self.path.join(name)
        }

        /// Everything this directory contains, by file name, sorted.
        fn entries(&self) -> Vec<String> {
            let Ok(entries) = std::fs::read_dir(&self.path) else {
                return Vec::new();
            };
            let mut names: Vec<String> = entries
                .filter_map(|entry| entry.ok())
                .map(|entry| entry.file_name().to_string_lossy().into_owned())
                .collect();
            names.sort();
            names
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.path);
        }
    }

    fn a_source() -> SourceId {
        let mut map = SourceMap::new();
        map.add_file("link.npt", "\n")
    }

    #[test]
    fn a_linker_that_cannot_be_launched_is_reported_and_leaves_nothing_behind() {
        let directory = TempDir::new("missing-linker");
        let output = directory.join("program with spaces");
        let diagnostic = link_object(
            b"not a real object",
            &output,
            OsStr::new("napitia-no-such-linker-exists"),
            a_source(),
        )
        .expect_err("a linker that is not installed cannot link");

        assert_eq!(diagnostic.code, codes::LINKER_LAUNCH_FAILED);
        assert!(!output.exists(), "a failed link writes no executable");
        assert!(
            directory.entries().is_empty(),
            "the build directory must be removed, found {:?}",
            directory.entries()
        );
    }

    /// The scratch directory is created exclusively, so a second build
    /// running beside the first picks a different name rather than
    /// writing into -- or later deleting -- the other one's.
    #[test]
    fn two_scratch_directories_beside_the_same_output_never_collide() {
        let directory = TempDir::new("scratch");
        let output = directory.join("program");
        let first = scratch_directory(&output).expect("a build directory is available");
        let second = scratch_directory(&output).expect("a second one is available too");
        assert_ne!(first, second);
        assert!(first.is_dir() && second.is_dir());
        std::fs::remove_dir_all(&first).expect("cleanup");
        std::fs::remove_dir_all(&second).expect("cleanup");
    }

    #[test]
    fn a_build_directory_always_sits_beside_its_output() {
        assert_eq!(
            build_directory_parent(Path::new("out/nested/program")),
            Path::new("out/nested")
        );
        // A bare name has no parent component; the build directory
        // belongs in the working directory, not at the filesystem root.
        assert_eq!(build_directory_parent(Path::new("program")), Path::new("."));
    }

    fn compiled(text: &str) -> (VerifiedModule, ItemRegistry, SourceId, Interner) {
        let mut map = SourceMap::new();
        let source = map.add_file("link.npt", text);
        let mut interner = Interner::new();
        match driver::ir(&map, source, &mut interner) {
            IrOutput::Ready { nir, registry } => (nir, registry, source, interner),
            IrOutput::Diagnostics(diagnostics) => {
                let codes: Vec<&str> = diagnostics.iter().map(|d| d.code).collect();
                panic!("this fixture must compile and verify cleanly, got {codes:?}")
            }
        }
    }

    /// The whole pipeline, end to end. On a host that can link for the
    /// native target this must produce a real executable; on any other
    /// host it must produce one specific, structured refusal -- never a
    /// panic, and never a half-written file.
    #[test]
    fn building_a_supported_program_either_links_or_says_exactly_why_it_cannot() {
        let directory = TempDir::new("end-to-end");
        let output = directory.join("scalar program");
        let (module, registry, source, interner) = compiled(
            "func add(a: i64, b: i64) -> i64 { return a + b; } func main() -> i64 { return add(2, 3); }",
        );

        let diagnostics = build_executable(&module, source, &interner, &registry, &[], &output);
        let observed: Vec<&str> = diagnostics.iter().map(|d| d.code).collect();

        // Four genuinely different situations, and the test asserts the
        // right one for whichever this host is rather than assuming
        // that "Linux on x86-64" implies "a usable GNU `cc`".
        match (
            host_can_link(),
            probe_linker_target(OsStr::new(DEFAULT_LINKER)),
        ) {
            (true, Ok(LinkerTarget::Native)) => {
                assert!(
                    diagnostics.is_empty(),
                    "a GNU host with a matching linker must build: {observed:?}"
                );
                assert!(output.is_file(), "the executable must exist");
            }
            (true, Ok(_)) => {
                assert_eq!(
                    observed,
                    vec![codes::LINKER_TARGET_MISMATCH],
                    "a linker targeting something else must be refused as such"
                );
                assert!(!output.exists());
            }
            (true, Err(_)) => {
                assert_eq!(
                    observed,
                    vec![codes::LINKER_LAUNCH_FAILED],
                    "a GNU host with no `cc` installed must say exactly that"
                );
                assert!(!output.exists());
            }
            (false, _) => {
                assert_eq!(observed, vec![codes::UNSUPPORTED_HOST]);
                assert!(
                    !output.exists(),
                    "nothing is written on a host that cannot link"
                );
            }
        }
        assert_eq!(
            directory
                .entries()
                .iter()
                .filter(|name| name.starts_with(".napitia-build-"))
                .count(),
            0,
            "no build directory is left behind either way"
        );
    }

    /// A program outside the native subset is refused for that reason
    /// on every host, before the question of linking arises at all.
    #[test]
    fn an_unsupported_program_is_refused_for_its_own_reason_on_every_host() {
        let directory = TempDir::new("unsupported");
        let output = directory.join("program");
        let (module, registry, source, interner) =
            compiled("func main() -> i64 { value a = 9; value b = 2; return a / b; }");

        let diagnostics = build_executable(&module, source, &interner, &registry, &[], &output);
        let observed: Vec<&str> = diagnostics.iter().map(|d| d.code).collect();
        assert_eq!(observed, vec![codes::UNSUPPORTED_OPERATOR]);
        assert!(!output.exists());
    }

    /// A build directory that cannot be created at all -- here because
    /// the directory the output was asked for does not exist -- is an
    /// I/O failure with its own code, not a panic and not a linker
    /// error blamed on the linker.
    #[test]
    fn an_output_in_a_directory_that_does_not_exist_is_an_io_failure() {
        let directory = TempDir::new("missing-parent");
        let output = directory.join("no such directory").join("program");
        let diagnostic = link_object(
            b"not a real object",
            &output,
            OsStr::new(DEFAULT_LINKER),
            a_source(),
        )
        .expect_err("there is nowhere to put a build directory");

        assert_eq!(diagnostic.code, codes::BUILD_IO_FAILED);
        assert!(!output.exists());
    }

    #[test]
    fn the_host_gate_requires_the_environment_too_not_just_linux_on_x86_64() {
        // The regression this replaces: the gate used to ask only for
        // Linux on x86-64, which a musl host answers yes to -- while
        // its `cc` builds against a different C runtime than the one
        // `x86_64-unknown-linux-gnu` names.
        let gate = host_can_link();
        let components = (
            cfg!(target_os = "linux"),
            cfg!(target_arch = "x86_64"),
            cfg!(target_env = "gnu"),
        );
        assert_eq!(
            gate,
            components == (true, true, true),
            "the gate holds exactly when every component of the native target does"
        );
        assert!(
            !(gate && cfg!(target_env = "musl")),
            "a musl host is Linux on x86-64 and still not a GNU host"
        );
    }

    /// The target this backend names must classify as its own target.
    /// If that ever stops holding, every probe below is measuring the
    /// wrong thing.
    #[test]
    fn the_supported_triple_classifies_as_native() {
        assert_eq!(
            classify_linker_target(true, TARGET_TRIPLE),
            LinkerTarget::Native
        );
    }

    #[test]
    fn every_gnu_spelling_a_real_toolchain_reports_is_accepted() {
        for reported in [
            "x86_64-unknown-linux-gnu",
            "x86_64-linux-gnu",
            "x86_64-pc-linux-gnu",
            // `-dumpmachine` output arrives with its newline attached.
            "x86_64-linux-gnu\n",
            "  x86_64-pc-linux-gnu  ",
        ] {
            assert_eq!(
                classify_linker_target(true, reported),
                LinkerTarget::Native,
                "`{reported}` is this target, spelled differently"
            );
        }
    }

    #[test]
    fn another_environment_architecture_or_os_is_not_this_target() {
        for reported in [
            // The case the host gate alone used to wave through.
            "x86_64-unknown-linux-musl",
            "x86_64-linux-musl",
            "i686-linux-gnu",
            "aarch64-linux-gnu",
            "aarch64-unknown-linux-gnu",
            "x86_64-apple-darwin",
            "riscv64-linux-gnu",
        ] {
            assert_eq!(
                classify_linker_target(true, reported),
                LinkerTarget::Other(reported.to_string()),
                "`{reported}` is not this target"
            );
        }
    }

    #[test]
    fn a_probe_that_fails_or_answers_nonsense_is_unreadable_not_a_match() {
        // Ran, but said no.
        assert!(matches!(
            classify_linker_target(false, "cc: error: unrecognized option '-dumpmachine'"),
            LinkerTarget::Unreadable(_)
        ));
        // Ran, said nothing at all.
        assert!(matches!(
            classify_linker_target(false, ""),
            LinkerTarget::Unreadable(_)
        ));
        // Ran, succeeded, and answered something that is not a triple.
        for reported in ["", "not a triple", "gcc version 12.2.0"] {
            assert!(
                matches!(
                    classify_linker_target(true, reported),
                    LinkerTarget::Unreadable(_)
                ),
                "`{reported}` is not a target triple"
            );
        }
    }

    #[test]
    fn probing_a_linker_that_is_not_installed_is_a_launch_failure() {
        let error = probe_linker_target(OsStr::new("napitia-no-such-linker-exists"))
            .expect_err("a linker that is not installed cannot be probed");
        assert_eq!(error.kind(), std::io::ErrorKind::NotFound);
    }

    /// Whatever this host's `cc` is, the probe has to reach a verdict
    /// about it without panicking -- and if it reaches `Native`, the
    /// host gate must agree that this is a GNU x86-64 Linux machine.
    #[test]
    fn probing_this_hosts_own_linker_reaches_a_verdict() {
        let Ok(verdict) = probe_linker_target(OsStr::new(DEFAULT_LINKER)) else {
            // No `cc` here at all; that is a launch failure, covered
            // above, not a target question.
            return;
        };
        if verdict == LinkerTarget::Native {
            assert!(
                host_can_link(),
                "a linker targeting `{TARGET_TRIPLE}` means this host is one"
            );
        }
    }

    // -- the sealed codegen boundary ---------------------------------------
    //
    // Nothing outside this crate can reach any of this: `capability`
    // and `lower` are crate-private modules, `build_executable` is a
    // crate-private function, and `NativePlan`'s fields are private to
    // `capability`, so the plan `lower::emit_object` demands cannot be
    // forged. What is left to test is the one question visibility does
    // not answer by itself -- what the sealed pipeline does when a
    // crate-internal caller hands it NIR the verifier would reject.

    use crate::hir::ItemId;
    use crate::nir::{
        BasicBlock, BlockId, Const, Function, Instruction, Param, Terminator, ValueId, ValueKind,
        verify_module,
    };
    use crate::types::Ty;

    /// Builds a module by hand, skipping every frontend stage, and puts
    /// it straight into [`build_executable`]. Reports what the verifier
    /// says about it and what the native pipeline says about it.
    fn build_unverified(
        module: &Module,
        interner: &Interner,
        output: &Path,
    ) -> (Vec<&'static str>, Vec<&'static str>) {
        let mut map = SourceMap::new();
        let source = map.add_file(
            "sealed.npt",
            "
",
        );
        let registry = ItemRegistry::default();

        let verifier: Vec<&str> = verify_module(module, source, interner, &registry)
            .iter()
            .map(|d| d.code)
            .collect();
        let native: Vec<&str> = build_executable(module, source, interner, &registry, &[], output)
            .iter()
            .map(|d| d.code)
            .collect();
        (verifier, native)
    }

    fn hand_built_block(
        id: u32,
        instructions: Vec<Instruction>,
        terminator: Terminator,
    ) -> BasicBlock {
        BasicBlock {
            id: BlockId(id),
            instructions,
            terminator,
        }
    }

    fn hand_built_int(result: u32, literal: i128) -> Instruction {
        Instruction::Value {
            result: ValueId(result),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(literal)),
        }
    }

    fn hand_built_main(
        interner: &mut Interner,
        return_type: Ty,
        blocks: Vec<BasicBlock>,
    ) -> Module {
        Module {
            functions: vec![Function {
                id: ItemId(0),
                name: interner.intern("main"),
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: Vec::<Param>::new(),
                return_type,
                raises: Vec::new(),
                blocks,
            }],
            ..Module::default()
        }
    }

    /// The shape every malformed case must have: the verifier objects,
    /// the native pass refuses it in its *verifier* layer rather than
    /// its backend layer, and nothing is written.
    fn assert_refused_before_codegen(module: &Module, interner: &Interner, tag: &str) {
        let directory = TempDir::new(tag);
        let output = directory.join("program");
        let (verifier, native) = build_unverified(module, interner, &output);

        assert!(
            !verifier.is_empty(),
            "{tag}: this NIR must fail `nir::verify` in the first place"
        );
        assert_eq!(
            native,
            vec![codes::UNVERIFIED_NIR],
            "{tag}: the native pass must refuse it as unverified NIR, not as a backend defect"
        );
        assert!(!output.exists(), "{tag}: nothing may be written");
        assert!(
            directory.entries().is_empty(),
            "{tag}: no build directory may be left behind"
        );
    }

    #[test]
    fn a_non_dominating_ssa_use_never_reaches_cranelift() {
        let mut interner = Interner::new();
        // bb1 defines %3 and does not dominate bb3, which uses it.
        let module = hand_built_main(
            &mut interner,
            Ty::I64,
            vec![
                hand_built_block(
                    0,
                    vec![
                        hand_built_int(0, 1),
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::Bool,
                            kind: ValueKind::Const(Const::Bool(true)),
                        },
                    ],
                    Terminator::CondBranch {
                        condition: ValueId(1),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                ),
                hand_built_block(
                    1,
                    vec![hand_built_int(3, 7)],
                    Terminator::Branch(BlockId(3)),
                ),
                hand_built_block(2, Vec::new(), Terminator::Branch(BlockId(3))),
                hand_built_block(3, Vec::new(), Terminator::Return(Some(ValueId(3)))),
            ],
        );
        assert_refused_before_codegen(&module, &interner, "non-dominating-use");
    }

    #[test]
    fn a_dangling_branch_target_never_reaches_cranelift() {
        let mut interner = Interner::new();
        let module = hand_built_main(
            &mut interner,
            Ty::I64,
            vec![hand_built_block(
                0,
                vec![hand_built_int(0, 1)],
                Terminator::Branch(BlockId(9)),
            )],
        );
        assert_refused_before_codegen(&module, &interner, "dangling-target");
    }

    #[test]
    fn a_function_with_no_entry_block_never_reaches_cranelift() {
        let mut interner = Interner::new();
        let module = hand_built_main(
            &mut interner,
            Ty::I64,
            vec![hand_built_block(
                4,
                vec![hand_built_int(0, 1)],
                Terminator::Return(Some(ValueId(0))),
            )],
        );
        assert_refused_before_codegen(&module, &interner, "no-entry-block");
    }

    /// The plan *is* the proof of validation: `lower::emit_object`
    /// takes one by reference and only `capability::validate` can build
    /// one, so a module validation refuses has nothing that could be
    /// handed to Cranelift instead.
    #[test]
    fn a_refused_module_produces_diagnostics_where_a_plan_would_be() {
        let mut map = SourceMap::new();
        let source = map.add_file("sealed.npt", "\n");
        let mut interner = Interner::new();
        let registry = ItemRegistry::default();
        let module = hand_built_main(
            &mut interner,
            Ty::Str,
            vec![hand_built_block(
                0,
                vec![Instruction::Value {
                    result: ValueId(0),
                    ty: Ty::Str,
                    kind: ValueKind::Const(Const::Str("no".to_string())),
                }],
                Terminator::Return(Some(ValueId(0))),
            )],
        );

        let refused =
            capability::validate(&module, source, &interner, &registry, TARGET_TRIPLE, &[])
                .expect_err("a `str` result is outside the native subset");
        assert_eq!(
            refused.iter().map(|d| d.code).collect::<Vec<_>>(),
            vec![codes::ENTRY_RETURN_TYPE]
        );
    }

    #[test]
    fn refusing_unverified_nir_is_deterministic_and_never_panics() {
        let mut interner = Interner::new();
        let module = hand_built_main(
            &mut interner,
            Ty::I64,
            vec![hand_built_block(
                0,
                vec![hand_built_int(0, 1)],
                Terminator::Branch(BlockId(9)),
            )],
        );
        let directory = TempDir::new("deterministic-seal");
        let first = build_unverified(&module, &interner, &directory.join("a"));
        let second = build_unverified(&module, &interner, &directory.join("b"));
        assert_eq!(first, second);
        assert_eq!(first.1, vec![codes::UNVERIFIED_NIR]);
    }

    // -- output and status atomicity ---------------------------------------

    /// The bytes an earlier build is pretending to have left behind.
    const PREVIOUS_BUILD: &[u8] = b"an executable from an earlier build";

    fn seeded_output(directory: &TempDir, name: &str) -> PathBuf {
        let output = directory.join(name);
        std::fs::write(&output, PREVIOUS_BUILD).expect("could not seed the output");
        output
    }

    fn assert_output_untouched(output: &Path, tag: &str) {
        assert_eq!(
            std::fs::read(output).expect("the previous output is still there"),
            PREVIOUS_BUILD,
            "{tag}: a failed build must leave the output byte-for-byte unchanged"
        );
    }

    #[test]
    fn a_linker_that_cannot_be_launched_leaves_an_existing_output_alone() {
        let directory = TempDir::new("preserve-launch");
        let output = seeded_output(&directory, "program with spaces");

        let diagnostic = link_object(
            b"not a real object",
            &output,
            OsStr::new("napitia-no-such-linker-exists"),
            a_source(),
        )
        .expect_err("a linker that is not installed cannot link");

        assert_eq!(diagnostic.code, codes::LINKER_LAUNCH_FAILED);
        assert_output_untouched(&output, "launch failure");
        assert!(
            directory
                .entries()
                .iter()
                .all(|name| name == "program with spaces"),
            "cleanup is attempted on the failure path too, found {:?}",
            directory.entries()
        );
    }

    /// A publication that cannot happen -- here because the requested
    /// output is a directory, which nothing can be renamed over -- must
    /// still leave what was there alone.
    #[test]
    fn a_publication_that_fails_leaves_what_was_there_alone() {
        let directory = TempDir::new("preserve-publish");
        let output = directory.join("program");
        std::fs::create_dir(&output).expect("could not seed the output");
        let occupant = output.join("kept");
        std::fs::write(&occupant, PREVIOUS_BUILD).expect("could not seed the output");

        // A "linker" that succeeds without producing the file the
        // rename then looks for is the same failure from the other
        // side; either way nothing may be published.
        let diagnostic = link_object(
            b"not a real object",
            &output,
            OsStr::new("napitia-no-such-linker-exists"),
            a_source(),
        )
        .expect_err("there is no executable to publish");

        assert!(
            diagnostic.code == codes::LINKER_LAUNCH_FAILED
                || diagnostic.code == codes::BUILD_IO_FAILED,
            "unexpected code {}",
            diagnostic.code
        );
        assert!(output.is_dir(), "the occupied path must survive");
        assert_eq!(
            std::fs::read(&occupant).expect("its contents survive too"),
            PREVIOUS_BUILD
        );
    }

    /// The two rules that make the outcome atomic, injected directly
    /// rather than waiting for a filesystem that fails on demand.
    #[test]
    fn a_cleanup_failure_never_turns_a_published_build_into_a_failure() {
        let cleanup_failed = || std::io::Error::other("the build directory could not be removed");

        // Published, then cleanup failed: still a success, because the
        // executable is already in place and nothing can un-place it.
        assert!(resolve_outcome(Ok(()), Err(cleanup_failed())).is_ok());
        // Published, cleanup fine: success.
        assert!(resolve_outcome(Ok(()), Ok(())).is_ok());
    }

    #[test]
    fn a_cleanup_failure_never_replaces_the_reason_a_build_failed() {
        let original = Box::new(Diagnostic::error(
            codes::LINKER_FAILED,
            a_source(),
            Span::dummy(),
            "the linker said no",
        ));
        let resolved = resolve_outcome(
            Err(original),
            Err(std::io::Error::other("and cleanup went wrong too")),
        )
        .expect_err("the build failed");

        assert_eq!(
            resolved.code,
            codes::LINKER_FAILED,
            "the build's own failure is what the user needs to see"
        );
        assert!(resolved.message.contains("the linker said no"));
    }
}
