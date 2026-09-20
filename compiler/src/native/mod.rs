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

pub mod capability;
pub mod lower;

use std::ffi::OsStr;
use std::path::{Path, PathBuf};

use crate::diagnostics::Diagnostic;
use crate::hir::ItemRegistry;
use crate::nir::Module;
use crate::source::{SourceId, Span};
use crate::symbol::Interner;
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

/// The linker `napitia build` runs: a C compiler driver, which is what
/// knows where this system's startup objects and C runtime live. It is
/// invoked as a program, never as a shell command line.
pub const DEFAULT_LINKER: &str = "cc";

/// Whether this host can link an executable for [`TARGET_TRIPLE`].
///
/// Object generation is host-independent -- Cranelift writes an ELF
/// object for the target from anywhere -- but linking one needs a
/// toolchain that targets it, which a non-Linux or non-x86-64 host does
/// not have. Saying so up front produces a deterministic, structured
/// refusal instead of whatever error a foreign linker would give for an
/// object it cannot read.
pub const fn host_can_link() -> bool {
    cfg!(target_os = "linux") && cfg!(target_arch = "x86_64")
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
pub fn build_executable(
    module: &Module,
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
    let object = match lower::emit_object(module, interner, &plan, TARGET_TRIPLE) {
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

    match link_object(&object, output, OsStr::new(DEFAULT_LINKER), source) {
        Ok(()) => Vec::new(),
        Err(diagnostic) => vec![*diagnostic],
    }
}

/// Writes `object` out and links it into `output` with `linker`.
///
/// The scratch directory this needs is created *beside* `output`, with
/// [`std::fs::create_dir`], which fails rather than succeeding on a
/// path that already exists -- so this only ever writes to, and only
/// ever removes, a directory it created itself. Nothing else on the
/// filesystem is touched, and `output` itself is only written at the
/// very end, by renaming a finished executable over it. A link that
/// fails therefore cannot leave a truncated file that looks like a
/// build.
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
    let result = link_in(object, output, linker, source, &scratch);
    let removed = std::fs::remove_dir_all(&scratch);
    result?;
    // Only worth reporting once the build itself succeeded: otherwise
    // it would bury the reason the build failed under a note about
    // tidying up after it.
    removed.map_err(|error| {
        io_failure(
            format!(
                "the executable was written, but the build directory `{}` could not be removed",
                scratch.display()
            ),
            &error,
        )
    })
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
            return Err(Box::new(
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
                )),
            ));
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

    fn compiled(text: &str) -> (Module, ItemRegistry, SourceId, Interner) {
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

        if host_can_link() {
            assert!(
                diagnostics.is_empty(),
                "this host can link, so the build must succeed: {:?}",
                diagnostics.iter().map(|d| d.code).collect::<Vec<_>>()
            );
            assert!(output.is_file(), "the executable must exist");
        } else {
            let observed: Vec<&str> = diagnostics.iter().map(|d| d.code).collect();
            assert_eq!(observed, vec![codes::UNSUPPORTED_HOST]);
            assert!(
                !output.exists(),
                "nothing is written on a host that cannot link"
            );
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

    #[test]
    fn the_host_gate_matches_the_target_this_backend_compiles_for() {
        assert_eq!(
            host_can_link(),
            cfg!(target_os = "linux") && cfg!(target_arch = "x86_64")
        );
        assert!(TARGET_TRIPLE.starts_with("x86_64-"));
        assert!(TARGET_TRIPLE.contains("linux"));
    }
}
