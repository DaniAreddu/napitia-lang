//! End-to-end tests for `napitia build`, exercising the real binary
//! the way a user does: a `.npt` file in, an executable out, and --
//! where the host can run the result -- its actual exit status compared
//! against what the interpreter says the same program means.
//!
//! # Hosts
//!
//! Object generation works anywhere; linking an
//! `x86_64-unknown-linux-gnu` executable needs a host that targets it.
//! No test here is skipped on a host that cannot: each one asserts the
//! exact structured refusal instead, so the Windows and macOS legs of
//! CI prove the refusal is the documented one rather than proving
//! nothing.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use compiler::native::codes;

fn napitia(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_napitia"))
        .args(args)
        .output()
        .expect("failed to run the napitia binary")
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn example(name: &str) -> String {
    format!("{}/../examples/{name}", env!("CARGO_MANIFEST_DIR"))
}

/// What this host actually does with a native build.
///
/// Established by *asking the compiler* -- building a program that is
/// certainly inside the native subset and reading the answer off the
/// result -- rather than by re-deriving its host and linker rules here.
/// A test that reimplements the rule it is checking cannot catch the
/// rule being wrong.
fn classify_host(workspace: &Workspace) -> Host {
    let source = workspace.source("host_probe", "func main() -> i64 { return 0; }");
    let output = workspace.output("host probe");
    let built = napitia(&["build", as_str(&source), "--output", as_str(&output)]);
    let err = stderr(&built);
    let _ = std::fs::remove_file(&output);

    if built.status.success() {
        return Host::Links;
    }
    for (code, host) in [
        (codes::UNSUPPORTED_HOST, Host::Unsupported),
        (codes::LINKER_LAUNCH_FAILED, Host::NoLinker),
        (codes::LINKER_TARGET_MISMATCH, Host::WrongLinkerTarget),
    ] {
        if err.contains(code) {
            return host;
        }
    }
    panic!("a program inside the native subset must build or say why it cannot:\n{err}")
}

/// What this host can do with a native build, so each test can assert
/// the one right outcome instead of skipping.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Host {
    /// A GNU x86-64 Linux host whose `cc` targets the same thing:
    /// builds produce executables.
    Links,
    /// The host qualifies, but no `cc` could be launched at all.
    NoLinker,
    /// The host qualifies and `cc` runs, but targets something else --
    /// a musl environment, another architecture, another OS.
    WrongLinkerTarget,
    /// The host itself is not `x86_64-unknown-linux-gnu`. The object is
    /// still generated; only linking it is unavailable.
    Unsupported,
}

/// A directory of this test's own, created exclusively. The name
/// carries a space deliberately: every path a build touches has to
/// survive one.
struct Workspace {
    path: PathBuf,
}

impl Workspace {
    fn new(tag: &str) -> Workspace {
        let base = std::env::temp_dir();
        for attempt in 0..1024u32 {
            let candidate = base.join(format!(
                "napitia build test {tag} {} {attempt}",
                std::process::id()
            ));
            match std::fs::create_dir(&candidate) {
                Ok(()) => return Workspace { path: candidate },
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("could not create a temporary directory: {error}"),
            }
        }
        panic!("no unused temporary directory name")
    }

    /// Writes `text` as a `.npt` source and returns its path.
    fn source(&self, name: &str, text: &str) -> PathBuf {
        let path = self.path.join(format!("{name}.npt"));
        std::fs::write(&path, text).expect("could not write a test source");
        path
    }

    fn output(&self, name: &str) -> PathBuf {
        self.path.join(name)
    }

    /// Anything left in this workspace that looks like a build's
    /// scratch directory. Always empty once a build has returned.
    fn leftover_build_directories(&self) -> Vec<String> {
        let Ok(entries) = std::fs::read_dir(&self.path) else {
            return Vec::new();
        };
        let mut names: Vec<String> = entries
            .filter_map(|entry| entry.ok())
            .map(|entry| entry.file_name().to_string_lossy().into_owned())
            .filter(|name| name.starts_with(".napitia-build-"))
            .collect();
        names.sort();
        names
    }
}

impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

fn as_str(path: &Path) -> &str {
    path.to_str().expect("test paths are UTF-8")
}

/// Builds `source` to `output` and reports the built program's exit
/// status, or `None` when this host cannot produce one -- having first
/// asserted the exact refusal it must give instead.
fn build_and_run(workspace: &Workspace, source: &Path, output: &Path) -> Option<i32> {
    let built = napitia(&["build", as_str(source), "--output", as_str(output)]);
    let expected = match classify_host(workspace) {
        Host::Links => {
            assert!(
                built.status.success(),
                "a GNU host with a matching linker must build:\n{}",
                stderr(&built)
            );
            assert!(output.is_file(), "the executable must exist");
            let run = Command::new(output)
                .output()
                .expect("the built executable must be runnable");
            return Some(run.status.code().expect("the program exits normally"));
        }
        Host::NoLinker => codes::LINKER_LAUNCH_FAILED,
        Host::WrongLinkerTarget => codes::LINKER_TARGET_MISMATCH,
        Host::Unsupported => codes::UNSUPPORTED_HOST,
    };
    assert_eq!(built.status.code(), Some(1));
    assert!(
        stderr(&built).contains(expected),
        "this host must refuse with {expected}:\n{}",
        stderr(&built)
    );
    assert!(
        !output.exists(),
        "a host that cannot link writes no executable"
    );
    None
}

/// What `napitia run` prints for the same program: the interpreter's
/// own answer, which is the reference every native result is measured
/// against.
fn interpreted(source: &Path) -> String {
    let output = napitia(&["run", as_str(source)]);
    assert!(
        output.status.success(),
        "the interpreter must run this program:\n{}",
        stderr(&output)
    );
    stdout(&output).trim().to_string()
}

// -- the supported subset, end to end ------------------------------------

const SCALAR_AND_CALLS: &str = "
func add(a: i64, b: i64) -> i64 { return a + b; }
func twice(x: i64) -> i64 { return add(x, x); }
func main() -> i64 {
    mutable total = 0;
    mutable index = 0;
    while index < 5 {
        total = add(total, twice(index));
        index = index + 1;
    }
    if total > 10 { return total; }
    return 0;
}
";

#[test]
fn a_scalar_program_with_a_loop_and_direct_calls_matches_the_interpreter() {
    let workspace = Workspace::new("scalar");
    let source = workspace.source("scalar", SCALAR_AND_CALLS);
    let output = workspace.output("scalar program");

    // 2 * (0 + 1 + 2 + 3 + 4) = 20.
    assert_eq!(interpreted(&source), "20");
    if let Some(status) = build_and_run(&workspace, &source, &output) {
        assert_eq!(status, 20, "the native result must match the interpreter");
    }
    assert!(workspace.leftover_build_directories().is_empty());
}

#[test]
fn a_unit_returning_main_exits_successfully() {
    let workspace = Workspace::new("unit");
    let source = workspace.source(
        "unit",
        "func nothing() -> unit { return; } func main() -> unit { nothing(); return; }",
    );
    let output = workspace.output("unit program");

    assert_eq!(interpreted(&source), "()");
    if let Some(status) = build_and_run(&workspace, &source, &output) {
        assert_eq!(status, 0, "`main() -> unit` exits 0");
    }
}

/// Every accepted operator, on both sides of every branch, checked
/// against the interpreter's own answer for the same program.
#[test]
fn every_accepted_operator_agrees_with_the_interpreter() {
    let cases: [(&str, &str, i32); 8] = [
        ("add", "return 17 + 25;", 42),
        ("sub", "return 50 - 8;", 42),
        ("mul", "return 6 * 7;", 42),
        ("neg", "value x = -42; return -x;", 42),
        ("bits", "return (60 & 43) | (40 ^ 2);", 42),
        ("bitnot", "value x = ~42; return ~x;", 42),
        (
            "compare",
            "value a = 1; value b = 2; \
             if (a < b) == !(a > b) { if (a <= b) != (a >= b) { return 42; } } return 0;",
            42,
        ),
        (
            "nested",
            "mutable n = 0; \
             if n == 0 { if n <= 0 { n = 42; } else { n = 1; } } else { n = 2; } return n;",
            42,
        ),
    ];

    let workspace = Workspace::new("operators");
    for (name, body, expected) in cases {
        let source = workspace.source(name, &format!("func main() -> i64 {{ {body} }}"));
        let output = workspace.output(name);
        assert_eq!(
            interpreted(&source),
            expected.to_string(),
            "the interpreter disagrees about `{name}`"
        );
        if let Some(status) = build_and_run(&workspace, &source, &output) {
            assert_eq!(
                status, expected,
                "the native build disagrees about `{name}`"
            );
        }
    }
}

/// Declaration order is not semantics: a callee declared after its
/// caller compiles to the same program.
#[test]
fn functions_declared_in_reverse_order_still_compile_and_agree() {
    let workspace = Workspace::new("reversed");
    let source = workspace.source(
        "reversed",
        "
        func main() -> i64 { return outer(4); }
        func outer(x: i64) -> i64 { return inner(x) + 1; }
        func inner(x: i64) -> i64 { return x * 10; }
        ",
    );
    let output = workspace.output("reversed");

    assert_eq!(interpreted(&source), "41");
    if let Some(status) = build_and_run(&workspace, &source, &output) {
        assert_eq!(status, 41);
    }
}

/// The documented exit-status conversion, tested on purpose rather
/// than avoided: the process status a parent observes is the Napitia
/// value's low byte.
#[test]
fn an_i64_result_larger_than_a_byte_is_reduced_the_way_the_docs_say() {
    let workspace = Workspace::new("exit-code");
    let source = workspace.source("wide", "func main() -> i64 { return 300; }");
    let output = workspace.output("wide");

    assert_eq!(interpreted(&source), "300");
    if let Some(status) = build_and_run(&workspace, &source, &output) {
        assert_eq!(status, 300 % 256, "300 is reported as 44");
    }
}

// -- determinism ---------------------------------------------------------

#[test]
fn building_the_same_program_twice_produces_identical_executables() {
    let workspace = Workspace::new("determinism");
    let source = workspace.source("scalar", SCALAR_AND_CALLS);
    let first = workspace.output("first build");
    let second = workspace.output("second build");

    if build_and_run(&workspace, &source, &first).is_none() {
        return;
    }
    build_and_run(&workspace, &source, &second).expect("the second build must also link");

    let first_bytes = std::fs::read(&first).expect("the first executable is readable");
    let second_bytes = std::fs::read(&second).expect("the second executable is readable");
    assert_eq!(
        first_bytes, second_bytes,
        "two builds of one program must be byte-identical"
    );
}

// -- refusals ------------------------------------------------------------

/// Every category the native backend refuses, with the exact code it
/// refuses it with. Each one still compiles, and still runs, through
/// the unchanged interpreter path.
#[test]
fn every_unsupported_category_is_refused_with_its_own_code() {
    let workspace = Workspace::new("refusals");
    let written: [(&str, &str, &str); 8] = [
        (
            "strings",
            "func main() -> i64 { value s = \"hi\"; if s == \"hi\" { return 1; } return 0; }",
            codes::UNSUPPORTED_TYPE,
        ),
        (
            "division",
            "func main() -> i64 { value a = 9; value b = 2; return a / b; }",
            codes::UNSUPPORTED_OPERATOR,
        ),
        (
            "remainder",
            "func main() -> i64 { value a = 9; value b = 2; return a % b; }",
            codes::UNSUPPORTED_OPERATOR,
        ),
        (
            "shift",
            "func main() -> i64 { value a = 9; value b = 2; return a << b; }",
            codes::UNSUPPORTED_OPERATOR,
        ),
        (
            "recursion",
            "func down(n: i64) -> i64 { if n <= 0 { return 0; } return down(n - 1); } \
             func main() -> i64 { return down(3); }",
            codes::RECURSIVE_CALL_GRAPH,
        ),
        (
            "missing_main",
            "func helper() -> i64 { return 1; }",
            codes::MISSING_ENTRY,
        ),
        (
            "bad_main_result",
            "func main() -> bool { return true; }",
            codes::ENTRY_RETURN_TYPE,
        ),
        (
            "imports",
            "import models.user.User;\nfunc main() -> i64 { return 1; }",
            codes::MULTI_MODULE_BUILD,
        ),
    ];

    for (name, text, expected) in written {
        let source = workspace.source(name, text);
        let output = workspace.output(name);
        let built = napitia(&["build", as_str(&source), "--output", as_str(&output)]);
        assert_eq!(
            built.status.code(),
            Some(1),
            "`{name}` must fail the build:\n{}",
            stderr(&built)
        );
        assert!(
            stderr(&built).contains(expected),
            "`{name}` must be refused with {expected}, got:\n{}",
            stderr(&built)
        );
        assert!(!output.exists(), "`{name}` must not leave an executable");
    }
    assert!(workspace.leftover_build_directories().is_empty());
}

/// The same refusals, for the language features that already have
/// example programs. Each of these is a *valid* Napitia program that
/// `check` accepts and the interpreter can still run.
#[test]
fn existing_examples_outside_the_subset_are_refused_but_still_check() {
    let workspace = Workspace::new("examples");
    let cases: [(&str, &str); 6] = [
        ("resource_basic.npt", codes::UNSUPPORTED_TYPE),
        ("resource_defer.npt", codes::UNSUPPORTED_TYPE),
        ("resource_observe_scope.npt", codes::UNSUPPORTED_TYPE),
        ("records_and_variants.npt", codes::UNSUPPORTED_TYPE),
        ("generic_identity.npt", codes::GENERIC_CODE),
        ("protocol_equal.npt", codes::ENTRY_RETURN_TYPE),
    ];

    for (name, expected) in cases {
        let path = example(name);
        let checked = napitia(&["check", &path]);
        assert!(
            checked.status.success(),
            "`{name}` must still type-check:\n{}",
            stderr(&checked)
        );

        let output = workspace.output(name);
        let built = napitia(&["build", &path, "--output", as_str(&output)]);
        assert_eq!(built.status.code(), Some(1), "`{name}` must fail the build");
        assert!(
            stderr(&built).contains(expected),
            "`{name}` must be refused with {expected}, got:\n{}",
            stderr(&built)
        );
        assert!(!output.exists());
    }
}

/// A program the native backend refuses still runs, unchanged, through
/// the interpreter. That is the whole shape of this release.
#[test]
fn a_refused_program_still_runs_through_the_interpreter() {
    let path = example("resource_basic.npt");
    let workspace = Workspace::new("interpreter-still-works");
    let output = workspace.output("resource");

    let built = napitia(&["build", &path, "--output", as_str(&output)]);
    assert_eq!(built.status.code(), Some(1));
    assert!(stderr(&built).contains(codes::UNSUPPORTED_TYPE));

    let run = napitia(&["run", &path]);
    assert!(run.status.success(), "{}", stderr(&run));
    assert_eq!(stdout(&run).trim(), "3");
}

#[test]
fn a_refusal_is_byte_identical_across_repeated_builds() {
    let workspace = Workspace::new("stable-diagnostics");
    let path = example("resource_basic.npt");
    let output = workspace.output("resource");

    let first = napitia(&["build", &path, "--output", as_str(&output)]);
    let second = napitia(&["build", &path, "--output", as_str(&output)]);
    assert_eq!(first.status.code(), second.status.code());
    assert_eq!(first.stderr, second.stderr);
    assert!(!stderr(&first).is_empty());
    assert!(
        !stderr(&first).contains("panicked"),
        "a refusal is a diagnostic, never a panic"
    );
}

// -- the linker ----------------------------------------------------------

/// A linker that runs but fails. The `napitia` binary itself stands in
/// for one: it is a real program on every platform, and it rejects the
/// linker argument list with a non-zero status, which is exactly the
/// situation being tested.
#[test]
fn a_linker_that_exits_non_zero_is_reported_with_its_own_output() {
    use std::ffi::OsStr;

    let workspace = Workspace::new("failing-linker");
    let output = workspace.output("program with spaces");
    // An executable an earlier build left behind. A failed link must
    // not disturb it -- reporting failure about an output that was
    // already replaced is exactly what must not happen.
    std::fs::write(&output, PREVIOUS_BUILD).expect("could not seed the output");
    let mut map = compiler::source::SourceMap::new();
    let source = map.add_file("linker.npt", "\n");

    let diagnostic = compiler::native::link_object(
        b"not a real object",
        &output,
        OsStr::new(env!("CARGO_BIN_EXE_napitia")),
        source,
    )
    .expect_err("this `linker` cannot link anything");

    assert_eq!(diagnostic.code, codes::LINKER_FAILED);
    assert_eq!(
        std::fs::read(&output).expect("the previous output is still there"),
        PREVIOUS_BUILD,
        "a failed link leaves the output byte-for-byte unchanged"
    );
    assert!(
        workspace.leftover_build_directories().is_empty(),
        "the build directory must be removed even when the linker fails"
    );
}

/// The bytes an earlier build is pretending to have left behind.
const PREVIOUS_BUILD: &[u8] = b"an executable from an earlier build";

#[test]
fn a_linker_that_cannot_be_launched_is_reported_separately() {
    use std::ffi::OsStr;

    let workspace = Workspace::new("absent-linker");
    let output = workspace.output("program");
    let mut map = compiler::source::SourceMap::new();
    let source = map.add_file("linker.npt", "\n");

    let diagnostic = compiler::native::link_object(
        b"not a real object",
        &output,
        OsStr::new("napitia-no-such-linker-exists"),
        source,
    )
    .expect_err("a linker that is not installed cannot be launched");

    assert_eq!(diagnostic.code, codes::LINKER_LAUNCH_FAILED);
    assert!(!output.exists());
    assert!(workspace.leftover_build_directories().is_empty());
}

/// A failed build must not replace an executable an earlier one left
/// behind with something truncated or half-written.
#[test]
fn a_failed_build_leaves_an_existing_output_untouched() {
    let workspace = Workspace::new("stale-output");

    // Every stage that can refuse, each against an output an earlier
    // build already wrote: the invariant is that a command reporting
    // failure never changed the file it was pointed at, whichever stage
    // did the refusing.
    let refusals: [(&str, &str); 4] = [
        // Capability: an operator outside the subset.
        (
            "division",
            "func main() -> i64 { value a = 1; return a / a; }",
        ),
        // Capability: no entry point at all.
        ("no_main", "func helper() -> i64 { return 1; }"),
        // Capability: recursion.
        (
            "recursion",
            "func down(n: i64) -> i64 { if n <= 0 { return 0; } return down(n - 1); } \
             func main() -> i64 { return down(2); }",
        ),
        // Frontend: never even reaches the native backend.
        ("broken", "func main() -> i64 { return "),
    ];

    for (name, text) in refusals {
        let output = workspace.output(&format!("{name} program"));
        std::fs::write(&output, PREVIOUS_BUILD).expect("could not seed the output");
        let source = workspace.source(name, text);

        let built = napitia(&["build", as_str(&source), "--output", as_str(&output)]);
        assert_eq!(
            built.status.code(),
            Some(1),
            "`{name}` must fail:\n{}",
            stderr(&built)
        );
        assert_eq!(
            std::fs::read(&output).expect("the previous output is still there"),
            PREVIOUS_BUILD,
            "`{name}`: a failed build must leave the output byte-for-byte unchanged"
        );
    }
    assert!(workspace.leftover_build_directories().is_empty());
}

// -- argument handling ---------------------------------------------------

#[test]
fn build_requires_a_source_and_an_output() {
    let workspace = Workspace::new("arguments");
    let source = workspace.source("ok", "func main() -> i64 { return 1; }");
    let output = workspace.output("program");

    for args in [
        vec!["build"],
        vec!["build", as_str(&source)],
        vec!["build", as_str(&source), "--output"],
        vec!["build", as_str(&source), "--outpt", as_str(&output)],
        vec![
            "build",
            as_str(&source),
            "--output",
            as_str(&output),
            "extra",
        ],
    ] {
        let built = napitia(&args);
        assert_eq!(
            built.status.code(),
            Some(2),
            "`{args:?}` must be a usage error"
        );
        assert!(stderr(&built).contains("Usage: napitia"));
    }
    assert!(!output.exists());
}

#[test]
fn build_refuses_a_project_path_rather_than_compiling_the_wrong_thing() {
    let workspace = Workspace::new("project-path");
    let output = workspace.output("program");
    let built = napitia(&[
        "build",
        env!("CARGO_MANIFEST_DIR"),
        "--output",
        as_str(&output),
    ]);
    assert_eq!(built.status.code(), Some(2));
    assert!(stderr(&built).contains("`.npt` file"));
    assert!(!output.exists());
}

#[test]
fn build_reports_an_unreadable_source_as_a_usage_error() {
    let workspace = Workspace::new("unreadable");
    let output = workspace.output("program");
    let built = napitia(&["build", "does/not/exist.npt", "--output", as_str(&output)]);
    assert_eq!(built.status.code(), Some(2));
    assert!(stderr(&built).contains("could not read"));
    assert!(!output.exists());
}

#[test]
fn help_lists_the_build_command() {
    let output = napitia(&["--help"]);
    assert!(output.status.success());
    assert!(stdout(&output).contains("build <file> --output <exe>"));
    assert!(stdout(&output).contains("x86_64-unknown-linux-gnu"));
}

/// A `unit` parameter occupies no ABI position at all, so the native
/// signature and every call to it have to agree about a value that is
/// not there. Getting that wrong would shift every later argument by
/// one, which is the kind of mistake that produces a program that runs
/// and is simply wrong -- so it is checked against the interpreter's
/// own answer rather than against "it linked".
#[test]
fn a_unit_parameter_occupies_no_abi_position() {
    let workspace = Workspace::new("unit-abi");
    let source = workspace.source(
        "unit_abi",
        "
        func nothing() -> unit { return; }
        func consume(before: unit, n: i64, after: unit, m: i64) -> i64 {
            return n + m;
        }
        func main() -> i64 {
            return consume(nothing(), 40, nothing(), 2);
        }
        ",
    );
    let output = workspace.output("unit abi");

    assert_eq!(interpreted(&source), "42");
    if let Some(status) = build_and_run(&workspace, &source, &output) {
        assert_eq!(status, 42, "a `unit` argument must not shift the others");
    }
}

/// Every `.npt` example, so a newly added one is swept in automatically
/// rather than needing to be listed here.
fn every_example() -> Vec<String> {
    let dir = format!("{}/../examples", env!("CARGO_MANIFEST_DIR"));
    let mut names: Vec<String> = std::fs::read_dir(&dir)
        .expect("the examples directory must exist")
        .map(|entry| entry.expect("a readable directory entry").file_name())
        .map(|name| name.to_string_lossy().into_owned())
        .filter(|name| name.ends_with(".npt"))
        .collect();
    // Sorted so a failure names the same example run to run.
    names.sort();
    assert!(
        names.len() > 20,
        "the sweep must actually be finding the examples, found {}",
        names.len()
    );
    names
}

/// The seam an over-strict, or merely buggy, native pass would break:
/// a program `check` accepted must never be told it is malformed, and
/// must never be shown a code that describes a defect in the compiler
/// rather than a limit of the subset.
///
/// `A0019` means "this NIR never went through the verifier" and `A0020`
/// means "the backend broke"; ordinary compilation can produce neither,
/// and a user who wrote a perfectly good program must never see either.
/// The build must also never panic, and never exit with anything but
/// success or the ordinary diagnostic status.
#[test]
fn no_example_that_checks_cleanly_leaks_an_internal_native_diagnostic() {
    let workspace = Workspace::new("example-sweep");
    for name in every_example() {
        let path = example(&name);
        if !napitia(&["check", &path]).status.success() {
            continue;
        }
        let output = workspace.output(&name);
        let built = napitia(&["build", &path, "--output", as_str(&output)]);
        let err = stderr(&built);

        assert!(
            matches!(built.status.code(), Some(0) | Some(1)),
            "`{name}`: build exited {:?}\n{err}",
            built.status.code()
        );
        assert!(
            !err.contains("panicked") && !err.contains("RUST_BACKTRACE"),
            "`{name}`: the build panicked\n{err}"
        );
        assert!(
            !err.contains(codes::UNVERIFIED_NIR),
            "`{name}` passes `check`, so it must never be called unverified NIR\n{err}"
        );
        assert!(
            !err.contains(codes::CODEGEN_FAILED),
            "`{name}` passes `check`, so a backend defect must not be blamed on it\n{err}"
        );
        if built.status.code() == Some(1) {
            assert!(
                err.contains("error[A"),
                "`{name}`: a failed build must say why\n{err}"
            );
            assert!(
                !output.exists(),
                "`{name}`: a failed build must leave no executable"
            );
        }
    }
    assert!(workspace.leftover_build_directories().is_empty());
}

// -- the scalar ABI at its boundaries -------------------------------------
//
// `i64` is a signed two's-complement 64-bit integer in both execution
// paths (`rfcs/0015`), so the interesting inputs are the edges of that
// width, not small positive numbers where every plausible
// representation agrees.
//
// Each program decides for itself whether it is correct and returns a
// small marker, so the answer never travels through the exit status'
// own 8-bit narrowing. Every one is run through the interpreter as
// well: the assertion is that the two agree, not that the native side
// produced some number.

const MIN: &str = "-9223372036854775808";
const MAX: &str = "9223372036854775807";

#[test]
fn the_scalar_abi_agrees_with_the_interpreter_at_its_boundaries() {
    let cases: [(&str, String); 10] = [
        // Both boundaries survive a binding and a comparison.
        (
            "boundaries_round_trip",
            format!(
                "value lo: i64 = {MIN}; value hi: i64 = {MAX}; \
                 if lo == {MIN} {{ if hi == {MAX} {{ return 42; }} }} return 0;"
            ),
        ),
        // Arithmetic that reaches a boundary exactly, without leaving
        // it. A 64-bit representation is the only one where these hold.
        (
            "arithmetic_reaches_the_edges",
            format!(
                "value lo: i64 = {MIN}; value hi: i64 = {MAX}; \
                 if lo + 1 == -9223372036854775807 {{ \
                 if hi - 1 == 9223372036854775806 {{ \
                 if lo + hi == -1 {{ return 42; }} }} }} return 0;"
            ),
        ),
        // The one value whose negation is not an `i64` -- negating the
        // *other* boundary is fine, and this checks that the checked
        // path did not break the ordinary one.
        (
            "negation_of_the_maximum",
            format!(
                "value hi: i64 = {MAX}; if -hi == -9223372036854775807 {{ return 42; }} return 0;"
            ),
        ),
        // Multiplication that stays in range across the sign.
        (
            "multiplication_across_the_sign",
            format!(
                "value hi: i64 = {MAX}; \
                 if hi * -1 == -9223372036854775807 {{ \
                 if -1 * -1 == 1 {{ return 42; }} }} return 0;"
            ),
        ),
        // Ordering has to be signed across the sign boundary, not
        // unsigned over the same bits.
        (
            "signed_order",
            format!(
                "value lo: i64 = {MIN}; value hi: i64 = {MAX}; \
                 if lo < 0 {{ if 0 < hi {{ if lo < hi {{ if hi > lo {{ \
                 if lo <= lo {{ if hi >= hi {{ return 42; }} }} }} }} }} }} \
                 return 0;"
            ),
        ),
        // Bitwise work on the high bit, where a narrower representation
        // would quietly drop the bits that matter.
        (
            "high_bits",
            format!(
                "value lo: i64 = {MIN}; value hi: i64 = {MAX}; \
                 if (lo & hi) == 0 {{ if (lo | hi) == -1 {{ \
                 if (lo ^ hi) == -1 {{ if ~hi == lo {{ if ~lo == hi {{ \
                 return 42; }} }} }} }} }} return 0;"
            ),
        ),
        // A boundary value crossing a call, in and back out again.
        (
            "call_carries_boundaries",
            format!(
                "if echo({MIN}) == {MIN} {{ if echo({MAX}) == {MAX} {{ return 42; }} }} return 0;"
            ),
        ),
        // Eight `i64` arguments: past what the platform passes in
        // registers, so this exercises the stack half of the sequence.
        (
            "high_arity_call",
            format!(
                "if many({MIN}, {MAX}, 1, 0, 0, 0, 0, 0) == 0 {{ \
                 if many(1, 2, 3, 4, 5, 6, 7, 8) == 36 {{ return 42; }} }} return 0;"
            ),
        ),
        // `unit` occupies no ABI position, so a `unit` parameter in the
        // middle of a signature must not shift the ones after it.
        (
            "mixed_scalars",
            "if mixed(nothing(), true, 40, nothing(), 2) == 42 { \
             if mixed(nothing(), false, 40, nothing(), 2) == 0 { return 42; } } return 0;"
                .to_string(),
        ),
        // A boundary value carried through a mutable slot and a loop.
        (
            "slot_and_loop",
            format!(
                "mutable x: i64 = {MIN}; mutable i: i64 = 0; \
                 while i < 3 {{ x = x + 1; i = i + 1; }} \
                 if x == -9223372036854775805 {{ return 42; }} return 0;"
            ),
        ),
    ];

    const HELPERS: &str = "
        func echo(n: i64) -> i64 { return n; }
        func many(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64) -> i64 {
            return a + b + c + d + e + f + g + h;
        }
        func nothing() -> unit { return; }
        func mixed(before: unit, flag: bool, x: i64, between: unit, y: i64) -> i64 {
            if flag { return x + y; }
            return 0;
        }
    ";

    let workspace = Workspace::new("abi-boundaries");
    for (name, body) in cases {
        let source = workspace.source(name, &format!("{HELPERS}\nfunc main() -> i64 {{ {body} }}"));
        let output = workspace.output(name);

        assert_eq!(
            interpreted(&source),
            "42",
            "`{name}`: the interpreter must agree the program is correct"
        );
        if let Some(status) = build_and_run(&workspace, &source, &output) {
            assert_eq!(
                status, 42,
                "`{name}`: the native build must reach the same answer as the interpreter"
            );
        }
    }
}

/// `main`'s returned value reaches the process as its low 8 bits, which
/// is a language rule (`rfcs/0015`) and the one place a native run's
/// answer is *not* the Napitia value.
#[test]
fn the_exit_status_is_the_returned_value_modulo_256() {
    let workspace = Workspace::new("exit-status");
    for (name, body, status) in [
        ("zero", "return 0".to_string(), 0),
        ("small", "return 42".to_string(), 42),
        ("above_a_byte", "return 300".to_string(), 44),
        ("boundary_max", format!("return {MAX}"), 255),
        ("boundary_min", format!("return {MIN}"), 0),
        ("negative", "return -1".to_string(), 255),
    ] {
        let source = workspace.source(name, &format!("func main() -> i64 {{ {body} }}"));
        let output = workspace.output(name);
        if let Some(observed) = build_and_run(&workspace, &source, &output) {
            assert_eq!(observed, status, "`{name}`");
        }
    }
}

/// The high-arity case again, but with the arguments arriving in an
/// order only a correct sequence can reproduce: each parameter
/// contributes a distinct power, so a shifted or dropped argument
/// changes the sum.
#[test]
fn a_high_arity_call_places_every_argument_where_the_callee_expects_it() {
    let workspace = Workspace::new("abi-arity");
    let source = workspace.source(
        "positions",
        "
        func weigh(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64, i: i64) -> i64 {
            return a * 1 + b * 10 + c * 100 + d * 1000 + e * 10000
                 + f * 100000 + g * 1000000 + h * 10000000 + i * 100000000;
        }
        func main() -> i64 {
            if weigh(1, 2, 3, 4, 5, 6, 7, 8, 9) == 987654321 { return 42; }
            return 0;
        }
        ",
    );
    let output = workspace.output("positions");

    assert_eq!(interpreted(&source), "42");
    if let Some(status) = build_and_run(&workspace, &source, &output) {
        assert_eq!(status, 42);
    }
}

// -- runtime failures, in both execution paths ----------------------------
//
// An operation whose exact result is outside `i64` produces no value in
// either path (`rfcs/0015`). The interpreter reports it and exits 1; a
// built executable writes the same sentence to standard error and exits
// with the one documented runtime-failure status. Neither wraps, and
// neither leaves a Rust panic or a backtrace behind.

/// The status a Napitia runtime failure exits a built executable with.
/// Written out rather than imported, so a change to the constant has to
/// be a deliberate change to this documented contract too.
const RUNTIME_FAILURE_STATUS: i32 = 70;

/// What `napitia run` does with a program that fails at run time: the
/// exit status and everything it wrote to standard error.
fn interpreted_failure(source: &Path) -> (i32, String) {
    let output = napitia(&["run", as_str(source)]);
    let err = stderr(&output);
    assert!(
        !output.status.success(),
        "this program must fail at run time, but `run` succeeded"
    );
    assert!(
        !err.contains("panicked at") && !err.contains("RUST_BACKTRACE"),
        "a Napitia runtime failure is never a Rust panic:\n{err}"
    );
    (
        output.status.code().expect("`run` exits normally"),
        err.trim().to_string(),
    )
}

/// Builds `source` and runs it, reporting the executable's status and
/// standard error -- or `None` when this host cannot link, having first
/// asserted the exact refusal it gives instead.
fn build_and_capture(workspace: &Workspace, source: &Path, output: &Path) -> Option<(i32, String)> {
    let built = napitia(&["build", as_str(source), "--output", as_str(output)]);
    let expected = match classify_host(workspace) {
        Host::Links => {
            assert!(
                built.status.success(),
                "a GNU host with a matching linker must build:\n{}",
                stderr(&built)
            );
            let run = Command::new(output)
                .output()
                .expect("the built executable must be runnable");
            return Some((
                run.status.code().expect("the program exits normally"),
                String::from_utf8_lossy(&run.stderr).trim().to_string(),
            ));
        }
        Host::NoLinker => codes::LINKER_LAUNCH_FAILED,
        Host::WrongLinkerTarget => codes::LINKER_TARGET_MISMATCH,
        Host::Unsupported => codes::UNSUPPORTED_HOST,
    };
    assert_eq!(built.status.code(), Some(1));
    assert!(
        stderr(&built).contains(expected),
        "this host must refuse with {expected}:\n{}",
        stderr(&built)
    );
    assert!(
        !output.exists(),
        "a host that cannot link writes no executable"
    );
    None
}

/// Every overflow the native subset can produce, in both paths.
///
/// The interpreter is the reference: whatever it says the failure is,
/// the executable must say the same thing, in the same words.
const OVERFLOWS: [(&str, &str, &str); 5] = [
    (
        "add_overflows",
        "value m: i64 = 9223372036854775807; return m + 1",
        "integer overflow in `add`",
    ),
    (
        "add_underflows",
        "value m: i64 = -9223372036854775808; return m + -1",
        "integer overflow in `add`",
    ),
    (
        "sub_underflows",
        "value m: i64 = -9223372036854775808; return m - 1",
        "integer overflow in `sub`",
    ),
    (
        "mul_overflows",
        "value m: i64 = 9223372036854775807; return m * 2",
        "integer overflow in `mul`",
    ),
    (
        "neg_of_the_minimum",
        "value m: i64 = -9223372036854775808; return -m",
        "integer overflow in `neg`",
    ),
];

#[test]
fn an_overflow_fails_the_same_way_in_both_execution_paths() {
    let workspace = Workspace::new("overflow");
    for (name, body, category) in OVERFLOWS {
        let source = workspace.source(name, &format!("func main() -> i64 {{ {body} }}"));
        let output = workspace.output(name);

        let (interpreted_status, interpreted_error) = interpreted_failure(&source);
        assert_ne!(interpreted_status, 0, "`{name}`");
        assert!(
            interpreted_error.contains(category),
            "`{name}`: the interpreter must name the failure: {interpreted_error}"
        );

        let Some((status, error)) = build_and_capture(&workspace, &source, &output) else {
            continue;
        };
        assert_eq!(
            status, RUNTIME_FAILURE_STATUS,
            "`{name}`: a runtime failure has one documented status"
        );
        assert!(
            error.contains(category),
            "`{name}`: the executable must name the same failure: {error}"
        );
        assert!(
            !error.contains("panicked at") && !error.contains("RUST_BACKTRACE"),
            "`{name}`: no panic, no backtrace: {error}"
        );
        assert_eq!(
            error,
            format!("napitia: {interpreted_error}"),
            "`{name}`: the executable reports exactly what `run` reports, \
             prefixed only by its own name"
        );
    }
    assert!(workspace.leftover_build_directories().is_empty());
}

/// The same program, built and run twice, answers identically. The
/// failure path is generated code like any other, so it is held to the
/// same determinism rule.
#[test]
fn a_failing_program_answers_identically_on_every_run() {
    let workspace = Workspace::new("overflow-determinism");
    let source = workspace.source(
        "repeat",
        "func main() -> i64 { value m: i64 = 9223372036854775807; return m * 2 }",
    );
    let output = workspace.output("repeat");

    let first = interpreted_failure(&source);
    for _ in 0..3 {
        assert_eq!(interpreted_failure(&source), first);
    }

    let Some(native) = build_and_capture(&workspace, &source, &output) else {
        return;
    };
    for _ in 0..3 {
        let again = Command::new(&output)
            .output()
            .expect("the built executable must be runnable");
        assert_eq!(
            (
                again.status.code().expect("the program exits normally"),
                String::from_utf8_lossy(&again.stderr).trim().to_string(),
            ),
            native,
            "repeated runs of one executable must agree"
        );
    }
}

/// A successful program writes nothing to standard error, which is what
/// makes that stream -- rather than the exit status, whose every byte a
/// returned value can produce -- the discriminator for a failure.
#[test]
fn a_successful_program_writes_nothing_to_standard_error() {
    let workspace = Workspace::new("quiet-success");
    let source = workspace.source("quiet", "func main() -> i64 { return 70 }");
    let output = workspace.output("quiet");

    let Some((status, error)) = build_and_capture(&workspace, &source, &output) else {
        return;
    };
    assert_eq!(
        status, RUNTIME_FAILURE_STATUS,
        "this program returns exactly the runtime-failure status"
    );
    assert!(
        error.is_empty(),
        "and is still distinguishable, because it says nothing: {error}"
    );
}

/// The operators whose exceptional cases the native subset does not
/// implement are refused before code generation, on every host, rather
/// than compiled to something that behaves differently.
#[test]
fn the_operators_outside_the_native_subset_are_still_refused() {
    let workspace = Workspace::new("outside-subset");
    for (name, body) in [
        ("div", "value a: i64 = 9; value b: i64 = 2; return a / b"),
        ("rem", "value a: i64 = 9; value b: i64 = 2; return a % b"),
        ("shl", "value a: i64 = 1; value b: i64 = 2; return a << b"),
        ("shr", "value a: i64 = 4; value b: i64 = 2; return a >> b"),
    ] {
        let source = workspace.source(name, &format!("func main() -> i64 {{ {body} }}"));
        let output = workspace.output(name);
        let built = napitia(&["build", as_str(&source), "--output", as_str(&output)]);
        assert_eq!(built.status.code(), Some(1), "`{name}`");
        assert!(
            stderr(&built).contains(codes::UNSUPPORTED_OPERATOR),
            "`{name}`: must be refused as an unsupported operator:\n{}",
            stderr(&built)
        );
        assert!(!output.exists(), "`{name}`: a refused build writes nothing");
    }
    assert!(workspace.leftover_build_directories().is_empty());
}

/// A literal outside `i64` stops every command at the same diagnostic,
/// before NIR lowering or code generation can run, and does so
/// byte-identically twice in a row.
#[test]
fn an_out_of_range_literal_stops_every_command_identically() {
    let workspace = Workspace::new("literal-range");
    for (name, literal) in [
        ("too_high", "9223372036854775808"),
        ("too_low", "-9223372036854775809"),
    ] {
        let source = workspace.source(
            name,
            &format!("func main() -> i64 {{ value x: i64 = {literal}; return 0 }}"),
        );
        let output = workspace.output(name);

        let mut renderings = Vec::new();
        for command in ["check", "ir", "run"] {
            let result = napitia(&[command, as_str(&source)]);
            assert_eq!(result.status.code(), Some(1), "`{name}`/{command}");
            assert!(
                stdout(&result).is_empty(),
                "`{name}`/{command}: nothing is produced past the diagnostic"
            );
            assert!(
                stderr(&result).contains("T0073"),
                "`{name}`/{command}: {}",
                stderr(&result)
            );
            renderings.push(stderr(&result));
        }

        let built = napitia(&["build", as_str(&source), "--output", as_str(&output)]);
        assert_eq!(built.status.code(), Some(1), "`{name}`/build");
        assert!(stderr(&built).contains("T0073"), "{}", stderr(&built));
        assert!(
            !output.exists(),
            "`{name}`: no executable from a failed build"
        );
        renderings.push(stderr(&built));

        assert!(
            renderings.windows(2).all(|pair| pair[0] == pair[1]),
            "`{name}`: every command must stop at the identical diagnostic: {renderings:?}"
        );

        // Twice, byte for byte.
        assert_eq!(
            stderr(&napitia(&["check", as_str(&source)])),
            stderr(&napitia(&["check", as_str(&source)])),
            "`{name}`: repeated runs must render identically"
        );
    }
    assert!(workspace.leftover_build_directories().is_empty());
}

/// A numeric type with no execution semantics is refused the same way,
/// by every command.
#[test]
fn an_unimplemented_numeric_type_stops_every_command_identically() {
    let workspace = Workspace::new("numeric-type");
    let source = workspace.source(
        "unsupported",
        "func main() -> i64 { value x: u8 = 0; return 0 }",
    );
    let output = workspace.output("unsupported");

    let mut renderings = Vec::new();
    for command in ["check", "ir", "run"] {
        let result = napitia(&[command, as_str(&source)]);
        assert_eq!(result.status.code(), Some(1), "{command}");
        assert!(stderr(&result).contains("T0074"), "{}", stderr(&result));
        renderings.push(stderr(&result));
    }
    let built = napitia(&["build", as_str(&source), "--output", as_str(&output)]);
    assert_eq!(built.status.code(), Some(1));
    assert!(stderr(&built).contains("T0074"), "{}", stderr(&built));
    assert!(!output.exists());
    renderings.push(stderr(&built));

    assert!(
        renderings.windows(2).all(|pair| pair[0] == pair[1]),
        "every command must stop at the identical diagnostic: {renderings:?}"
    );
}

// -- overflow reached through control flow --------------------------------
//
// An overflow in `main`'s own straight-line body is the easy case. These
// put the failing operation behind a call, a loop and a branch, so the
// backend's failure path has to be correct in a block that is not the
// entry block and is not the only predecessor of what follows it.
//
// Every one is run through the interpreter first and the executable
// second, and the two are compared exactly -- status and stderr.

/// Programs whose overflow is reached only through control flow. Each
/// returns a value on the path that does *not* fail, so a build that
/// simply never failed would be caught by the success case too.
const CONTROL_FLOW_OVERFLOWS: [(&str, &str, &str); 6] = [
    (
        "nested_call",
        "func bump(n: i64) -> i64 { return n + 1; } \
         func main() -> i64 { return bump(9223372036854775807); }",
        "integer overflow in `add`",
    ),
    (
        "twice_nested_call",
        "func inner(n: i64) -> i64 { return n * 2; } \
         func middle(n: i64) -> i64 { return inner(n); } \
         func main() -> i64 { return middle(9223372036854775807); }",
        "integer overflow in `mul`",
    ),
    (
        "loop_body",
        "func main() -> i64 { \
           mutable x: i64 = 9223372036854775800; \
           mutable i: i64 = 0; \
           while i < 100 { x = x + 1; i = i + 1; } \
           return x; }",
        "integer overflow in `add`",
    ),
    (
        "loop_counter_negation",
        "func main() -> i64 { \
           mutable x: i64 = -9223372036854775808; \
           mutable i: i64 = 0; \
           while i < 3 { x = -x; i = i + 1; } \
           return x; }",
        "integer overflow in `neg`",
    ),
    (
        "taken_branch",
        "func main() -> i64 { \
           value chosen: bool = true; \
           value m: i64 = -9223372036854775808; \
           if chosen { return m - 1; } \
           return 7; }",
        "integer overflow in `sub`",
    ),
    (
        "branch_inside_a_call",
        "func pick(flag: bool, n: i64) -> i64 { if flag { return n + 1; } return 0; } \
         func main() -> i64 { return pick(true, 9223372036854775807); }",
        "integer overflow in `add`",
    ),
];

#[test]
fn an_overflow_reached_through_control_flow_fails_identically_in_both_paths() {
    let workspace = Workspace::new("overflow-control-flow");
    for (name, program, category) in CONTROL_FLOW_OVERFLOWS {
        let source = workspace.source(name, program);
        let output = workspace.output(name);

        let (interpreted_status, interpreted_error) = interpreted_failure(&source);
        assert_eq!(
            interpreted_status, 1,
            "`{name}`: `run` reports failure as 1"
        );
        assert!(
            interpreted_error.contains(category),
            "`{name}`: the interpreter must name the failure: {interpreted_error}"
        );

        let Some((status, error)) = build_and_capture(&workspace, &source, &output) else {
            continue;
        };
        assert_eq!(
            status, RUNTIME_FAILURE_STATUS,
            "`{name}`: a runtime failure has one documented status"
        );
        assert_eq!(
            error,
            format!("napitia: {interpreted_error}"),
            "`{name}`: the executable must report exactly what `run` reports"
        );
        assert!(
            !error.contains("panicked at") && !error.contains("RUST_BACKTRACE"),
            "`{name}`: {error}"
        );
    }
    assert!(workspace.leftover_build_directories().is_empty());
}

/// The same shapes, on the path that does *not* overflow: a build whose
/// failure path was always taken, or never taken, fails one of these.
#[test]
fn the_same_control_flow_shapes_succeed_when_nothing_overflows() {
    let workspace = Workspace::new("control-flow-success");
    for (name, program, expected) in [
        (
            "nested_call_ok",
            "func bump(n: i64) -> i64 { return n + 1; } \
             func main() -> i64 { if bump(41) == 42 { return 42; } return 0; }",
            42,
        ),
        (
            "loop_ok",
            "func main() -> i64 { \
               mutable x: i64 = 9223372036854775800; \
               mutable i: i64 = 0; \
               while i < 7 { x = x + 1; i = i + 1; } \
               if x == 9223372036854775807 { return 42; } \
               return 0; }",
            42,
        ),
        (
            "untaken_branch_ok",
            "func main() -> i64 { \
               value chosen: bool = false; \
               value m: i64 = 9223372036854775807; \
               if chosen { return m + 1; } \
               return 42; }",
            42,
        ),
        (
            "negation_of_the_maximum_ok",
            "func main() -> i64 { \
               value m: i64 = 9223372036854775807; \
               if -m == -9223372036854775807 { return 42; } \
               return 0; }",
            42,
        ),
    ] {
        let source = workspace.source(name, program);
        let output = workspace.output(name);

        assert_eq!(
            interpreted(&source),
            expected.to_string(),
            "`{name}`: the interpreter must reach the answer"
        );
        if let Some(status) = build_and_run(&workspace, &source, &output) {
            assert_eq!(status, expected, "`{name}`");
        }
    }
    assert!(workspace.leftover_build_directories().is_empty());
}

/// Multiplication across every sign combination, at magnitudes that
/// stay in range and at magnitudes that do not. A sign error in the
/// overflow test would show up here rather than in a single case.
#[test]
fn multiplication_agrees_on_every_sign_combination() {
    let workspace = Workspace::new("multiplication-signs");

    let ok = workspace.source(
        "signs_ok",
        "func main() -> i64 { \
           if 3 * 4 == 12 { if -3 * 4 == -12 { if 3 * -4 == -12 { if -3 * -4 == 12 { \
           return 42; } } } } return 0; }",
    );
    let ok_output = workspace.output("signs_ok");
    assert_eq!(interpreted(&ok), "42");
    if let Some(status) = build_and_run(&workspace, &ok, &ok_output) {
        assert_eq!(status, 42);
    }

    for (name, body, category) in [
        (
            "positive_times_positive",
            "value m: i64 = 9223372036854775807; return m * 2",
            "integer overflow in `mul`",
        ),
        (
            "negative_times_positive",
            "value m: i64 = -9223372036854775808; return m * 2",
            "integer overflow in `mul`",
        ),
        (
            "negative_times_negative",
            "value m: i64 = -9223372036854775808; value n: i64 = -1; return m * n",
            "integer overflow in `mul`",
        ),
        (
            "positive_times_negative",
            "value m: i64 = 9223372036854775807; value n: i64 = -2; return m * n",
            "integer overflow in `mul`",
        ),
    ] {
        let source = workspace.source(name, &format!("func main() -> i64 {{ {body} }}"));
        let output = workspace.output(name);
        let (_, interpreted_error) = interpreted_failure(&source);
        assert!(interpreted_error.contains(category), "`{name}`");
        if let Some((status, error)) = build_and_capture(&workspace, &source, &output) {
            assert_eq!(status, RUNTIME_FAILURE_STATUS, "`{name}`");
            assert_eq!(error, format!("napitia: {interpreted_error}"), "`{name}`");
        }
    }
    assert!(workspace.leftover_build_directories().is_empty());
}

/// The operations the native backend does not implement are refused
/// with `A0009`, deterministically, and are *not* claimed to have
/// native parity -- the interpreter runs them and the backend does not.
#[test]
fn operations_outside_native_capability_are_a0009_and_still_interpret() {
    let workspace = Workspace::new("a0009-boundary");
    for (name, body, interpreted_answer) in [
        (
            "div",
            "value a: i64 = 9; value b: i64 = 2; return a / b",
            "4",
        ),
        (
            "rem",
            "value a: i64 = 9; value b: i64 = 2; return a % b",
            "1",
        ),
        (
            "shl",
            "value a: i64 = 1; value b: i64 = 4; return a << b",
            "16",
        ),
        (
            "shr",
            "value a: i64 = 16; value b: i64 = 2; return a >> b",
            "4",
        ),
    ] {
        let source = workspace.source(name, &format!("func main() -> i64 {{ {body} }}"));
        let output = workspace.output(name);

        // The interpreter is the complete execution path and runs it.
        assert_eq!(interpreted(&source), interpreted_answer, "`{name}`");

        // The backend refuses it, by name, on every host, twice
        // identically.
        let first = napitia(&["build", as_str(&source), "--output", as_str(&output)]);
        assert_eq!(first.status.code(), Some(1), "`{name}`");
        assert!(
            stderr(&first).contains(codes::UNSUPPORTED_OPERATOR),
            "`{name}`: must be A0009:\n{}",
            stderr(&first)
        );
        assert!(!output.exists(), "`{name}`: a refused build writes nothing");
        let second = napitia(&["build", as_str(&source), "--output", as_str(&output)]);
        assert_eq!(
            stderr(&first),
            stderr(&second),
            "`{name}`: the refusal must be byte-identical across runs"
        );
    }
    assert!(workspace.leftover_build_directories().is_empty());
}

/// `f64` is outside the native subset too, and is refused for its type
/// rather than silently compiled as something else. Which code depends
/// on where the float is: `main`'s own result is the entry point's
/// business, a float anywhere else is the type rule's.
#[test]
fn a_float_program_is_refused_by_the_native_backend_but_still_interprets() {
    let workspace = Workspace::new("float-boundary");
    for (name, program, answer, expected) in [
        (
            "float_result",
            "func main() -> f64 { value x: f64 = 1.5; return x + 0.5 }",
            "2",
            codes::ENTRY_RETURN_TYPE,
        ),
        (
            "float_local",
            "func main() -> i64 { value x: f64 = 1.5; if x > 1.0 { return 42; } return 0 }",
            "42",
            codes::UNSUPPORTED_TYPE,
        ),
    ] {
        let source = workspace.source(name, program);
        let output = workspace.output(name);

        // The interpreter is the complete execution path and runs it.
        assert_eq!(interpreted(&source), answer, "`{name}`");

        let built = napitia(&["build", as_str(&source), "--output", as_str(&output)]);
        assert_eq!(built.status.code(), Some(1), "`{name}`");
        assert!(
            stderr(&built).contains(expected),
            "`{name}`: must be refused with {expected}:\n{}",
            stderr(&built)
        );
        assert!(!output.exists(), "`{name}`");
    }
    assert!(workspace.leftover_build_directories().is_empty());
}
