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

use compiler::native::{codes, host_can_link};

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

/// Whether a C compiler driver is actually installed. A Linux host
/// without one is a real configuration, and the build says so with its
/// own code rather than pretending it linked.
fn linker_installed() -> bool {
    Command::new("cc")
        .arg("--version")
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
}

/// What this host can do with a native build, so each test can assert
/// the one right outcome instead of skipping.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Host {
    /// x86_64 Linux with a C toolchain: builds produce executables.
    Links,
    /// x86_64 Linux with no `cc` on PATH.
    NoLinker,
    /// Anything else: the object is generated, linking is not possible.
    WrongTarget,
}

fn host() -> Host {
    if !host_can_link() {
        Host::WrongTarget
    } else if linker_installed() {
        Host::Links
    } else {
        Host::NoLinker
    }
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
fn build_and_run(source: &Path, output: &Path) -> Option<i32> {
    let built = napitia(&["build", as_str(source), "--output", as_str(output)]);
    match host() {
        Host::Links => {
            assert!(
                built.status.success(),
                "the build must succeed on this host:\n{}",
                stderr(&built)
            );
            assert!(output.is_file(), "the executable must exist");
            let run = Command::new(output)
                .output()
                .expect("the built executable must be runnable");
            Some(run.status.code().expect("the program exits normally"))
        }
        Host::NoLinker => {
            assert_eq!(built.status.code(), Some(1));
            assert!(
                stderr(&built).contains(codes::LINKER_LAUNCH_FAILED),
                "{}",
                stderr(&built)
            );
            assert!(!output.exists());
            None
        }
        Host::WrongTarget => {
            assert_eq!(built.status.code(), Some(1));
            assert!(
                stderr(&built).contains(codes::UNSUPPORTED_HOST),
                "{}",
                stderr(&built)
            );
            assert!(!output.exists());
            None
        }
    }
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
    if let Some(status) = build_and_run(&source, &output) {
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
    if let Some(status) = build_and_run(&source, &output) {
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
        if let Some(status) = build_and_run(&source, &output) {
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
    if let Some(status) = build_and_run(&source, &output) {
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
    if let Some(status) = build_and_run(&source, &output) {
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

    if build_and_run(&source, &first).is_none() {
        return;
    }
    build_and_run(&source, &second).expect("the second build must also link");

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
    assert!(!output.exists(), "a failed link writes no executable");
    assert!(
        workspace.leftover_build_directories().is_empty(),
        "the build directory must be removed even when the linker fails"
    );
}

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
    let output = workspace.output("program");
    std::fs::write(&output, b"a previous build").expect("could not seed the output");

    let source = workspace.source("bad", "func main() -> i64 { value a = 1; return a / a; }");
    let built = napitia(&["build", as_str(&source), "--output", as_str(&output)]);
    assert_eq!(built.status.code(), Some(1));
    assert_eq!(
        std::fs::read(&output).expect("the previous output is still there"),
        b"a previous build"
    );
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
    if let Some(status) = build_and_run(&source, &output) {
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
