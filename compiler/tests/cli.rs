//! End-to-end tests for the `napitia` CLI, exercising the actual built
//! binary (not the driver functions directly) so exit codes and
//! stdout/stderr separation are covered as a real user would see them.

use std::process::{Command, Output};

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/{name}", env!("CARGO_MANIFEST_DIR"))
}

fn example(name: &str) -> String {
    format!("{}/../examples/{name}", env!("CARGO_MANIFEST_DIR"))
}

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

#[test]
fn help_prints_usage_and_succeeds() {
    let output = napitia(&["--help"]);
    assert!(output.status.success());
    assert!(stdout(&output).contains("Usage: napitia"));
}

#[test]
fn no_arguments_prints_usage_and_succeeds() {
    let output = napitia(&[]);
    assert!(output.status.success());
    assert!(stdout(&output).contains("Usage: napitia"));
}

#[test]
fn version_prints_a_version_and_succeeds() {
    let output = napitia(&["--version"]);
    assert!(output.status.success());
    assert!(stdout(&output).contains("napitia"));
}

#[test]
fn missing_file_argument_is_a_usage_error_for_lex_and_parse() {
    for command in ["lex", "parse"] {
        let output = napitia(&[command]);
        assert_eq!(
            output.status.code(),
            Some(2),
            "`{command}` should require a path"
        );
        assert!(stderr(&output).contains("missing"));
    }
}

#[test]
fn run_with_no_path_defaults_to_the_current_directory_as_a_project() {
    // `check`/`ir`/`run` accept an omitted path and default to the
    // current directory, treating it as a project rather than requiring
    // a `.npt` file. The test binary's working directory has no
    // `napitia.toml`, so this must fail with an M0001 diagnostic rather
    // than a usage error -- the important thing is it no longer treats
    // a missing argument as a usage error for these three commands.
    let output = napitia(&["run"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("M0001"));
}

#[test]
fn unreadable_file_is_a_usage_error() {
    let output = napitia(&["run", "does/not/exist.npt"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(stderr(&output).contains("could not read"));
}

#[test]
fn extra_arguments_are_a_usage_error_not_silently_ignored() {
    for args in [
        vec!["lex", &fixture("valid.npt"), "extra"],
        vec!["parse", &fixture("valid.npt"), "extra"],
        vec!["check", &fixture("valid.npt"), "extra"],
        vec!["ir", &fixture("valid.npt"), "extra"],
        vec!["run", &fixture("valid.npt"), "extra"],
    ] {
        let output = napitia(&args);
        assert_eq!(
            output.status.code(),
            Some(2),
            "`{args:?}` should reject the unexpected extra argument"
        );
        assert!(
            stderr(&output).contains("unexpected extra argument"),
            "`{args:?}` produced: {}",
            stderr(&output)
        );
    }
}

#[test]
fn unknown_command_is_a_usage_error() {
    let output = napitia(&["frobnicate", &fixture("valid.npt")]);
    assert_eq!(output.status.code(), Some(2));
    assert!(stderr(&output).contains("unknown command"));
}

#[test]
fn lex_succeeds_on_a_valid_file() {
    let output = napitia(&["lex", &fixture("valid.npt")]);
    assert!(output.status.success());
    assert!(stdout(&output).contains("Func"));
}

#[test]
fn parse_prints_an_ast_for_a_valid_file() {
    let output = napitia(&["parse", &fixture("valid.npt")]);
    assert!(output.status.success());
    assert!(stdout(&output).contains("FunctionDecl"));
}

#[test]
fn check_reports_no_errors_for_a_valid_file() {
    let output = napitia(&["check", &fixture("valid.npt")]);
    assert!(output.status.success());
    assert!(stdout(&output).contains("no errors"));
}

#[test]
fn check_reports_a_syntax_diagnostic_with_exit_code_one() {
    let output = napitia(&["check", &fixture("invalid_syntax.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[P0001]"));
}

#[test]
fn check_reports_a_type_diagnostic_with_exit_code_one() {
    let output = napitia(&["check", &fixture("invalid_types.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0001]"));
}

#[test]
fn ir_prints_nir_for_a_valid_file() {
    let output = napitia(&["ir", &fixture("valid.npt")]);
    assert!(output.status.success());
    assert!(stdout(&output).contains("func @main"));
    assert!(stdout(&output).contains("func @add"));
}

#[test]
fn textual_nir_names_a_variant_local_by_its_declaration_not_its_case() {
    // A local's declared type in textual NIR (`alloc.<ty>`) must show the
    // variant's own name (`LookupResult`), never the case it happened to
    // be constructed through (`Found`) -- `Ty::Named` must always carry
    // the declaration's own symbol.
    let output = napitia(&["ir", &fixture("variant_type_display_name.npt")]);
    assert!(output.status.success(), "ir failed: {}", stderr(&output));
    let text = stdout(&output);
    assert!(
        text.contains("alloc.LookupResult"),
        "expected the variant's own name in textual NIR: {text}"
    );
    assert!(
        !text.contains("alloc.Found") && !text.contains("alloc.Missing"),
        "textual NIR leaked a case name as a type: {text}"
    );
}

#[test]
fn ir_reports_diagnostics_instead_of_running_for_an_invalid_file() {
    let output = napitia(&["ir", &fixture("invalid_types.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0001]"));
}

#[test]
fn run_executes_main_and_prints_its_result() {
    let output = napitia(&["run", &fixture("valid.npt")]);
    assert!(output.status.success());
    assert_eq!(stdout(&output).trim(), "42");
}

#[test]
fn run_reports_diagnostics_for_an_invalid_file() {
    let output = napitia(&["run", &fixture("invalid_syntax.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(!stderr(&output).is_empty());
}

/// Runs `check`, `ir`, and `run` on the same fixture and asserts every
/// stage succeeds and never surfaces an internal `V`-coded verifier
/// diagnostic, since that would mean typeck and lowering disagreed
/// about a program that was accepted.
fn assert_pipeline_is_clean_and_returns(fixture_name: &str, expected_run_output: &str) {
    let path = fixture(fixture_name);

    let checked = napitia(&["check", &path]);
    assert!(
        checked.status.success(),
        "check failed: {}",
        stderr(&checked)
    );
    assert!(!stdout(&checked).contains("error["));

    let ired = napitia(&["ir", &path]);
    assert!(ired.status.success(), "ir failed: {}", stderr(&ired));
    assert!(
        !stdout(&ired).contains("V0"),
        "leaked internal diagnostic: {}",
        stdout(&ired)
    );

    let ran = napitia(&["run", &path]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), expected_run_output);
}

#[test]
fn a_diverging_while_condition_leaves_no_orphan_block_and_returns_unit() {
    assert_pipeline_is_clean_and_returns("diverging_while_condition.npt", "()");
}

#[test]
fn an_if_without_an_else_is_unit_typed_and_discards_its_value() {
    assert_pipeline_is_clean_and_returns("if_without_else_is_unit.npt", "()");
}

#[test]
fn never_join_result_does_not_depend_on_which_branch_diverges() {
    assert_pipeline_is_clean_and_returns("never_join_then_diverges.npt", "2");
    assert_pipeline_is_clean_and_returns("never_join_else_diverges.npt", "2");
}

#[test]
fn never_propagates_through_a_strict_unary_operand() {
    assert_pipeline_is_clean_and_returns("never_through_unary.npt", "7");
}

#[test]
fn never_propagates_through_a_strict_comparison_operand() {
    assert_pipeline_is_clean_and_returns("never_through_comparison.npt", "7");
}

#[test]
fn never_propagates_through_an_assignments_right_hand_side() {
    assert_pipeline_is_clean_and_returns("never_through_assignment.npt", "7");
}

#[test]
fn a_value_carrying_break_is_rejected_at_every_stage() {
    let path = fixture("value_carrying_break.npt");
    for command in ["check", "ir", "run"] {
        let output = napitia(&[command, &path]);
        assert_eq!(output.status.code(), Some(1), "`{command}` should fail");
        assert!(
            stderr(&output).contains("T0007"),
            "`{command}` should report T0007, got: {}",
            stderr(&output)
        );
    }
}

#[test]
fn a_named_aggregate_return_type_now_lowers_and_runs_successfully() {
    // Alpha 0.1.1: records have a real aggregate runtime representation,
    // so a named type in a function signature is no longer rejected --
    // it lowers, verifies, and runs cleanly through every stage.
    assert_pipeline_is_clean_and_returns("named_aggregate_return_type.npt", "42");
}

/// The example program from RFC 0005 / this milestone's requirements:
/// records, a variant payload, field access, and an exhaustive match,
/// all the way through `run`.
#[test]
fn records_and_variants_example_runs_end_to_end() {
    let path = format!(
        "{}/../examples/records_and_variants.npt",
        env!("CARGO_MANIFEST_DIR")
    );

    let checked = napitia(&["check", &path]);
    assert!(
        checked.status.success(),
        "check failed: {}",
        stderr(&checked)
    );

    let ired = napitia(&["ir", &path]);
    assert!(ired.status.success(), "ir failed: {}", stderr(&ired));
    assert!(
        !stdout(&ired).contains("V0"),
        "leaked internal diagnostic: {}",
        stdout(&ired)
    );

    let ran = napitia(&["run", &path]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "42");
}

#[test]
fn missing_record_field_is_a_diagnostic() {
    let output = napitia(&["check", &fixture("missing_record_field.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[R0009]"));
}

#[test]
fn unknown_record_field_is_a_diagnostic() {
    let output = napitia(&["check", &fixture("unknown_record_field.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[R0008]"));
}

#[test]
fn field_mutation_is_a_diagnostic() {
    let output = napitia(&["check", &fixture("field_mutation.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0015]"));
}

#[test]
fn non_exhaustive_match_reports_a_concrete_missing_pattern() {
    let output = napitia(&["check", &fixture("non_exhaustive_match.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0017]"));
    assert!(stderr(&output).contains("LookupResult.Missing"));
}

#[test]
fn unreachable_match_arm_is_a_diagnostic() {
    let output = napitia(&["check", &fixture("unreachable_match_arm.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0018]"));
}

#[test]
fn unreachable_arm_with_a_different_result_type_reports_only_the_unreachable_diagnostic() {
    // The unreachable second arm's body (`false`, a bool) would
    // mismatch the reachable first arm's body (`1`, an i64) if it were
    // joined into the match's result type -- it must not be: only the
    // unreachable-arm diagnostic is expected, never an additional
    // "match arms must have the same type" diagnostic on top of it.
    let output = napitia(&[
        "check",
        &fixture("unreachable_arm_result_type_mismatch.npt"),
    ]);
    assert_eq!(output.status.code(), Some(1));
    let err = stderr(&output);
    assert!(err.contains("error[T0018]"));
    assert!(!err.contains("error[T0001]"));
    assert_eq!(err.matches("error[").count(), 1);
}

#[test]
fn infinite_aggregate_layout_is_a_diagnostic() {
    let output = napitia(&["check", &fixture("infinite_aggregate_layout.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0020]"));
}

/// Every invalid fixture above must fail at `check` already -- `ir`/
/// `run` must never be reached for a program `check` already rejected,
/// and neither may ever leak an internal `Ixxxx`/`Vxxxx` diagnostic for
/// these ordinary, user-triggerable errors.
#[test]
fn invalid_aggregate_fixtures_fail_at_check_with_no_leaked_internal_diagnostic() {
    for name in [
        "missing_record_field.npt",
        "unknown_record_field.npt",
        "field_mutation.npt",
        "non_exhaustive_match.npt",
        "unreachable_match_arm.npt",
        "unreachable_arm_result_type_mismatch.npt",
        "infinite_aggregate_layout.npt",
    ] {
        let path = fixture(name);
        let output = napitia(&["check", &path]);
        assert_eq!(output.status.code(), Some(1), "`{name}` should fail check");
        let err = stderr(&output);
        assert!(
            !err.contains("I0") && !err.contains("V0"),
            "`{name}` leaked an internal diagnostic: {err}"
        );
    }
}

/// A pattern nested far past the compiler's structural depth limit,
/// generated here rather than committed as a giant fixture file. Every
/// stage that could ever see it (parsing, then -- if it somehow got
/// past that -- checking, IR lowering, and running) must terminate
/// with an ordinary diagnostic and a non-zero exit code, never a panic,
/// a Rust backtrace, or a hang.
#[test]
fn deeply_nested_pattern_terminates_diagnostically_at_every_stage() {
    let depth = 300;
    let mut pattern = "Leaf".to_string();
    for _ in 0..depth {
        pattern = format!("Wrap({pattern})");
    }
    let source = format!(
        "variant Rec {{ Wrap(Rec), Leaf }}\n\
         func f(x: Rec) -> i64 {{ return match x {{ {pattern} => 1, _ => 0 }} }}\n\
         func main() -> i64 {{ return 0 }}\n"
    );
    let path =
        std::env::temp_dir().join(format!("napitia_deep_pattern_{}.npt", std::process::id()));
    std::fs::write(&path, &source).expect("failed to write the temp fixture");
    let path_str = path.to_string_lossy().into_owned();

    for cmd in ["check", "ir", "run"] {
        let output = napitia(&[cmd, &path_str]);
        assert!(
            !output.status.success(),
            "`{cmd}` unexpectedly succeeded on a pattern nested {depth} levels deep"
        );
        assert_ne!(
            output.status.code(),
            None,
            "`{cmd}` was killed by a signal (likely a stack overflow), not a clean exit"
        );
        let err = stderr(&output);
        assert!(
            !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
            "`{cmd}` panicked instead of reporting a diagnostic: {err}"
        );
    }

    let _ = std::fs::remove_file(&path);
}

/// Expressions nested far past the parser's own nesting bound, one
/// shape per grammar recursion, generated here rather than committed as
/// giant fixture files.
///
/// Each of these used to abort the process with a native stack overflow
/// -- no diagnostic, no error code, nothing on stderr -- because every
/// stage after the parser walks the expression tree on the call stack.
/// The exit code is asserted exactly: a stack overflow on Windows exits
/// with a status code too (`0xC0000409`), so "not a signal" is not
/// enough to tell the two apart, while "exit 1 and a P0001 on stderr"
/// is.
///
/// The size of stderr is asserted as well. A refused expression resumes
/// mid-construct, so every surplus token can produce its own follow-on
/// syntax error; on a chain this long that is tens of thousands of
/// diagnostics, each re-rendering the same tens-of-kilobytes source
/// line, which is slow enough to be indistinguishable from a hang.
#[test]
fn deeply_nested_expressions_terminate_diagnostically_at_every_stage() {
    let depth = 20_000;
    let cases = [
        (
            "parentheses",
            format!(
                "func main() -> i64 {{ return {}1{}; }}\n",
                "(".repeat(depth),
                ")".repeat(depth)
            ),
        ),
        (
            "blocks",
            format!(
                "func main() -> i64 {{ return {}1{}; }}\n",
                "{".repeat(depth),
                "}".repeat(depth)
            ),
        ),
        (
            "unary operators",
            format!("func main() -> i64 {{ return {}1; }}\n", "-".repeat(depth)),
        ),
        (
            "a binary fold",
            format!(
                "func main() -> i64 {{ return 1{}; }}\n",
                " + 1".repeat(depth)
            ),
        ),
        (
            "a postfix fold",
            format!(
                "func g() -> i64 {{ return 0; }}\nfunc main() -> i64 {{ return g{}; }}\n",
                "()".repeat(depth)
            ),
        ),
        (
            "an assignment chain",
            format!(
                "func main() -> i64 {{ mutable a = 0; a {}= 1; return a; }}\n",
                "= a ".repeat(depth)
            ),
        ),
        (
            "an else-if chain",
            format!(
                "func main() -> i64 {{ if false {{ return 0; }}{} else {{ return 1; }} }}\n",
                " else if false { return 0; }".repeat(depth)
            ),
        ),
    ];

    for (index, (what, source)) in cases.iter().enumerate() {
        let path = std::env::temp_dir().join(format!(
            "napitia_deep_expr_{}_{index}.npt",
            std::process::id()
        ));
        std::fs::write(&path, source).expect("failed to write the temp fixture");
        let path_str = path.to_string_lossy().into_owned();

        for cmd in ["check", "ir", "run"] {
            let output = napitia(&[cmd, &path_str]);
            let err = stderr(&output);
            assert_eq!(
                output.status.code(),
                Some(1),
                "`{cmd}` on {what} nested {depth} deep did not exit with a diagnostic status: {err}"
            );
            assert!(
                err.contains("P0001") && err.contains("nested too deeply"),
                "`{cmd}` on {what} did not report the depth diagnostic: {err}"
            );
            assert!(
                !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
                "`{cmd}` on {what} panicked instead of reporting a diagnostic: {err}"
            );
            assert!(
                err.len() < 1_000_000,
                "`{cmd}` on {what} produced {} bytes of diagnostics for one defect",
                err.len()
            );
        }

        let _ = std::fs::remove_file(&path);
    }
}

/// One Napitia call frame is one native interpreter frame, so recursion
/// used to be bounded by whatever stack the platform handed the main
/// thread -- roughly 25 frames in a debug build on Windows -- and
/// exceeding it aborted the process: no diagnostic, no usable exit code,
/// nothing on stderr, while `check` and `ir` on the very same file
/// succeeded. Both halves of the repair are asserted here, because
/// either alone still fails: enough stack to make ordinary recursion
/// work, and a depth budget so a recursion that never unwinds ends in an
/// ordinary runtime error rather than further out on the same cliff.
#[test]
fn recursion_runs_to_a_real_depth_and_then_reports_rather_than_aborting() {
    let program = |depth: i64| {
        format!(
            "func down(n: i64) -> i64 {{\n\
             \x20   if n <= 0 {{ return 0; }}\n\
             \x20   return down(n - 1) + 1;\n\
             }}\n\
             func main() -> i64 {{ return down({depth}); }}\n"
        )
    };
    let path = std::env::temp_dir().join(format!("napitia_recursion_{}.npt", std::process::id()));

    // Deep enough that the platform's own default main-thread stack
    // could not have carried it.
    std::fs::write(&path, program(400)).expect("failed to write the temp fixture");
    let path_str = path.to_string_lossy().into_owned();
    let deep = napitia(&["run", &path_str]);
    assert!(
        deep.status.success(),
        "400 frames of ordinary recursion should run: {}",
        stderr(&deep)
    );
    assert_eq!(stdout(&deep).trim(), "400");

    // Past the budget: a runtime error, not an abort.
    std::fs::write(&path, program(100_000)).expect("failed to write the temp fixture");
    let over = napitia(&["run", &path_str]);
    assert_eq!(
        over.status.code(),
        Some(1),
        "a recursion past the budget did not exit with a runtime-error status: {}",
        stderr(&over)
    );
    let err = stderr(&over);
    assert!(
        err.contains("call depth exceeded"),
        "expected the call-depth diagnostic, got: {err}"
    );
    assert!(
        !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
        "the depth budget panicked instead of reporting: {err}"
    );

    // A recursion that never terminates at all ends the same way, rather
    // than running until something outside the program stops it.
    let endless = "func forever(n: i64) -> i64 { return forever(n + 1); }\n\
                   func main() -> i64 { return forever(0); }\n";
    std::fs::write(&path, endless).expect("failed to write the temp fixture");
    let looped = napitia(&["run", &path_str]);
    assert_eq!(
        looped.status.code(),
        Some(1),
        "an unterminated recursion did not exit with a runtime-error status: {}",
        stderr(&looped)
    );
    assert!(stderr(&looped).contains("call depth exceeded"));

    let _ = std::fs::remove_file(&path);
}

/// `check`, `ir` and `run` must agree about what they accept. A type
/// nested this deep compiled cleanly and then aborted the process at
/// run time, which is the sharpest possible form of that disagreement:
/// two stages said yes and the third did not say anything at all.
#[test]
fn a_deeply_nested_generic_value_runs_as_cleanly_as_it_checks() {
    let depth = 60;
    let mut source = String::from("resource File { descriptor: i64 }\nrecord Box[T] { item: T }\n");
    source.push_str("func w0() -> File { return File { descriptor: 1 }; }\n");
    let mut ty = String::from("File");
    for level in 1..=depth {
        source.push_str(&format!(
            "func w{level}() -> Box[{ty}] {{ return Box[{ty}] {{ item: w{} }}; }}\n",
            format_args!("{}()", level - 1)
        ));
        ty = format!("Box[{ty}]");
    }
    source.push_str(&format!(
        "func main() -> i64 {{\n    value b = w{depth}();\n    return 0;\n}}\n"
    ));

    let path = std::env::temp_dir().join(format!("napitia_deep_value_{}.npt", std::process::id()));
    std::fs::write(&path, &source).expect("failed to write the temp fixture");
    let path_str = path.to_string_lossy().into_owned();

    for cmd in ["check", "ir", "run"] {
        let output = napitia(&[cmd, &path_str]);
        assert!(
            output.status.success(),
            "`{cmd}` failed on a value nested {depth} levels deep: {}",
            stderr(&output)
        );
    }

    let _ = std::fs::remove_file(&path);
}

// -- Generics (`rfcs/0008`) ---------------------------------------------

/// A generic body writes its own constructions symbolically
/// (`record.create @Box[Box[T]]`), and the value it builds must carry
/// the instantiation actually running, not the parameter. Keeping the
/// parameter made the value's declared field types resolve to
/// `Ty::Param` while the value stored there was concrete, so this
/// program checked and lowered cleanly and was then refused at run time
/// for a shape disagreement it does not have.
#[test]
fn a_generic_body_constructing_a_nested_generic_runs_as_cleanly_as_it_checks() {
    let source = "record Box[T] { item: T }\n\
                  variant Pair[T] { Both(Box[T]), Neither }\n\
                  func depth[T](x: Box[T]) -> i64 {\n\
                  \x20   value nested = Box[Box[T]] { item: x };\n\
                  \x20   value tagged = Pair[Box[T]].Both(nested);\n\
                  \x20   return match tagged { Both(_) => 1, Neither => 0 };\n\
                  }\n\
                  func main() -> i64 { return depth[i64](Box[i64] { item: 7 }); }\n";
    let path =
        std::env::temp_dir().join(format!("napitia_generic_frame_{}.npt", std::process::id()));
    std::fs::write(&path, source).expect("failed to write the temp fixture");
    let path_str = path.to_string_lossy().into_owned();

    for cmd in ["check", "ir"] {
        let output = napitia(&[cmd, &path_str]);
        assert!(
            output.status.success(),
            "`{cmd}` failed: {}",
            stderr(&output)
        );
    }
    let ran = napitia(&["run", &path_str]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "1");

    let _ = std::fs::remove_file(&path);
}

/// A generic function whose own type argument grows on every call names
/// an instantiation that never converges. It must end in the depth
/// diagnostic that actually describes it, not in a shape error about a
/// disagreement the program does not have.
#[test]
fn an_endlessly_growing_instantiation_reports_its_depth() {
    let source = "record Box[T] { item: T }\n\
                  func f[T](x: Box[T]) -> i64 { return g[Box[T]](Box[Box[T]] { item: x }); }\n\
                  func g[T](x: Box[T]) -> i64 { return f[T](x); }\n\
                  func main() -> i64 { return f[i64](Box[i64] { item: 1 }); }\n";
    let path =
        std::env::temp_dir().join(format!("napitia_generic_grow_{}.npt", std::process::id()));
    std::fs::write(&path, source).expect("failed to write the temp fixture");
    let path_str = path.to_string_lossy().into_owned();

    let ran = napitia(&["run", &path_str]);
    assert_eq!(
        ran.status.code(),
        Some(1),
        "an unbounded instantiation did not exit with a runtime-error status: {}",
        stderr(&ran)
    );
    let err = stderr(&ran);
    assert!(
        err.contains("nested more deeply"),
        "expected the nesting-depth diagnostic, got: {err}"
    );
    assert!(
        !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
        "an unbounded instantiation panicked instead of reporting: {err}"
    );

    let _ = std::fs::remove_file(&path);
}

#[test]
fn generic_identity_check_ir_and_run_all_succeed() {
    let path = fixture("generic_identity.npt");
    assert!(napitia(&["check", &path]).status.success());
    assert!(napitia(&["ir", &path]).status.success());
    let ran = napitia(&["run", &path]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "42");
}

#[test]
fn generic_box_check_ir_and_run_all_succeed() {
    let path = fixture("generic_box.npt");
    assert!(napitia(&["check", &path]).status.success());
    assert!(napitia(&["ir", &path]).status.success());
    let ran = napitia(&["run", &path]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "42");
}

#[test]
fn generic_maybe_exhaustive_match_check_ir_and_run_all_succeed() {
    let path = fixture("generic_maybe_exhaustive.npt");
    assert!(napitia(&["check", &path]).status.success());
    assert!(napitia(&["ir", &path]).status.success());
    let ran = napitia(&["run", &path]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "1");
}

#[test]
fn generic_arity_mismatch_is_a_diagnostic() {
    let output = napitia(&["check", &fixture("generic_arity_mismatch.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0024]"));
}

#[test]
fn generic_inference_conflict_is_a_diagnostic() {
    let output = napitia(&["check", &fixture("generic_inference_conflict.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0026]") || stderr(&output).contains("error[T0025]"));
}

#[test]
fn generic_infinite_layout_is_a_diagnostic() {
    let output = napitia(&["check", &fixture("generic_infinite_layout.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0020]"));
}

/// Every invalid generic fixture above must fail at `check` already, and
/// never leak an internal `Ixxxx`/`Vxxxx` diagnostic for these ordinary,
/// user-triggerable errors.
#[test]
fn invalid_generic_fixtures_fail_at_check_with_no_leaked_internal_diagnostic() {
    for name in [
        "generic_arity_mismatch.npt",
        "generic_inference_conflict.npt",
        "generic_infinite_layout.npt",
    ] {
        let path = fixture(name);
        let output = napitia(&["check", &path]);
        assert_eq!(output.status.code(), Some(1), "`{name}` should fail check");
        let err = stderr(&output);
        assert!(
            !err.contains("I0") && !err.contains("V0"),
            "`{name}` leaked an internal diagnostic: {err}"
        );
    }
}

/// A generic type application nested far past
/// `crate::limits::MAX_GENERIC_DEPTH`, generated here rather than
/// committed as a giant fixture file. Every stage that could ever parse
/// it must terminate with an ordinary diagnostic and a non-zero exit
/// code, never a panic, a Rust backtrace, or a hang.
#[test]
fn deeply_nested_generic_type_application_terminates_diagnostically() {
    let depth = 200;
    let mut ty = "i64".to_string();
    for _ in 0..depth {
        ty = format!("Box[{ty}]");
    }
    let source = format!(
        "record Box[T] {{ payload: T }}\n\
         func f(x: {ty}) -> i64 {{ return 0 }}\n\
         func main() -> i64 {{ return 0 }}\n"
    );
    let path =
        std::env::temp_dir().join(format!("napitia_deep_generic_{}.npt", std::process::id()));
    std::fs::write(&path, &source).expect("failed to write the temp fixture");
    let path_str = path.to_string_lossy().into_owned();

    for cmd in ["check", "ir", "run"] {
        let output = napitia(&[cmd, &path_str]);
        assert!(
            !output.status.success(),
            "`{cmd}` unexpectedly succeeded on a type nested {depth} levels deep"
        );
        assert_ne!(
            output.status.code(),
            None,
            "`{cmd}` was killed by a signal (likely a stack overflow), not a clean exit"
        );
        let err = stderr(&output);
        assert!(
            !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
            "`{cmd}` panicked instead of reporting a diagnostic: {err}"
        );
    }

    let _ = std::fs::remove_file(&path);
}

// -- Capability protocols (`rfcs/0009`) -----------------------------------

/// Every valid protocol example must `check`, `ir`, and `run` cleanly,
/// leaking no internal `Vxxxx` diagnostic, and return exactly the given
/// value.
fn assert_protocol_example_runs(name: &str, expected_run_output: &str) {
    let path = example(name);

    let checked = napitia(&["check", &path]);
    assert!(
        checked.status.success(),
        "check failed for {name}: {}",
        stderr(&checked)
    );

    let ired = napitia(&["ir", &path]);
    assert!(
        ired.status.success(),
        "ir failed for {name}: {}",
        stderr(&ired)
    );
    assert!(
        !stdout(&ired).contains("V0"),
        "{name} leaked an internal diagnostic: {}",
        stdout(&ired)
    );

    let ran = napitia(&["run", &path]);
    assert!(
        ran.status.success(),
        "run failed for {name}: {}",
        stderr(&ran)
    );
    assert_eq!(stdout(&ran).trim(), expected_run_output);
}

#[test]
fn protocol_equal_example_runs_end_to_end() {
    assert_protocol_example_runs("protocol_equal.npt", "true");
}

#[test]
fn protocol_conditional_extension_example_runs_end_to_end() {
    assert_protocol_example_runs("protocol_conditional_extension.npt", "true");
}

#[test]
fn protocol_generic_forwarding_example_runs_end_to_end() {
    assert_protocol_example_runs("protocol_generic_forwarding.npt", "true");
}

#[test]
fn protocol_missing_capability_example_is_t0039() {
    let output = napitia(&["check", &example("protocol_missing_capability_invalid.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0039]"));
}

#[test]
fn protocol_overlap_example_is_t0037() {
    let output = napitia(&["check", &example("protocol_overlap_invalid.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0037]"));
}

#[test]
fn protocol_invalid_method_signature_example_is_t0034() {
    let output = napitia(&[
        "check",
        &example("protocol_invalid_method_signature_invalid.npt"),
    ]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0034]"));
}

#[test]
fn protocol_entry_main_capability_example_is_t0045() {
    let output = napitia(&[
        "check",
        &example("protocol_entry_main_capability_invalid.npt"),
    ]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0045]"));
}

/// Every invalid protocol example above must fail at every stage
/// (`check`, `ir`, `run`), with a non-zero exit code and no leaked
/// internal (`Ixxxx`/`Vxxxx`) diagnostic, and deterministic output
/// across two runs.
#[test]
fn invalid_protocol_examples_fail_at_every_stage_with_no_leaked_internal_diagnostic() {
    for name in [
        "protocol_missing_capability_invalid.npt",
        "protocol_overlap_invalid.npt",
        "protocol_invalid_method_signature_invalid.npt",
        "protocol_entry_main_capability_invalid.npt",
    ] {
        let path = example(name);
        for cmd in ["check", "ir", "run"] {
            let first = napitia(&[cmd, &path]);
            assert_eq!(
                first.status.code(),
                Some(1),
                "`{cmd}` on `{name}` should fail with exit code 1"
            );
            let err = stderr(&first);
            assert!(
                !err.contains("I0") && !err.contains("V0"),
                "`{cmd}` on `{name}` leaked an internal diagnostic: {err}"
            );
            assert!(
                !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
                "`{cmd}` on `{name}` panicked instead of reporting a diagnostic: {err}"
            );

            let second = napitia(&[cmd, &path]);
            assert_eq!(
                stderr(&first),
                stderr(&second),
                "`{cmd}` on `{name}` was not deterministic across two runs"
            );
        }
    }
}

// -- Typed outcomes (`rfcs/0010`) ------------------------------------

/// Every valid raises example must `check`, `ir`, and `run` cleanly,
/// leaking no internal `Vxxxx` diagnostic, and return exactly the given
/// value.
fn assert_raises_example_runs(name: &str, expected_run_output: &str) {
    let path = example(name);

    let checked = napitia(&["check", &path]);
    assert!(
        checked.status.success(),
        "check failed for {name}: {}",
        stderr(&checked)
    );

    let ired = napitia(&["ir", &path]);
    assert!(
        ired.status.success(),
        "ir failed for {name}: {}",
        stderr(&ired)
    );
    assert!(
        !stdout(&ired).contains("V0"),
        "{name} leaked an internal diagnostic: {}",
        stdout(&ired)
    );

    let ran = napitia(&["run", &path]);
    assert!(
        ran.status.success(),
        "run failed for {name}: {}",
        stderr(&ran)
    );
    assert_eq!(stdout(&ran).trim(), expected_run_output);
}

#[test]
fn raises_basic_example_runs_end_to_end() {
    assert_raises_example_runs("raises_basic.npt", "default");
}

#[test]
fn raises_exhaustive_handler_example_runs_end_to_end() {
    assert_raises_example_runs("raises_exhaustive_handler.npt", "36");
}

/// A generic fallible function's own `Invoke` must substitute its own
/// success slot's type through the call site's own concrete type
/// arguments -- a regression test for a bug Fix 6's own new coverage
/// found: an unsubstituted symbolic `Ty::Param` success slot leaked
/// V0032/V0066/V0008 from `ir`/`run` even though `check` accepted the
/// program cleanly.
#[test]
fn raises_generic_fallible_function_example_runs_end_to_end() {
    assert_raises_example_runs("raises_generic_fallible_function.npt", "42");
}

#[test]
fn raises_non_exhaustive_handler_example_is_t0053() {
    let output = napitia(&[
        "check",
        &example("raises_non_exhaustive_handler_invalid.npt"),
    ]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("error[T0053]"));
}

/// A `raises` entry naming a generic variant is rejected at the
/// frontend (R0030), at every stage, with no leaked internal (`Ixxxx`/
/// `Vxxxx`) diagnostic and no panic (generic error variants are
/// explicitly out of scope, `rfcs/0010`).
#[test]
fn raises_generic_variant_example_is_r0030_at_every_stage_with_no_leaked_internal_diagnostic() {
    let path = example("raises_generic_variant_invalid.npt");
    for cmd in ["check", "ir", "run"] {
        let output = napitia(&[cmd, &path]);
        assert_eq!(
            output.status.code(),
            Some(1),
            "`{cmd}` should fail with exit code 1"
        );
        let err = stderr(&output);
        assert!(
            err.contains("error[R0030]"),
            "`{cmd}` should report R0030: {err}"
        );
        assert!(
            !err.contains("I0") && !err.contains("V0"),
            "`{cmd}` leaked an internal diagnostic: {err}"
        );
        assert!(
            !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
            "`{cmd}` panicked instead of reporting a diagnostic: {err}"
        );
    }
}

/// An `extend` method declaring its own `raises` clause is rejected at
/// the frontend (R0031), at every stage, with no leaked internal
/// (`Ixxxx`/`Vxxxx`) diagnostic and no panic -- protocol methods have no
/// raised-effect signature yet (`rfcs/0010`).
#[test]
fn raises_extend_method_example_is_r0031_at_every_stage_with_no_leaked_internal_diagnostic() {
    let path = example("raises_extend_method_invalid.npt");
    for cmd in ["check", "ir", "run"] {
        let output = napitia(&[cmd, &path]);
        assert_eq!(
            output.status.code(),
            Some(1),
            "`{cmd}` should fail with exit code 1"
        );
        let err = stderr(&output);
        assert!(
            err.contains("error[R0031]"),
            "`{cmd}` should report R0031: {err}"
        );
        assert!(
            !err.contains("I0") && !err.contains("V0"),
            "`{cmd}` leaked an internal diagnostic: {err}"
        );
        assert!(
            !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
            "`{cmd}` panicked instead of reporting a diagnostic: {err}"
        );
    }
}

/// Every valid resource example (`rfcs/0011`) must `check`, `ir`, and
/// `run` cleanly, leaking no internal `Vxxxx` diagnostic, and return
/// exactly the given value.
fn assert_resource_example_runs(name: &str, expected_run_output: &str) {
    let path = example(name);

    let checked = napitia(&["check", &path]);
    assert!(
        checked.status.success(),
        "check failed for {name}: {}",
        stderr(&checked)
    );

    let ired = napitia(&["ir", &path]);
    assert!(
        ired.status.success(),
        "ir failed for {name}: {}",
        stderr(&ired)
    );
    assert!(
        !stdout(&ired).contains("V0"),
        "{name} leaked an internal diagnostic: {}",
        stdout(&ired)
    );
    // Two independent `ir` runs must produce byte-identical output.
    let ired_again = napitia(&["ir", &path]);
    assert_eq!(
        stdout(&ired),
        stdout(&ired_again),
        "{name}'s own NIR is not deterministic across repeated runs"
    );

    let ran = napitia(&["run", &path]);
    assert!(
        ran.status.success(),
        "run failed for {name}: {}",
        stderr(&ran)
    );
    assert_eq!(stdout(&ran).trim(), expected_run_output);
}

#[test]
fn resource_basic_example_runs_end_to_end() {
    assert_resource_example_runs("resource_basic.npt", "3");
}

#[test]
fn resource_move_example_runs_end_to_end() {
    assert_resource_example_runs("resource_move.npt", "7");
}

#[test]
fn resource_defer_example_runs_end_to_end() {
    assert_resource_example_runs("resource_defer.npt", "9");
}

#[test]
fn resource_match_return_example_runs_end_to_end() {
    assert_resource_example_runs("resource_match_return.npt", "4");
}

#[test]
fn resource_defer_break_example_runs_end_to_end() {
    assert_resource_example_runs("resource_defer_break.npt", "6");
}

#[test]
fn resource_if_observed_example_runs_end_to_end() {
    assert_resource_example_runs("resource_if_observed.npt", "5");
}

#[test]
fn resource_handle_return_example_runs_end_to_end() {
    assert_resource_example_runs("resource_handle_return.npt", "99");
}

#[test]
fn resource_raise_cleanup_example_runs_end_to_end() {
    assert_resource_example_runs("resource_raise_cleanup.npt", "5");
}

#[test]
fn resource_handle_cleanup_example_runs_end_to_end() {
    assert_resource_example_runs("resource_handle_cleanup.npt", "4");
}

#[test]
fn resource_nested_example_runs_end_to_end() {
    assert_resource_example_runs("resource_nested.npt", "3");
}

#[test]
fn resource_field_move_example_runs_end_to_end() {
    assert_resource_example_runs("resource_field_move.npt", "20");
}

#[test]
fn resource_partial_drop_example_runs_end_to_end() {
    assert_resource_example_runs("resource_partial_drop.npt", "0");
}

#[test]
fn resource_field_reinitialize_example_runs_end_to_end() {
    assert_resource_example_runs("resource_field_reinitialize.npt", "5");
}

/// Assigning a place to itself, as a whole binding and as one
/// structural field. The right-hand side moves the value out and the
/// assignment puts the same value straight back, so nothing is
/// discarded -- and every stage has to agree, since an overwrite check
/// that looked only at the destination would call it a leak.
#[test]
fn resource_self_assignment_example_runs_end_to_end() {
    assert_resource_example_runs("resource_self_assignment.npt", "7");
}

#[test]
fn resource_variant_payload_example_runs_end_to_end() {
    assert_resource_example_runs("resource_variant_payload.npt", "8");
}

/// Each invalid resource example is rejected at `check` with its own
/// exact code, and every stage that runs it agrees, with no leaked
/// internal (`Ixxxx`/`Vxxxx`) diagnostic and no panic.
fn assert_resource_example_rejected(name: &str, code: &str) {
    let path = example(name);
    for cmd in ["check", "ir", "run"] {
        let output = napitia(&[cmd, &path]);
        assert_eq!(
            output.status.code(),
            Some(1),
            "`{cmd}` should fail with exit code 1 for {name}"
        );
        let err = stderr(&output);
        assert!(
            err.contains(&format!("error[{code}]")),
            "`{cmd}` should report {code} for {name}: {err}"
        );
        assert!(
            !err.contains("I0") && !err.contains("V0"),
            "`{cmd}` leaked an internal diagnostic for {name}: {err}"
        );
        assert!(
            !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
            "`{cmd}` panicked instead of reporting a diagnostic for {name}: {err}"
        );
        // The same invalid program must produce byte-identical output
        // across two independent runs: no `HashMap` iteration order may
        // reach a user-visible diagnostic (`rfcs/0012`).
        let again = napitia(&[cmd, &path]);
        assert_eq!(
            err,
            stderr(&again),
            "`{cmd}`'s own diagnostics for {name} are not deterministic across repeated runs"
        );
    }
}

#[test]
fn resource_invalid_use_after_move_example_is_u0001_at_every_stage() {
    assert_resource_example_rejected("resource_invalid_use_after_move.npt", "U0001");
}

#[test]
fn resource_invalid_double_drop_example_is_u0003_at_every_stage() {
    assert_resource_example_rejected("resource_invalid_double_drop.npt", "U0003");
}

#[test]
fn resource_invalid_escape_example_is_u0005_at_every_stage() {
    assert_resource_example_rejected("resource_invalid_escape.npt", "U0005");
}

#[test]
fn resource_invalid_generic_take_example_is_t0065_at_every_stage() {
    assert_resource_example_rejected("resource_invalid_generic_take.npt", "T0065");
}

#[test]
fn resource_invalid_parent_after_partial_move_example_is_u0014_at_every_stage() {
    assert_resource_example_rejected("resource_invalid_parent_after_partial_move.npt", "U0014");
}

#[test]
fn resource_invalid_live_field_overwrite_example_is_u0010_at_every_stage() {
    assert_resource_example_rejected("resource_invalid_live_field_overwrite.npt", "U0010");
}

#[test]
fn resource_invalid_field_double_drop_example_is_u0003_at_every_stage() {
    assert_resource_example_rejected("resource_invalid_field_double_drop.npt", "U0003");
}

// -- Alpha 0.1.8 structural ownership repairs (`rfcs/0012`) -------------
//
// Every example below is one of the blockers the first Alpha 0.1.8
// review rejected the milestone for, exercised end to end through the
// real binary: `check` accepts it, `ir` produces deterministic NIR with
// no leaked verifier code, and `run` produces the value that proves each
// affine identity was transferred or destroyed exactly once.

#[test]
fn resource_wildcard_payload_example_runs_end_to_end() {
    assert_resource_example_runs("resource_wildcard_payload.npt", "1");
}

#[test]
fn resource_wildcard_partial_payload_example_runs_end_to_end() {
    assert_resource_example_runs("resource_wildcard_partial_payload.npt", "11");
}

#[test]
fn resource_mixed_nesting_example_runs_end_to_end() {
    assert_resource_example_runs("resource_mixed_nesting.npt", "82");
}

#[test]
fn resource_generic_aggregate_example_runs_end_to_end() {
    assert_resource_example_runs("resource_generic_aggregate.npt", "69");
}

#[test]
fn resource_generic_variant_payload_example_runs_end_to_end() {
    assert_resource_example_runs("resource_generic_variant_payload.npt", "5");
}

#[test]
fn resource_defer_field_example_runs_end_to_end() {
    assert_resource_example_runs("resource_defer_field.npt", "2");
}

#[test]
fn resource_field_drop_example_runs_end_to_end() {
    assert_resource_example_runs("resource_field_drop.npt", "2");
}

#[test]
fn resource_structural_exits_example_runs_end_to_end() {
    assert_resource_example_runs("resource_structural_exits.npt", "5");
}

#[test]
fn resource_invalid_local_double_drop_example_is_u0003_at_every_stage() {
    assert_resource_example_rejected("resource_invalid_local_double_drop.npt", "U0003");
}

/// One call handing the same resource to an observing and a `take`
/// parameter. The taken parameter may destroy it anywhere in the body
/// while the observation stays readable, and no signature says which
/// order the body uses -- so every stage refuses the pairing.
///
/// Reported as `U0015` at every stage because the pipeline stops at the
/// first one that refuses; the NIR verifier's own independent answer
/// (`V0101`) is exercised on hand-built NIR, which never passes through
/// the source checker at all.
#[test]
fn resource_invalid_mixed_observe_take_example_is_u0015_at_every_stage() {
    assert_resource_example_rejected("resource_invalid_mixed_observe_take.npt", "U0015");
}

/// The same alias with the observing argument spelled as an `if`.
///
/// The compound spelling is what makes it a distinct regression: an
/// argument that is neither a bare local nor a field chain has no single
/// place, and reading that as "names nothing" let this reach the
/// interpreter as a stale handle after both earlier stages had accepted
/// it.
#[test]
fn resource_invalid_compound_mixed_alias_example_is_u0015_at_every_stage() {
    assert_resource_example_rejected("resource_invalid_compound_mixed_alias.npt", "U0015");
}

#[test]
fn resource_invalid_defer_parent_drop_example_is_u0004_at_every_stage() {
    assert_resource_example_rejected("resource_invalid_defer_parent_drop.npt", "U0004");
}

/// The field-level double drop reports the *field* as double-dropped,
/// not merely the generic whole-local diagnostic a local extracted out
/// of that field first would produce -- the two examples exist side by
/// side precisely so a regression collapsing one into the other is
/// visible.
#[test]
fn the_field_and_local_double_drop_examples_name_their_own_target() {
    let field = stderr(&napitia(&[
        "check",
        &example("resource_invalid_field_double_drop.npt"),
    ]));
    assert!(
        field.contains("drop session.input;"),
        "the field double drop must be reported against the field itself: {field}"
    );
    let local = stderr(&napitia(&[
        "check",
        &example("resource_invalid_local_double_drop.npt"),
    ]));
    assert!(
        local.contains("drop input;"),
        "the local double drop must be reported against the local: {local}"
    );
}

#[test]
fn resource_structural_drop_example_runs_end_to_end() {
    assert_resource_example_runs("resource_structural_drop.npt", "0");
}

/// `drop` still refuses a value that owns nothing at all -- extending it
/// to every transitively affine value must not quietly turn it into a
/// no-op accepted on any expression.
#[test]
fn dropping_a_value_that_owns_no_resource_is_still_t0061() {
    let output = napitia(&["check", &fixture("drop_non_affine_invalid.npt")]);
    assert_eq!(output.status.code(), Some(1));
    assert!(
        stderr(&output).contains("error[T0061]"),
        "expected T0061: {}",
        stderr(&output)
    );
}

#[test]
fn resource_partial_sibling_access_example_runs_end_to_end() {
    assert_resource_example_runs("resource_partial_sibling_access.npt", "13");
}

/// The advice `U0014` gives must actually work: a partially moved
/// aggregate stays usable for an unaffected field (affine or not), and
/// only using it as a *whole* value is rejected. A regression that
/// widened the whole-value rule back over ordinary field reads would
/// make the diagnostic's own suggestion impossible to follow.
#[test]
fn a_partially_moved_parent_still_permits_what_u0014_suggests() {
    let ok = napitia(&["check", &example("resource_partial_sibling_access.npt")]);
    assert!(
        ok.status.success(),
        "reading an unaffected field of a partially moved parent must stay legal: {}",
        stderr(&ok)
    );
    let rejected = napitia(&[
        "check",
        &example("resource_invalid_parent_after_partial_move.npt"),
    ]);
    assert_eq!(rejected.status.code(), Some(1));
    assert!(stderr(&rejected).contains("error[U0014]"));
}

// -- Alpha 0.1.8 generic runtime ownership (`rfcs/0008`, `rfcs/0012`) ---
//
// A runtime aggregate carries its own concrete type arguments, so
// destroying one asks what *this instantiation* owns rather than what
// its declaration's symbolic parameter owns. Both examples destroy
// generic aggregates as a whole, which is the shape that reaches the
// runtime's own structural drop -- and the shape under which a
// discarded type argument leaks silently.

#[test]
fn resource_generic_whole_drop_example_runs_end_to_end() {
    assert_resource_example_runs("resource_generic_whole_drop.npt", "14");
}

#[test]
fn resource_generic_nested_ownership_example_runs_end_to_end() {
    assert_resource_example_runs("resource_generic_nested_ownership.npt", "0");
}

/// Textual NIR carries each construction's own concrete type arguments,
/// which is what the interpreter reads them back from -- a regression
/// dropping them from the printed form would mean they were dropped
/// from the instruction too.
#[test]
fn textual_nir_shows_a_generic_constructions_type_arguments() {
    let output = napitia(&["ir", &example("resource_generic_whole_drop.npt")]);
    assert!(output.status.success(), "ir failed: {}", stderr(&output));
    let text = stdout(&output);
    assert!(
        text.contains("record.create @Box") && text.contains("[File"),
        "expected a generic record construction to print its type arguments: {text}"
    );
    assert!(
        text.contains("variant.create @Maybe") && text.contains("[File"),
        "expected a generic variant construction to print its type arguments: {text}"
    );
}

/// A malformed program whose parser recovery produces a self-referential
/// layout must terminate. `typeck::cycles` rejects it as an infinite
/// layout, but checking never stops at the first error, so `resourceck`
/// still walks the same HIR -- and its own place decomposition has to
/// bound the infinite place tree that layout describes rather than
/// descending it forever.
#[test]
fn a_recovered_self_referential_layout_terminates_instead_of_hanging() {
    for cmd in ["check", "ir", "run"] {
        let output = napitia(&[cmd, &fixture("cyclic_recovery_hang_invalid.npt")]);
        assert_eq!(
            output.status.code(),
            Some(1),
            "`{cmd}` should reject the recovered cyclic layout"
        );
        let err = stderr(&output);
        assert!(
            err.contains("error["),
            "`{cmd}` should report a diagnostic: {err}"
        );
        assert!(
            !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
            "`{cmd}` panicked: {err}"
        );
    }
}

// -- Alpha 0.1.8 path-sensitive variant ownership (`rfcs/0012`) ---------
//
// Variant ownership is per *path*: one branch may destroy the whole
// value while a disjoint branch takes it apart and owns the payload, and
// neither may suppress or discharge the other's obligations.

#[test]
fn resource_branch_local_variant_example_runs_end_to_end() {
    assert_resource_example_runs("resource_branch_local_variant.npt", "36");
}

#[test]
fn resource_variant_decomposition_example_runs_end_to_end() {
    assert_resource_example_runs("resource_variant_decomposition.npt", "134");
}

// Observation is transitive: an ordinary parameter is a call-scoped view
// of a value the caller still owns, and so is every field reached
// through it.

#[test]
fn resource_observed_aggregate_example_runs_end_to_end() {
    assert_resource_example_runs("resource_observed_aggregate.npt", "31");
}

/// Moving a field out of an observed aggregate is refused by `check`
/// itself -- not by the verifier after `check` already accepted it.
#[test]
fn resource_invalid_observed_field_move_example_is_rejected() {
    assert_resource_example_rejected("resource_invalid_observed_field_move.npt", "U0005");
}

// -- Lexically scoped observations (`rfcs/0013`) ----------------------
//
// `observe <place> as <name> { ... }`: the same read-only capability an
// ordinary parameter already carried, with the extent written down by
// the author instead of implied by a call.

#[test]
fn resource_observe_scope_example_runs_end_to_end() {
    assert_resource_example_runs("resource_observe_scope.npt", "17");
}

#[test]
fn resource_observe_nested_example_runs_end_to_end() {
    assert_resource_example_runs("resource_observe_nested.npt", "5");
}

#[test]
fn resource_observe_siblings_example_runs_end_to_end() {
    assert_resource_example_runs("resource_observe_siblings.npt", "18");
}

#[test]
fn resource_observe_failure_example_runs_end_to_end() {
    assert_resource_example_runs("resource_observe_failure.npt", "125");
}

/// Moving the ancestor of an observed place is refused by `check`
/// itself -- not by the verifier after `check` already accepted it.
#[test]
fn resource_invalid_observe_move_example_is_rejected() {
    assert_resource_example_rejected("resource_invalid_observe_move.npt", "U0017");
}

#[test]
fn resource_invalid_observe_drop_example_is_rejected() {
    assert_resource_example_rejected("resource_invalid_observe_drop.npt", "U0017");
}

#[test]
fn resource_invalid_observe_escape_example_is_rejected() {
    assert_resource_example_rejected("resource_invalid_observe_escape.npt", "U0016");
}

#[test]
fn resource_invalid_observe_defer_example_is_rejected() {
    assert_resource_example_rejected("resource_invalid_observe_defer.npt", "U0016");
}

#[test]
fn resource_invalid_observe_non_affine_example_is_rejected() {
    assert_resource_example_rejected("resource_invalid_observe_non_affine.npt", "T0070");
}

/// Textual NIR shows an observation's own boundaries explicitly -- the
/// begin, its place, and the matching end -- rather than leaving them
/// implicit in a lowering-side map or a use count.
#[test]
fn textual_nir_shows_explicit_observation_boundaries() {
    let output = napitia(&["ir", &example("resource_observe_scope.npt")]);
    assert!(output.status.success(), "ir failed: {}", stderr(&output));
    let text = stdout(&output);
    assert!(
        text.contains("observe.place @obs"),
        "expected an explicit observation begin in textual NIR: {text}"
    );
    assert!(
        text.contains("end.observe @obs"),
        "expected an explicit observation end in textual NIR: {text}"
    );
    // Three scopes across the two functions, each begun and ended once.
    assert_eq!(
        text.matches("observe.place @obs").count(),
        text.matches("end.observe @obs").count(),
        "every begin must have exactly one matching end: {text}"
    );
}

/// Every exit out of an observation block emits its own end -- and the
/// end always precedes the ownership cleanup on that same edge, because
/// that cleanup is precisely what an active observation forbids.
#[test]
fn textual_nir_ends_an_observation_before_the_cleanup_on_the_same_edge() {
    let output = napitia(&["ir", &example("resource_observe_failure.npt")]);
    assert!(output.status.success(), "ir failed: {}", stderr(&output));
    let text = stdout(&output);
    let lines: Vec<&str> = text.lines().collect();
    for (index, line) in lines.iter().enumerate() {
        if !line.trim_start().starts_with("drop ") {
            continue;
        }
        // Walk back to the nearest observation instruction: if it is a
        // begin rather than an end, this drop runs inside a live scope.
        let preceding = lines[..index].iter().rev().find(|earlier| {
            earlier.contains("observe.place @obs") || earlier.contains("end.observe @obs")
        });
        if let Some(earlier) = preceding {
            assert!(
                !earlier.contains("observe.place @obs"),
                "a drop follows a begin with no intervening end: {text}"
            );
        }
    }
}

/// Textual NIR shows the decomposition explicitly, on the arm's own
/// path -- the ownership event a function-global consumption scan used
/// to stand in for.
#[test]
fn textual_nir_shows_variant_decomposition_on_the_claiming_path() {
    let output = napitia(&["ir", &example("resource_branch_local_variant.npt")]);
    assert!(output.status.success(), "ir failed: {}", stderr(&output));
    let text = stdout(&output);
    assert!(
        text.contains("decompose "),
        "expected an explicit decomposition in textual NIR: {text}"
    );
    // The branch that drops the whole value must not decompose it.
    assert!(
        text.contains("drop "),
        "expected the sibling branch's whole-value drop: {text}"
    );
}

// -- Cross-stage ownership agreement (`rfcs/0011`, `rfcs/0012`) -------
//
// The three stages each reconstruct ownership independently -- the
// source checker from HIR, `nir::verify` from NIR alone, the interpreter
// from runtime values -- and that independence is the point: each is a
// backstop for the others rather than a restatement. What it must never
// become is disagreement. A program the source checker accepts must not
// then be rejected downstream for ownership, and the internal `Vxxxx`
// family must never reach a user who wrote a program `check` accepted.

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

/// A source `check` accepted must never be rejected by `ir` afterwards,
/// and `ir` must never leak an internal diagnostic.
///
/// `ir` is where `nir::verify` runs, so this is the exact seam an
/// over-strict NIR ownership rule would break: a false positive there
/// shows up as a program that checks cleanly and then fails to compile,
/// blaming the user for a defect in the verifier.
#[test]
fn no_example_that_checks_cleanly_is_rejected_by_ir() {
    for name in every_example() {
        let path = example(&name);
        if !napitia(&["check", &path]).status.success() {
            continue;
        }
        let ired = napitia(&["ir", &path]);
        let err = stderr(&ired);
        assert!(
            ired.status.success(),
            "`{name}` passes `check` but `ir` rejected it: {err}"
        );
        assert!(
            !err.contains("V0") && !err.contains("I0"),
            "`ir` leaked an internal diagnostic for `{name}`, which `check` had accepted: {err}"
        );
    }
}

/// The same seam one stage further on: a source `check` accepted must
/// never have the *interpreter* reject it for ownership, and must never
/// see an internal `Vxxxx`/`Ixxxx` code either.
///
/// `run` may still legitimately fail -- a `main` that raises is a real
/// program outcome, not a defect -- so this asserts what must never
/// happen rather than demanding success: no ownership rejection, no
/// internal diagnostic, no panic.
#[test]
fn no_example_that_checks_cleanly_is_rejected_by_run_for_ownership() {
    // The vocabulary the ownership backstops use when they refuse
    // something. Any of these reaching a user whose program `check`
    // accepted means the stages disagree.
    let ownership_refusals = [
        "undestroyed resource",
        "merely-observing resource handle",
        "already dropped",
        "stale resource handle",
        "still owns an undestroyed resource",
        "same resource identity",
    ];
    for name in every_example() {
        let path = example(&name);
        if !napitia(&["check", &path]).status.success() {
            continue;
        }
        let output = napitia(&["run", &path]);
        let err = stderr(&output);
        assert!(
            !err.contains("V0") && !err.contains("I0"),
            "`run` leaked an internal diagnostic for `{name}`, which `check` had accepted: {err}"
        );
        assert!(
            !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
            "`run` panicked on `{name}`, which `check` had accepted: {err}"
        );
        for refusal in ownership_refusals {
            assert!(
                !err.contains(refusal),
                "`run` refused `{name}` for ownership ({refusal}), but `check` had accepted it: \
                 {err}"
            );
        }
    }
}

/// Whatever a stage decides, it must decide the same way twice, at every
/// stage, for every example -- the property every `HashMap`/`HashSet` in
/// the ownership analyses has to preserve.
#[test]
fn every_example_produces_identical_output_at_every_stage_across_two_runs() {
    for name in every_example() {
        let path = example(&name);
        for cmd in ["check", "ir", "run"] {
            let first = napitia(&[cmd, &path]);
            let second = napitia(&[cmd, &path]);
            assert_eq!(
                first.status.code(),
                second.status.code(),
                "`{cmd}` on `{name}` was not deterministic in its exit code"
            );
            assert_eq!(
                stderr(&first),
                stderr(&second),
                "`{cmd}` on `{name}` was not deterministic on stderr"
            );
            assert_eq!(
                stdout(&first),
                stdout(&second),
                "`{cmd}` on `{name}` was not deterministic on stdout"
            );
        }
    }
}

// -- the numeric contract, through the real binary (`rfcs/0015`) ----------

/// A directory of this section's own `.npt` fixtures, removed when the
/// test that made it ends. The numeric contract needs programs written
/// around exact boundary values, and a shared temporary name would let
/// two of these tests overwrite each other's source mid-run.
struct Fixtures {
    path: std::path::PathBuf,
}

impl Fixtures {
    fn new(tag: &str) -> Fixtures {
        let path =
            std::env::temp_dir().join(format!("napitia numeric {tag} {}", std::process::id()));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).expect("could not create a fixture directory");
        Fixtures { path }
    }

    fn write(&self, name: &str, text: &str) -> String {
        let path = self.path.join(name);
        std::fs::write(&path, text).expect("could not write a fixture");
        path.to_string_lossy().into_owned()
    }
}

impl Drop for Fixtures {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

#[test]
fn the_numeric_boundaries_example_answers_the_same_thing_every_time() {
    let path = example("numeric_boundaries.npt");
    let first = napitia(&["run", &path]);
    assert!(
        first.status.success(),
        "the example must run:\n{}",
        stderr(&first)
    );
    assert_eq!(stdout(&first).trim(), "42");
    assert!(
        stderr(&first).is_empty(),
        "a successful run says nothing on stderr: {}",
        stderr(&first)
    );

    let second = napitia(&["run", &path]);
    assert_eq!(stdout(&first), stdout(&second));

    // And its NIR is byte-identical across runs, since nothing about
    // lowering may depend on a hash order.
    let ir_first = napitia(&["ir", &path]);
    let ir_second = napitia(&["ir", &path]);
    assert!(ir_first.status.success());
    assert_eq!(stdout(&ir_first), stdout(&ir_second));
}

#[test]
fn the_out_of_range_literal_example_is_t0073_at_every_stage() {
    assert_resource_example_rejected("numeric_literal_range_invalid.npt", "T0073");
}

/// Both boundaries are literals the compiler accepts; neither
/// neighbour is. Exercised through the binary rather than the library,
/// because the point is that the whole pipeline agrees.
#[test]
fn the_boundary_literals_are_accepted_and_their_neighbours_are_not() {
    let directory = Fixtures::new("literal-boundaries");
    for (name, literal, accepted) in [
        ("min", "-9223372036854775808", true),
        ("max", "9223372036854775807", true),
        ("below_min", "-9223372036854775809", false),
        ("above_max", "9223372036854775808", false),
    ] {
        let path = directory.write(
            &format!("{name}.npt"),
            &format!("func main() -> i64 {{ value x: i64 = {literal}; return 0 }}"),
        );
        let checked = napitia(&["check", &path]);
        assert_eq!(
            checked.status.success(),
            accepted,
            "`{literal}`:\n{}",
            stderr(&checked)
        );
        if !accepted {
            assert!(stderr(&checked).contains("error[T0073]"), "`{literal}`");
        }
    }
}

/// An overflow is a runtime failure with a stable code and a stable
/// line, not a wrapped value and not a Rust panic.
#[test]
fn an_overflow_is_a_structured_runtime_failure() {
    let directory = Fixtures::new("overflow");
    for (name, body, code, text) in [
        (
            "add",
            "value m: i64 = 9223372036854775807; return m + 1",
            "X0002",
            "integer overflow in `add`",
        ),
        (
            "neg",
            "value m: i64 = -9223372036854775808; return -m",
            "X0002",
            "integer overflow in `neg`",
        ),
        (
            "div_by_zero",
            "value z: i64 = 0; return 1 / z",
            "X0001",
            "`div` by zero",
        ),
        (
            "shift",
            "value n: i64 = 64; return 1 << n",
            "X0003",
            "shift amount 64 is outside 0..64",
        ),
    ] {
        let path = directory.write(
            &format!("{name}.npt"),
            &format!("func main() -> i64 {{ {body} }}"),
        );
        let output = napitia(&["run", &path]);
        let err = stderr(&output);
        assert_eq!(output.status.code(), Some(1), "`{name}`: {err}");
        assert_eq!(err.trim(), format!("error[{code}]: {text}"), "`{name}`");
        assert!(
            stdout(&output).is_empty(),
            "`{name}`: a failed run prints no value"
        );
        assert!(
            !err.to_lowercase().contains("panic") && !err.contains("RUST_BACKTRACE"),
            "`{name}`: {err}"
        );
        assert_eq!(
            err,
            stderr(&napitia(&["run", &path])),
            "`{name}`: repeated runs differ"
        );
    }
}

/// A numeric type this milestone does not execute is refused by
/// `check`, so it never reaches a stage that would have to invent
/// behavior for it.
#[test]
fn an_unimplemented_numeric_type_is_t0074_at_every_stage() {
    let directory = Fixtures::new("numeric-types");
    for name in [
        "i8", "i16", "i32", "isize", "u8", "u16", "u32", "u64", "usize", "f32",
    ] {
        let path = directory.write(
            &format!("ty_{name}.npt"),
            &format!("func f(x: {name}) -> i64 {{ return 0 }}\nfunc main() -> i64 {{ return 0 }}"),
        );
        for cmd in ["check", "ir", "run"] {
            let output = napitia(&[cmd, &path]);
            let err = stderr(&output);
            assert_eq!(output.status.code(), Some(1), "`{name}`/{cmd}: {err}");
            assert!(err.contains("error[T0074]"), "`{name}`/{cmd}: {err}");
            assert!(
                !err.contains("I0") && !err.contains("V0"),
                "`{name}`/{cmd} leaked an internal diagnostic: {err}"
            );
        }
    }
}

/// `i64` and `f64` are the two that do run.
#[test]
fn the_two_implemented_numeric_types_run() {
    let directory = Fixtures::new("implemented-numerics");
    let integer = directory.write(
        "int.npt",
        "func f(x: i64) -> i64 { return x + 1 }\nfunc main() -> i64 { return f(41) }",
    );
    let output = napitia(&["run", &integer]);
    assert!(output.status.success(), "{}", stderr(&output));
    assert_eq!(stdout(&output).trim(), "42");

    let float = directory.write(
        "float.npt",
        "func f(x: f64) -> f64 { return x + 0.5 }\nfunc main() -> f64 { return f(41.5) }",
    );
    let output = napitia(&["run", &float]);
    assert!(output.status.success(), "{}", stderr(&output));
    assert_eq!(stdout(&output).trim(), "42");
}

// -- NaN and fatal aborts, through the real binary (`rfcs/0015`) ----------

/// A NaN comparison is an ordinary answer on stdout, not a diagnostic.
/// This is the CLI-level half of the guarantee: no `X0004`, no
/// diagnostic of any kind, and the same bytes twice.
#[test]
fn a_nan_comparison_is_an_ordinary_answer_at_the_command_line() {
    let directory = Fixtures::new("nan-cli");
    const NAN: &str = "value zero: f64 = 0.0; value nan: f64 = 0.0 / zero;";

    for (name, operator, expected) in [
        ("lt", "<", "false"),
        ("le", "<=", "false"),
        ("gt", ">", "false"),
        ("ge", ">=", "false"),
        ("eq", "==", "false"),
        ("ne", "!=", "true"),
    ] {
        let path = directory.write(
            &format!("nan_{name}.npt"),
            &format!("func main() -> bool {{ {NAN} return nan {operator} nan }}"),
        );
        let first = napitia(&["run", &path]);
        assert!(
            first.status.success(),
            "`{operator}` on a NaN must succeed:\n{}",
            stderr(&first)
        );
        assert_eq!(stdout(&first).trim(), expected, "`{operator}`");
        assert!(
            stderr(&first).is_empty(),
            "`{operator}` must produce no diagnostic: {}",
            stderr(&first)
        );
        assert!(
            !stderr(&first).contains("X0004"),
            "`{operator}`: a valid NaN comparison is not malformed NIR"
        );

        let second = napitia(&["run", &path]);
        assert_eq!(stdout(&first), stdout(&second), "`{operator}`");
        assert_eq!(stderr(&first), stderr(&second), "`{operator}`");
    }
}

/// A fatal abort with a live resource and a pending `defer`: the CLI
/// reports the arithmetic failure, exits non-zero, prints nothing on
/// stdout, and does not claim any cleanup happened.
#[test]
fn a_fatal_abort_with_live_cleanup_pending_reports_only_the_arithmetic_failure() {
    let directory = Fixtures::new("fatal-abort-cli");
    let path = directory.write(
        "abort.npt",
        "resource File { descriptor: i64 }\n\
         func open(descriptor: i64) -> File { return File { descriptor: descriptor }; }\n\
         func close(file: File) -> unit { }\n\
         func main() -> i64 {\n\
           value file = open(7);\n\
           defer close(file);\n\
           value m: i64 = 9223372036854775807;\n\
           value bad: i64 = m + 1;\n\
           return 0\n\
         }\n",
    );

    let first = napitia(&["run", &path]);
    assert_eq!(first.status.code(), Some(1), "{}", stderr(&first));
    assert_eq!(
        stderr(&first).trim(),
        "error[X0002]: integer overflow in `add`",
        "the abort reports the arithmetic failure and nothing else"
    );
    assert!(
        stdout(&first).is_empty(),
        "a failed run prints no value: {}",
        stdout(&first)
    );
    assert!(
        !stderr(&first).to_lowercase().contains("panic")
            && !stderr(&first).contains("RUST_BACKTRACE"),
        "{}",
        stderr(&first)
    );

    let second = napitia(&["run", &path]);
    assert_eq!(stderr(&first), stderr(&second), "repeated runs differ");
    assert_eq!(first.status.code(), second.status.code());
}

/// Every X-class boundary, through the binary, with its exact code and
/// exit status.
#[test]
fn every_runtime_failure_code_is_reachable_and_exact() {
    let directory = Fixtures::new("x-codes");
    for (name, body, code, text) in [
        (
            "div_zero",
            "value z: i64 = 0; return 1 / z",
            "X0001",
            "`div` by zero",
        ),
        (
            "rem_zero",
            "value z: i64 = 0; return 1 % z",
            "X0001",
            "`rem` by zero",
        ),
        (
            "min_over_minus_one",
            "value m: i64 = -9223372036854775808; value d: i64 = -1; return m / d",
            "X0002",
            "integer overflow in `div`",
        ),
        (
            "shift_width",
            "value n: i64 = 64; return 1 << n",
            "X0003",
            "shift amount 64 is outside 0..64",
        ),
        (
            "shift_negative",
            "value n: i64 = -1; return 1 >> n",
            "X0003",
            "shift amount -1 is outside 0..64",
        ),
        (
            "shift_large",
            "value n: i64 = 9223372036854775807; return 1 << n",
            "X0003",
            "shift amount 9223372036854775807 is outside 0..64",
        ),
    ] {
        let path = directory.write(
            &format!("{name}.npt"),
            &format!("func main() -> i64 {{ {body} }}"),
        );
        let output = napitia(&["run", &path]);
        assert_eq!(output.status.code(), Some(1), "`{name}`");
        assert_eq!(
            stderr(&output).trim(),
            format!("error[{code}]: {text}"),
            "`{name}`"
        );
    }
}

/// `i64::MIN % -1` is `0`, not a failure: the exact remainder is in
/// range even though the exact quotient is not.
#[test]
fn the_minimum_remainder_by_minus_one_is_zero_at_the_command_line() {
    let directory = Fixtures::new("min-rem");
    let path = directory.write(
        "min_rem.npt",
        "func main() -> i64 { value m: i64 = -9223372036854775808; value d: i64 = -1; return m % d }",
    );
    let output = napitia(&["run", &path]);
    assert!(output.status.success(), "{}", stderr(&output));
    assert_eq!(stdout(&output).trim(), "0");
}

// -- The verified execution boundary (`rfcs/0016`) --------------------
//
// `check`, `ir`, `run` and `build` all share one pipeline, and since
// Alpha 0.2.2 everything downstream of NIR lowering takes a sealed
// module. That must change none of their documented acceptance
// boundaries, and must never turn a refusal into a panic, a backtrace
// or an internal code reaching a user.

/// Every diagnostic code a run reported, in the order it reported them.
fn codes_of(text: &str) -> Vec<String> {
    text.lines()
        .filter_map(|line| line.split_once("error["))
        .filter_map(|(_, rest)| rest.split_once(']'))
        .map(|(code, _)| code.to_string())
        .collect()
}

/// Nothing a user can reach may panic or print a Rust backtrace.
fn assert_no_panic(output: &Output, what: &str) {
    let err = stderr(output);
    for marker in [
        "panicked at",
        "RUST_BACKTRACE",
        "stack backtrace",
        "note: run with",
    ] {
        assert!(!err.contains(marker), "`{what}` leaked `{marker}`:\n{err}");
    }
    assert_ne!(
        output.status.code(),
        Some(101),
        "`{what}` exited with the panic status:\n{err}"
    );
}

#[test]
fn check_ir_and_run_all_accept_a_valid_program_through_the_seal() {
    let path = example("hello.npt");

    let checked = napitia(&["check", &path]);
    assert_no_panic(&checked, "check");
    assert!(checked.status.success());
    assert!(stdout(&checked).contains("no errors"));

    // `ir` is where verification runs and where the seal is printed.
    let ired = napitia(&["ir", &path]);
    assert_no_panic(&ired, "ir");
    assert!(ired.status.success(), "{}", stderr(&ired));
    assert!(
        stdout(&ired).contains("func @main"),
        "`ir` must print the verified module: {}",
        stdout(&ired)
    );
    assert!(stderr(&ired).is_empty(), "{}", stderr(&ired));

    // And `run` executes that same sealed module.
    let ran = napitia(&["run", &path]);
    assert_no_panic(&ran, "run");
    assert!(ran.status.success(), "{}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "42");
    assert!(stderr(&ran).is_empty(), "{}", stderr(&ran));
}

#[test]
fn check_ir_run_and_build_refuse_an_invalid_program_with_the_same_codes() {
    let path = example("invalid_types.npt");

    let checked = napitia(&["check", &path]);
    assert_no_panic(&checked, "check");
    assert_eq!(checked.status.code(), Some(1));
    let expected = codes_of(&stderr(&checked));
    assert!(
        expected.iter().any(|code| code.starts_with('T')),
        "the fixture must fail type checking, got {expected:?}"
    );

    // Every later command refuses the same program for the same
    // reasons: nothing is lowered, nothing is sealed, nothing runs and
    // nothing is compiled.
    for command in ["ir", "run"] {
        let output = napitia(&[command, &path]);
        assert_no_panic(&output, command);
        assert_eq!(output.status.code(), Some(1), "`{command}` must refuse");
        assert_eq!(
            codes_of(&stderr(&output)),
            expected,
            "`{command}` must report exactly what `check` reported"
        );
        assert!(
            stdout(&output).is_empty(),
            "`{command}` must produce no output for a refused program: {}",
            stdout(&output)
        );
    }

    // `build` fails at the same stage, before the native backend is
    // consulted at all: no `Axxxx` code, no executable.
    let output = std::env::temp_dir().join(format!("napitia boundary {}", std::process::id()));
    let _ = std::fs::remove_file(&output);
    let built = napitia(&[
        "build",
        &path,
        "--output",
        output.to_str().expect("a printable path"),
    ]);
    assert_no_panic(&built, "build");
    assert_eq!(built.status.code(), Some(1));
    assert_eq!(codes_of(&stderr(&built)), expected);
    assert!(
        !stderr(&built).contains("error[A0"),
        "the native backend must never be reached: {}",
        stderr(&built)
    );
    assert!(!output.exists(), "a refused build must write no executable");
}

#[test]
fn ir_and_run_are_byte_identical_across_repeated_invocations() {
    for name in ["hello.npt", "invalid_types.npt"] {
        let path = example(name);
        for command in ["ir", "run"] {
            let first = napitia(&[command, &path]);
            for _ in 0..2 {
                let again = napitia(&[command, &path]);
                assert_eq!(
                    stdout(&first),
                    stdout(&again),
                    "`{command} {name}` stdout is not deterministic"
                );
                assert_eq!(
                    stderr(&first),
                    stderr(&again),
                    "`{command} {name}` stderr is not deterministic"
                );
                assert_eq!(first.status.code(), again.status.code());
            }
        }
    }
}

/// A user can never be shown a `V` code for a program the frontend
/// accepted -- the verifier only ever sees NIR this compiler built
/// itself. This sweeps every example rather than one fixture, so a
/// newly added one is covered automatically.
#[test]
fn no_command_ever_leaks_a_verifier_code_or_a_panic() {
    for name in every_example() {
        let path = example(&name);
        for command in ["check", "ir", "run"] {
            let output = napitia(&[command, &path]);
            assert_no_panic(&output, &format!("{command} {name}"));
            assert!(
                !stderr(&output).contains("error[V0"),
                "`{command} {name}` leaked a verifier diagnostic: {}",
                stderr(&output)
            );
        }
    }
}
