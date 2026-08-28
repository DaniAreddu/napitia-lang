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

// -- Generics (`rfcs/0008`) ---------------------------------------------

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
fn resource_raise_cleanup_example_runs_end_to_end() {
    assert_resource_example_runs("resource_raise_cleanup.npt", "5");
}

#[test]
fn resource_handle_cleanup_example_runs_end_to_end() {
    assert_resource_example_runs("resource_handle_cleanup.npt", "4");
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
