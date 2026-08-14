//! End-to-end tests for the `napitia` CLI, exercising the actual built
//! binary (not the driver functions directly) so exit codes and
//! stdout/stderr separation are covered as a real user would see them.

use std::process::{Command, Output};

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/{name}", env!("CARGO_MANIFEST_DIR"))
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
fn missing_file_argument_is_a_usage_error() {
    let output = napitia(&["run"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(stderr(&output).contains("missing"));
}

#[test]
fn unreadable_file_is_a_usage_error() {
    let output = napitia(&["run", "does/not/exist.npt"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(stderr(&output).contains("could not read"));
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
