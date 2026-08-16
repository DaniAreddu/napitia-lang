//! End-to-end tests for multi-file project compilation, exercising the
//! actual built `napitia` binary against real fixture project
//! directories under `tests/projects/`. Complements `cli.rs` (single-file
//! mode) and the unit tests in `src/project/`, which cover the same
//! resolution logic without going through argument parsing or the
//! filesystem-facing CLI dispatch.

use std::process::{Command, Output};

fn project(name: &str) -> String {
    format!("{}/tests/projects/{name}", env!("CARGO_MANIFEST_DIR"))
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
fn a_two_file_project_compiles_and_runs_through_the_directory_path() {
    let dir = project("basic_two_file");

    let checked = napitia(&["check", &dir]);
    assert!(
        checked.status.success(),
        "check failed: {}",
        stderr(&checked)
    );
    assert!(stdout(&checked).contains("no errors"));

    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "42");
}

#[test]
fn a_two_file_project_also_compiles_through_an_explicit_manifest_path() {
    let manifest = format!("{}/napitia.toml", project("basic_two_file"));

    let ran = napitia(&["run", &manifest]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "42");
}

#[test]
fn ir_prints_nir_for_a_project_naming_both_modules() {
    let dir = project("basic_two_file");
    let output = napitia(&["ir", &dir]);
    assert!(output.status.success(), "ir failed: {}", stderr(&output));
    let text = stdout(&output);
    assert!(text.contains("func @main"));
    assert!(text.contains("func @add"));
}

#[test]
fn repeated_project_compiles_produce_byte_identical_output() {
    let dir = project("basic_two_file");
    let first = stdout(&napitia(&["ir", &dir]));
    let second = stdout(&napitia(&["ir", &dir]));
    assert_eq!(first, second);
    assert!(!first.is_empty());
}

#[test]
fn a_nested_module_import_supports_records_in_params_field_access_and_returns() {
    let dir = project("nested_record");
    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "12");
}

#[test]
fn an_imported_variant_constructs_and_matches_exhaustively_across_modules() {
    let dir = project("imported_variant");
    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "25");
}

#[test]
fn forward_reference_across_modules_resolves_regardless_of_discovery_order() {
    let dir = project("forward_reference");
    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "99");
}

#[test]
fn main_defined_in_a_non_entry_module_is_never_the_entry_point() {
    let dir = project("main_in_non_entry_ignored");
    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "5");
}

fn assert_project_check_fails_with(fixture_name: &str, code: &str) {
    let dir = project(fixture_name);
    let output = napitia(&["check", &dir]);
    assert_eq!(
        output.status.code(),
        Some(1),
        "`{fixture_name}` should fail check"
    );
    let err = stderr(&output);
    assert!(
        err.contains(&format!("error[{code}]")),
        "`{fixture_name}` expected {code}, got: {err}"
    );
}

#[test]
fn importing_a_private_function_is_m0006() {
    assert_project_check_fails_with("private_function_import", "M0006");
}

#[test]
fn importing_a_private_record_is_m0006() {
    assert_project_check_fails_with("private_record_import", "M0006");
}

#[test]
fn importing_a_private_variant_is_m0006() {
    assert_project_check_fails_with("private_variant_import", "M0006");
}

#[test]
fn accessing_a_private_field_across_modules_is_m0011() {
    assert_project_check_fails_with("private_field_access", "M0011");
}

#[test]
fn constructing_a_record_naming_a_private_field_across_modules_is_m0011() {
    assert_project_check_fails_with("private_field_construction", "M0011");
}

#[test]
fn a_public_function_exposing_a_private_local_record_is_m0012() {
    assert_project_check_fails_with("private_type_leak", "M0012");
}

#[test]
fn importing_from_an_unknown_module_is_m0004() {
    assert_project_check_fails_with("missing_module", "M0004");
}

#[test]
fn importing_an_unknown_item_is_m0005() {
    assert_project_check_fails_with("missing_item", "M0005");
}

#[test]
fn a_single_segment_import_path_is_m0003() {
    assert_project_check_fails_with("single_segment_import", "M0003");
}

#[test]
fn importing_the_same_item_twice_is_m0007() {
    assert_project_check_fails_with("duplicate_import", "M0007");
}

#[test]
fn two_imports_introducing_the_same_local_name_is_m0007() {
    assert_project_check_fails_with("same_local_name_import", "M0007");
}

#[test]
fn a_local_declaration_conflicting_with_an_import_is_m0007() {
    assert_project_check_fails_with("import_local_collision", "M0007");
}

#[test]
fn a_module_import_cycle_is_m0008_with_a_deterministic_witness() {
    let dir = project("import_cycle");
    let output = napitia(&["check", &dir]);
    assert_eq!(output.status.code(), Some(1));
    let err = stderr(&output);
    assert!(err.contains("error[M0008]"), "expected M0008, got: {err}");
    // The witness must be deterministic across repeated runs, not just
    // present -- run again and require byte-identical stderr.
    let again = stderr(&napitia(&["check", &dir]));
    assert_eq!(err, again);
}

#[test]
fn an_entry_escaping_the_source_root_is_m0002() {
    assert_project_check_fails_with("entry_path_escape", "M0002");
}

#[test]
fn a_manifest_missing_a_required_field_is_m0001() {
    assert_project_check_fails_with("manifest_missing_field", "M0001");
}

#[test]
fn a_manifest_with_an_unknown_field_is_m0001() {
    assert_project_check_fails_with("manifest_unknown_field", "M0001");
}

#[test]
fn a_missing_entry_main_is_m0010() {
    assert_project_check_fails_with("missing_entry_main", "M0010");
}

#[test]
fn a_failing_project_never_prints_partial_nir() {
    let dir = project("missing_item");
    let output = napitia(&["ir", &dir]);
    assert_eq!(output.status.code(), Some(1));
    assert!(
        !stdout(&output).contains("func @"),
        "a failed project must never print partial NIR: {}",
        stdout(&output)
    );
}

#[test]
fn a_cross_file_diagnostic_names_both_the_importing_and_declaring_files() {
    let dir = project("private_function_import");
    let output = napitia(&["check", &dir]);
    assert_eq!(output.status.code(), Some(1));
    let err = stderr(&output);
    assert!(err.contains("main.npt"), "expected main.npt in: {err}");
    assert!(err.contains("math.npt"), "expected math.npt in: {err}");
}

#[test]
fn an_npt_path_inside_a_project_directory_still_uses_legacy_single_file_mode() {
    // Explicit `.npt` paths always win over project discovery, even when
    // a `napitia.toml` sits right next to the file: `main.npt` alone,
    // outside of project compilation, cannot see `math.npt`'s `add`.
    let main_path = format!("{}/src/main.npt", project("basic_two_file"));
    let output = napitia(&["check", &main_path]);
    assert_eq!(
        output.status.code(),
        Some(1),
        "single-file mode must not resolve the sibling module"
    );
}

#[test]
fn forward_slash_paths_reach_the_project() {
    // `\` is only a path separator on Windows -- on POSIX it is a valid,
    // ordinary filename character, so a "does `\` also work" assertion
    // only makes sense on Windows (see the cfg(windows) test below).
    // Every platform, however, must accept `/`-separated paths, which is
    // what this asserts.
    let unix_style = project("basic_two_file").replace('\\', "/");
    let via_unix = napitia(&["run", &unix_style]);
    assert!(via_unix.status.success(), "{}", stderr(&via_unix));
    assert_eq!(stdout(&via_unix).trim(), "42");
}

#[cfg(windows)]
#[test]
fn backslash_paths_also_reach_the_project_on_windows() {
    let unix_style = project("basic_two_file").replace('\\', "/");
    let windows_style = unix_style.replace('/', "\\");
    let via_windows = napitia(&["run", &windows_style]);
    assert!(via_windows.status.success(), "{}", stderr(&via_windows));
    assert_eq!(stdout(&via_windows).trim(), "42");
}
