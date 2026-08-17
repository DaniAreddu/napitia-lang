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

fn napitia_in_dir(dir: &str, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_napitia"))
        .args(args)
        .current_dir(dir)
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
fn a_bare_relative_manifest_path_works_from_inside_the_project_directory() {
    // `Path::parent()` returns `Some("")`, not `None`, for a bare
    // relative path like `napitia.toml` -- passing that empty path
    // straight to `canonicalize()` used to fail outright, breaking the
    // exact invocation style the README documents (`cd` into a project,
    // then `napitia check napitia.toml`).
    let dir = project("basic_two_file");

    let checked = napitia_in_dir(&dir, &["check", "napitia.toml"]);
    assert!(
        checked.status.success(),
        "check failed: {}",
        stderr(&checked)
    );
    assert!(stdout(&checked).contains("no errors"));

    let ir = napitia_in_dir(&dir, &["ir", "napitia.toml"]);
    assert!(ir.status.success(), "ir failed: {}", stderr(&ir));
    let ir_text = stdout(&ir);
    assert!(ir_text.contains("func @main.main#"));
    assert!(ir_text.contains("func @math.add#"));

    let ran = napitia_in_dir(&dir, &["run", "napitia.toml"]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "42");
}

#[test]
fn a_dot_slash_prefixed_manifest_path_also_works() {
    let dir = project("basic_two_file");
    let ran = napitia_in_dir(&dir, &["run", "./napitia.toml"]);
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
    // Module-qualified (rfcs/0007): `main.npt`'s own `main` is module
    // `main`, `math.npt`'s `add` is module `math`.
    assert!(text.contains("func @main.main#"));
    assert!(text.contains("func @math.add#"));
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
fn a_parameterized_main_in_a_non_entry_module_is_an_ordinary_function() {
    // The entry-signature check ("`main` takes no parameters") used to
    // apply to *any* function literally named `main` anywhere in the
    // merged project, rejecting a non-entry module's differently-shaped
    // `main` with T0012. It must now be scoped to the entry module's own
    // `main` by identity: a non-entry `main(n: i64)` is legal, and the
    // entry module's own zero-argument `main` still runs.
    let dir = project("non_entry_parameterized_main");
    let checked = napitia(&["check", &dir]);
    assert!(
        checked.status.success(),
        "check failed: {}",
        stderr(&checked)
    );

    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "42");
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
fn two_modules_declaring_the_same_type_name_do_not_collide() {
    // `a` and `b` each declare their own, differently-shaped `User` --
    // nominal identity is resolved against each module's own namespace
    // before merging, so the two declarations must never collide into a
    // single global `User`, regardless of which module's declaration a
    // project-global symbol table would have kept.
    let dir = project("duplicate_type_across_modules");
    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "340");
}

#[test]
fn import_declaration_order_does_not_change_which_user_identity_is_used() {
    // Same modules as above, but `main` imports `b` before `a` -- the
    // result must be identical, proving type identity is resolved
    // per-declaration, never re-derived from a project-global map whose
    // final contents could depend on processing order.
    let dir = project("duplicate_type_across_modules_reordered");
    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "340");
}

#[test]
fn a_type_reachable_but_not_imported_is_t0006_not_a_successful_compile() {
    // `main` imports `helper.ping` but never `helper.Secret` -- `Secret`
    // being reachable (another item in the same module was successfully
    // imported) must not make it usable; it is not in `main`'s own
    // namespace, so it must be genuinely unknown there.
    assert_project_check_fails_with("unimported_reachable_type", "T0006");
}

#[test]
fn a_cycle_with_an_acyclic_outbound_leaf_is_m0008_not_a_panic_through_the_real_binary() {
    // `a <-> b` is a real cycle; `a` also imports the acyclic leaf `c`.
    // The old witness-extraction code could wander from `a` into `c`
    // (which has no edge back into the residual set) and panic. Exercise
    // the actual built binary, not just the unit-level algorithm.
    let dir = project("import_cycle_with_acyclic_leaf");
    let checked = napitia(&["check", &dir]);
    assert_eq!(checked.status.code(), Some(1), "expected exit code 1");
    let err = stderr(&checked);
    assert!(
        !err.contains("panicked at"),
        "expected no panic, got: {err}"
    );
    assert!(err.contains("error[M0008]"), "expected M0008, got: {err}");
    assert!(
        err.contains("cycle: a -> b -> a"),
        "unexpected witness: {err}"
    );
}

#[test]
fn a_failed_transitive_dependency_fails_atomically_instead_of_panicking() {
    // `main` imports `a`, which imports `b.secret` (private) -- `a`'s
    // own import resolution fails, so `a` is never lowered. `main`
    // importing a *public* item from `a` used to reach `resolve_imports`
    // with a target module that was never inserted into
    // `lowered_by_module`, panicking instead of failing as a
    // diagnostic. Must fail atomically: exit code 1, exactly the root
    // M0006 diagnostic (no cascade, no panic, no partial NIR), and
    // byte-identical across repeated runs.
    let dir = project("failed_transitive_dependency");

    let checked = napitia(&["check", &dir]);
    assert_eq!(checked.status.code(), Some(1), "expected exit code 1");
    let err = stderr(&checked);
    assert!(
        !err.contains("panicked at") && !err.contains("RUST_BACKTRACE"),
        "expected no panic, got: {err}"
    );
    assert!(
        err.contains("error[M0006]"),
        "expected the root M0006 diagnostic, got: {err}"
    );
    assert_eq!(
        err.matches("error[").count(),
        1,
        "expected exactly one diagnostic (no cascade), got: {err}"
    );

    let ir_output = napitia(&["ir", &dir]);
    assert_eq!(ir_output.status.code(), Some(1));
    assert!(
        stdout(&ir_output).trim().is_empty(),
        "expected no partial NIR on stdout, got: {}",
        stdout(&ir_output)
    );

    let second = napitia(&["check", &dir]);
    assert_eq!(stderr(&second), err, "expected byte-identical diagnostics");
}

#[test]
fn an_unimported_private_type_cannot_be_exposed_through_a_public_function() {
    // `Secret` is private to `helper` *and* never imported into `main`
    // -- it must be rejected as unknown (T0006), never silently resolved
    // against a project-global symbol table that would let a public
    // function leak a type its own module never imported.
    assert_project_check_fails_with("unimported_private_type_not_exposed", "T0006");
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
fn an_imported_function_arity_mismatch_labels_the_actual_declaration_not_the_import() {
    // `FunctionSig` used to carry only a `Span`, so the "function
    // defined here" label was always rendered against the *caller's*
    // own `SourceId` -- pointing at the `import` statement in
    // `main.npt` instead of `add`'s actual declaration in `math.npt`.
    let dir = project("cross_file_arity_mismatch");
    let output = napitia(&["check", &dir]);
    assert_eq!(output.status.code(), Some(1));
    let err = stderr(&output);
    assert!(err.contains("error[T0002]"), "expected T0002, got: {err}");
    assert!(
        err.contains("main.npt") && err.contains("math.npt"),
        "expected both files named: {err}"
    );
    // The secondary "function defined here" label must be the
    // declaration's own signature line in math.npt, not the `import`
    // line in main.npt.
    assert!(
        err.contains("func add(left: i64, right: i64)"),
        "expected the label to point at add's real declaration: {err}"
    );
    assert!(
        !err.contains("import math.add"),
        "the import statement itself must not be labeled as the declaration: {err}"
    );
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

#[test]
fn two_same_named_record_types_are_usable_together_through_aliases() {
    // `sales.user.User` and `admin.user.User` share both a name and a
    // field shape; only aliasing lets both be named in `main`'s scope
    // at once. 40 (from the aliased `SalesUser`) + 2 (from the aliased
    // `AdminUser`) is the exact worked example from `rfcs/0007`.
    let dir = project("alias_same_named_records");
    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "42");
}

#[test]
fn an_alias_never_makes_two_same_named_types_nominally_compatible() {
    // Same two same-named, same-shaped `User` types as above, but this
    // time a value of the aliased `SalesUser` is passed where
    // `admin.user`'s own `user_id` expects its own `User` -- aliasing is
    // only a local spelling, never a bridge between distinct types, so
    // this must still be rejected as an ordinary type mismatch.
    assert_project_check_fails_with("alias_nominal_mismatch", "T0001");
}

#[test]
fn two_same_named_functions_are_callable_together_through_aliases() {
    // `ops_a.calculate` and `ops_b.calculate` share a name; aliasing
    // brings both into scope under distinct local names and each still
    // calls its own, exact declaration (11 + 20).
    let dir = project("alias_same_named_functions");
    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "31");
}

#[test]
fn a_generic_variant_matched_exhaustively_through_an_import_alias_runs_end_to_end() {
    // `Optional` is a local alias for `shapes.Maybe`; exhaustiveness
    // keys off the canonical declaration, not the alias a particular
    // file happens to construct/match it through, so a fully-covered
    // match on `Optional[bool]` must not be reported as incomplete
    // (rfcs/0007, rfcs/0008).
    let dir = project("generic_variant_alias_exhaustive");
    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "3");
}

#[test]
fn two_same_named_generic_records_from_different_modules_remain_distinct() {
    // `sales.Box[T]` and `admin.Box[T]` are two distinct declarations
    // that happen to share a name and shape -- each is only usable
    // through its own module's own function, and instantiating both
    // with the same type argument never makes them the same type
    // (rfcs/0007, rfcs/0008).
    let dir = project("generic_same_named_records_across_modules");
    let ran = napitia(&["run", &dir]);
    assert!(ran.status.success(), "run failed: {}", stderr(&ran));
    assert_eq!(stdout(&ran).trim(), "42");
}
