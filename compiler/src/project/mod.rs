//! Multi-file Napitia projects: manifests, module discovery, the
//! module dependency graph, and cross-module import resolution
//! (`rfcs/0006`).

pub mod loader;
pub mod manifest;
pub mod module;
pub mod resolve;

use std::collections::HashMap;
use std::path::Path;

use crate::diagnostics::Diagnostic;
use crate::hir::{self, HirModule, ItemId};
use crate::nir::{self, Module as NirModule};
use crate::source::{SourceId, SourceMap};
use crate::symbol::Interner;
use crate::syntax::ast;
use crate::typeck;

pub(crate) mod codes {
    pub const INVALID_MANIFEST: &str = "M0001";
    pub const INVALID_PROJECT_PATH: &str = "M0002";
    pub const INVALID_IMPORT_PATH: &str = "M0003";
    pub const MODULE_NOT_FOUND: &str = "M0004";
    pub const ITEM_NOT_FOUND: &str = "M0005";
    pub const ITEM_PRIVATE: &str = "M0006";
    pub const DUPLICATE_IMPORT: &str = "M0007";
    pub const IMPORT_CYCLE: &str = "M0008";
    pub const MODULE_PATH_COLLISION: &str = "M0009";
    pub const INVALID_ENTRY: &str = "M0010";
    pub const INACCESSIBLE_FIELD: &str = "M0011";
    pub const PRIVATE_TYPE_LEAKED: &str = "M0012";
    pub const DUPLICATE_PHYSICAL_MODULE: &str = "M0013";
}

/// A fully compiled, verified project, ready to print or execute.
#[derive(Debug)]
pub struct CompiledProject {
    pub nir: NirModule,
    /// The entry module's own `main`, resolved by identity -- never a
    /// name lookup over the merged module, which a project with more
    /// than one module could make ambiguous.
    pub entry_item: ItemId,
    /// Canonical module-qualified identity for every item in `nir`
    /// (`rfcs/0007`) -- what `nir::print_module`/`nir::verify_module`
    /// and any future qualified diagnostic read from, rather than each
    /// keeping its own name lookup that could drift from this one.
    pub registry: hir::ItemRegistry,
}

/// Loads, resolves, and compiles the project rooted at `manifest_path`
/// clear through to a single verified NIR module, atomically: any
/// failure at any stage returns every diagnostic found so far, never a
/// partial result.
///
/// Each module is parsed and HIR-lowered *separately*, in dependency
/// order, with its own imports resolved against already-lowered
/// dependency modules -- never by concatenating source text -- and
/// only the resulting `HirModule`s are merged into one, after every
/// module has its own globally-unique item ids (`hir::IdCursor`,
/// threaded across the whole loop). Typeck and NIR lowering/
/// verification then run exactly once, unchanged, over that merged
/// module, since by construction it is already as internally
/// consistent as a single hand-written file.
pub fn compile_project(
    manifest_path: &Path,
    map: &mut SourceMap,
    interner: &mut Interner,
) -> Result<CompiledProject, Vec<Diagnostic>> {
    let loaded = loader::load_project(manifest_path, map, interner)?;
    validate_entry_main(&loaded, interner)?;

    let module_path_by_dotted: HashMap<String, module::ModuleId> = loaded
        .modules
        .iter()
        .map(|m| (m.path.dotted(), m.id))
        .collect();
    let mut imports_by_module: HashMap<module::ModuleId, Vec<&loader::ImportRef>> = HashMap::new();
    for import in &loaded.imports {
        imports_by_module
            .entry(import.importing_module)
            .or_default()
            .push(import);
    }

    // Keyed by ModuleId so each module's imports can look up any
    // dependency's already-lowered HirModule; `loaded.modules` is
    // already in dependency-first order, so every module's own
    // dependencies are guaranteed present by the time it's this
    // module's turn -- *provided* every dependency actually succeeded.
    // `failed_modules` tracks every module whose own import resolution
    // failed (so it was never inserted into `lowered_by_module`), so a
    // dependent can be skipped safely instead of asking
    // `resolve_imports` to look up a dependency that was never lowered.
    let mut lowered_by_module: HashMap<module::ModuleId, (HirModule, SourceId)> = HashMap::new();
    let mut failed_modules: std::collections::HashSet<module::ModuleId> =
        std::collections::HashSet::new();
    let mut ids = hir::IdCursor::default();
    let mut diagnostics: Vec<Diagnostic> = Vec::new();

    for module in &loaded.modules {
        let owned_imports: Vec<loader::ImportRef> = imports_by_module
            .get(&module.id)
            .into_iter()
            .flatten()
            .map(|import_ref| (*import_ref).clone())
            .collect();

        // A module that imports from a dependency which itself already
        // failed to lower cannot be resolved either -- skip it (and
        // propagate the failure to whatever imports *this* module in
        // turn) without manufacturing a second diagnostic on top of the
        // root cause already recorded when the dependency failed. This
        // is what keeps a cascading failure from ever reaching
        // `resolve_imports` with a target module that was never
        // actually lowered.
        let depends_on_failed_module = owned_imports.iter().any(|import| {
            module::ModulePath::split_import_path(&import.segments)
                .and_then(|(path, _)| module_path_by_dotted.get(&path.dotted()))
                .is_some_and(|target| failed_modules.contains(target))
        });
        if depends_on_failed_module {
            failed_modules.insert(module.id);
            continue;
        }

        let resolved_imports = match resolve::resolve_imports(
            &owned_imports,
            module.source,
            &module_path_by_dotted,
            &lowered_by_module,
            interner,
        ) {
            Ok(resolved) => resolved,
            Err(mut diags) => {
                diagnostics.append(&mut diags);
                failed_modules.insert(module.id);
                continue;
            }
        };

        let (module_hir, next_ids, mut lower_diagnostics) = hir::lower_module_with_imports(
            &module.ast,
            module.source,
            interner,
            ids,
            resolved_imports,
        );
        ids = next_ids;
        if !lower_diagnostics.is_empty() {
            diagnostics.append(&mut lower_diagnostics);
        }
        lowered_by_module.insert(module.id, (module_hir, module.source));
    }

    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }

    // Merged in the same dependency-first order `loaded.modules` is
    // already in -- deterministic, and never dependent on a HashMap's
    // iteration order.
    //
    // The `expect` below is a genuine internal invariant, not a
    // user-triggerable one: `diagnostics` was just checked non-empty
    // above, and every module inserted into `failed_modules` -- whether
    // directly (its own import resolution failed) or transitively (it
    // depended on an already-failed module) -- always did so alongside
    // pushing at least one diagnostic onto `diagnostics` first. So an
    // empty `diagnostics` here implies an empty `failed_modules`, which
    // implies every discovered module was actually lowered and inserted
    // above. The three-module cascading-failure regression below
    // (`fails_atomically_instead_of_panicking_on_a_transitively_failed_dependency`)
    // is what enforces this at the public boundary.
    let mut merged = HirModule::default();
    let mut entry_source = None;
    for module in &loaded.modules {
        let (module_hir, source) = lowered_by_module
            .remove(&module.id)
            .expect("every discovered module was lowered above");
        if module.id == loaded.entry_module {
            entry_source = Some(source);
        }
        merged.functions.extend(module_hir.functions);
        merged.records.extend(module_hir.records);
        merged.variants.extend(module_hir.variants);
        // Every protocol declared anywhere in the project, and every
        // extend anywhere in the project -- coherence (authority,
        // overlap) and requirement resolution are project-wide concerns
        // (`rfcs/0009`), not scoped to one module, so `typeck` must see
        // every one of them merged together the same deterministic,
        // dependency-first order every other item kind already is,
        // never a HashMap's.
        merged.protocols.extend(module_hir.protocols);
        merged.extends.extend(module_hir.extends);
        merged.other_items.extend(module_hir.other_items);
    }
    let entry_source = entry_source.expect("the entry module is always among loaded.modules");

    // Canonical module-qualified identity for every item, built once
    // from the already-merged HIR (`rfcs/0007`) -- the single source of
    // truth `nir::print_module`/`nir::verify_module` and any future
    // qualified diagnostic read from, never a second name map that
    // could disagree with it.
    let module_path_of: HashMap<SourceId, String> = loaded
        .modules
        .iter()
        .map(|m| (m.source, m.path.dotted()))
        .collect();
    let registry = hir::registry::build(&merged, &module_path_of);

    // Identified by `ItemId` *before* typeck ever runs, so typeck's own
    // entry-signature check (`EntryMain::ByIdentity`) can be scoped to
    // this exact declaration -- never a global "any function named
    // `main`" check, which would also wrongly flag an ordinary,
    // differently-shaped `main` in a non-entry module (`rfcs/0006`).
    // `validate_entry_main` already guaranteed, from the entry module's
    // own AST, that it declares *exactly* one function named `main`
    // before any lowering ran -- and every module lowered with zero
    // diagnostics, checked just above -- so this lookup finding anything
    // other than exactly one match here would mean lowering silently
    // dropped or duplicated a declaration the AST preflight already
    // counted, a genuine internal invariant rather than a user-facing
    // condition.
    let main_symbol = interner.intern("main");
    let entry_item = merged
        .functions
        .iter()
        .find(|f| f.source == entry_source && f.name == main_symbol)
        .expect("validate_entry_main already guaranteed exactly one entry `main`")
        .id;

    let typeck_result = typeck::check_module_with_registry(
        &merged,
        loaded.manifest_source,
        interner,
        typeck::EntryMain::ByIdentity(Some(entry_item)),
        &registry,
    );
    if !typeck_result.diagnostics.is_empty() {
        return Err(typeck_result.diagnostics);
    }

    let resourceck_result = crate::resourceck::check_module(
        &merged,
        &typeck_result.local_types,
        &typeck_result.expr_types,
        interner,
    );
    if !resourceck_result.diagnostics.is_empty() {
        return Err(resourceck_result.diagnostics);
    }

    let nir_module = nir::lower_module_with_paths(
        &merged,
        &typeck_result.local_types,
        &typeck_result.expr_types,
        &typeck_result.pattern_case,
        &typeck_result.call_type_args,
        &typeck_result.call_evidence,
        &typeck_result.protocol_call_evidence,
        &resourceck_result.cleanup_edges,
        &resourceck_result.consume_sites,
        &resourceck_result.defer_plans,
        interner,
        loaded.manifest_source,
        &module_path_of,
    )?;

    let verify_diagnostics =
        nir::verify_module(&nir_module, loaded.manifest_source, interner, &registry);
    if !verify_diagnostics.is_empty() {
        return Err(verify_diagnostics);
    }

    Ok(CompiledProject {
        nir: nir_module,
        entry_item,
        registry,
    })
}

/// Checks the configured entry module's own AST for exactly one
/// function named `main`, *before* any HIR lowering runs -- so a
/// project with two entry-module `main` declarations gets one
/// deterministic `M0010`, anchored to the entry module's own source,
/// rather than `hir::lower`'s ordinary same-name-collision `R0001`.
/// `R0001` is still the right diagnostic for every *other* duplicate
/// declaration (including a non-`main` name, or `main` colliding with a
/// differently-kinded item like a `record`) -- this only ever looks at
/// function items literally named `main`, and only within the entry
/// module, so it never shadows `hir::lower`'s own check for anything
/// else. A `main` declared in any other module is untouched by this at
/// all (`rfcs/0006`).
fn validate_entry_main(
    loaded: &loader::LoadedProject,
    interner: &mut Interner,
) -> Result<(), Vec<Diagnostic>> {
    let entry_module = loaded
        .modules
        .iter()
        .find(|m| m.id == loaded.entry_module)
        .expect("the entry module is always among loaded.modules");
    let main_symbol = interner.intern("main");
    let mains: Vec<crate::source::Span> = entry_module
        .ast
        .items
        .iter()
        .filter_map(|item| match item {
            ast::Item::Function(f) if f.name.symbol == main_symbol => Some(f.name.span),
            _ => None,
        })
        .collect();

    match mains[..] {
        [] => Err(vec![
            Diagnostic::error(
                codes::INVALID_ENTRY,
                entry_module.source,
                crate::source::Span::dummy(),
                format!(
                    "entry module `{}` has no `main` function",
                    loaded.manifest.entry
                ),
            )
            .with_primary_label("configured entry point"),
        ]),
        [_] => Ok(()),
        [first, second, ..] => Err(vec![
            Diagnostic::error(
                codes::INVALID_ENTRY,
                entry_module.source,
                second,
                format!(
                    "entry module declares more than one `main` function ({} total)",
                    mains.len()
                ),
            )
            .with_primary_label("duplicate `main`")
            .with_label(first, "first declared here"),
        ]),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::Interpreter;
    use std::path::PathBuf;

    struct TempProject {
        dir: PathBuf,
    }

    impl TempProject {
        fn new(name: &str) -> Self {
            static COUNTER: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
            let n = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let dir = std::env::temp_dir().join(format!(
                "napitia_compile_test_{}_{name}_{n}",
                std::process::id()
            ));
            std::fs::create_dir_all(&dir).expect("failed to create scratch project dir");
            TempProject { dir }
        }

        fn write(&self, relative: &str, content: &str) {
            let path = self.dir.join(relative);
            std::fs::create_dir_all(path.parent().unwrap()).expect("failed to create parent dir");
            std::fs::write(path, content).expect("failed to write scratch file");
        }

        fn manifest_path(&self) -> PathBuf {
            self.dir.join("napitia.toml")
        }
    }

    impl Drop for TempProject {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.dir);
        }
    }

    const MANIFEST: &str = "[package]\nname = \"hello\"\nversion = \"0.1.0\"\n\n\
                             [project]\nsource-root = \"src\"\nentry = \"main.npt\"\n";

    #[test]
    fn compiles_and_runs_a_two_file_project() {
        let project = TempProject::new("two_file_run");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import math.add;\nfunc main() -> i64 { return add(20, 22) }\n",
        );
        project.write(
            "src/math.npt",
            "public func add(left: i64, right: i64) -> i64 { left + right }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(42)));
    }

    #[test]
    fn compiles_a_nested_module_import() {
        let project = TempProject::new("nested_run");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import models.user.User;\n\
             func main() -> i64 { value u = User { id: 7 }; return u.id }\n",
        );
        project.write(
            "src/models/user.npt",
            "public record User { public id: i64 }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(7)));
    }

    #[test]
    fn forward_reference_across_modules_works_regardless_of_discovery_order() {
        // main imports from both b and a; a also imports from b, so b
        // must be lowered before both -- this only works if module
        // lowering order is dependency-first, not discovery order.
        let project = TempProject::new("forward_ref");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import a.thing;\nfunc main() -> i64 { return thing() }\n",
        );
        project.write(
            "src/a.npt",
            "import b.helper;\npublic func thing() -> i64 { return helper() }\n",
        );
        project.write("src/b.npt", "public func helper() -> i64 { return 99 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(99)));
    }

    #[test]
    fn private_function_import_is_rejected() {
        let project = TempProject::new("private_fn");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import math.secret;\nfunc main() -> i64 { return secret() }\n",
        );
        project.write("src/math.npt", "func secret() -> i64 { return 1 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0006");
    }

    #[test]
    fn missing_entry_main_is_m0010() {
        let project = TempProject::new("missing_main");
        project.write("napitia.toml", MANIFEST);
        project.write("src/main.npt", "func not_main() -> i64 { return 0 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0010");
        // Must name the actual entry file (from the manifest's own
        // `entry` key), never the manifest path itself.
        assert_eq!(
            diags[0].message,
            "entry module `main.npt` has no `main` function"
        );
    }

    #[test]
    fn two_main_functions_in_the_entry_module_is_exactly_m0010_not_r0001() {
        // `hir::lower`'s own same-name-collision check would otherwise
        // fire first (R0001) -- the entry module's `main` is special
        // enough (it decides the whole project's executable entry
        // point) to get its own diagnostic instead, checked before any
        // lowering runs at all.
        let project = TempProject::new("duplicate_main");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "func main() -> i64 { return 1 } func main() -> i64 { return 2 }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0010");
    }

    #[test]
    fn a_duplicate_non_main_declaration_in_the_entry_module_is_still_r0001() {
        // The entry-`main` preflight only ever looks at functions named
        // `main` -- every other duplicate declaration (including one
        // colliding on the entry module's own `main` name but as a
        // *different* item kind, or a same-name/same-kind duplicate of
        // anything else) is untouched, and still goes through
        // `hir::lower`'s ordinary same-name-collision check.
        let project = TempProject::new("duplicate_non_main");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "func main() -> i64 { return helper() } \
             func helper() -> i64 { return 1 } \
             func helper() -> i64 { return 2 }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0001");
    }

    #[test]
    fn a_parameterized_entry_main_still_produces_the_signature_diagnostic() {
        let project = TempProject::new("parameterized_entry_main");
        project.write("napitia.toml", MANIFEST);
        project.write("src/main.npt", "func main(n: i64) -> i64 { return n }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0012");
    }

    #[test]
    fn main_in_a_non_entry_module_is_ignored() {
        let project = TempProject::new("non_entry_main");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import helper.thing;\nfunc main() -> i64 { return thing() }\n",
        );
        // helper also declares its own (private) `main` -- must never
        // be treated as the entry point.
        project.write(
            "src/helper.npt",
            "public func thing() -> i64 { return 5 } \
             func main() -> i64 { return 999 }",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(5)));
    }

    #[test]
    fn repeated_compiles_produce_identical_nir_output() {
        let project = TempProject::new("deterministic_nir");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import math.add;\nfunc main() -> i64 { return add(1, 2) }\n",
        );
        project.write(
            "src/math.npt",
            "public func add(left: i64, right: i64) -> i64 { left + right }\n",
        );

        let render = || {
            let mut map = SourceMap::new();
            let mut interner = Interner::new();
            let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
                .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
            crate::nir::print_module(&compiled.nir, &interner, &compiled.registry)
        };
        assert_eq!(render(), render());
    }

    #[test]
    fn a_function_alias_resolves_to_the_exact_original_item_id() {
        let project = TempProject::new("alias_function");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import math.add as plus;\nfunc main() -> i64 { return plus(1, 2) }\n",
        );
        project.write(
            "src/math.npt",
            "public func add(left: i64, right: i64) -> i64 { left + right }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(3)));
    }

    #[test]
    fn a_record_alias_resolves_in_annotations_and_construction() {
        let project = TempProject::new("alias_record");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import models.User as Account;\n\
             func id_of(a: Account) -> i64 { return a.id }\n\
             func main() -> i64 { value a = Account { id: 9 }; return id_of(a) }\n",
        );
        project.write("src/models.npt", "public record User { public id: i64 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(9)));
    }

    #[test]
    fn a_variant_alias_resolves_in_annotations_construction_and_patterns() {
        let project = TempProject::new("alias_variant");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import shapes.Shape as Figure;\n\
             func area(s: Figure) -> i64 { return match s { Circle(r) => r * r, Square(x) => x * x } }\n\
             func main() -> i64 { value c = Figure.Circle(3); return area(c) }\n",
        );
        project.write(
            "src/shapes.npt",
            "public variant Shape { Circle(i64), Square(i64) }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(9)));
    }

    #[test]
    fn the_original_name_is_unavailable_once_aliased() {
        let project = TempProject::new("alias_hides_original");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import models.User as Account;\n\
             func main() -> i64 { value u = User { id: 1 }; return u.id }\n",
        );
        project.write("src/models.npt", "public record User { public id: i64 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0007");
    }

    #[test]
    fn two_same_named_cross_module_records_coexist_through_aliases() {
        let project = TempProject::new("alias_coexist");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import sales.User as SalesUser;\n\
             import admin.User as AdminUser;\n\
             func sales_id(u: SalesUser) -> i64 { return u.id }\n\
             func admin_id(u: AdminUser) -> i64 { return u.id }\n\
             func main() -> i64 {\n\
             \x20   value s = SalesUser { id: 20 };\n\
             \x20   value a = AdminUser { id: 22 };\n\
             \x20   return sales_id(s) + admin_id(a)\n\
             }\n",
        );
        project.write("src/sales.npt", "public record User { public id: i64 }\n");
        project.write("src/admin.npt", "public record User { public id: i64 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(42)));
    }

    #[test]
    fn an_alias_does_not_create_a_new_nominal_type() {
        // `SalesUser` and `AdminUser` are just local spellings for two
        // still-genuinely-distinct declarations -- passing one where
        // the other is expected must still be rejected.
        let project = TempProject::new("alias_nominal_incompatible");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import sales.User as SalesUser;\n\
             import admin.User as AdminUser;\n\
             func sales_id(u: SalesUser) -> i64 { return u.id }\n\
             func main() -> i64 { value a = AdminUser { id: 22 }; return sales_id(a) }\n",
        );
        project.write("src/sales.npt", "public record User { public id: i64 }\n");
        project.write("src/admin.npt", "public record User { public id: i64 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
        // Both same-named `User` records must read as genuinely
        // different in the message text, not the same ambiguous `User`
        // on both sides (`rfcs/0007`); no raw ItemId anywhere in it,
        // since typeck diagnostics -- unlike textual NIR -- never
        // attach a bare `#id`.
        assert_eq!(
            diags[0].message,
            "argument type does not match the parameter's declared type: \
             expected `sales.User`, found `admin.User`"
        );
        assert!(!diags[0].message.contains('#'));
    }

    #[test]
    fn cross_module_same_named_record_mismatch_names_both_nested_module_paths() {
        // Nested module paths (`sales.user`/`admin.user`, not flat
        // `sales`/`admin`) -- the exact worked example rfcs/0007 itself
        // documents.
        let project = TempProject::new("typeck_qualify_nested_records");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import sales.user.User as SalesUser;\n\
             import admin.user.User;\n\
             import admin.user.user_id;\n\
             func main() -> i64 { value s = SalesUser { id: 1 }; return user_id(s) }\n",
        );
        project.write(
            "src/admin/user.npt",
            "public record User { public id: i64 }\n\
             public func user_id(u: User) -> i64 { return u.id }\n",
        );
        project.write(
            "src/sales/user.npt",
            "public record User { public id: i64 }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
        assert_eq!(
            diags[0].message,
            "argument type does not match the parameter's declared type: \
             expected `admin.user.User`, found `sales.user.User`"
        );
    }

    #[test]
    fn cross_module_same_named_variants_show_both_qualified_names() {
        let project = TempProject::new("typeck_qualify_variants");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import sales.Status as SalesStatus;\n\
             import admin.accept;\n\
             func main() -> i64 { value s = SalesStatus.Open; return accept(s) }\n",
        );
        project.write(
            "src/admin.npt",
            "public variant Status { Open, Closed }\n\
             public func accept(s: Status) -> i64 { return 0 }\n",
        );
        project.write("src/sales.npt", "public variant Status { Open, Closed }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "T0001");
        assert_eq!(
            diags[0].message,
            "argument type does not match the parameter's declared type: \
             expected `admin.Status`, found `sales.Status`"
        );
    }

    #[test]
    fn aliases_of_the_same_declaration_remain_type_compatible() {
        // Unlike the mismatch tests above: `models.User` imported twice,
        // under two different local aliases, is still exactly one
        // declaration -- passing a value built through one alias where
        // the other is expected must compile cleanly, never T0001.
        let project = TempProject::new("typeck_alias_same_decl_compatible");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import models.User as Account;\n\
             import models.User as Profile;\n\
             import models.user_id;\n\
             func main() -> i64 { value p = Profile { id: 7 }; return user_id(p) }\n",
        );
        project.write(
            "src/models.npt",
            "public record User { public id: i64 }\n\
             public func user_id(u: User) -> i64 { return u.id }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(7)));
    }

    #[test]
    fn an_alias_named_after_a_primitive_never_shadows_it() {
        let project = TempProject::new("alias_primitive_precedence");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import models.User as i64;\n\
             func main() -> i64 { return 1 }\n",
        );
        project.write("src/models.npt", "public record User { public id: i64 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(1)));
    }

    #[test]
    fn a_failed_import_leaves_no_partial_alias_in_the_namespace() {
        // `helper.secret` is private, so this whole module's imports
        // must fail atomically -- the earlier, individually-valid
        // `helper.thing as greet` alias must never partially register
        // before the later failure is discovered.
        let project = TempProject::new("alias_partial_failure");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import helper.thing as greet;\n\
             import helper.secret as whisper;\n\
             func main() -> i64 { return greet() }\n",
        );
        project.write(
            "src/helper.npt",
            "public func thing() -> i64 { return 1 }\nfunc secret() -> i64 { return 2 }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0006");
    }

    #[test]
    fn the_same_variant_imported_under_two_aliases_is_not_falsely_ambiguous() {
        // `Shape` is imported twice, as `Figure` and as `Form` -- both
        // resolve to the exact same `ItemId`, so an *unqualified* case
        // constructor and a `match` over it must both still work: the
        // variant having two local names must never make its own cases
        // look like they belong to two different variants.
        let project = TempProject::new("alias_same_variant_two_aliases");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import shapes.Shape as Figure;\n\
             import shapes.Shape as Form;\n\
             func main() -> i64 {\n\
             \x20   value first = Circle(4);\n\
             \x20   value second = Form.Square(2);\n\
             \x20   return match first {\n\
             \x20       Circle(n) => n,\n\
             \x20       Square(n) => n,\n\
             \x20   } + match second {\n\
             \x20       Circle(n) => n,\n\
             \x20       Square(n) => n,\n\
             \x20   }\n\
             }\n",
        );
        project.write(
            "src/shapes.npt",
            "public variant Shape { Circle(i64), Square(i64) }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(6)));
    }

    #[test]
    fn qualified_construction_works_through_every_alias_of_the_same_variant() {
        let project = TempProject::new("alias_same_variant_qualified");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import shapes.Shape as Figure;\n\
             import shapes.Shape as Form;\n\
             func main() -> i64 {\n\
             \x20   value a = Figure.Circle(3);\n\
             \x20   value b = Form.Circle(9);\n\
             \x20   return match a { Circle(n) => n, Square(n) => n }\n\
             \x20       + match b { Circle(n) => n, Square(n) => n }\n\
             }\n",
        );
        project.write(
            "src/shapes.npt",
            "public variant Shape { Circle(i64), Square(i64) }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(12)));
    }

    #[test]
    fn two_genuinely_distinct_variants_sharing_a_case_name_remain_ambiguous() {
        // Unlike the two-aliases-of-one-variant case above, `shapes.Shape`
        // and `vehicles.Vehicle` are two real, different declarations that
        // both happen to declare a case named `Circle` -- this must still
        // be rejected, and the message must name both (sorted, deduplicated)
        // local names.
        let project = TempProject::new("alias_two_distinct_variants_ambiguous");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import shapes.Shape as Figure;\n\
             import vehicles.Vehicle as Ride;\n\
             func main() -> i64 { value x = Circle(4); return 0 }\n",
        );
        project.write(
            "src/shapes.npt",
            "public variant Shape { Circle(i64), Square(i64) }\n",
        );
        project.write(
            "src/vehicles.npt",
            "public variant Vehicle { Circle(i64), Truck(i64) }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0006");
        assert_eq!(
            diags[0].message,
            "`Circle` is ambiguous: it names a case in more than one variant (Figure, Ride); \
             use a qualified path (`Variant.Circle`)"
        );
    }

    #[test]
    fn the_ambiguous_constructor_diagnostic_is_identical_regardless_of_import_order() {
        let render = |first: &str, second: &str| {
            let project = TempProject::new("alias_ambiguity_order");
            project.write("napitia.toml", MANIFEST);
            project.write(
                "src/main.npt",
                &format!(
                    "import {first};\n\
                     import {second};\n\
                     func main() -> i64 {{ value x = Circle(4); return 0 }}\n"
                ),
            );
            project.write(
                "src/shapes.npt",
                "public variant Shape { Circle(i64), Square(i64) }\n",
            );
            project.write(
                "src/vehicles.npt",
                "public variant Vehicle { Circle(i64), Truck(i64) }\n",
            );

            let mut map = SourceMap::new();
            let mut interner = Interner::new();
            let diags =
                compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
            assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
            diags[0].message.clone()
        };

        let forward = render("shapes.Shape as Figure", "vehicles.Vehicle as Ride");
        let reversed = render("vehicles.Vehicle as Ride", "shapes.Shape as Figure");
        assert_eq!(forward, reversed);
    }

    #[test]
    fn three_aliases_of_the_same_variant_do_not_panic_or_duplicate_candidates() {
        // Guards `add_case_candidate`'s dedup directly against more than
        // two aliases of the same declaration, and against
        // `variant_name`'s internal lookup ever panicking when a variant
        // has several local names in scope at once.
        let project = TempProject::new("alias_same_variant_three_aliases");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import shapes.Shape as Figure;\n\
             import shapes.Shape as Form;\n\
             import shapes.Shape as Outline;\n\
             func main() -> i64 {\n\
             \x20   value x = Circle(5);\n\
             \x20   return match x { Circle(n) => n, Square(n) => n }\n\
             }\n",
        );
        project.write(
            "src/shapes.npt",
            "public variant Shape { Circle(i64), Square(i64) }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Int(5)));
    }

    /// A project with two same-named, same-shaped `User` records, each
    /// used (via an alias) as a parameter type, a return type, and a
    /// `mutable`-bound (alloc/store/load) local -- the fixture shared by
    /// every qualified-NIR test below (`rfcs/0007`).
    fn write_same_named_record_project(project: &TempProject) {
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import sales.User as SalesUser;\n\
             import admin.User as AdminUser;\n\
             func sales_id(u: SalesUser) -> i64 { return u.id }\n\
             func admin_id(u: AdminUser) -> i64 { return u.id }\n\
             func make_sales() -> SalesUser { mutable s = SalesUser { id: 1 }; return s }\n\
             func make_admin() -> AdminUser { mutable a = AdminUser { id: 2 }; return a }\n\
             func main() -> i64 {\n\
             \x20   return sales_id(make_sales()) + admin_id(make_admin())\n\
             }\n",
        );
        project.write("src/sales.npt", "public record User { public id: i64 }\n");
        project.write("src/admin.npt", "public record User { public id: i64 }\n");
    }

    fn compile_and_print(project: &TempProject) -> String {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        crate::nir::print_module(&compiled.nir, &interner, &compiled.registry)
    }

    #[test]
    fn qualified_nir_distinguishes_same_named_types_in_parameter_position() {
        let project = TempProject::new("nir_qualify_params");
        write_same_named_record_project(&project);
        let text = compile_and_print(&project);
        assert!(text.contains("(%0: sales.User#"), "{text}");
        assert!(text.contains("(%0: admin.User#"), "{text}");
    }

    #[test]
    fn qualified_nir_distinguishes_same_named_types_in_return_position() {
        let project = TempProject::new("nir_qualify_returns");
        write_same_named_record_project(&project);
        let text = compile_and_print(&project);
        assert!(
            text.contains("make_sales") && text.contains(") -> sales.User#"),
            "{text}"
        );
        assert!(
            text.contains("make_admin") && text.contains(") -> admin.User#"),
            "{text}"
        );
    }

    #[test]
    fn qualified_nir_distinguishes_same_named_types_in_allocations() {
        let project = TempProject::new("nir_qualify_alloc");
        write_same_named_record_project(&project);
        let text = compile_and_print(&project);
        assert!(text.contains("alloc.sales.User#"), "{text}");
        assert!(text.contains("alloc.admin.User#"), "{text}");
    }

    #[test]
    fn qualified_nir_never_prints_an_import_alias() {
        let project = TempProject::new("nir_qualify_no_alias");
        write_same_named_record_project(&project);
        let text = compile_and_print(&project);
        assert!(!text.contains("SalesUser"), "{text}");
        assert!(!text.contains("AdminUser"), "{text}");
    }

    #[test]
    fn qualified_nir_declaration_and_reference_formatting_agree() {
        // Whatever `sales.User`'s declaration-site id is (from its
        // `record.create`), every reference to it -- its qualified
        // parameter type, its qualified return type, its `alloc` -- must
        // repeat that exact same qualified name, never a different
        // spelling or a different id for the same item.
        let project = TempProject::new("nir_qualify_agree");
        write_same_named_record_project(&project);
        let text = compile_and_print(&project);
        let start = text.find("record.create @sales.User#").expect(&text);
        let rest = &text[start + "record.create @".len()..];
        let end = rest.find('(').expect(&text);
        let sales_ref = &rest[..end];
        assert!(text.contains(&format!("(%0: {sales_ref})")), "{text}");
        assert!(text.contains(&format!("-> {sales_ref}")), "{text}");
        assert!(text.contains(&format!("alloc.{sales_ref}")), "{text}");
    }

    #[test]
    fn qualified_nir_is_byte_identical_across_repeated_compiles() {
        let project = TempProject::new("nir_qualify_repeatable");
        write_same_named_record_project(&project);
        assert_eq!(compile_and_print(&project), compile_and_print(&project));
    }

    #[test]
    fn qualified_nir_is_identical_regardless_of_import_order() {
        let forward = TempProject::new("nir_qualify_order_forward");
        write_same_named_record_project(&forward);

        let reversed = TempProject::new("nir_qualify_order_reversed");
        reversed.write("napitia.toml", MANIFEST);
        reversed.write(
            "src/main.npt",
            "import admin.User as AdminUser;\n\
             import sales.User as SalesUser;\n\
             func sales_id(u: SalesUser) -> i64 { return u.id }\n\
             func admin_id(u: AdminUser) -> i64 { return u.id }\n\
             func make_sales() -> SalesUser { mutable s = SalesUser { id: 1 }; return s }\n\
             func make_admin() -> AdminUser { mutable a = AdminUser { id: 2 }; return a }\n\
             func main() -> i64 {\n\
             \x20   return sales_id(make_sales()) + admin_id(make_admin())\n\
             }\n",
        );
        reversed.write("src/sales.npt", "public record User { public id: i64 }\n");
        reversed.write("src/admin.npt", "public record User { public id: i64 }\n");

        assert_eq!(compile_and_print(&forward), compile_and_print(&reversed));
    }

    /// The exact source text a diagnostic's label span covers, sliced
    /// out of `text` -- used to assert *which token* a label points at
    /// without hand-computing byte offsets (`rfcs/0007`).
    fn label_text(text: &str, span_start: u32, span_end: u32) -> &str {
        &text[span_start as usize..span_end as usize]
    }

    #[test]
    fn alias_collision_labels_precisely_the_alias_token_not_the_whole_import() {
        let project = TempProject::new("alias_span_alias_vs_alias");
        project.write("napitia.toml", MANIFEST);
        let main_text = "import a.f as shared;\n\
                          import b.g as shared;\n\
                          func main() -> i64 { return shared() }\n";
        project.write("src/main.npt", main_text);
        project.write("src/a.npt", "public func f() -> i64 { return 1 }\n");
        project.write("src/b.npt", "public func g() -> i64 { return 2 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0007");
        // The new (conflicting) import's own primary span is just its
        // alias token, `shared` on line 2 -- not the whole `import b.g
        // as shared;` statement.
        assert_eq!(
            label_text(
                main_text,
                diags[0].primary_span.start,
                diags[0].primary_span.end
            ),
            "shared"
        );
        // The "already imported here" label is the *first* import's own
        // alias token -- also just `shared`, not its whole statement.
        let already_imported = diags[0]
            .labels
            .iter()
            .find(|l| l.message == "already imported here")
            .expect("expected an \"already imported here\" label");
        assert_eq!(
            label_text(
                main_text,
                already_imported.span.start,
                already_imported.span.end
            ),
            "shared"
        );
    }

    #[test]
    fn alias_collision_with_an_unaliased_import_labels_each_side_precisely() {
        let project = TempProject::new("alias_span_alias_vs_unaliased");
        project.write("napitia.toml", MANIFEST);
        let main_text = "import a.thing;\n\
                          import b.other as thing;\n\
                          func main() -> i64 { return thing() }\n";
        project.write("src/main.npt", main_text);
        project.write("src/a.npt", "public func thing() -> i64 { return 1 }\n");
        project.write("src/b.npt", "public func other() -> i64 { return 2 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0007");
        // The new aliased import's primary span is its alias token.
        assert_eq!(
            label_text(
                main_text,
                diags[0].primary_span.start,
                diags[0].primary_span.end
            ),
            "thing"
        );
        // The earlier, unaliased import has no alias to point at -- its
        // label is the imported item's own written name (also `thing`,
        // the last path segment of `import a.thing;`), never the whole
        // statement.
        let already_imported = diags[0]
            .labels
            .iter()
            .find(|l| l.message == "already imported here")
            .expect("expected an \"already imported here\" label");
        assert_eq!(
            label_text(
                main_text,
                already_imported.span.start,
                already_imported.span.end
            ),
            "thing"
        );
    }

    #[test]
    fn alias_collision_with_a_local_function_labels_the_alias_token() {
        let project = TempProject::new("alias_span_alias_vs_local_function");
        project.write("napitia.toml", MANIFEST);
        let main_text = "import a.thing as helper;\n\
                          func helper() -> i64 { return 0 }\n\
                          func main() -> i64 { return helper() }\n";
        project.write("src/main.npt", main_text);
        project.write("src/a.npt", "public func thing() -> i64 { return 1 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0007");
        let already_imported = diags[0]
            .labels
            .iter()
            .find(|l| l.message == "already imported here")
            .expect("expected an \"already imported here\" label");
        assert_eq!(
            label_text(
                main_text,
                already_imported.span.start,
                already_imported.span.end
            ),
            "helper"
        );
    }

    #[test]
    fn alias_collision_with_a_local_record_labels_the_alias_token() {
        let project = TempProject::new("alias_span_alias_vs_local_record");
        project.write("napitia.toml", MANIFEST);
        let main_text = "import a.Thing as Helper;\n\
                          record Helper { x: i64 }\n\
                          func main() -> i64 { return 0 }\n";
        project.write("src/main.npt", main_text);
        project.write("src/a.npt", "public record Thing { public y: i64 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0007");
        let already_imported = diags[0]
            .labels
            .iter()
            .find(|l| l.message == "already imported here")
            .expect("expected an \"already imported here\" label");
        assert_eq!(
            label_text(
                main_text,
                already_imported.span.start,
                already_imported.span.end
            ),
            "Helper"
        );
    }

    #[test]
    fn alias_collision_with_a_local_variant_labels_the_alias_token() {
        let project = TempProject::new("alias_span_alias_vs_local_variant");
        project.write("napitia.toml", MANIFEST);
        let main_text = "import a.Thing as Helper;\n\
                          variant Helper { A, B }\n\
                          func main() -> i64 { return 0 }\n";
        project.write("src/main.npt", main_text);
        project.write("src/a.npt", "public variant Thing { X, Y }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0007");
        let already_imported = diags[0]
            .labels
            .iter()
            .find(|l| l.message == "already imported here")
            .expect("expected an \"already imported here\" label");
        assert_eq!(
            label_text(
                main_text,
                already_imported.span.start,
                already_imported.span.end
            ),
            "Helper"
        );
    }

    #[test]
    fn wrong_variant_with_a_single_alternative_owner_keeps_its_wording() {
        let project = TempProject::new("wrong_variant_single_owner");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import first.First;\n\
             import target.Target;\n\
             func main() -> i64 { value x = Target.Shared; return 0 }\n",
        );
        project.write(
            "src/first.npt",
            "public variant First { Shared(i64), Other }\n",
        );
        project.write("src/target.npt", "public variant Target { Solo }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0013");
        assert_eq!(
            diags[0].message,
            "`Shared` is a case of variant `First`, not `Target`"
        );
    }

    /// Shared fixture for the multi-owner `WRONG_VARIANT` tests below:
    /// `First` and `Second` both declare `Shared`; `Target` does not.
    fn write_wrong_variant_multi_owner_project(project: &TempProject, first_import_first: bool) {
        project.write("napitia.toml", MANIFEST);
        let imports = if first_import_first {
            "import first.First;\nimport second.Second;\n"
        } else {
            "import second.Second;\nimport first.First;\n"
        };
        project.write(
            "src/main.npt",
            &format!(
                "{imports}import target.Target;\n\
                 func main() -> i64 {{ value x = Target.Shared; return 0 }}\n"
            ),
        );
        project.write(
            "src/first.npt",
            "public variant First { Shared(i64), Other }\n",
        );
        project.write(
            "src/second.npt",
            "public variant Second { Shared(i64), Alt }\n",
        );
        project.write("src/target.npt", "public variant Target { Solo }\n");
    }

    #[test]
    fn wrong_variant_with_two_alternative_owners_lists_them_deterministically() {
        let project = TempProject::new("wrong_variant_two_owners");
        write_wrong_variant_multi_owner_project(&project, true);

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0013");
        assert_eq!(
            diags[0].message,
            "`Shared` is a case of variants `First`, `Second`, not `Target`"
        );
    }

    #[test]
    fn wrong_variant_message_is_identical_regardless_of_import_order() {
        let forward = TempProject::new("wrong_variant_order_forward");
        write_wrong_variant_multi_owner_project(&forward, true);
        let reversed = TempProject::new("wrong_variant_order_reversed");
        write_wrong_variant_multi_owner_project(&reversed, false);

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let forward_diags =
            compile_project(&forward.manifest_path(), &mut map, &mut interner).unwrap_err();
        let reversed_diags =
            compile_project(&reversed.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(forward_diags.len(), 1, "unexpected: {forward_diags:?}");
        assert_eq!(reversed_diags.len(), 1, "unexpected: {reversed_diags:?}");
        assert_eq!(forward_diags[0].message, reversed_diags[0].message);
        assert_eq!(
            forward_diags[0].message,
            "`Shared` is a case of variants `First`, `Second`, not `Target`"
        );
    }

    #[test]
    fn wrong_variant_never_duplicates_an_owner_reached_through_two_aliases() {
        // `First` is imported twice, under two different aliases -- it
        // must still be named exactly once in the owner list, alongside
        // `Second` (a genuinely distinct variant), never twice.
        let project = TempProject::new("wrong_variant_duplicate_alias");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import first.First as Figure;\n\
             import first.First as Form;\n\
             import second.Second;\n\
             import target.Target;\n\
             func main() -> i64 { value x = Target.Shared; return 0 }\n",
        );
        project.write(
            "src/first.npt",
            "public variant First { Shared(i64), Other }\n",
        );
        project.write(
            "src/second.npt",
            "public variant Second { Shared(i64), Alt }\n",
        );
        project.write("src/target.npt", "public variant Target { Solo }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0013");
        // `First` has no unaliased import in scope here -- only its two
        // aliases, `Figure` and `Form` -- so the owner list names it by
        // whichever local spelling `variant_name` deterministically picks
        // (`Figure`, lexicographically smallest), exactly once, never
        // both `Figure` and `Form` for the same underlying ItemId.
        assert_eq!(
            diags[0].message,
            "`Shared` is a case of variants `Figure`, `Second`, not `Target`"
        );
    }

    // -- Fix 1 / Fix 2: cross-module protocols, extends, and calls --

    /// Protocol declared in one module, extend declared in a *different*
    /// module (authorized through the aggregate it extends, not the
    /// protocol itself), call made from the entry module -- every stage
    /// (load, import resolution, HIR merge, typeck, NIR, verifier,
    /// interpreter) must see the whole picture, not just the module it
    /// happened to be declared in.
    #[test]
    fn cross_module_protocol_and_extend_compile_and_run() {
        let project = TempProject::new("cross_module_protocol");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/protocols.npt",
            "public protocol Equal[T] {\n    func equal(left: T, right: T) -> bool;\n}\n",
        );
        project.write(
            "src/shapes.npt",
            "import protocols.Equal;\n\
             public record Point { public x: i64 }\n\
             extend Equal[Point] {\n    func equal(left: Point, right: Point) -> bool {\n        return left.x == right.x\n    }\n}\n",
        );
        project.write(
            "src/main.npt",
            "import protocols.Equal;\n\
             import shapes.Point;\n\
             func main() -> bool {\n    \
                 value a = Point { x: 1 };\n    \
                 value b = Point { x: 1 };\n    \
                 return Equal[Point].equal(a, b)\n\
             }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Bool(true)));
    }

    #[test]
    fn cross_module_protocol_call_through_an_import_alias_resolves() {
        let project = TempProject::new("cross_module_alias");
        project.write("napitia.toml", MANIFEST);
        // The extend lives in protocols.npt, the protocol's own module --
        // a primitive first type argument (i64) has no declaring module
        // of its own to lend authority, so only the protocol-owning
        // module may extend it (`rfcs/0009`).
        project.write(
            "src/protocols.npt",
            "public protocol Equal[T] {\n    func equal(left: T, right: T) -> bool;\n}\n\
             extend Equal[i64] {\n    func equal(left: i64, right: i64) -> bool {\n        return left == right\n    }\n}\n",
        );
        project.write(
            "src/main.npt",
            "import protocols.Equal as Eq;\n\
             func main() -> bool {\n    return Eq[i64].equal(1, 1)\n}\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Bool(true)));
    }

    #[test]
    fn importing_a_private_protocol_across_modules_is_rejected() {
        let project = TempProject::new("private_protocol");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/protocols.npt",
            "protocol Equal[T] {\n    func equal(left: T, right: T) -> bool;\n}\n",
        );
        project.write(
            "src/main.npt",
            "import protocols.Equal;\n\
             func main() -> i64 { return 0 }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0006");
    }

    #[test]
    fn calling_an_unknown_method_on_an_imported_protocol_is_r0024() {
        let project = TempProject::new("unknown_imported_method");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/protocols.npt",
            "public protocol Equal[T] {\n    func equal(left: T, right: T) -> bool;\n}\n",
        );
        project.write(
            "src/main.npt",
            "import protocols.Equal;\n\
             func main() -> bool { return Equal[i64].nope(1, 1) }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert!(
            diags.iter().any(|d| d.code == "R0024"),
            "unexpected diagnostics: {diags:?}"
        );
    }

    #[test]
    fn two_aliases_of_the_same_imported_protocol_do_not_create_duplicate_identities() {
        // Two different local names for the *same* imported protocol
        // (Equal, and Eq) are not a collision at all (that only applies
        // to two imports introducing the *same* local name) -- the real
        // requirement is that calling through either alias resolves to
        // the exact same canonical protocol identity, never two
        // independent ones that could (for instance) falsely overlap
        // with each other or double-count as two separate extends.
        let project = TempProject::new("two_protocol_aliases");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/protocols.npt",
            "public protocol Equal[T] {\n    func equal(left: T, right: T) -> bool;\n}\n\
             extend Equal[i64] {\n    func equal(left: i64, right: i64) -> bool {\n        return left == right\n    }\n}\n",
        );
        project.write(
            "src/main.npt",
            "import protocols.Equal;\n\
             import protocols.Equal as Eq;\n\
             func main() -> bool {\n    return Equal[i64].equal(1, 1) == Eq[i64].equal(1, 1)\n}\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let compiled = compile_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let result = Interpreter::new(&compiled.nir).run_item(compiled.entry_item);
        assert_eq!(result, Ok(crate::interpreter::Value::Bool(true)));

        // Neither alias may influence the canonical printed identity of
        // the protocol, the extend, or its method: there is exactly one
        // `extend` declaration and one `equal` method declaration,
        // regardless of how many local names resolve to it (each is
        // referenced twice in the NIR text below: once at its own
        // declaration, once from the call site / method table).
        let text = crate::nir::print_module(&compiled.nir, &interner, &compiled.registry);
        assert!(!text.contains("<item #"), "{text}");
        assert_eq!(text.matches("extend @").count(), 1, "{text}");
        assert_eq!(text.matches("equal#").count(), 2, "{text}");
    }

    /// Reverse import order (`Point` before `Equal` instead of after)
    /// must produce byte-identical NIR and an identical run result --
    /// resolution must never depend on declaration/import order.
    #[test]
    fn reverse_import_order_produces_identical_nir_and_result() {
        let forward = TempProject::new("import_order_forward");
        forward.write("napitia.toml", MANIFEST);
        forward.write(
            "src/protocols.npt",
            "public protocol Equal[T] {\n    func equal(left: T, right: T) -> bool;\n}\n",
        );
        forward.write(
            "src/shapes.npt",
            "import protocols.Equal;\n\
             public record Point { public x: i64 }\n\
             extend Equal[Point] {\n    func equal(left: Point, right: Point) -> bool {\n        return left.x == right.x\n    }\n}\n",
        );
        forward.write(
            "src/main.npt",
            "import protocols.Equal;\n\
             import shapes.Point;\n\
             func main() -> bool {\n    \
                 value a = Point { x: 3 };\n    \
                 value b = Point { x: 3 };\n    \
                 return Equal[Point].equal(a, b)\n\
             }\n",
        );

        let reversed = TempProject::new("import_order_reversed");
        reversed.write("napitia.toml", MANIFEST);
        reversed.write(
            "src/protocols.npt",
            "public protocol Equal[T] {\n    func equal(left: T, right: T) -> bool;\n}\n",
        );
        reversed.write(
            "src/shapes.npt",
            "import protocols.Equal;\n\
             public record Point { public x: i64 }\n\
             extend Equal[Point] {\n    func equal(left: Point, right: Point) -> bool {\n        return left.x == right.x\n    }\n}\n",
        );
        reversed.write(
            "src/main.npt",
            "import shapes.Point;\n\
             import protocols.Equal;\n\
             func main() -> bool {\n    \
                 value a = Point { x: 3 };\n    \
                 value b = Point { x: 3 };\n    \
                 return Equal[Point].equal(a, b)\n\
             }\n",
        );

        let mut forward_map = SourceMap::new();
        let mut forward_interner = Interner::new();
        let forward_compiled = compile_project(
            &forward.manifest_path(),
            &mut forward_map,
            &mut forward_interner,
        )
        .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let mut reversed_map = SourceMap::new();
        let mut reversed_interner = Interner::new();
        let reversed_compiled = compile_project(
            &reversed.manifest_path(),
            &mut reversed_map,
            &mut reversed_interner,
        )
        .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));

        let forward_text = crate::nir::print_module(
            &forward_compiled.nir,
            &forward_interner,
            &forward_compiled.registry,
        );
        let reversed_text = crate::nir::print_module(
            &reversed_compiled.nir,
            &reversed_interner,
            &reversed_compiled.registry,
        );
        assert_eq!(
            forward_text, reversed_text,
            "import order must never change printed NIR"
        );
        assert!(
            !forward_text.contains("<item #"),
            "the extend and its method must resolve a real registered identity: {forward_text}"
        );

        let forward_result =
            Interpreter::new(&forward_compiled.nir).run_item(forward_compiled.entry_item);
        let reversed_result =
            Interpreter::new(&reversed_compiled.nir).run_item(reversed_compiled.entry_item);
        assert_eq!(forward_result, reversed_result);
        assert_eq!(forward_result, Ok(crate::interpreter::Value::Bool(true)));
    }

    /// Fix 5 (0.1.5 follow-up): importing an item that is itself only an
    /// `import` declaration in its own module (re-exporting is not
    /// supported) must report a grammatically correct, version-
    /// independent message -- not the stale "cannot be imported in
    /// Alpha 0.1.2" wording, and not "is a `import`".
    #[test]
    fn importing_an_import_declaration_reports_a_stable_grammatically_correct_message() {
        let project = TempProject::new("import_of_an_import");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/math.npt",
            "public func add(left: i64, right: i64) -> i64 {\n    return left + right\n}\n",
        );
        project.write("src/a.npt", "import math.add;\n");
        project.write(
            "src/main.npt",
            "import a.add;\n\nfunc main() -> i64 {\n    return add(1, 2)\n}\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = compile_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert!(
            diags.iter().any(|d| d.message
                == "`add` in module `a` is an import declaration and cannot itself be imported"),
            "unexpected diagnostics: {diags:?}"
        );
        assert!(
            !diags.iter().any(|d| d.message.contains("Alpha 0.1.2")),
            "stale version-specific wording leaked: {diags:?}"
        );
    }
}
