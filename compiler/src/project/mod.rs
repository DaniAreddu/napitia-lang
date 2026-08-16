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
}

/// A fully compiled, verified project, ready to print or execute.
#[derive(Debug)]
pub struct CompiledProject {
    pub nir: NirModule,
    /// The entry module's own `main`, resolved by identity -- never a
    /// name lookup over the merged module, which a project with more
    /// than one module could make ambiguous.
    pub entry_item: ItemId,
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
    // module's turn.
    let mut lowered_by_module: HashMap<module::ModuleId, (HirModule, SourceId)> = HashMap::new();
    let mut ids = hir::IdCursor::default();
    let mut diagnostics: Vec<Diagnostic> = Vec::new();

    for module in &loaded.modules {
        let owned_imports: Vec<loader::ImportRef> = imports_by_module
            .get(&module.id)
            .into_iter()
            .flatten()
            .map(|import_ref| (*import_ref).clone())
            .collect();
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
        merged.other_items.extend(module_hir.other_items);
    }
    let entry_source = entry_source.expect("the entry module is always among loaded.modules");

    // Identified by `ItemId` *before* typeck ever runs, so typeck's own
    // entry-signature check (`EntryMain::ByIdentity`) can be scoped to
    // this exact declaration -- never a global "any function named
    // `main`" check, which would also wrongly flag an ordinary,
    // differently-shaped `main` in a non-entry module (`rfcs/0006`).
    let main_symbol = interner.intern("main");
    let mut entry_candidates = merged
        .functions
        .iter()
        .filter(|f| f.source == entry_source && f.name == main_symbol);
    let entry_hir = entry_candidates.next();
    let entry_item = match (entry_hir, entry_candidates.next()) {
        (Some(entry), None) => entry.id,
        (None, _) => {
            return Err(vec![
                Diagnostic::error(
                    codes::INVALID_ENTRY,
                    loaded.manifest_source,
                    crate::source::Span::dummy(),
                    format!(
                        "entry module `{}` has no `main` function",
                        manifest_path.display()
                    ),
                )
                .with_primary_label("configured entry point"),
            ]);
        }
        (Some(_), Some(_)) => {
            return Err(vec![
                Diagnostic::error(
                    codes::INVALID_ENTRY,
                    loaded.manifest_source,
                    crate::source::Span::dummy(),
                    "entry module declares more than one `main` function",
                )
                .with_primary_label("configured entry point"),
            ]);
        }
    };

    let typeck_result = typeck::check_module(
        &merged,
        loaded.manifest_source,
        interner,
        typeck::EntryMain::ByIdentity(Some(entry_item)),
    );
    if !typeck_result.diagnostics.is_empty() {
        return Err(typeck_result.diagnostics);
    }

    let nir_module = nir::lower_module(
        &merged,
        &typeck_result.local_types,
        &typeck_result.expr_types,
        &typeck_result.pattern_case,
        interner,
        loaded.manifest_source,
    )?;

    let verify_diagnostics = nir::verify_module(&nir_module, loaded.manifest_source, interner);
    if !verify_diagnostics.is_empty() {
        return Err(verify_diagnostics);
    }

    Ok(CompiledProject {
        nir: nir_module,
        entry_item,
    })
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
            crate::nir::print_module(&compiled.nir, &interner)
        };
        assert_eq!(render(), render());
    }
}
