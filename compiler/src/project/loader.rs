//! Discovers every module reachable from a project's entry module,
//! parses each exactly once, and orders them deterministically by
//! module dependency (`rfcs/0006`).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use super::codes;
use super::manifest::{self, Manifest};
use super::module::{ModuleId, ModulePath, resolve_relative_path};
use crate::diagnostics::Diagnostic;
use crate::source::{SourceId, SourceMap, Span};
use crate::symbol::Interner;
use crate::syntax::ast;

/// One discovered, parsed module, not yet HIR-lowered.
#[derive(Debug)]
pub struct LoadedModule {
    pub id: ModuleId,
    pub path: ModulePath,
    pub source: SourceId,
    pub ast: ast::Module,
}

/// One `import` statement, as found while scanning a module -- kept
/// separate from `ast::ImportDecl` so the loader can attach the
/// resolved `(module path, item name)` split (or note that the path was
/// too short to have one) without mutating the AST.
#[derive(Debug)]
pub struct ImportRef {
    pub importing_module: ModuleId,
    pub segments: Vec<String>,
    pub span: Span,
}

/// Every module reachable from the entry module, in a deterministic
/// topological (dependency-first) order, plus the raw import
/// references discovered while scanning them -- resolving those
/// against the now-complete module set is a later step
/// (`project::resolve`), since resolving one module's imports needs
/// every other module to have been discovered first.
#[derive(Debug)]
pub struct LoadedProject {
    pub manifest: Manifest,
    pub manifest_source: SourceId,
    pub project_dir: PathBuf,
    pub source_root: PathBuf,
    pub modules: Vec<LoadedModule>,
    pub imports: Vec<ImportRef>,
    pub entry_module: ModuleId,
}

/// Loads and validates the manifest at `manifest_path`, then discovers
/// and parses every module reachable from the configured entry module.
/// Does not resolve imports or run HIR lowering -- this is purely
/// "find every file that matters and get its AST", atomically: any
/// failure here returns every diagnostic found, not a partial project.
pub fn load_project(
    manifest_path: &Path,
    map: &mut SourceMap,
    interner: &mut Interner,
) -> Result<LoadedProject, Vec<Diagnostic>> {
    let manifest_content = std::fs::read_to_string(manifest_path).map_err(|err| {
        vec![Diagnostic::error(
            codes::INVALID_MANIFEST,
            {
                // A manifest that can't even be read yet still needs a
                // SourceId for the diagnostic to point at; register it
                // with empty content rather than failing without one.
                map.add_file(manifest_path.display().to_string(), String::new())
            },
            Span::dummy(),
            format!("could not read manifest: {err}"),
        )]
    })?;
    let manifest_source = map.add_file(
        manifest_path.display().to_string(),
        manifest_content.clone(),
    );
    let manifest = manifest::parse_manifest(manifest_source, &manifest_content)?;

    let project_dir = manifest_path
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from("."));

    let source_root =
        resolve_relative_path(&project_dir, &manifest.source_root).map_err(|reason| {
            vec![invalid_path_diagnostic(
                manifest_source,
                "project.source-root",
                &reason,
            )]
        })?;
    if !source_root.is_dir() {
        return Err(vec![invalid_path_diagnostic(
            manifest_source,
            "project.source-root",
            &format!("`{}` is not a directory", source_root.display()),
        )]);
    }

    let entry_relative =
        resolve_relative_path(Path::new(""), &manifest.entry).map_err(|reason| {
            vec![invalid_path_diagnostic(
                manifest_source,
                "project.entry",
                &reason,
            )]
        })?;
    let entry_path = source_root.join(&entry_relative);
    if !entry_path.is_file() {
        return Err(vec![
            Diagnostic::error(
                codes::INVALID_ENTRY,
                manifest_source,
                Span::dummy(),
                format!(
                    "entry file `{}` does not exist under source-root `{}`",
                    manifest.entry, manifest.source_root
                ),
            )
            .with_primary_label("configured entry point"),
        ]);
    }
    // Defense in depth against a symlink inside source-root resolving
    // outside the project directory: resolve_relative_path already
    // rejects textual `..` traversal, but a symlink can still escape
    // without ever writing `..` in the manifest itself.
    if let (Ok(canonical_root), Ok(canonical_entry)) =
        (source_root.canonicalize(), entry_path.canonicalize())
        && !canonical_entry.starts_with(&canonical_root)
    {
        return Err(vec![invalid_path_diagnostic(
            manifest_source,
            "project.entry",
            "entry resolves outside of source-root",
        )]);
    }
    let Some(entry_module_path) = ModulePath::from_relative_npt_path(&entry_relative) else {
        return Err(vec![invalid_path_diagnostic(
            manifest_source,
            "project.entry",
            &format!("`{}` is not a valid module path", manifest.entry),
        )]);
    };

    let mut modules: Vec<LoadedModule> = Vec::new();
    let mut by_path: BTreeMap<String, ModuleId> = BTreeMap::new();
    let mut by_case_folded: BTreeMap<String, String> = BTreeMap::new();
    let mut imports: Vec<ImportRef> = Vec::new();
    let mut diagnostics: Vec<Diagnostic> = Vec::new();
    let mut queue: Vec<ModulePath> = vec![entry_module_path.clone()];
    let mut queued: BTreeSet<String> = BTreeSet::from([entry_module_path.dotted()]);

    // Breadth-first, but the *result* does not depend on this order:
    // only the reachable set and each module's own import list matter,
    // both of which are independent of visit order.
    while let Some(module_path) = queue.pop() {
        let dotted = module_path.dotted();
        let case_folded = module_path.case_folded();
        if let Some(existing) = by_case_folded.get(&case_folded)
            && *existing != dotted
        {
            diagnostics.push(
                Diagnostic::error(
                    codes::MODULE_PATH_COLLISION,
                    manifest_source,
                    Span::dummy(),
                    format!("module paths `{existing}` and `{dotted}` differ only by ASCII case"),
                )
                .with_primary_label("would be ambiguous on a case-insensitive filesystem"),
            );
            continue;
        }
        by_case_folded.insert(case_folded, dotted.clone());

        let relative_file = module_path.to_relative_npt_path();
        let file_path = source_root.join(&relative_file);
        let content = match std::fs::read_to_string(&file_path) {
            Ok(content) => content,
            Err(_) => {
                diagnostics.push(
                    Diagnostic::error(
                        codes::MODULE_NOT_FOUND,
                        manifest_source,
                        Span::dummy(),
                        format!(
                            "module `{dotted}` not found (expected `{}`)",
                            file_path.display()
                        ),
                    )
                    .with_primary_label("referenced but not found"),
                );
                continue;
            }
        };
        let display_name = relative_file.display().to_string();
        let source = map.add_file(display_name, content);
        let parsed = crate::driver::parse(map, source, interner);
        diagnostics.extend(parsed.diagnostics);

        let id = ModuleId(modules.len() as u32);
        by_path.insert(dotted, id);

        for item in &parsed.module.items {
            if let ast::Item::Import(import) = item {
                let segments: Vec<String> = import
                    .path
                    .segments
                    .iter()
                    .map(|seg| interner.resolve(seg.symbol).to_string())
                    .collect();
                if let Some((target_module, _)) = ModulePath::split_import_path(&segments) {
                    let target_dotted = target_module.dotted();
                    if !queued.contains(&target_dotted) {
                        queued.insert(target_dotted);
                        queue.push(target_module);
                    }
                }
                imports.push(ImportRef {
                    importing_module: id,
                    segments,
                    span: import.span,
                });
            }
        }

        modules.push(LoadedModule {
            id,
            path: ModulePath::from_relative_npt_path(&relative_file)
                .expect("relative_file was just derived from a valid ModulePath"),
            source,
            ast: parsed.module,
        });
    }

    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }

    let ordered = match topological_order(&modules, &imports, &by_path) {
        Ok(order) => order,
        Err(cycle_diagnostic) => return Err(vec![cycle_diagnostic]),
    };
    let modules = reorder(modules, &ordered);
    let entry_module = *by_path
        .get(&entry_module_path.dotted())
        .expect("entry module was discovered first and always inserted into by_path");

    Ok(LoadedProject {
        manifest,
        manifest_source,
        project_dir,
        source_root,
        modules,
        imports,
        entry_module,
    })
}

fn invalid_path_diagnostic(source: SourceId, key: &str, reason: &str) -> Diagnostic {
    Diagnostic::error(
        codes::INVALID_PROJECT_PATH,
        source,
        Span::dummy(),
        format!("invalid `{key}`: {reason}"),
    )
    .with_primary_label("invalid path")
}

/// Reorders `modules` (currently in discovery order) into `order`
/// (a list of `ModuleId`s, dependency-first), returning them in that
/// new order with each `LoadedModule` moved, not cloned.
fn reorder(modules: Vec<LoadedModule>, order: &[ModuleId]) -> Vec<LoadedModule> {
    let mut by_id: BTreeMap<u32, LoadedModule> = modules.into_iter().map(|m| (m.id.0, m)).collect();
    order
        .iter()
        .map(|id| {
            by_id
                .remove(&id.0)
                .expect("order only names discovered modules")
        })
        .collect()
}

/// Kahn's algorithm (iterative, no native recursion regardless of
/// project size): computes a dependency-first order over `modules`'
/// import edges, always advancing the lexicographically-smallest ready
/// module when more than one is ready, so the result is identical
/// across repeated runs regardless of discovery order. An import
/// naming a module that was never discovered (already reported as
/// `M0004` elsewhere) is simply not an edge -- this function only ever
/// sees edges between modules that exist.
fn topological_order(
    modules: &[LoadedModule],
    imports: &[ImportRef],
    by_path: &BTreeMap<String, ModuleId>,
) -> Result<Vec<ModuleId>, Diagnostic> {
    let dotted_by_id: BTreeMap<u32, String> =
        modules.iter().map(|m| (m.id.0, m.path.dotted())).collect();

    let mut edges: BTreeMap<u32, BTreeSet<u32>> =
        modules.iter().map(|m| (m.id.0, BTreeSet::new())).collect();
    let mut in_degree: BTreeMap<u32, usize> = modules.iter().map(|m| (m.id.0, 0)).collect();
    for import in imports {
        let Some((target_module, _)) = ModulePath::split_import_path(&import.segments) else {
            continue;
        };
        let Some(&target_id) = by_path.get(&target_module.dotted()) else {
            continue;
        };
        if edges
            .get_mut(&import.importing_module.0)
            .expect("importing module was discovered")
            .insert(target_id.0)
        {
            *in_degree
                .get_mut(&target_id.0)
                .expect("target module was discovered") += 1;
        }
    }

    // `order` accumulates dependencies before dependents: a module is
    // only ready to be placed once every module it depends on already
    // has been.
    let mut ready: BTreeSet<u32> = in_degree
        .iter()
        .filter(|&(_, &deg)| deg == 0)
        .map(|(&id, _)| id)
        .collect();
    let mut remaining_in_degree = in_degree.clone();
    let mut order = Vec::with_capacity(modules.len());

    while let Some(&next) = ready.iter().next_back() {
        ready.remove(&next);
        order.push(ModuleId(next));
        if let Some(dependents) = edges.get(&next) {
            for &dependent in dependents {
                let deg = remaining_in_degree
                    .get_mut(&dependent)
                    .expect("dependent module was discovered");
                *deg -= 1;
                if *deg == 0 {
                    ready.insert(dependent);
                }
            }
        }
    }

    if order.len() == modules.len() {
        // Kahn's algorithm places dependencies before dependents, but
        // this project wants dependents *lowered* after their
        // dependencies, which is the same order -- a module's imports
        // must already be lowered before the module itself is.
        order.reverse();
        return Ok(order);
    }

    // Every module still missing from `order` is part of (or reaches
    // into) a cycle. Build one deterministic witness path: start from
    // the lexicographically-smallest cyclic module and iteratively
    // follow an edge back into the cyclic set (always the
    // lexicographically-smallest such edge) until a module repeats.
    let placed: BTreeSet<u32> = order.iter().map(|id| id.0).collect();
    let cyclic: BTreeSet<u32> = modules
        .iter()
        .map(|m| m.id.0)
        .filter(|id| !placed.contains(id))
        .collect();
    let mut witness = Vec::new();
    let mut visited = BTreeSet::new();
    let mut current = *cyclic
        .iter()
        .next()
        .expect("order is short, so a cycle exists");
    loop {
        let dotted = dotted_by_id.get(&current).cloned().unwrap_or_default();
        if !visited.insert(current) {
            witness.push(dotted);
            break;
        }
        witness.push(dotted);
        current = *edges
            .get(&current)
            .into_iter()
            .flatten()
            .filter(|next| cyclic.contains(next))
            .min()
            .expect("a cyclic module has at least one edge back into the cycle");
    }

    let any_source = modules
        .first()
        .expect("a cycle requires at least one module")
        .source;
    Err(Diagnostic::error(
        codes::IMPORT_CYCLE,
        any_source,
        Span::dummy(),
        format!("module import cycle: {}", witness.join(" -> ")),
    )
    .with_primary_label("cyclic module dependency"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A scratch project directory under the OS temp dir, torn down on
    /// drop. Every test gets its own directory (named after this
    /// process's id plus a per-call counter) so parallel test runs
    /// never collide.
    struct TempProject {
        dir: PathBuf,
    }

    impl TempProject {
        fn new(name: &str) -> Self {
            static COUNTER: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
            let n = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let dir = std::env::temp_dir().join(format!(
                "napitia_loader_test_{}_{name}_{n}",
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
    fn discovers_a_two_file_project() {
        let project = TempProject::new("two_file");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import math.add;\nfunc main() -> i64 { return add(1, 2) }\n",
        );
        project.write(
            "src/math.npt",
            "public func add(left: i64, right: i64) -> i64 { left + right }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let loaded = load_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));

        let mut paths: Vec<String> = loaded.modules.iter().map(|m| m.path.dotted()).collect();
        paths.sort();
        assert_eq!(paths, vec!["main".to_string(), "math".to_string()]);
        // math is imported by main, so it must be lowered (and thus
        // ordered) before main.
        let math_index = loaded
            .modules
            .iter()
            .position(|m| m.path.dotted() == "math")
            .unwrap();
        let main_index = loaded
            .modules
            .iter()
            .position(|m| m.path.dotted() == "main")
            .unwrap();
        assert!(math_index < main_index);
    }

    #[test]
    fn discovers_a_nested_module() {
        let project = TempProject::new("nested");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import models.user.User;\nfunc main() -> i64 { return 0 }\n",
        );
        project.write(
            "src/models/user.npt",
            "public record User { public id: i64 }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let loaded = load_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let mut paths: Vec<String> = loaded.modules.iter().map(|m| m.path.dotted()).collect();
        paths.sort();
        assert_eq!(paths, vec!["main".to_string(), "models.user".to_string()]);
    }

    #[test]
    fn missing_module_is_m0004() {
        let project = TempProject::new("missing_module");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import nope.thing;\nfunc main() -> i64 { return 0 }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = load_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0004");
    }

    #[test]
    fn direct_two_module_cycle_is_m0008_with_a_deterministic_witness() {
        let project = TempProject::new("cycle");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import a.thing;\nfunc main() -> i64 { return 0 }\n",
        );
        project.write(
            "src/a.npt",
            "import b.thing;\npublic func thing() -> i64 { 0 }\n",
        );
        project.write(
            "src/b.npt",
            "import a.thing;\npublic func thing() -> i64 { 0 }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = load_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0008");
        assert!(
            diags[0].message.contains("a -> b -> a") || diags[0].message.contains("b -> a -> b"),
            "expected a deterministic cycle witness: {}",
            diags[0].message
        );
    }

    #[test]
    fn entry_escaping_source_root_is_rejected() {
        let project = TempProject::new("escape_entry");
        project.write(
            "napitia.toml",
            "[package]\nname = \"hello\"\nversion = \"0.1.0\"\n\n\
             [project]\nsource-root = \"src\"\nentry = \"../outside.npt\"\n",
        );
        project.write("src/main.npt", "func main() -> i64 { return 0 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = load_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0002");
    }

    #[test]
    fn missing_source_root_is_m0002() {
        let project = TempProject::new("missing_root");
        project.write("napitia.toml", MANIFEST);
        // src/ is never created at all.

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = load_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0002");
    }

    #[test]
    fn repeated_loads_produce_identical_module_ordering() {
        let project = TempProject::new("deterministic");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import math.add;\nimport models.user.User;\nfunc main() -> i64 { return 0 }\n",
        );
        project.write(
            "src/math.npt",
            "public func add(left: i64, right: i64) -> i64 { left + right }\n",
        );
        project.write(
            "src/models/user.npt",
            "public record User { public id: i64 }\n",
        );

        let order_of = || {
            let mut map = SourceMap::new();
            let mut interner = Interner::new();
            let loaded = load_project(&project.manifest_path(), &mut map, &mut interner)
                .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
            loaded
                .modules
                .iter()
                .map(|m| m.path.dotted())
                .collect::<Vec<_>>()
        };
        assert_eq!(order_of(), order_of());
    }
}
