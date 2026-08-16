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
#[derive(Debug, Clone)]
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
        Err(cycle_diagnostic) => return Err(vec![*cycle_diagnostic]),
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
) -> Result<Vec<ModuleId>, Box<Diagnostic>> {
    let dotted_by_id: BTreeMap<u32, String> =
        modules.iter().map(|m| (m.id.0, m.path.dotted())).collect();

    // `edges[m]` is every module `m` itself imports (`m`'s own
    // dependencies) -- deduplicated, so importing the same module twice
    // under different item names is still exactly one graph edge.
    let mut edges: BTreeMap<u32, BTreeSet<u32>> =
        modules.iter().map(|m| (m.id.0, BTreeSet::new())).collect();
    for import in imports {
        let Some((target_module, _)) = ModulePath::split_import_path(&import.segments) else {
            continue;
        };
        let Some(&target_id) = by_path.get(&target_module.dotted()) else {
            continue;
        };
        edges
            .get_mut(&import.importing_module.0)
            .expect("importing module was discovered")
            .insert(target_id.0);
    }
    // The reverse adjacency: `importers_of[m]` is every module that
    // imports `m`, used below to advance a module's *importers* once
    // `m` itself is placed.
    let mut importers_of: BTreeMap<u32, BTreeSet<u32>> =
        modules.iter().map(|m| (m.id.0, BTreeSet::new())).collect();
    for (&importer, targets) in &edges {
        for &target in targets {
            importers_of
                .get_mut(&target)
                .expect("target module was discovered")
                .insert(importer);
        }
    }

    // `order` accumulates dependencies before dependents directly (no
    // reverse-then-flip trick): a module is ready once every module it
    // itself imports has already been placed, and ties among
    // simultaneously-ready modules are broken by dotted module path,
    // never by numeric `ModuleId` (assigned in file-discovery order,
    // which carries no semantic meaning) -- keying `ready` on `(dotted
    // path, id)` makes a plain `BTreeSet`'s own ordering pick the
    // lexicographically smallest ready module, with `.next()`
    // (smallest).
    let mut remaining_deps: BTreeMap<u32, usize> = edges
        .iter()
        .map(|(&id, targets)| (id, targets.len()))
        .collect();
    let mut ready: BTreeSet<(String, u32)> = remaining_deps
        .iter()
        .filter(|&(_, &deg)| deg == 0)
        .map(|(&id, _)| (dotted_by_id[&id].clone(), id))
        .collect();
    let mut order = Vec::with_capacity(modules.len());

    while let Some((path, next)) = ready.iter().next().cloned() {
        ready.remove(&(path, next));
        order.push(ModuleId(next));
        if let Some(importers) = importers_of.get(&next) {
            for &importer in importers {
                let deg = remaining_deps
                    .get_mut(&importer)
                    .expect("importer module was discovered");
                *deg -= 1;
                if *deg == 0 {
                    ready.insert((dotted_by_id[&importer].clone(), importer));
                }
            }
        }
    }

    if order.len() == modules.len() {
        return Ok(order);
    }

    // Every module still missing from `order` reaches into a cycle, but
    // is not necessarily itself a cycle member (e.g. an acyclic leaf
    // only reachable *from* a cycle). Extracting a witness must isolate
    // the actual cycle, never wander into such a leaf and assume it has
    // an edge back into the residual set, which is exactly what used to
    // panic. An iterative DFS (explicit stack, no native recursion) over
    // the residual subgraph -- choosing both the start node and each
    // node's own edges by dotted path, never numeric `ModuleId` -- finds
    // one closed cycle deterministically.
    let placed: BTreeSet<u32> = order.iter().map(|id| id.0).collect();
    let residual: BTreeSet<u32> = modules
        .iter()
        .map(|m| m.id.0)
        .filter(|id| !placed.contains(id))
        .collect();
    let mut residual_by_path: Vec<u32> = residual.iter().copied().collect();
    residual_by_path.sort_by(|a, b| dotted_by_id[a].cmp(&dotted_by_id[b]));

    #[derive(Copy, Clone, PartialEq, Eq)]
    enum Color {
        White,
        Gray,
        Black,
    }
    let mut color: BTreeMap<u32, Color> = residual.iter().map(|&id| (id, Color::White)).collect();
    let sorted_residual_edges = |node: u32| -> Vec<u32> {
        let mut targets: Vec<u32> = edges
            .get(&node)
            .into_iter()
            .flatten()
            .copied()
            .filter(|target| residual.contains(target))
            .collect();
        targets.sort_by(|a, b| dotted_by_id[a].cmp(&dotted_by_id[b]));
        targets
    };

    let mut witness: Option<Vec<u32>> = None;
    'outer: for &start in &residual_by_path {
        if color[&start] != Color::White {
            continue;
        }
        // Each stack frame: the node being visited, and an index into
        // its (dotted-path-sorted) edge list of which edge to try next.
        let mut stack: Vec<(u32, usize)> = vec![(start, 0)];
        color.insert(start, Color::Gray);
        let mut path: Vec<u32> = vec![start];

        while let Some((current, edge_idx)) = stack.pop() {
            let targets = sorted_residual_edges(current);
            if edge_idx >= targets.len() {
                color.insert(current, Color::Black);
                path.pop();
                continue;
            }
            stack.push((current, edge_idx + 1));
            let target = targets[edge_idx];
            match color.get(&target).copied().unwrap_or(Color::Black) {
                Color::White => {
                    color.insert(target, Color::Gray);
                    path.push(target);
                    stack.push((target, 0));
                }
                Color::Gray => {
                    // `target` is still on the current path -- close the
                    // witness from its first occurrence back to itself.
                    if let Some(start_idx) = path.iter().position(|id| *id == target) {
                        witness = Some(path[start_idx..].to_vec());
                        break 'outer;
                    }
                }
                Color::Black => {}
            }
        }
    }

    // Every residual node has in-degree >= 1 *within the residual
    // subgraph* (that's exactly why Kahn's algorithm never placed it) --
    // a finite graph where every node has in-degree >= 1 always
    // contains a cycle, and a DFS covering every node (as this loop
    // does, restarting from each not-yet-visited residual node) is
    // guaranteed to find one, the same argument `typeck::cycles`
    // already relies on for its own iterative DFS.
    let witness_ids = witness.expect("the residual module set always contains a cycle");
    let mut witness_text: Vec<String> = witness_ids
        .iter()
        .map(|id| dotted_by_id[id].clone())
        .collect();
    witness_text.push(dotted_by_id[&witness_ids[0]].clone());

    let any_source = modules
        .first()
        .expect("a cycle requires at least one module")
        .source;
    Err(Box::new(
        Diagnostic::error(
            codes::IMPORT_CYCLE,
            any_source,
            Span::dummy(),
            format!("module import cycle: {}", witness_text.join(" -> ")),
        )
        .with_primary_label("cyclic module dependency"),
    ))
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
    fn cycle_with_an_acyclic_outbound_leaf_excludes_the_leaf_and_does_not_panic() {
        // a <-> b is a real cycle; a also imports the acyclic leaf `c`,
        // which the old witness-extraction code could wander into and
        // panic on (it has no edge back into the residual set). The
        // witness must name only the actual cycle members.
        let project = TempProject::new("cycle_with_leaf");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import a.thing;\nfunc main() -> i64 { return 0 }\n",
        );
        project.write(
            "src/a.npt",
            "import b.helper;\nimport c.leaf;\n\
             public func thing() -> i64 { return helper() + leaf() }\n",
        );
        project.write(
            "src/b.npt",
            "import a.thing;\npublic func helper() -> i64 { return thing() }\n",
        );
        project.write("src/c.npt", "public func leaf() -> i64 { return 1 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = load_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0008");
        assert!(
            diags[0].message.contains("cycle: a -> b -> a"),
            "expected the cycle witness to be exactly a -> b -> a: {}",
            diags[0].message
        );
        // Checking for a bare `'c'` char would false-positive on the
        // word "cycle" itself -- the witness has exactly two arrows
        // (`a -> b -> a`); a third module would add a third.
        assert_eq!(
            diags[0].message.matches("->").count(),
            2,
            "acyclic leaf `c` must never appear in the witness: {}",
            diags[0].message
        );
    }

    #[test]
    fn longer_cycle_path_text_is_exact() {
        let project = TempProject::new("longer_cycle");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import a.thing;\nfunc main() -> i64 { return 0 }\n",
        );
        project.write(
            "src/a.npt",
            "import b.thing;\npublic func thing() -> i64 { return thing() }\n",
        );
        project.write(
            "src/b.npt",
            "import c.thing;\npublic func thing() -> i64 { return thing() }\n",
        );
        project.write(
            "src/c.npt",
            "import a.thing;\npublic func thing() -> i64 { return thing() }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = load_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0008");
        assert!(
            diags[0].message.contains("a -> b -> c -> a"),
            "unexpected witness: {}",
            diags[0].message
        );
    }

    #[test]
    fn multiple_disjoint_cycles_select_the_lexicographically_smallest_deterministically() {
        // Two entirely disjoint cycles (a <-> b, and y <-> z) both reach
        // into the residual set. The witness must always be the one
        // starting from the lexicographically smallest residual module
        // (`a`), never `y`, and never depend on which happens to be
        // discovered first.
        let project = TempProject::new("multiple_cycles");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import a.thing;\nimport y.thing;\nfunc main() -> i64 { return 0 }\n",
        );
        project.write(
            "src/a.npt",
            "import b.thing;\npublic func thing() -> i64 { return thing() }\n",
        );
        project.write(
            "src/b.npt",
            "import a.thing;\npublic func thing() -> i64 { return thing() }\n",
        );
        project.write(
            "src/y.npt",
            "import z.thing;\npublic func thing() -> i64 { return thing() }\n",
        );
        project.write(
            "src/z.npt",
            "import y.thing;\npublic func thing() -> i64 { return thing() }\n",
        );

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = load_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0008");
        assert!(
            diags[0].message.contains("cycle: a -> b -> a"),
            "expected the a<->b cycle to be selected: {}",
            diags[0].message
        );
        assert_eq!(
            diags[0].message.matches("->").count(),
            2,
            "the y<->z cycle must not be selected: {}",
            diags[0].message
        );
    }

    #[test]
    fn repeated_cycle_detection_is_byte_identical() {
        let project = TempProject::new("cycle_deterministic");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import a.thing;\nfunc main() -> i64 { return 0 }\n",
        );
        project.write(
            "src/a.npt",
            "import b.thing;\npublic func thing() -> i64 { return thing() }\n",
        );
        project.write(
            "src/b.npt",
            "import a.thing;\npublic func thing() -> i64 { return thing() }\n",
        );

        let message_of = || {
            let mut map = SourceMap::new();
            let mut interner = Interner::new();
            load_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err()[0]
                .message
                .clone()
        };
        assert_eq!(message_of(), message_of());
    }

    #[test]
    fn a_deep_cyclic_chain_does_not_overflow_the_native_stack() {
        // A single long cycle through many modules -- the witness
        // extraction is an explicit-stack iterative DFS, so this must
        // not blow the native call stack the way a recursive
        // implementation would.
        const DEPTH: usize = 3000;
        let project = TempProject::new("deep_cycle");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import m0.thing;\nfunc main() -> i64 { return 0 }\n",
        );
        for i in 0..DEPTH {
            let next = (i + 1) % DEPTH;
            project.write(
                &format!("src/m{i}.npt"),
                &format!(
                    "import m{next}.thing;\npublic func thing() -> i64 {{ return thing() }}\n"
                ),
            );
        }

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let diags = load_project(&project.manifest_path(), &mut map, &mut interner).unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0008");
    }

    #[test]
    fn simultaneously_ready_modules_are_placed_in_lexical_path_order() {
        // `main` imports three mutually-independent leaf modules -- all
        // three become ready at the same Kahn step, so only the
        // lexical-path tie-break decides their relative order.
        let project = TempProject::new("lexical_order");
        project.write("napitia.toml", MANIFEST);
        project.write(
            "src/main.npt",
            "import z.thing;\nimport m.thing;\nimport a.thing;\n\
             func main() -> i64 { return 0 }\n",
        );
        project.write("src/a.npt", "public func thing() -> i64 { return 1 }\n");
        project.write("src/m.npt", "public func thing() -> i64 { return 1 }\n");
        project.write("src/z.npt", "public func thing() -> i64 { return 1 }\n");

        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let loaded = load_project(&project.manifest_path(), &mut map, &mut interner)
            .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        let paths: Vec<String> = loaded.modules.iter().map(|m| m.path.dotted()).collect();
        assert_eq!(paths, vec!["a", "m", "z", "main"]);
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
