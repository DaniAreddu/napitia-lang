//! Module identity and module-path derivation (`rfcs/0006`).

use std::path::{Component, Path, PathBuf};

/// Identifies one discovered module for the lifetime of one project
/// compilation. Distinct from [`crate::hir::ItemId`] and
/// [`crate::source::SourceId`] -- a module owns exactly one source file
/// and mints many items, but the three concepts are never conflated.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModuleId(pub(crate) u32);

/// A module's dotted path, derived deterministically from its `.npt`
/// file's path relative to the project's `source-root`
/// (`src/models/user.npt` -> `models.user`) -- never from declaration
/// order or directory-iteration order. Segments keep their as-written
/// case for display; comparison for path *identity* is exact (two
/// modules are the same path only if every segment matches exactly),
/// while [`ModulePath::case_folded`] exists specifically for the
/// separate "do these differ only by case" collision check.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModulePath {
    segments: Vec<String>,
}

impl ModulePath {
    /// Derives a module path from a `.npt` file's path relative to
    /// `source-root`. `None` if the path is empty, has an unexpected
    /// extension, or contains a segment that isn't a plain path
    /// component (`.`/`..`/a root/prefix) -- all of which indicate the
    /// path was never actually produced by walking `source-root` itself.
    pub fn from_relative_npt_path(relative: &Path) -> Option<ModulePath> {
        if relative.extension().and_then(|e| e.to_str()) != Some("npt") {
            return None;
        }
        let without_ext = relative.with_extension("");
        let mut segments = Vec::new();
        for component in without_ext.components() {
            match component {
                Component::Normal(part) => segments.push(part.to_str()?.to_string()),
                _ => return None,
            }
        }
        if segments.is_empty() {
            return None;
        }
        Some(ModulePath { segments })
    }

    /// Splits an import path's segments into `(module_path,
    /// item_name)`: every segment but the last is the module path, the
    /// last is the imported item. `None` if there are fewer than two
    /// segments (a module path needs at least one segment of its own).
    pub fn split_import_path(segments: &[String]) -> Option<(ModulePath, &str)> {
        if segments.len() < 2 {
            return None;
        }
        let (item, module_segments) = segments.split_last().expect("checked len >= 2 above");
        Some((
            ModulePath {
                segments: module_segments.to_vec(),
            },
            item.as_str(),
        ))
    }

    /// The file path this module's own source lives at, relative to
    /// `source-root`, using this platform's own separator -- callers
    /// join it onto an actual `source-root` directory, never construct
    /// an absolute path from it directly.
    pub fn to_relative_npt_path(&self) -> PathBuf {
        let mut path = PathBuf::new();
        for segment in &self.segments {
            path.push(segment);
        }
        path.set_extension("npt");
        path
    }

    /// The dotted display form (`models.user`), also used as this
    /// module's stable sort key for deterministic traversal/output.
    pub fn dotted(&self) -> String {
        self.segments.join(".")
    }

    /// An ASCII-lowercase version of [`Self::dotted`], used only to
    /// detect two module paths that differ solely by case -- real on a
    /// case-sensitive filesystem, and exactly the ambiguity that would
    /// silently collide on a case-insensitive one (Windows' default).
    pub fn case_folded(&self) -> String {
        self.dotted().to_ascii_lowercase()
    }
}

/// Validates that `relative` (as written in the manifest, forward-slash
/// separated) is a well-formed relative path with no `..` traversal and
/// no absolute/rooted component, then joins it onto `base`. Returns the
/// offending reason as `Err(String)` rather than a full `Diagnostic` --
/// the caller already knows which manifest key this path came from and
/// builds the `M0002` diagnostic itself.
pub fn resolve_relative_path(base: &Path, relative: &str) -> Result<PathBuf, String> {
    if relative.is_empty() {
        return Err("path must not be empty".to_string());
    }
    let mut resolved = base.to_path_buf();
    for part in relative.split(['/', '\\']) {
        match part {
            "" | "." => continue,
            ".." => return Err(format!("path `{relative}` may not contain `..`")),
            _ => resolved.push(part),
        }
    }
    Ok(resolved)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn derives_a_flat_module_path() {
        let path = ModulePath::from_relative_npt_path(Path::new("math.npt")).unwrap();
        assert_eq!(path.dotted(), "math");
    }

    #[test]
    fn derives_a_nested_module_path() {
        let path = ModulePath::from_relative_npt_path(Path::new("models/user.npt")).unwrap();
        assert_eq!(path.dotted(), "models.user");
    }

    #[test]
    fn rejects_a_non_npt_extension() {
        assert!(ModulePath::from_relative_npt_path(Path::new("math.rs")).is_none());
    }

    #[test]
    fn splits_an_import_path_into_module_and_item() {
        let segments = vec!["models".to_string(), "user".to_string(), "User".to_string()];
        let (module, item) = ModulePath::split_import_path(&segments).unwrap();
        assert_eq!(module.dotted(), "models.user");
        assert_eq!(item, "User");
    }

    #[test]
    fn a_single_segment_import_path_has_no_module() {
        let segments = vec!["math".to_string()];
        assert!(ModulePath::split_import_path(&segments).is_none());
    }

    #[test]
    fn case_folded_ignores_ascii_case_only() {
        let a = ModulePath::from_relative_npt_path(Path::new("Math.npt")).unwrap();
        let b = ModulePath::from_relative_npt_path(Path::new("math.npt")).unwrap();
        assert_eq!(a.case_folded(), b.case_folded());
        assert_ne!(a, b);
    }

    #[test]
    fn resolve_relative_path_rejects_parent_traversal() {
        let base = Path::new("/project/src");
        assert!(resolve_relative_path(base, "../escape.npt").is_err());
        assert!(resolve_relative_path(base, "sub/../../escape.npt").is_err());
    }

    #[test]
    fn resolve_relative_path_joins_forward_and_back_slash_segments_the_same_way() {
        let base = Path::new("/project");
        let forward = resolve_relative_path(base, "src/models/user.npt").unwrap();
        let back = resolve_relative_path(base, "src\\models\\user.npt").unwrap();
        assert_eq!(forward, back);
    }
}
