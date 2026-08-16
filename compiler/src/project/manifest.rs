//! Parses and validates `napitia.toml` project manifests.

use crate::diagnostics::Diagnostic;
use crate::source::{SourceId, Span};

use super::codes;

/// The validated contents of a `napitia.toml` manifest. Every field is
/// required; there is no notion of an optional or defaulted field in
/// Alpha 0.1.2 -- a manifest missing one is rejected outright (`M0001`),
/// never silently defaulted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
    pub package_name: String,
    pub package_version: String,
    /// As written in the manifest, forward-slash-separated, relative to
    /// the project directory (the manifest's own parent directory).
    pub source_root: String,
    /// As written in the manifest, forward-slash-separated, relative to
    /// `source_root`.
    pub entry: String,
}

/// Parses and fully validates `content` (the text of a `napitia.toml`
/// file at `source`), returning every problem found rather than
/// stopping at the first -- a manifest missing two required fields
/// should be told about both at once.
pub fn parse_manifest(source: SourceId, content: &str) -> Result<Manifest, Vec<Diagnostic>> {
    let table: toml::Table = match content.parse() {
        Ok(table) => table,
        Err(err) => {
            return Err(vec![
                Diagnostic::error(
                    codes::INVALID_MANIFEST,
                    source,
                    Span::dummy(),
                    format!("malformed TOML: {err}"),
                )
                .with_primary_label("could not parse this manifest"),
            ]);
        }
    };

    let mut diagnostics = Vec::new();
    for key in table.keys() {
        if key != "package" && key != "project" {
            diagnostics.push(unknown_key_diagnostic(source, key, "top level"));
        }
    }

    let package = expect_table(&table, "package", source, &mut diagnostics);
    let project = expect_table(&table, "project", source, &mut diagnostics);

    if let Some(t) = &package {
        check_known_keys(t, "package", &["name", "version"], source, &mut diagnostics);
    }
    if let Some(t) = &project {
        check_known_keys(
            t,
            "project",
            &["source-root", "entry"],
            source,
            &mut diagnostics,
        );
    }

    let package_name = package
        .as_ref()
        .and_then(|t| expect_string_field(t, "name", "package", source, &mut diagnostics));
    let package_version = package
        .as_ref()
        .and_then(|t| expect_string_field(t, "version", "package", source, &mut diagnostics));
    let source_root = project
        .as_ref()
        .and_then(|t| expect_string_field(t, "source-root", "project", source, &mut diagnostics));
    let entry = project
        .as_ref()
        .and_then(|t| expect_string_field(t, "entry", "project", source, &mut diagnostics));

    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }

    Ok(Manifest {
        // Every `expect_string_field` call above succeeded (the early
        // return above fires on any failure), so each `Option` here is
        // always `Some`.
        package_name: package_name.expect("validated above"),
        package_version: package_version.expect("validated above"),
        source_root: source_root.expect("validated above"),
        entry: entry.expect("validated above"),
    })
}

fn expect_table<'a>(
    table: &'a toml::Table,
    key: &str,
    source: SourceId,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<&'a toml::Table> {
    match table.get(key) {
        None => {
            diagnostics.push(
                Diagnostic::error(
                    codes::INVALID_MANIFEST,
                    source,
                    Span::dummy(),
                    format!("missing required `[{key}]` section"),
                )
                .with_primary_label("manifest is missing this section"),
            );
            None
        }
        Some(toml::Value::Table(t)) => Some(t),
        Some(_) => {
            diagnostics.push(
                Diagnostic::error(
                    codes::INVALID_MANIFEST,
                    source,
                    Span::dummy(),
                    format!("`{key}` must be a table (`[{key}]`), not a plain value"),
                )
                .with_primary_label("wrong type for this key"),
            );
            None
        }
    }
}

fn check_known_keys(
    table: &toml::Table,
    section: &str,
    known_keys: &[&str],
    source: SourceId,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for present_key in table.keys() {
        if !known_keys.contains(&present_key.as_str()) {
            diagnostics.push(unknown_key_diagnostic(
                source,
                &format!("{section}.{present_key}"),
                section,
            ));
        }
    }
}

fn expect_string_field(
    table: &toml::Table,
    key: &str,
    section: &str,
    source: SourceId,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<String> {
    match table.get(key) {
        None => {
            diagnostics.push(
                Diagnostic::error(
                    codes::INVALID_MANIFEST,
                    source,
                    Span::dummy(),
                    format!("missing required key `{section}.{key}`"),
                )
                .with_primary_label("manifest is missing this key"),
            );
            None
        }
        Some(toml::Value::String(s)) => Some(s.clone()),
        Some(_) => {
            diagnostics.push(
                Diagnostic::error(
                    codes::INVALID_MANIFEST,
                    source,
                    Span::dummy(),
                    format!("`{section}.{key}` must be a string"),
                )
                .with_primary_label("wrong type for this key"),
            );
            None
        }
    }
}

fn unknown_key_diagnostic(source: SourceId, key: &str, where_: &str) -> Diagnostic {
    Diagnostic::error(
        codes::INVALID_MANIFEST,
        source,
        Span::dummy(),
        format!("unknown manifest key `{key}` ({where_})"),
    )
    .with_primary_label("not a recognized manifest key")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::SourceMap;

    fn parse(content: &str) -> Result<Manifest, Vec<Diagnostic>> {
        let mut map = SourceMap::new();
        let id = map.add_file("napitia.toml", content);
        parse_manifest(id, content)
    }

    #[test]
    fn valid_manifest_parses() {
        let manifest = parse(
            "[package]\nname = \"hello\"\nversion = \"0.1.0\"\n\n\
             [project]\nsource-root = \"src\"\nentry = \"main.npt\"\n",
        )
        .expect("expected a valid manifest");
        assert_eq!(manifest.package_name, "hello");
        assert_eq!(manifest.package_version, "0.1.0");
        assert_eq!(manifest.source_root, "src");
        assert_eq!(manifest.entry, "main.npt");
    }

    #[test]
    fn malformed_toml_is_m0001() {
        let diags = parse("this is not [ valid toml").unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0001");
    }

    #[test]
    fn missing_required_field_is_m0001() {
        let diags = parse("[package]\nname = \"hello\"\n\n[project]\nsource-root = \"src\"\nentry = \"main.npt\"\n")
            .unwrap_err();
        assert!(diags.iter().all(|d| d.code == "M0001"));
        assert!(
            diags.iter().any(|d| d.message.contains("package.version")),
            "expected a diagnostic naming the missing field: {diags:?}"
        );
    }

    #[test]
    fn missing_multiple_fields_reports_all_of_them() {
        let diags =
            parse("[package]\nname = \"hello\"\n\n[project]\nentry = \"main.npt\"\n").unwrap_err();
        assert_eq!(diags.len(), 2, "unexpected diagnostics: {diags:?}");
        assert!(diags.iter().all(|d| d.code == "M0001"));
    }

    #[test]
    fn unknown_top_level_key_is_m0001() {
        let diags = parse(
            "[package]\nname = \"hello\"\nversion = \"0.1.0\"\n\n\
             [project]\nsource-root = \"src\"\nentry = \"main.npt\"\n\n\
             [dependencies]\n",
        )
        .unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0001");
        assert!(diags[0].message.contains("dependencies"));
    }

    #[test]
    fn unknown_field_within_a_known_section_is_m0001() {
        let diags = parse(
            "[package]\nname = \"hello\"\nversion = \"0.1.0\"\nauthor = \"nobody\"\n\n\
             [project]\nsource-root = \"src\"\nentry = \"main.npt\"\n",
        )
        .unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert!(diags[0].message.contains("package.author"));
    }

    #[test]
    fn wrong_typed_field_is_m0001() {
        let diags = parse(
            "[package]\nname = \"hello\"\nversion = 1\n\n\
             [project]\nsource-root = \"src\"\nentry = \"main.npt\"\n",
        )
        .unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0001");
    }

    #[test]
    fn duplicate_key_is_rejected_by_the_underlying_toml_syntax() {
        let diags = parse(
            "[package]\nname = \"hello\"\nname = \"hello-again\"\nversion = \"0.1.0\"\n\n\
             [project]\nsource-root = \"src\"\nentry = \"main.npt\"\n",
        )
        .unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0001");
    }
}
