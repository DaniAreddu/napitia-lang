//! Resolves one module's `import` statements against already-lowered
//! dependency modules (`rfcs/0006`).

use std::collections::HashMap;

use super::codes;
use super::loader::ImportRef;
use super::module::{ModuleId, ModulePath};
use crate::diagnostics::Diagnostic;
use crate::hir::{HirModule, ImportedItem, ImportedItemKind, OtherItemKind};
use crate::source::{SourceId, Span};
use crate::symbol::Interner;

/// Resolves every import belonging to one module against the modules it
/// depends on, all of which -- by construction, since modules are
/// processed in dependency order -- have already been fully lowered.
/// Returns every problem found rather than stopping at the first.
pub fn resolve_imports(
    imports: &[ImportRef],
    importing_source: SourceId,
    module_path_by_dotted: &HashMap<String, ModuleId>,
    lowered_by_module: &HashMap<ModuleId, (HirModule, SourceId)>,
    interner: &mut Interner,
) -> Result<Vec<ImportedItem>, Vec<Diagnostic>> {
    let mut resolved = Vec::new();
    let mut diagnostics = Vec::new();

    for import in imports {
        match resolve_one_import(
            import,
            importing_source,
            module_path_by_dotted,
            lowered_by_module,
            interner,
        ) {
            Ok(item) => resolved.push(item),
            Err(diag) => diagnostics.push(*diag),
        }
    }

    if diagnostics.is_empty() {
        Ok(resolved)
    } else {
        Err(diagnostics)
    }
}

fn resolve_one_import(
    import: &ImportRef,
    importing_source: SourceId,
    module_path_by_dotted: &HashMap<String, ModuleId>,
    lowered_by_module: &HashMap<ModuleId, (HirModule, SourceId)>,
    interner: &mut Interner,
) -> Result<ImportedItem, Box<Diagnostic>> {
    let Some((module_path, item_name)) = ModulePath::split_import_path(&import.segments) else {
        return Err(Box::new(
            Diagnostic::error(
                codes::INVALID_IMPORT_PATH,
                importing_source,
                import.span,
                format!(
                    "import path `{}` needs at least a module segment and an item segment",
                    import.segments.join(".")
                ),
            )
            .with_primary_label("incomplete import path"),
        ));
    };
    let dotted = module_path.dotted();
    let Some(&target_module) = module_path_by_dotted.get(&dotted) else {
        return Err(Box::new(
            Diagnostic::error(
                codes::MODULE_NOT_FOUND,
                importing_source,
                import.span,
                format!("module `{dotted}` not found"),
            )
            .with_primary_label("no such module"),
        ));
    };
    // Ordinarily unreachable: `project::compile_project` never calls
    // this with an import whose target module already failed to lower
    // (it skips the whole importing module first, propagating the
    // failure instead) -- but this is the one place a caller-side gap
    // in that pre-check would otherwise turn into a panic on user input,
    // so it fails as a diagnostic here too, defense in depth.
    let Some((target_hir, target_source)) = lowered_by_module.get(&target_module) else {
        return Err(Box::new(
            Diagnostic::error(
                codes::MODULE_NOT_FOUND,
                importing_source,
                import.span,
                format!("module `{dotted}` could not be loaded"),
            )
            .with_primary_label("dependency failed to compile"),
        ));
    };

    // The target module is always searched by the item's own *declared*
    // name -- an alias never changes what a dotted import path actually
    // names in the target module, only what the importing module calls
    // it afterward.
    let declared_name = interner.intern(item_name);
    // An `as <alias>` clause makes the alias the item's local name in
    // the importing module instead of its own declared name (rfcs/0007)
    // -- the declaration itself, and its identity, are untouched; only
    // the name this module refers to it by changes. Without an alias,
    // behavior is exactly Alpha 0.1.2's: the local name is the item's
    // own declared name.
    let local_name = match &import.alias {
        Some((alias_text, _)) => interner.intern(alias_text),
        None => declared_name,
    };

    if let Some(function) = target_hir
        .functions
        .iter()
        .find(|f| f.name == declared_name)
    {
        if !function.public {
            return Err(Box::new(private_item_diagnostic(
                importing_source,
                import.span,
                item_name,
                &dotted,
                *target_source,
                function.name_span,
            )));
        }
        return Ok(ImportedItem {
            local_name,
            kind: ImportedItemKind::Function(function.id),
            import_span: import.span,
            declared_source: *target_source,
            declared_span: function.name_span,
        });
    }
    if let Some(record) = target_hir.records.iter().find(|r| r.name == declared_name) {
        if !record.public {
            return Err(Box::new(private_item_diagnostic(
                importing_source,
                import.span,
                item_name,
                &dotted,
                *target_source,
                record.span,
            )));
        }
        let fields = record
            .fields
            .iter()
            .enumerate()
            .map(|(index, field)| (field.name, index, field.public))
            .collect();
        return Ok(ImportedItem {
            local_name,
            kind: ImportedItemKind::Record {
                item: record.id,
                declared_name: record.name,
                fields,
            },
            import_span: import.span,
            declared_source: *target_source,
            declared_span: record.span,
        });
    }
    if let Some(variant) = target_hir.variants.iter().find(|v| v.name == declared_name) {
        if !variant.public {
            return Err(Box::new(private_item_diagnostic(
                importing_source,
                import.span,
                item_name,
                &dotted,
                *target_source,
                variant.span,
            )));
        }
        let cases = variant
            .cases
            .iter()
            .enumerate()
            .map(|(index, case)| (case.name, index))
            .collect();
        return Ok(ImportedItem {
            local_name,
            kind: ImportedItemKind::Variant {
                item: variant.id,
                declared_name: variant.name,
                cases,
            },
            import_span: import.span,
            declared_source: *target_source,
            declared_span: variant.span,
        });
    }
    if let Some(other) = target_hir
        .other_items
        .iter()
        .find(|o| o.name == declared_name)
    {
        let kind_text = match other.kind {
            OtherItemKind::Protocol => "protocol",
            OtherItemKind::Extend => "extend block",
            OtherItemKind::Import => "import",
        };
        return Err(Box::new(
            Diagnostic::error(
                codes::ITEM_NOT_FOUND,
                importing_source,
                import.span,
                format!(
                    "`{item_name}` in module `{dotted}` is {} `{kind_text}`, which cannot be imported in Alpha 0.1.2",
                    if matches!(other.kind, OtherItemKind::Extend) { "an" } else { "a" }
                ),
            )
            .with_primary_label("not an importable kind")
            .with_label_in(*target_source, other.span, "declared here"),
        ));
    }

    Err(Box::new(
        Diagnostic::error(
            codes::ITEM_NOT_FOUND,
            importing_source,
            import.span,
            format!("module `{dotted}` has no item named `{item_name}`"),
        )
        .with_primary_label("not found"),
    ))
}

fn private_item_diagnostic(
    importing_source: SourceId,
    import_span: Span,
    item_name: &str,
    module_dotted: &str,
    declared_source: SourceId,
    declared_span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::ITEM_PRIVATE,
        importing_source,
        import_span,
        format!("`{item_name}` in module `{module_dotted}` is private"),
    )
    .with_primary_label("cannot import a private item")
    .with_label_in(declared_source, declared_span, "declared here")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::lower_module;
    use crate::lexer::tokenize;
    use crate::parser::Parser;
    use crate::source::SourceMap;

    /// Lowers `text` as the target module, returning its `HirModule`
    /// plus the `SourceId` it was lowered against.
    fn lowered_target(
        map: &mut SourceMap,
        interner: &mut Interner,
        text: &str,
    ) -> (HirModule, SourceId) {
        let id = map.add_file("math.npt", text);
        let (tokens, diags) = tokenize(map.get(id).content(), id, interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, diags) = lower_module(&module, id, interner);
        assert!(
            diags.is_empty(),
            "unexpected resolve diagnostics: {diags:?}"
        );
        (hir, id)
    }

    fn import_ref(segments: &[&str], span: Span) -> ImportRef {
        ImportRef {
            importing_module: ModuleId(1),
            segments: segments.iter().map(|s| s.to_string()).collect(),
            span,
            item_span: span,
            alias: None,
        }
    }

    fn aliased_import_ref(segments: &[&str], alias: &str, span: Span) -> ImportRef {
        ImportRef {
            alias: Some((alias.to_string(), span)),
            ..import_ref(segments, span)
        }
    }

    #[test]
    fn resolves_a_public_function_import() {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let (target_hir, target_source) =
            lowered_target(&mut map, &mut interner, "public func add() -> i64 { 0 }");
        let importing_source = map.add_file("main.npt", "");
        let mut module_paths = HashMap::new();
        module_paths.insert("math".to_string(), ModuleId(0));
        let mut lowered = HashMap::new();
        lowered.insert(ModuleId(0), (target_hir, target_source));

        let imports = vec![import_ref(&["math", "add"], Span::dummy())];
        let resolved = resolve_imports(
            &imports,
            importing_source,
            &module_paths,
            &lowered,
            &mut interner,
        )
        .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        assert_eq!(resolved.len(), 1);
        assert!(matches!(resolved[0].kind, ImportedItemKind::Function(_)));
    }

    #[test]
    fn an_aliased_import_uses_the_alias_as_its_local_name() {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let (target_hir, target_source) =
            lowered_target(&mut map, &mut interner, "public func add() -> i64 { 0 }");
        let importing_source = map.add_file("main.npt", "");
        let mut module_paths = HashMap::new();
        module_paths.insert("math".to_string(), ModuleId(0));
        let mut lowered = HashMap::new();
        lowered.insert(ModuleId(0), (target_hir, target_source));

        let imports = vec![aliased_import_ref(&["math", "add"], "plus", Span::dummy())];
        let resolved = resolve_imports(
            &imports,
            importing_source,
            &module_paths,
            &lowered,
            &mut interner,
        )
        .unwrap_or_else(|diags| panic!("unexpected diagnostics: {diags:?}"));
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].local_name, interner.intern("plus"));
        assert_ne!(resolved[0].local_name, interner.intern("add"));
    }

    #[test]
    fn importing_a_private_function_is_m0006() {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let (target_hir, target_source) =
            lowered_target(&mut map, &mut interner, "func secret() -> i64 { 0 }");
        let importing_source = map.add_file("main.npt", "");
        let mut module_paths = HashMap::new();
        module_paths.insert("math".to_string(), ModuleId(0));
        let mut lowered = HashMap::new();
        lowered.insert(ModuleId(0), (target_hir, target_source));

        let imports = vec![import_ref(&["math", "secret"], Span::dummy())];
        let diags = resolve_imports(
            &imports,
            importing_source,
            &module_paths,
            &lowered,
            &mut interner,
        )
        .unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0006");
    }

    #[test]
    fn importing_an_unknown_item_is_m0005() {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let (target_hir, target_source) =
            lowered_target(&mut map, &mut interner, "public func add() -> i64 { 0 }");
        let importing_source = map.add_file("main.npt", "");
        let mut module_paths = HashMap::new();
        module_paths.insert("math".to_string(), ModuleId(0));
        let mut lowered = HashMap::new();
        lowered.insert(ModuleId(0), (target_hir, target_source));

        let imports = vec![import_ref(&["math", "nope"], Span::dummy())];
        let diags = resolve_imports(
            &imports,
            importing_source,
            &module_paths,
            &lowered,
            &mut interner,
        )
        .unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0005");
    }

    #[test]
    fn importing_from_a_discovered_but_never_lowered_module_is_a_diagnostic_not_a_panic() {
        // Simulates the gap `project::compile_project`'s own pre-check
        // now closes: `math` is discovered (present in `module_paths`)
        // but never actually lowered (absent from `lowered`) -- e.g.
        // because its own imports failed to resolve. Resolving an
        // import that targets it must never panic, even if some future
        // caller forgets that pre-check.
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let importing_source = map.add_file("main.npt", "");
        let mut module_paths = HashMap::new();
        module_paths.insert("math".to_string(), ModuleId(0));
        let lowered = HashMap::new();

        let imports = vec![import_ref(&["math", "add"], Span::dummy())];
        let diags = resolve_imports(
            &imports,
            importing_source,
            &module_paths,
            &lowered,
            &mut interner,
        )
        .unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0004");
    }

    #[test]
    fn importing_from_an_unknown_module_is_m0004() {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let importing_source = map.add_file("main.npt", "");
        let module_paths = HashMap::new();
        let lowered = HashMap::new();

        let imports = vec![import_ref(&["nope", "thing"], Span::dummy())];
        let diags = resolve_imports(
            &imports,
            importing_source,
            &module_paths,
            &lowered,
            &mut interner,
        )
        .unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0004");
    }

    #[test]
    fn single_segment_import_path_is_m0003() {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let importing_source = map.add_file("main.npt", "");
        let module_paths = HashMap::new();
        let lowered = HashMap::new();

        let imports = vec![import_ref(&["math"], Span::dummy())];
        let diags = resolve_imports(
            &imports,
            importing_source,
            &module_paths,
            &lowered,
            &mut interner,
        )
        .unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0003");
    }

    #[test]
    fn importing_a_protocol_is_m0005_not_silently_ignored() {
        let mut map = SourceMap::new();
        let mut interner = Interner::new();
        let (target_hir, target_source) = lowered_target(
            &mut map,
            &mut interner,
            "protocol Drawable { func draw() -> i64; }",
        );
        let importing_source = map.add_file("main.npt", "");
        let mut module_paths = HashMap::new();
        module_paths.insert("shapes".to_string(), ModuleId(0));
        let mut lowered = HashMap::new();
        lowered.insert(ModuleId(0), (target_hir, target_source));

        let imports = vec![import_ref(&["shapes", "Drawable"], Span::dummy())];
        let diags = resolve_imports(
            &imports,
            importing_source,
            &module_paths,
            &lowered,
            &mut interner,
        )
        .unwrap_err();
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0005");
    }
}
