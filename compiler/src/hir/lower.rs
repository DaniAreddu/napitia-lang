//! AST-to-HIR lowering and name resolution.
//!
//! Lowering and resolution happen in the same pass: as each expression
//! is lowered, identifiers are immediately resolved against the current
//! [`Scopes`] stack (for locals), the module's function table (for
//! calls), and the module's type/field/case namespaces (for record
//! construction and variant constructors), rather than annotating the
//! AST first and resolving in a second walk.

use std::collections::HashMap;

use super::{
    AggregateKind, ExprId, HirBinding, HirBlock, HirCapabilityRequirement, HirCase, HirElse,
    HirExpr, HirExtend, HirField, HirFieldInit, HirFunction, HirMatchArm, HirMatchArmBody,
    HirModule, HirParam, HirPattern, HirProtocol, HirProtocolMethod, HirRecord, HirStmt, HirType,
    HirTypeParam, HirVariant, ItemId, LocalId, OtherItem, OtherItemKind, PatternId, TypeParamId,
};
use crate::diagnostics::Diagnostic;
use crate::limits::MAX_GENERIC_DEPTH;
use crate::resolve::Scopes;
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
use crate::syntax::ast;
use crate::syntax::ast::Path;
use crate::types::primitive_from_name;

mod codes {
    pub const DUPLICATE_DEFINITION: &str = "R0001";
    pub const UNRESOLVED_NAME: &str = "R0002";
    pub const DUPLICATE_PARAMETER: &str = "R0003";
    pub const DUPLICATE_FIELD_DECL: &str = "R0004";
    pub const DUPLICATE_CASE_DECL: &str = "R0005";
    pub const AMBIGUOUS_CONSTRUCTOR: &str = "R0006";
    pub const UNKNOWN_RECORD_TYPE: &str = "R0007";
    pub const UNKNOWN_FIELD_IN_CONSTRUCTION: &str = "R0008";
    pub const MISSING_FIELD: &str = "R0009";
    pub const DUPLICATE_FIELD_INIT: &str = "R0010";
    pub const UNKNOWN_VARIANT_TYPE: &str = "R0011";
    pub const UNKNOWN_VARIANT_CASE: &str = "R0012";
    pub const WRONG_VARIANT: &str = "R0013";
    pub const DUPLICATE_PATTERN_BINDING: &str = "R0014";
    pub const PATTERN_TOO_DEEP: &str = "R0015";
    pub const DUPLICATE_TYPE_PARAMETER: &str = "R0016";
    pub const PRIMITIVE_TYPE_PARAMETER_NAME: &str = "R0017";
    pub const TYPE_PARAMETER_APPLIED: &str = "R0018";
    pub const GENERIC_DEPTH_EXCEEDED: &str = "R0019";
    pub const INVALID_TYPE_APPLICATION: &str = "R0020";
    pub const DUPLICATE_PROTOCOL_METHOD: &str = "R0021";
    pub const UNKNOWN_PROTOCOL: &str = "R0022";
    pub const CAPABILITY_REQUIREMENT_DOTTED_PATH: &str = "R0023";
    pub const UNKNOWN_PROTOCOL_METHOD: &str = "R0024";
    pub const EXTEND_METHOD_OWN_TYPE_PARAMS: &str = "R0025";
    pub const PROTOCOL_NOT_A_VALUE: &str = "R0026";
    pub const EXTEND_METHOD_OWN_USES_CLAUSE: &str = "R0027";
}

/// Which kind of item a name in the type namespace refers to -- needed
/// to tell "unknown record type" (named a variant, or nothing) apart
/// from "unknown variant type" (named a record, or nothing) with an
/// accurate diagnostic either way.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum TypeNameKind {
    Record,
    Variant,
}

/// The four counters `Lowering` mints fresh ids from, threaded across
/// every module in a project compilation (`rfcs/0006`) so two items in
/// different modules can never collide by reusing the same numeric id.
/// Single-file compilation just starts and discards one of these per
/// call, same as before this type existed.
#[derive(Copy, Clone, Debug, Default)]
pub struct IdCursor {
    pub next_item_id: u32,
    pub next_local_id: u32,
    pub next_expr_id: u32,
    pub next_pattern_id: u32,
    pub next_type_param_id: u32,
}

/// One item made visible to a module via `import`, already resolved to
/// a concrete declaration in another (already-lowered) module. Built by
/// `project::resolve`, which is the only place that knows how to turn
/// an `import` statement's dotted path into one of these.
#[derive(Debug)]
pub struct ImportedItem {
    pub local_name: Symbol,
    pub kind: ImportedItemKind,
    /// The `import` statement's own span, in the *importing* module --
    /// used as a diagnostic's own primary location when the import
    /// itself (module resolution, privacy) is what's rejected.
    pub import_span: Span,
    /// The precise span of `local_name` itself: the alias identifier's
    /// own span for `import a.b as alias;`, or the imported item's own
    /// written name's span when there is no alias -- never the whole
    /// `import_span`. Used as this name's "declared here"/"already
    /// imported here" location for a collision diagnostic, so `import
    /// a.b as Alias;` colliding with something else labels `Alias`
    /// itself, not the entire statement (`rfcs/0007`).
    pub local_name_span: Span,
    /// Where the imported item was actually declared -- a different
    /// file than the importing module's own, in every real case. Used
    /// for a cross-file "declared here" label when this import
    /// conflicts with something else.
    pub declared_source: SourceId,
    pub declared_span: Span,
}

#[derive(Debug)]
pub enum ImportedItemKind {
    Function(ItemId),
    Record {
        item: ItemId,
        /// The record's own declared name -- e.g. `User`, never a local
        /// `as` alias -- carried so a `HirType::Aggregate` reference
        /// through this import can be tagged with the *canonical* name
        /// (see `resolve_type_ref`), never the alias it happened to be
        /// spelled with at this particular annotation. `Ty::Named`'s own
        /// display symbol, and every diagnostic/textual-NIR name, must
        /// stay alias-independent (`rfcs/0007`).
        declared_name: Symbol,
        /// `(field name, declaration index, is_public)`, in declaration
        /// order.
        fields: Vec<(Symbol, usize, bool)>,
    },
    Variant {
        item: ItemId,
        /// See `Record::declared_name`.
        declared_name: Symbol,
        /// `(case name, declaration index)`, in declaration order.
        cases: Vec<(Symbol, usize)>,
    },
    Protocol {
        item: ItemId,
        /// See `Record::declared_name`.
        declared_name: Symbol,
    },
}

/// Where a name in this module's namespace came from -- needed to
/// choose the right diagnostic (and labeling) when a second name
/// collides with it: two same-file declarations is `R0001`, anything
/// touching an import is `M0007`.
#[derive(Clone)]
enum NameOrigin {
    Local(Span),
    Imported {
        local_name_span: Span,
        declared_source: SourceId,
        declared_span: Span,
    },
}

pub fn lower_module(
    module: &ast::Module,
    source: SourceId,
    interner: &Interner,
) -> (HirModule, Vec<Diagnostic>) {
    let (hir, _cursor, diagnostics) =
        lower_module_with_imports(module, source, interner, IdCursor::default(), Vec::new());
    (hir, diagnostics)
}

/// Like [`lower_module`], but for one module in a multi-module project:
/// `ids` is where this module's own fresh ids start counting from
/// (threaded in from whatever the previously-lowered module in
/// dependency order left off at), and `imports` is every name this
/// module's own `import` statements successfully resolved to elsewhere
/// in the project, seeded into this module's namespaces before its own
/// declarations are processed -- so a local declaration reusing an
/// imported name is caught the same way a same-file duplicate already
/// is, just with a different diagnostic and a cross-file label.
pub fn lower_module_with_imports(
    module: &ast::Module,
    source: SourceId,
    interner: &Interner,
    ids: IdCursor,
    imports: Vec<ImportedItem>,
) -> (HirModule, IdCursor, Vec<Diagnostic>) {
    let mut lowering = Lowering {
        source,
        interner,
        diagnostics: Vec::new(),
        functions_by_name: HashMap::new(),
        type_names: HashMap::new(),
        protocol_names: HashMap::new(),
        protocol_methods: HashMap::new(),
        record_fields: HashMap::new(),
        variant_cases: HashMap::new(),
        case_lookup: HashMap::new(),
        imported_record_field_public: HashMap::new(),
        type_param_scope: HashMap::new(),
        next_item_id: ids.next_item_id,
        next_local_id: ids.next_local_id,
        next_expr_id: ids.next_expr_id,
        next_pattern_id: ids.next_pattern_id,
        next_type_param_id: ids.next_type_param_id,
    };
    let hir = lowering.run_with_imports(module, imports);
    let cursor = IdCursor {
        next_item_id: lowering.next_item_id,
        next_local_id: lowering.next_local_id,
        next_expr_id: lowering.next_expr_id,
        next_pattern_id: lowering.next_pattern_id,
        next_type_param_id: lowering.next_type_param_id,
    };
    (hir, cursor, lowering.diagnostics)
}

struct Lowering<'a> {
    source: SourceId,
    interner: &'a Interner,
    diagnostics: Vec<Diagnostic>,
    functions_by_name: HashMap<Symbol, ItemId>,
    /// The module's type namespace: every declared `record`/`variant`
    /// name, or the local (possibly aliased) name of one imported --
    /// primitives live entirely in `typeck`/`nir::lower`'s own copy of
    /// this concept, since they need no `ItemId`. The third element is
    /// the item's own canonical declared name (identical to the key
    /// unless this entry came from an aliased import), used to build
    /// every `HirType::Aggregate` so `Ty::Named`'s display symbol never
    /// depends on which local spelling resolved it (`rfcs/0007`).
    type_names: HashMap<Symbol, (ItemId, TypeNameKind, Symbol)>,
    /// The module's protocol namespace (`rfcs/0009`): every declared
    /// `protocol` name, or the local (possibly aliased) name of one
    /// imported, mapped to its `ItemId` plus its own canonical declared
    /// name (see `type_names`'s own doc comment for why the latter is
    /// kept). Deliberately separate from `type_names`: a protocol is
    /// never itself a value type (no dynamic protocol objects in Alpha
    /// 0.1.5), so it is never a candidate when resolving an ordinary
    /// field/param/return type reference, only the extend head, `uses`
    /// clause, and protocol-call positions that explicitly look here.
    protocol_names: HashMap<Symbol, (ItemId, Symbol)>,
    /// Per-protocol method name -> declaration index, populated once
    /// every protocol is fully lowered (before any function or extend
    /// body, which may reference it via a `Protocol[Args].method` call,
    /// `rfcs/0009`) -- mirrors `variant_cases`'s own role for case
    /// names.
    protocol_methods: HashMap<ItemId, HashMap<Symbol, usize>>,
    /// Per-record field name -> declaration index, for resolving a
    /// record literal's field initializers.
    record_fields: HashMap<ItemId, HashMap<Symbol, usize>>,
    /// Per-variant case name -> declaration index, for resolving a
    /// qualified (`Variant.Case`) or scrutinee-typed pattern reference.
    variant_cases: HashMap<ItemId, HashMap<Symbol, usize>>,
    /// Case name -> every `(variant, case index)` it names anywhere in
    /// the module, for resolving an *unqualified* constructor reference
    /// and detecting ambiguity when it names more than one variant.
    case_lookup: HashMap<Symbol, Vec<(ItemId, usize)>>,
    /// Field-name -> public/private, but *only* for records reaching
    /// this module via `import` -- a record declared locally never
    /// needs this (its fields are always accessible from inside its own
    /// module), so this map staying empty for a purely single-file
    /// compilation costs nothing.
    imported_record_field_public: HashMap<ItemId, HashMap<Symbol, bool>>,
    /// The *currently-being-lowered* declaration's own generic
    /// parameters, name -> (identity, declaration span) -- populated by
    /// [`Self::lower_type_params`] right before that declaration's own
    /// field/param/return/payload types are resolved, and cleared
    /// immediately after, so a type parameter is visible only while its
    /// own declaration is being lowered and never leaks into an
    /// unrelated one (`rfcs/0008`).
    type_param_scope: HashMap<Symbol, (TypeParamId, Span)>,
    next_item_id: u32,
    next_local_id: u32,
    next_expr_id: u32,
    next_pattern_id: u32,
    next_type_param_id: u32,
}

impl<'a> Lowering<'a> {
    fn run_with_imports(&mut self, module: &ast::Module, imports: Vec<ImportedItem>) -> HirModule {
        let mut names: HashMap<Symbol, NameOrigin> = HashMap::new();

        // Imported names are seeded *before* this module's own
        // declarations are processed, so a local declaration reusing
        // one is caught by the same collision check below, and so is a
        // second import introducing a name this module already
        // imported once.
        for imported in imports {
            if let Some(existing) = names.get(&imported.local_name).cloned() {
                self.diagnostics.push(self.import_collision_diagnostic(
                    imported.local_name,
                    imported.local_name_span,
                    &existing,
                ));
                continue;
            }
            let origin = NameOrigin::Imported {
                local_name_span: imported.local_name_span,
                declared_source: imported.declared_source,
                declared_span: imported.declared_span,
            };
            names.insert(imported.local_name, origin);
            match imported.kind {
                ImportedItemKind::Function(item) => {
                    self.functions_by_name.insert(imported.local_name, item);
                }
                ImportedItemKind::Record {
                    item,
                    declared_name,
                    fields,
                } => {
                    self.type_names.insert(
                        imported.local_name,
                        (item, TypeNameKind::Record, declared_name),
                    );
                    let mut field_indices = HashMap::new();
                    let mut field_public = HashMap::new();
                    for (name, index, is_public) in fields {
                        field_indices.insert(name, index);
                        field_public.insert(name, is_public);
                    }
                    self.record_fields.insert(item, field_indices);
                    self.imported_record_field_public.insert(item, field_public);
                }
                ImportedItemKind::Variant {
                    item,
                    declared_name,
                    cases,
                } => {
                    self.type_names.insert(
                        imported.local_name,
                        (item, TypeNameKind::Variant, declared_name),
                    );
                    let mut case_indices = HashMap::new();
                    for (name, index) in cases {
                        case_indices.insert(name, index);
                        self.add_case_candidate(name, item, index);
                    }
                    self.variant_cases.insert(item, case_indices);
                }
                ImportedItemKind::Protocol {
                    item,
                    declared_name,
                } => {
                    self.protocol_names
                        .insert(imported.local_name, (item, declared_name));
                }
            }
        }

        let mut function_decls: Vec<(ItemId, &ast::FunctionDecl)> = Vec::new();
        let mut record_decls: Vec<(ItemId, &ast::RecordDecl)> = Vec::new();
        let mut variant_decls: Vec<(ItemId, &ast::VariantDecl)> = Vec::new();
        let mut protocol_decls: Vec<(ItemId, &ast::ProtocolDecl)> = Vec::new();
        let mut extend_decls: Vec<(ItemId, &ast::ExtendDecl)> = Vec::new();
        let mut other_items = Vec::new();

        // First pass: mint every item's `ItemId` and populate the
        // module-wide namespaces (functions, types, fields, cases)
        // *before* lowering any function body or record/variant
        // internals -- a forward reference (a field typed with a
        // record declared later, a function calling one declared
        // later) must resolve exactly like Alpha 0.1's existing
        // forward-referenced function calls already do.
        for item in &module.items {
            match item {
                ast::Item::Function(f) => {
                    let id = self.fresh_item();
                    self.check_duplicate(&mut names, f.name, id);
                    self.functions_by_name.insert(f.name.symbol, id);
                    function_decls.push((id, f));
                }
                ast::Item::Record(r) => {
                    let id = self.fresh_item();
                    self.check_duplicate(&mut names, r.name, id);
                    self.type_names
                        .insert(r.name.symbol, (id, TypeNameKind::Record, r.name.symbol));
                    record_decls.push((id, r));
                }
                ast::Item::Variant(v) => {
                    let id = self.fresh_item();
                    self.check_duplicate(&mut names, v.name, id);
                    self.type_names
                        .insert(v.name.symbol, (id, TypeNameKind::Variant, v.name.symbol));
                    variant_decls.push((id, v));
                }
                ast::Item::Protocol(p) => {
                    let id = self.fresh_item();
                    self.check_duplicate(&mut names, p.name, id);
                    self.protocol_names
                        .insert(p.name.symbol, (id, p.name.symbol));
                    protocol_decls.push((id, p));
                }
                ast::Item::Extend(e) => {
                    let id = self.fresh_item();
                    extend_decls.push((id, e));
                }
                ast::Item::Import(i) => {
                    let id = self.fresh_item();
                    let name = *i
                        .path
                        .segments
                        .last()
                        .expect("a path has at least one segment");
                    other_items.push(other_item(id, name, i.span, OtherItemKind::Import));
                }
            }
        }

        // A public function/record field/variant case payload naming a
        // *locally-declared* private record/variant leaks a type
        // nothing outside this module can ever refer to -- any type
        // name that instead resolves to something imported must already
        // be public (a successful import guarantees that), so this
        // check only ever needs to look at this module's own
        // declarations.
        let local_public: HashMap<Symbol, bool> = record_decls
            .iter()
            .map(|(_, r)| (r.name.symbol, r.public))
            .chain(variant_decls.iter().map(|(_, v)| (v.name.symbol, v.public)))
            .collect();
        for (_, f) in &function_decls {
            if !f.public {
                continue;
            }
            for param in &f.params {
                self.check_public_api_leak(&param.ty, &local_public);
            }
            if let Some(ret) = &f.return_type {
                self.check_public_api_leak(ret, &local_public);
            }
        }
        for (_, r) in &record_decls {
            if !r.public {
                continue;
            }
            for field in &r.fields {
                if field.public {
                    self.check_public_api_leak(&field.ty, &local_public);
                }
            }
        }
        for (_, v) in &variant_decls {
            if !v.public {
                continue;
            }
            for case in &v.cases {
                for payload_ty in &case.payload {
                    self.check_public_api_leak(payload_ty, &local_public);
                }
            }
        }

        let records: Vec<HirRecord> = record_decls
            .into_iter()
            .map(|(id, r)| self.lower_record(id, r))
            .collect();
        let variants: Vec<HirVariant> = variant_decls
            .into_iter()
            .map(|(id, v)| self.lower_variant(id, v))
            .collect();
        // Protocols are lowered before any function or extend body: a
        // `Protocol[Args].method(...)` call anywhere in either needs
        // `self.protocol_methods`'s name -> index table already built
        // (`rfcs/0009`), the same way `variant_cases` must already be
        // populated before any body that qualifies a case constructor.
        let protocols: Vec<HirProtocol> = protocol_decls
            .into_iter()
            .map(|(id, p)| self.lower_protocol(id, p))
            .collect();
        for protocol in &protocols {
            let table = protocol.methods.iter().map(|m| (m.name, m.index)).collect();
            self.protocol_methods.insert(protocol.id, table);
        }
        let functions = function_decls
            .into_iter()
            .map(|(id, f)| self.lower_function(id, f))
            .collect();
        let extends: Vec<HirExtend> = extend_decls
            .into_iter()
            .map(|(id, e)| self.lower_extend(id, e))
            .collect();

        HirModule {
            functions,
            records,
            variants,
            protocols,
            extends,
            other_items,
        }
    }

    /// `M0012`: a public function signature, public field type, or
    /// variant case payload type naming a record/variant declared
    /// private in *this* module.
    fn check_public_api_leak(&mut self, ty: &ast::Type, local_public: &HashMap<Symbol, bool>) {
        // Same primitive-first rule as `resolve_type_ref`: a primitive
        // name always wins over a same-named local aggregate, so a
        // private `record i64 { .. }` must never make `-> i64` look
        // like it leaks a private type -- the annotation means the
        // primitive, not the record, regardless of what else in this
        // module happens to share its name.
        if primitive_from_name(self.interner.resolve(ty.name.symbol)).is_some() {
            return;
        }
        if let Some(&is_public) = local_public.get(&ty.name.symbol)
            && !is_public
        {
            let text = self.interner.resolve(ty.name.symbol);
            self.diagnostics.push(
                Diagnostic::error(
                    crate::project::codes::PRIVATE_TYPE_LEAKED,
                    self.source,
                    ty.name.span,
                    format!("`{text}` is private, but is exposed here through a public API"),
                )
                .with_primary_label("private type used in a public signature"),
            );
        }
        // A public generic type's own type *arguments* can leak a
        // private type just as easily as the head can (`public func f()
        // -> Box[Secret]` leaks `Secret` even though `Box` itself is
        // public) -- checked recursively, the same way argument
        // resolution itself is (`rfcs/0008`).
        for arg in &ty.args {
            self.check_public_api_leak(arg, local_public);
        }
    }

    fn lower_record(&mut self, id: ItemId, r: &ast::RecordDecl) -> HirRecord {
        let type_params = self.lower_type_params(&r.type_params);
        let mut seen: HashMap<Symbol, usize> = HashMap::new();
        let mut fields = Vec::new();
        for field in &r.fields {
            if let Some(&first_index) = seen.get(&field.name.symbol) {
                let text = self.interner.resolve(field.name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::DUPLICATE_FIELD_DECL,
                        self.source,
                        field.name.span,
                        format!("field `{text}` is declared more than once"),
                    )
                    .with_primary_label("duplicate field")
                    .with_label(r.fields[first_index].name.span, "first declared here"),
                );
                continue;
            }
            seen.insert(field.name.symbol, fields.len());
            let ty = self.resolve_type_ref(&field.ty);
            fields.push(HirField {
                name: field.name.symbol,
                span: field.span,
                public: field.public,
                ty,
            });
        }
        self.record_fields.insert(id, seen);
        self.clear_type_param_scope();
        HirRecord {
            id,
            name: r.name.symbol,
            type_params,
            span: r.span,
            source: self.source,
            public: r.public,
            fields,
        }
    }

    fn lower_variant(&mut self, id: ItemId, v: &ast::VariantDecl) -> HirVariant {
        let type_params = self.lower_type_params(&v.type_params);
        let mut seen: HashMap<Symbol, usize> = HashMap::new();
        let mut cases = Vec::new();
        for case in &v.cases {
            if let Some(&first_index) = seen.get(&case.name.symbol) {
                let text = self.interner.resolve(case.name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::DUPLICATE_CASE_DECL,
                        self.source,
                        case.name.span,
                        format!("case `{text}` is declared more than once"),
                    )
                    .with_primary_label("duplicate case")
                    .with_label(v.cases[first_index].name.span, "first declared here"),
                );
                continue;
            }
            let index = cases.len();
            seen.insert(case.name.symbol, index);
            self.add_case_candidate(case.name.symbol, id, index);
            let payload = case
                .payload
                .iter()
                .map(|t| self.resolve_type_ref(t))
                .collect();
            cases.push(HirCase {
                name: case.name.symbol,
                span: case.span,
                payload,
            });
        }
        self.variant_cases.insert(id, seen);
        self.clear_type_param_scope();
        HirVariant {
            id,
            name: v.name.symbol,
            type_params,
            span: v.span,
            source: self.source,
            public: v.public,
            cases,
        }
    }

    fn check_duplicate(
        &mut self,
        names: &mut HashMap<Symbol, NameOrigin>,
        name: ast::Ident,
        _id: ItemId,
    ) {
        match names.get(&name.symbol).cloned() {
            None => {
                names.insert(name.symbol, NameOrigin::Local(name.span));
            }
            Some(NameOrigin::Local(first_span)) => {
                let text = self.interner.resolve(name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::DUPLICATE_DEFINITION,
                        self.source,
                        name.span,
                        format!("`{text}` is defined multiple times"),
                    )
                    .with_primary_label("redefined here")
                    .with_label(first_span, "first defined here"),
                );
            }
            Some(imported @ NameOrigin::Imported { .. }) => {
                self.diagnostics.push(self.import_collision_diagnostic(
                    name.symbol,
                    name.span,
                    &imported,
                ));
            }
        }
    }

    /// Builds the `M0007` diagnostic for a name that collides with an
    /// already-known import -- whether the new name is itself another
    /// import (two imports naming the same local name) or a local
    /// declaration reusing an imported name. `existing` is always
    /// `NameOrigin::Imported`; the caller already checked that.
    fn import_collision_diagnostic(
        &self,
        symbol: Symbol,
        new_span: Span,
        existing: &NameOrigin,
    ) -> Diagnostic {
        let NameOrigin::Imported {
            local_name_span,
            declared_source,
            declared_span,
        } = existing
        else {
            unreachable!("caller only passes an Imported origin")
        };
        let text = self.interner.resolve(symbol);
        let diag = Diagnostic::error(
            crate::project::codes::DUPLICATE_IMPORT,
            self.source,
            new_span,
            format!("`{text}` conflicts with a name already imported into this module"),
        )
        .with_primary_label("conflicting name")
        .with_label(*local_name_span, "already imported here");
        if *declared_source == self.source && *local_name_span == *declared_span {
            diag
        } else {
            diag.with_label_in(*declared_source, *declared_span, "declared here")
        }
    }

    /// Resolves a written type name against *this module's own*
    /// type namespace (`self.type_names`, seeded with imports before any
    /// local declaration is processed -- see `run_with_imports`) to an
    /// exact declaration identity, before this module is ever merged
    /// with any other. This is the one and only place an aggregate type
    /// reference is resolved: it must never be re-derived later from a
    /// project-global surface name, which is exactly what let two
    /// modules' same-named types collide, or a module reach a type it
    /// never imported (`rfcs/0006`). A name that isn't a locally-known
    /// aggregate is left `Unresolved` -- it may still be a primitive, or
    /// genuinely unknown, neither of which HIR lowering itself decides.
    fn resolve_type_ref(&mut self, ty: &ast::Type) -> HirType {
        self.resolve_type_ref_at_depth(ty, 0)
    }

    /// `depth` counts one level per bracketed nesting level
    /// (`Box[Maybe[i64]]` resolves `Maybe[i64]` at `depth + 1`), bounded
    /// by [`MAX_GENERIC_DEPTH`] so a pathologically (or adversarially)
    /// deep annotation fails with a diagnostic instead of exhausting the
    /// native call stack (`rfcs/0008`).
    fn resolve_type_ref_at_depth(&mut self, ty: &ast::Type, depth: usize) -> HirType {
        if depth > MAX_GENERIC_DEPTH {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::GENERIC_DEPTH_EXCEEDED,
                    self.source,
                    ty.span,
                    "generic type application is nested too deeply to resolve",
                )
                .with_primary_label("type application is too deeply nested"),
            );
            return HirType::Unresolved {
                name: ty.name.symbol,
                span: ty.span,
            };
        }
        // A declaration's own type parameter takes precedence over
        // everything else: inside `func identity[T](value: T) -> T`,
        // `T` always means that parameter, never a same-named primitive
        // or aggregate (which, since primitive names are already
        // rejected as parameter names, could only be a hypothetical
        // module-level `record T { .. }` -- still shadowed, matching how
        // a parameter shadows an outer name everywhere else in this
        // grammar).
        if let Some(&(id, _)) = self.type_param_scope.get(&ty.name.symbol) {
            if !ty.args.is_empty() {
                let text = self.interner.resolve(ty.name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::TYPE_PARAMETER_APPLIED,
                        self.source,
                        ty.span,
                        format!(
                            "`{text}` is a type parameter and cannot itself be applied to type arguments"
                        ),
                    )
                    .with_primary_label("type parameter applied to arguments"),
                );
            }
            return HirType::Param {
                id,
                name: ty.name.symbol,
                span: ty.span,
            };
        }
        // Primitive names take precedence over an aggregate of the same
        // name, matching the pre-project-era rule (typeck always checked
        // its primitive namespace first): a local or imported `record`/
        // `variant` literally named `i64`/`bool`/etc. must never steal a
        // primitive type annotation out from under it. Left `Unresolved`
        // here (HIR itself has no notion of primitives) so typeck's own
        // `resolve_named_type` -- which already checks primitives first
        // -- resolves it the same way it always has.
        if primitive_from_name(self.interner.resolve(ty.name.symbol)).is_some() {
            if !ty.args.is_empty() {
                let text = self.interner.resolve(ty.name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::TYPE_PARAMETER_APPLIED,
                        self.source,
                        ty.span,
                        format!(
                            "`{text}` is a primitive type and cannot be applied to type arguments"
                        ),
                    )
                    .with_primary_label("primitive type applied to arguments"),
                );
            }
            return HirType::Unresolved {
                name: ty.name.symbol,
                span: ty.name.span,
            };
        }
        match self.type_names.get(&ty.name.symbol) {
            Some(&(item, kind, declared_name)) => {
                let args = ty
                    .args
                    .iter()
                    .map(|a| self.resolve_type_ref_at_depth(a, depth + 1))
                    .collect();
                HirType::Aggregate {
                    item,
                    kind: match kind {
                        TypeNameKind::Record => AggregateKind::Record,
                        TypeNameKind::Variant => AggregateKind::Variant,
                    },
                    // The item's own canonical name, never the local
                    // (possibly aliased) spelling this annotation
                    // happened to use -- `Ty::Named`'s display symbol
                    // must be alias-independent (`rfcs/0007`).
                    name: declared_name,
                    args,
                    span: ty.span,
                }
            }
            None => HirType::Unresolved {
                name: ty.name.symbol,
                span: ty.name.span,
            },
        }
    }

    fn fresh_item(&mut self) -> ItemId {
        let id = ItemId(self.next_item_id);
        self.next_item_id += 1;
        id
    }

    fn fresh_local(&mut self) -> LocalId {
        let id = LocalId(self.next_local_id);
        self.next_local_id += 1;
        id
    }

    fn fresh_expr_id(&mut self) -> ExprId {
        let id = ExprId(self.next_expr_id);
        self.next_expr_id += 1;
        id
    }

    fn fresh_pattern_id(&mut self) -> PatternId {
        let id = PatternId(self.next_pattern_id);
        self.next_pattern_id += 1;
        id
    }

    fn fresh_type_param(&mut self) -> TypeParamId {
        let id = TypeParamId(self.next_type_param_id);
        self.next_type_param_id += 1;
        id
    }

    /// Resolves a `func`/`record`/`variant`'s own `[T, U]` parameter
    /// list into stable identities, populating `self.type_param_scope`
    /// for the caller to resolve that same declaration's own field/
    /// param/return/payload types against (`rfcs/0008`). The caller is
    /// responsible for clearing the scope again once done (see
    /// [`Self::clear_type_param_scope`]) -- a type parameter's own
    /// identity must never be visible while lowering a different
    /// declaration.
    fn lower_type_params(&mut self, params: &[ast::Ident]) -> Vec<HirTypeParam> {
        self.type_param_scope.clear();
        let mut result = Vec::with_capacity(params.len());
        for p in params {
            if let Some(&(_, first_span)) = self.type_param_scope.get(&p.symbol) {
                let text = self.interner.resolve(p.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::DUPLICATE_TYPE_PARAMETER,
                        self.source,
                        p.span,
                        format!("type parameter `{text}` is declared more than once"),
                    )
                    .with_primary_label("duplicate type parameter")
                    .with_label(first_span, "first declared here"),
                );
                continue;
            }
            if primitive_from_name(self.interner.resolve(p.symbol)).is_some() {
                let text = self.interner.resolve(p.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::PRIMITIVE_TYPE_PARAMETER_NAME,
                        self.source,
                        p.span,
                        format!("`{text}` is a primitive type name and cannot be used as a type parameter"),
                    )
                    .with_primary_label("primitive type name"),
                );
                continue;
            }
            let id = self.fresh_type_param();
            self.type_param_scope.insert(p.symbol, (id, p.span));
            result.push(HirTypeParam {
                id,
                name: p.symbol,
                span: p.span,
            });
        }
        result
    }

    /// Ends the currently-lowered declaration's type-parameter scope --
    /// called once its own signature/fields/body are fully lowered, so
    /// its parameters never remain visible while lowering the next
    /// declaration (`rfcs/0008`).
    fn clear_type_param_scope(&mut self) {
        self.type_param_scope.clear();
    }

    /// Lowers one parameter list against a fresh `local` per parameter,
    /// diagnosing (but not aborting on) a repeated name -- shared by
    /// `lower_function` and `lower_extend_method`, the two places a
    /// parameter list is ever lowered.
    fn lower_params(&mut self, params: &[ast::Param], scopes: &mut Scopes) -> Vec<HirParam> {
        let mut seen_params: HashMap<Symbol, Span> = HashMap::new();
        params
            .iter()
            .map(|p| {
                if let Some(&first_span) = seen_params.get(&p.name.symbol) {
                    let text = self.interner.resolve(p.name.symbol);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::DUPLICATE_PARAMETER,
                            self.source,
                            p.name.span,
                            format!("parameter `{text}` is declared more than once"),
                        )
                        .with_primary_label("duplicate parameter")
                        .with_label(first_span, "first declared here"),
                    );
                } else {
                    seen_params.insert(p.name.symbol, p.name.span);
                }
                let local = self.fresh_local();
                scopes.define(p.name.symbol, local);
                let ty = self.resolve_type_ref(&p.ty);
                HirParam {
                    local,
                    name: p.name.symbol,
                    span: p.span,
                    ty,
                }
            })
            .collect()
    }

    /// Splits one `uses` clause's entries into this declaration's own
    /// capability requirements (`rfcs/0009`: a single name followed by a
    /// bracketed type-argument list) and its bare effect paths
    /// (`spec/0005`'s pre-existing, still-unchecked declarations, e.g.
    /// `Database.Read`, left completely untouched by this milestone).
    /// Must run while the enclosing declaration's own `type_param_scope`
    /// is still active, since a requirement's own arguments may
    /// reference it (`uses Equal[T]`).
    fn lower_uses_clause(
        &mut self,
        clauses: &[ast::UsesClause],
    ) -> (Vec<HirCapabilityRequirement>, Vec<Path>) {
        let mut requirements = Vec::new();
        let mut effects = Vec::new();
        for clause in clauses {
            if clause.args.is_empty() {
                effects.push(clause.path.clone());
                continue;
            }
            if clause.path.segments.len() != 1 {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::CAPABILITY_REQUIREMENT_DOTTED_PATH,
                        self.source,
                        clause.span,
                        "a capability requirement names a single protocol, not a dotted path",
                    )
                    .with_primary_label("dotted capability requirement"),
                );
                continue;
            }
            let name = clause.path.segments[0];
            let Some(&(protocol, _)) = self.protocol_names.get(&name.symbol) else {
                let text = self.interner.resolve(name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::UNKNOWN_PROTOCOL,
                        self.source,
                        name.span,
                        format!("`{text}` is not a declared protocol"),
                    )
                    .with_primary_label("unknown protocol"),
                );
                continue;
            };
            let arguments = clause
                .args
                .iter()
                .map(|a| self.resolve_type_ref(a))
                .collect();
            requirements.push(HirCapabilityRequirement {
                protocol,
                arguments,
                span: clause.span,
            });
        }
        (requirements, effects)
    }

    fn lower_function(&mut self, id: ItemId, f: &ast::FunctionDecl) -> HirFunction {
        let type_params = self.lower_type_params(&f.type_params);
        let mut scopes = Scopes::new();
        let params = self.lower_params(&f.params, &mut scopes);
        let return_type = f.return_type.as_ref().map(|t| self.resolve_type_ref(t));
        let (requirements, uses) = self.lower_uses_clause(&f.uses);
        let body = self.lower_block(&f.body, &mut scopes);
        self.clear_type_param_scope();
        HirFunction {
            id,
            name: f.name.symbol,
            name_span: f.name.span,
            type_params,
            source: self.source,
            public: f.public,
            params,
            return_type,
            uses,
            requirements,
            raises: f.raises.clone(),
            body,
            span: f.span,
        }
    }

    /// Lowers one `protocol Name[T, ...] { func sig(...) -> RT; ... }`
    /// declaration (`rfcs/0009`): its own type parameters, then each
    /// method signature in that same scope. A repeated method name is
    /// diagnosed but does not stop lowering the rest -- every method
    /// still gets a canonical `index`, so a later duplicate never
    /// silently shifts an earlier method's identity.
    fn lower_protocol(&mut self, id: ItemId, p: &ast::ProtocolDecl) -> HirProtocol {
        let type_params = self.lower_type_params(&p.type_params);
        let mut seen_methods: HashMap<Symbol, Span> = HashMap::new();
        let mut methods = Vec::with_capacity(p.members.len());
        for (index, member) in p.members.iter().enumerate() {
            if let Some(&first_span) = seen_methods.get(&member.name.symbol) {
                let text = self.interner.resolve(member.name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::DUPLICATE_PROTOCOL_METHOD,
                        self.source,
                        member.name.span,
                        format!("protocol method `{text}` is declared more than once"),
                    )
                    .with_primary_label("duplicate method")
                    .with_label(first_span, "first declared here"),
                );
            } else {
                seen_methods.insert(member.name.symbol, member.name.span);
            }
            let params = member
                .params
                .iter()
                .map(|prm| self.resolve_type_ref(&prm.ty))
                .collect();
            let return_type = member
                .return_type
                .as_ref()
                .map(|t| self.resolve_type_ref(t));
            methods.push(HirProtocolMethod {
                index,
                name: member.name.symbol,
                name_span: member.name.span,
                params,
                return_type,
                span: member.span,
            });
        }
        self.clear_type_param_scope();
        HirProtocol {
            id,
            name: p.name.symbol,
            name_span: p.name.span,
            type_params,
            methods,
            span: p.span,
            source: self.source,
            public: p.public,
        }
    }

    /// Lowers one `extend Equal[i64] { ... }` / `extend[T] Equal[Box[T]]
    /// uses Equal[T] { ... }` declaration (`rfcs/0009`). An unknown
    /// protocol name still produces an `HirExtend` (forward progress),
    /// carrying the sentinel [`unresolved_protocol_id`] as its
    /// `protocol` -- `typeck` never looks that id up in its own merged
    /// protocol table, since the diagnostic was already recorded here.
    fn lower_extend(&mut self, id: ItemId, e: &ast::ExtendDecl) -> HirExtend {
        let type_params = self.lower_type_params(&e.type_params);
        let protocol = match self.protocol_names.get(&e.protocol.name.symbol) {
            Some(&(item, _)) => item,
            None => {
                let text = self.interner.resolve(e.protocol.name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::UNKNOWN_PROTOCOL,
                        self.source,
                        e.protocol.name.span,
                        format!("`{text}` is not a declared protocol"),
                    )
                    .with_primary_label("unknown protocol"),
                );
                unresolved_protocol_id()
            }
        };
        let protocol_arguments = e
            .protocol
            .args
            .iter()
            .map(|a| self.resolve_type_ref(a))
            .collect();
        let (requirements, _effects) = self.lower_uses_clause(&e.uses);
        let methods = e
            .functions
            .iter()
            .map(|f| self.lower_extend_method(f, &requirements))
            .collect();
        self.clear_type_param_scope();
        HirExtend {
            id,
            type_params,
            protocol,
            protocol_arguments,
            protocol_ref_span: e.protocol.span,
            requirements,
            methods,
            span: e.span,
            source: self.source,
        }
    }

    /// Lowers one method body inside an `extend` block. Unlike an
    /// ordinary function, it never introduces its own type-parameter
    /// scope: its body resolves `T` against the *enclosing extend's*
    /// own `type_param_scope` (already active -- see `lower_extend`),
    /// so `HirFunction::type_params` is always empty here, and any type
    /// parameters explicitly (and invalidly) written on the method
    /// itself are diagnosed rather than silently accepted. Likewise, a
    /// method never declares its own `uses` clause: `requirements` is
    /// always the *enclosing extend's own* (`lower_extend`'s `uses
    /// Equal[T]`), passed in directly rather than derived from this
    /// method's own (expected-empty) `f.uses`.
    fn lower_extend_method(
        &mut self,
        f: &ast::FunctionDecl,
        requirements: &[HirCapabilityRequirement],
    ) -> HirFunction {
        let id = self.fresh_item();
        if !f.type_params.is_empty() {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::EXTEND_METHOD_OWN_TYPE_PARAMS,
                    self.source,
                    f.span,
                    "an extend method may not declare its own type parameters; use the extend's own `extend[...]` parameters instead",
                )
                .with_primary_label("unexpected type parameters"),
            );
        }
        if !f.uses.is_empty() {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::EXTEND_METHOD_OWN_USES_CLAUSE,
                    self.source,
                    f.span,
                    "an extend method may not declare its own `uses` clause; the extend's own `uses` clause already applies to every one of its methods",
                )
                .with_primary_label("unexpected `uses` clause"),
            );
        }
        let mut scopes = Scopes::new();
        let params = self.lower_params(&f.params, &mut scopes);
        let return_type = f.return_type.as_ref().map(|t| self.resolve_type_ref(t));
        let body = self.lower_block(&f.body, &mut scopes);
        HirFunction {
            id,
            name: f.name.symbol,
            name_span: f.name.span,
            type_params: Vec::new(),
            source: self.source,
            public: false,
            params,
            return_type,
            uses: Vec::new(),
            requirements: requirements.to_vec(),
            raises: f.raises.clone(),
            body,
            span: f.span,
        }
    }

    fn lower_block(&mut self, block: &ast::Block, scopes: &mut Scopes) -> HirBlock {
        scopes.push();
        let statements = block
            .statements
            .iter()
            .map(|s| self.lower_stmt(s, scopes))
            .collect();
        let tail = block
            .tail
            .as_ref()
            .map(|e| Box::new(self.lower_expr(e, scopes)));
        scopes.pop();
        HirBlock {
            id: self.fresh_expr_id(),
            statements,
            tail,
            span: block.span,
        }
    }

    fn lower_stmt(&mut self, stmt: &ast::Stmt, scopes: &mut Scopes) -> HirStmt {
        match stmt {
            ast::Stmt::Binding(b) => {
                let value = self.lower_expr(&b.value, scopes);
                let local = self.fresh_local();
                scopes.define(b.name.symbol, local);
                let ty = b.ty.as_ref().map(|t| self.resolve_type_ref(t));
                HirStmt::Binding(HirBinding {
                    local,
                    name: b.name.symbol,
                    mutable: b.mutable,
                    ty,
                    value,
                    span: b.span,
                })
            }
            ast::Stmt::Expr(e) => HirStmt::Expr(self.lower_expr(e, scopes)),
            ast::Stmt::Defer { expr, span } => HirStmt::Defer {
                expr: self.lower_expr(expr, scopes),
                span: *span,
            },
            ast::Stmt::While(w) => {
                let condition = Box::new(self.lower_expr(&w.condition, scopes));
                let body = self.lower_block(&w.body, scopes);
                HirStmt::While {
                    condition,
                    body,
                    span: w.span,
                }
            }
            ast::Stmt::Loop(l) => {
                let body = self.lower_block(&l.body, scopes);
                HirStmt::Loop { body, span: l.span }
            }
        }
    }

    fn lower_expr(&mut self, expr: &ast::Expr, scopes: &mut Scopes) -> HirExpr {
        match expr {
            ast::Expr::Int { value, base, span } => HirExpr::Int {
                id: self.fresh_expr_id(),
                value: *value,
                base: *base,
                span: *span,
            },
            ast::Expr::Float { value, span } => HirExpr::Float {
                id: self.fresh_expr_id(),
                value: *value,
                span: *span,
            },
            ast::Expr::Str { value, span } => HirExpr::Str {
                id: self.fresh_expr_id(),
                value: value.clone(),
                span: *span,
            },
            ast::Expr::Char { value, span } => HirExpr::Char {
                id: self.fresh_expr_id(),
                value: *value,
                span: *span,
            },
            ast::Expr::Bool { value, span } => HirExpr::Bool {
                id: self.fresh_expr_id(),
                value: *value,
                span: *span,
            },
            ast::Expr::Ident(ident) => self.resolve_ident(*ident, scopes),
            ast::Expr::Paren { inner, .. } => self.lower_expr(inner, scopes),
            ast::Expr::Unary { op, operand, span } => HirExpr::Unary {
                id: self.fresh_expr_id(),
                op: *op,
                operand: Box::new(self.lower_expr(operand, scopes)),
                span: *span,
            },
            ast::Expr::Binary {
                op,
                left,
                right,
                span,
            } => HirExpr::Binary {
                id: self.fresh_expr_id(),
                op: *op,
                left: Box::new(self.lower_expr(left, scopes)),
                right: Box::new(self.lower_expr(right, scopes)),
                span: *span,
            },
            ast::Expr::Assign {
                target,
                op,
                value,
                span,
            } => HirExpr::Assign {
                id: self.fresh_expr_id(),
                target: Box::new(self.lower_expr(target, scopes)),
                op: *op,
                value: Box::new(self.lower_expr(value, scopes)),
                span: *span,
            },
            ast::Expr::Call { callee, args, span } => HirExpr::Call {
                id: self.fresh_expr_id(),
                callee: Box::new(self.lower_expr(callee, scopes)),
                args: args.iter().map(|a| self.lower_expr(a, scopes)).collect(),
                span: *span,
            },
            ast::Expr::Field { base, name, span } => self.lower_field(base, *name, *span, scopes),
            ast::Expr::Cast { expr, ty, span } => HirExpr::Cast {
                id: self.fresh_expr_id(),
                expr: Box::new(self.lower_expr(expr, scopes)),
                ty: self.resolve_type_ref(ty),
                span: *span,
            },
            ast::Expr::Try { expr, span } => HirExpr::Try {
                id: self.fresh_expr_id(),
                expr: Box::new(self.lower_expr(expr, scopes)),
                span: *span,
            },
            ast::Expr::If(if_expr) => self.lower_if(if_expr, scopes),
            ast::Expr::Match(m) => self.lower_match(m, scopes),
            ast::Expr::Block(b) => HirExpr::Block(Box::new(self.lower_block(b, scopes))),
            ast::Expr::Return { value, span } => HirExpr::Return {
                id: self.fresh_expr_id(),
                value: value.as_ref().map(|v| Box::new(self.lower_expr(v, scopes))),
                span: *span,
            },
            ast::Expr::Break { value, span } => HirExpr::Break {
                id: self.fresh_expr_id(),
                value: value.as_ref().map(|v| Box::new(self.lower_expr(v, scopes))),
                span: *span,
            },
            ast::Expr::Continue { span } => HirExpr::Continue {
                id: self.fresh_expr_id(),
                span: *span,
            },
            ast::Expr::RecordLiteral {
                type_name,
                type_args,
                fields,
                span,
            } => self.lower_record_literal(*type_name, type_args, fields, *span, scopes),
            ast::Expr::TypeApply { base, args, span } => {
                self.lower_type_apply(base, args, *span, scopes)
            }
            ast::Expr::Error { span } => HirExpr::Error {
                id: self.fresh_expr_id(),
                span: *span,
            },
        }
    }

    /// Lowers `Base[Args]` in a non-record-literal position
    /// (`identity[i64]`, or the base of `Maybe[i64].Some(...)` once
    /// `lower_field` has already handled and returned early for that
    /// shape) -- `rfcs/0008`. Only ever legal directly on a plain,
    /// unshadowed function name in this milestone: a local variable, an
    /// unresolved name, or anything else `base` might structurally be is
    /// rejected here, never silently reinterpreted.
    fn lower_type_apply(
        &mut self,
        base: &ast::Expr,
        args: &[ast::Type],
        span: Span,
        scopes: &mut Scopes,
    ) -> HirExpr {
        let ast::Expr::Ident(ident) = base else {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::INVALID_TYPE_APPLICATION,
                    self.source,
                    span,
                    "type arguments may only follow a plain function or type name",
                )
                .with_primary_label("invalid type application"),
            );
            return HirExpr::Error {
                id: self.fresh_expr_id(),
                span,
            };
        };
        if scopes.lookup(ident.symbol).is_some() {
            let text = self.interner.resolve(ident.symbol);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::INVALID_TYPE_APPLICATION,
                    self.source,
                    span,
                    format!("`{text}` is a local binding and cannot take type arguments"),
                )
                .with_primary_label("invalid type application"),
            );
            return HirExpr::Error {
                id: self.fresh_expr_id(),
                span,
            };
        }
        if let Some(&item) = self.functions_by_name.get(&ident.symbol) {
            let type_args = args.iter().map(|a| self.resolve_type_ref(a)).collect();
            return HirExpr::Function {
                id: self.fresh_expr_id(),
                item,
                name: ident.symbol,
                type_args,
                span,
            };
        }
        if self.type_names.contains_key(&ident.symbol) {
            // A generic type name standing alone (no `.Case` qualifier,
            // no record-literal `{ .. }`) is never itself a value --
            // `lower_field`'s own `TypeApply`-aware handling intercepts
            // the `Maybe[i64].Some` shape before `lower_expr` (and so
            // this function) ever sees it, and `parse_record_literal`
            // intercepts the `Box[i64] { .. }` shape at parse time, so
            // reaching here with a known type name means neither
            // followed.
            let text = self.interner.resolve(ident.symbol);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::INVALID_TYPE_APPLICATION,
                    self.source,
                    span,
                    format!("`{text}` is a type, not a value"),
                )
                .with_primary_label("type used as a value"),
            );
            return HirExpr::Error {
                id: self.fresh_expr_id(),
                span,
            };
        }
        if self.protocol_names.contains_key(&ident.symbol) {
            return self.protocol_not_a_value(*ident, span);
        }
        let text = self.interner.resolve(ident.symbol);
        self.diagnostics.push(
            Diagnostic::error(
                codes::UNRESOLVED_NAME,
                self.source,
                ident.span,
                format!("cannot find `{text}` in this scope"),
            )
            .with_primary_label("not found"),
        );
        HirExpr::Error {
            id: self.fresh_expr_id(),
            span,
        }
    }

    /// `rfcs/0009`: there are no dynamic/first-class protocol references
    /// in Alpha 0.1.5 -- a protocol name is only ever meaningful as
    /// `Protocol[Args].method(...)`, never standing alone (bare, or
    /// applied but not immediately qualified by a method).
    fn protocol_not_a_value(&mut self, ident: ast::Ident, span: Span) -> HirExpr {
        let text = self.interner.resolve(ident.symbol);
        self.diagnostics.push(
            Diagnostic::error(
                codes::PROTOCOL_NOT_A_VALUE,
                self.source,
                span,
                format!(
                    "`{text}` is a protocol, not a value; call one of its methods explicitly (`{text}[..].method(..)`)"
                ),
            )
            .with_primary_label("protocol used as a value"),
        );
        HirExpr::Error {
            id: self.fresh_expr_id(),
            span,
        }
    }

    fn resolve_ident(&mut self, ident: ast::Ident, scopes: &Scopes) -> HirExpr {
        if let Some(local) = scopes.lookup(ident.symbol) {
            return HirExpr::Local {
                id: self.fresh_expr_id(),
                local,
                name: ident.symbol,
                span: ident.span,
            };
        }
        if let Some(&item) = self.functions_by_name.get(&ident.symbol) {
            return HirExpr::Function {
                id: self.fresh_expr_id(),
                item,
                name: ident.symbol,
                type_args: Vec::new(),
                span: ident.span,
            };
        }
        // Not a local or a function: an unqualified reference to a
        // variant case constructor is accepted when its name is
        // unambiguous across every declared variant in the module (see
        // RFC 0005's "Namespaces" section).
        if let Some(candidates) = self.case_lookup.get(&ident.symbol) {
            return self.resolve_case_candidates(ident, candidates.clone());
        }
        if self.protocol_names.contains_key(&ident.symbol) {
            return self.protocol_not_a_value(ident, ident.span);
        }
        let text = self.interner.resolve(ident.symbol);
        self.diagnostics.push(
            Diagnostic::error(
                codes::UNRESOLVED_NAME,
                self.source,
                ident.span,
                format!("cannot find `{text}` in this scope"),
            )
            .with_primary_label("not found"),
        );
        HirExpr::Error {
            id: self.fresh_expr_id(),
            span: ident.span,
        }
    }

    fn resolve_case_candidates(
        &mut self,
        ident: ast::Ident,
        candidates: Vec<(ItemId, usize)>,
    ) -> HirExpr {
        if candidates.len() > 1 {
            let text = self.interner.resolve(ident.symbol);
            // Sorted and deduplicated so the message text is independent
            // of both `case_lookup`'s insertion order (itself a function
            // of import declaration order) and `variant_name`'s own
            // internal `HashMap` traversal.
            let mut variant_names: Vec<&str> = candidates
                .iter()
                .map(|(variant, _)| self.variant_name(*variant))
                .collect();
            variant_names.sort_unstable();
            variant_names.dedup();
            self.diagnostics.push(
                Diagnostic::error(
                    codes::AMBIGUOUS_CONSTRUCTOR,
                    self.source,
                    ident.span,
                    format!(
                        "`{text}` is ambiguous: it names a case in more than one variant ({}); \
                         use a qualified path (`Variant.{text}`)",
                        variant_names.join(", ")
                    ),
                )
                .with_primary_label("ambiguous constructor"),
            );
            return HirExpr::Error {
                id: self.fresh_expr_id(),
                span: ident.span,
            };
        }
        let (variant, case) = candidates[0];
        HirExpr::CaseRef {
            id: self.fresh_expr_id(),
            variant,
            case,
            name: ident.symbol,
            type_args: Vec::new(),
            span: ident.span,
        }
    }

    /// Records that `item`'s case `index`, named `name`, is reachable
    /// under an unqualified reference in this module -- deduplicated by
    /// `(item, index)` so importing the very same variant under two (or
    /// more) different aliases pushes only one candidate, not one per
    /// alias. Without this, an unqualified constructor could become
    /// falsely "ambiguous" against itself merely because it was reachable
    /// under more than one local spelling (`rfcs/0007`).
    fn add_case_candidate(&mut self, name: Symbol, item: ItemId, index: usize) {
        let candidates = self.case_lookup.entry(name).or_default();
        if !candidates.contains(&(item, index)) {
            candidates.push((item, index));
        }
    }

    /// Looks up a declared item's name for use inside another
    /// diagnostic's message; every `ItemId` reaching this function came
    /// from this module's own `type_names`/`case_lookup` tables, so the
    /// name is always present.
    fn variant_name(&self, item: ItemId) -> &'a str {
        // A variant reachable under more than one local alias has more
        // than one matching key in `type_names` -- iterating a `HashMap`
        // would make the choice depend on that map's (unspecified, and
        // in practice randomized per process) iteration order, so every
        // matching name is collected and the lexicographically smallest
        // one is used instead: deterministic regardless of which alias
        // was inserted first, and independent of import order.
        let mut names: Vec<&str> = self
            .type_names
            .iter()
            .filter(|(_, (id, kind, _))| *id == item && *kind == TypeNameKind::Variant)
            .map(|(name, _)| self.interner.resolve(*name))
            .collect();
        names.sort_unstable();
        names
            .into_iter()
            .next()
            .expect("internal invariant: every case_lookup entry names a known variant")
    }

    /// Lowers `base.name`, distinguishing three shapes: ordinary field
    /// access on a value, a qualified variant constructor
    /// (`Variant.Case`), and a qualified reference into a record's
    /// namespace (rejected -- records have no "cases").
    fn lower_field(
        &mut self,
        base: &ast::Expr,
        name: ast::Ident,
        span: Span,
        scopes: &mut Scopes,
    ) -> HirExpr {
        // `Variant.Case` and `Variant[Args].Case` are both qualified
        // case references -- `[Args]` (if any) binds to the base name
        // before this field access, exactly like a record literal's own
        // `[Args] { .. }` (`rfcs/0008`).
        let (base_ident, type_args_ast): (Option<&ast::Ident>, &[ast::Type]) = match base {
            ast::Expr::Ident(ident) => (Some(ident), &[]),
            ast::Expr::TypeApply {
                base: inner, args, ..
            } => match inner.as_ref() {
                ast::Expr::Ident(ident) => (Some(ident), args.as_slice()),
                _ => (None, &[]),
            },
            _ => (None, &[]),
        };
        if let Some(base_ident) = base_ident
            && scopes.lookup(base_ident.symbol).is_none()
            && !self.functions_by_name.contains_key(&base_ident.symbol)
            && let Some(&(protocol, _)) = self.protocol_names.get(&base_ident.symbol)
        {
            return self.resolve_protocol_method(protocol, *base_ident, type_args_ast, name, span);
        }
        if let Some(base_ident) = base_ident
            && scopes.lookup(base_ident.symbol).is_none()
            && !self.functions_by_name.contains_key(&base_ident.symbol)
            && let Some(&(item, kind, _)) = self.type_names.get(&base_ident.symbol)
        {
            return match kind {
                TypeNameKind::Variant => {
                    self.resolve_qualified_case(item, *base_ident, type_args_ast, name)
                }
                TypeNameKind::Record => {
                    let base_text = self.interner.resolve(base_ident.symbol);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::UNKNOWN_VARIANT_TYPE,
                            self.source,
                            base_ident.span,
                            format!("`{base_text}` is a record, which has no cases to qualify"),
                        )
                        .with_primary_label("not a variant type"),
                    );
                    HirExpr::Error {
                        id: self.fresh_expr_id(),
                        span,
                    }
                }
            };
        }
        HirExpr::Field {
            id: self.fresh_expr_id(),
            base: Box::new(self.lower_expr(base, scopes)),
            name: name.symbol,
            span,
        }
    }

    /// Resolves `Protocol[Args].method` (`rfcs/0009`) -- mirrors
    /// `resolve_qualified_case`. Arity of `Args` against the protocol's
    /// own declared type-parameter count is left to `typeck`, the same
    /// way an ordinary aggregate type application's arity is (see
    /// `resolve_type_ref_at_depth`'s own doc comment); an unknown method
    /// name is rejected here, immediately, the same way an unknown case
    /// name is.
    fn resolve_protocol_method(
        &mut self,
        protocol: ItemId,
        base_ident: ast::Ident,
        type_args_ast: &[ast::Type],
        method_name: ast::Ident,
        span: Span,
    ) -> HirExpr {
        let arguments = type_args_ast
            .iter()
            .map(|a| self.resolve_type_ref(a))
            .collect();
        let Some(&method) = self
            .protocol_methods
            .get(&protocol)
            .and_then(|methods| methods.get(&method_name.symbol))
        else {
            let base_text = self.interner.resolve(base_ident.symbol);
            let method_text = self.interner.resolve(method_name.symbol);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::UNKNOWN_PROTOCOL_METHOD,
                    self.source,
                    method_name.span,
                    format!("protocol `{base_text}` has no method named `{method_text}`"),
                )
                .with_primary_label("unknown protocol method"),
            );
            return HirExpr::Error {
                id: self.fresh_expr_id(),
                span,
            };
        };
        HirExpr::ProtocolMethodRef {
            id: self.fresh_expr_id(),
            protocol,
            arguments,
            method,
            name: method_name.symbol,
            span,
        }
    }

    fn resolve_qualified_case(
        &mut self,
        variant: ItemId,
        base_ident: ast::Ident,
        type_args_ast: &[ast::Type],
        case_name: ast::Ident,
    ) -> HirExpr {
        let span = base_ident.span.join(case_name.span);
        if let Some(&index) = self
            .variant_cases
            .get(&variant)
            .and_then(|cases| cases.get(&case_name.symbol))
        {
            let type_args = type_args_ast
                .iter()
                .map(|a| self.resolve_type_ref(a))
                .collect();
            return HirExpr::CaseRef {
                id: self.fresh_expr_id(),
                variant,
                case: index,
                name: case_name.symbol,
                type_args,
                span,
            };
        }
        let case_text = self.interner.resolve(case_name.symbol);
        let variant_text = self.interner.resolve(base_ident.symbol);
        if let Some(elsewhere) = self.case_lookup.get(&case_name.symbol) {
            // Every *distinct* variant (other than the one actually
            // named) that also declares this case, resolved through the
            // same deterministic local-name lookup `variant_name` itself
            // uses -- never picked via `.find()` on `elsewhere`, whose
            // order is `case_lookup`'s own insertion order (a function of
            // import declaration order, and of how many aliases happen to
            // reach the same variant). Sorted and deduplicated so the
            // message text is independent of both.
            let mut owner_names: Vec<&str> = elsewhere
                .iter()
                .map(|(v, _)| *v)
                .filter(|v| *v != variant)
                .map(|id| self.variant_name(id))
                .collect();
            owner_names.sort_unstable();
            owner_names.dedup();
            if !owner_names.is_empty() {
                let message = if let [only] = owner_names.as_slice() {
                    format!("`{case_text}` is a case of variant `{only}`, not `{variant_text}`")
                } else {
                    let owners = owner_names
                        .iter()
                        .map(|name| format!("`{name}`"))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("`{case_text}` is a case of variants {owners}, not `{variant_text}`")
                };
                self.diagnostics.push(
                    Diagnostic::error(codes::WRONG_VARIANT, self.source, case_name.span, message)
                        .with_primary_label("wrong variant"),
                );
                return HirExpr::Error {
                    id: self.fresh_expr_id(),
                    span,
                };
            }
        }
        self.diagnostics.push(
            Diagnostic::error(
                codes::UNKNOWN_VARIANT_CASE,
                self.source,
                case_name.span,
                format!("variant `{variant_text}` has no case named `{case_text}`"),
            )
            .with_primary_label("unknown case"),
        );
        HirExpr::Error {
            id: self.fresh_expr_id(),
            span,
        }
    }

    fn lower_record_literal(
        &mut self,
        type_name: ast::Ident,
        type_args_ast: &[ast::Type],
        fields: &[ast::FieldInit],
        span: Span,
        scopes: &mut Scopes,
    ) -> HirExpr {
        let record = match self.type_names.get(&type_name.symbol) {
            Some(&(item, TypeNameKind::Record, _)) => item,
            Some(&(_, TypeNameKind::Variant, _)) => {
                let text = self.interner.resolve(type_name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::UNKNOWN_RECORD_TYPE,
                        self.source,
                        type_name.span,
                        format!("`{text}` is a variant, which is constructed with `.Case(...)`, not `{{ ... }}`"),
                    )
                    .with_primary_label("not a record type"),
                );
                // Still lower every field's value expression, for
                // cascading diagnostics, before giving up.
                for f in fields {
                    self.lower_expr(&f.value, scopes);
                }
                return HirExpr::Error {
                    id: self.fresh_expr_id(),
                    span,
                };
            }
            None => {
                let text = self.interner.resolve(type_name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::UNKNOWN_RECORD_TYPE,
                        self.source,
                        type_name.span,
                        format!("cannot find record type `{text}` in this scope"),
                    )
                    .with_primary_label("unknown record type"),
                );
                for f in fields {
                    self.lower_expr(&f.value, scopes);
                }
                return HirExpr::Error {
                    id: self.fresh_expr_id(),
                    span,
                };
            }
        };

        let field_indices = self.record_fields.get(&record).cloned().unwrap_or_default();
        let mut seen: HashMap<Symbol, Span> = HashMap::new();
        let mut resolved = Vec::with_capacity(fields.len());
        for f in fields {
            let value = self.lower_expr(&f.value, scopes);
            if let Some(&first_span) = seen.get(&f.name.symbol) {
                let text = self.interner.resolve(f.name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::DUPLICATE_FIELD_INIT,
                        self.source,
                        f.name.span,
                        format!("field `{text}` is initialized more than once"),
                    )
                    .with_primary_label("duplicate initializer")
                    .with_label(first_span, "first initialized here"),
                );
                continue;
            }
            seen.insert(f.name.symbol, f.name.span);
            let is_private_imported_field = self
                .imported_record_field_public
                .get(&record)
                .and_then(|fields| fields.get(&f.name.symbol))
                .is_some_and(|&is_public| !is_public);
            if is_private_imported_field {
                let text = self.interner.resolve(f.name.symbol);
                let record_text = self.interner.resolve(type_name.symbol);
                self.diagnostics.push(
                    Diagnostic::error(
                        crate::project::codes::INACCESSIBLE_FIELD,
                        self.source,
                        f.name.span,
                        format!(
                            "field `{text}` of `{record_text}` is private to its declaring module"
                        ),
                    )
                    .with_primary_label("cannot initialize a private field from here"),
                );
                continue;
            }
            match field_indices.get(&f.name.symbol) {
                Some(&field_index) => resolved.push(HirFieldInit {
                    field_index,
                    value,
                    span: f.span,
                }),
                None => {
                    let text = self.interner.resolve(f.name.symbol);
                    let record_text = self.interner.resolve(type_name.symbol);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::UNKNOWN_FIELD_IN_CONSTRUCTION,
                            self.source,
                            f.name.span,
                            format!("record `{record_text}` has no field named `{text}`"),
                        )
                        .with_primary_label("unknown field"),
                    );
                }
            }
        }

        // `field_indices` is a `HashMap`, whose iteration order is not
        // itself meaningful -- but its value *is* each field's
        // declaration index, so sorting by that recovers exact
        // declaration order without needing a separately-threaded
        // ordered field list. Diagnostic text must never depend on
        // HashMap iteration order: it is not deterministic across runs.
        let mut missing: Vec<(usize, &str)> = field_indices
            .iter()
            .filter(|(name, _)| !seen.contains_key(*name))
            .map(|(name, &index)| (index, self.interner.resolve(*name)))
            .collect();
        missing.sort_by_key(|(index, _)| *index);
        let missing: Vec<&str> = missing.into_iter().map(|(_, name)| name).collect();
        if !missing.is_empty() {
            let record_text = self.interner.resolve(type_name.symbol);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::MISSING_FIELD,
                    self.source,
                    span,
                    format!(
                        "missing field(s) in construction of `{record_text}`: {}",
                        missing.join(", ")
                    ),
                )
                .with_primary_label("missing field(s)"),
            );
        }

        let type_args = type_args_ast
            .iter()
            .map(|a| self.resolve_type_ref(a))
            .collect();
        HirExpr::RecordLiteral {
            id: self.fresh_expr_id(),
            record,
            type_args,
            fields: resolved,
            span,
        }
    }

    fn lower_if(&mut self, if_expr: &ast::IfExpr, scopes: &mut Scopes) -> HirExpr {
        let condition = Box::new(self.lower_expr(&if_expr.condition, scopes));
        let then_branch = self.lower_block(&if_expr.then_branch, scopes);
        let else_branch = if_expr.else_branch.as_ref().map(|branch| match branch {
            ast::ElseBranch::Block(b) => HirElse::Block(self.lower_block(b, scopes)),
            ast::ElseBranch::If(i) => HirElse::If(Box::new(self.lower_if(i, scopes))),
        });
        HirExpr::If {
            id: self.fresh_expr_id(),
            condition,
            then_branch,
            else_branch,
            span: if_expr.span,
        }
    }

    fn lower_match(&mut self, m: &ast::MatchExpr, scopes: &mut Scopes) -> HirExpr {
        let scrutinee = Box::new(self.lower_expr(&m.scrutinee, scopes));
        let arms = m
            .arms
            .iter()
            .map(|arm| {
                scopes.push();
                let mut bound: HashMap<Symbol, Span> = HashMap::new();
                let pattern = self.lower_pattern(&arm.pattern, scopes, &mut bound);
                let body = match &arm.body {
                    ast::MatchArmBody::Expr(e) => HirMatchArmBody::Expr(self.lower_expr(e, scopes)),
                    ast::MatchArmBody::Block(b) => {
                        HirMatchArmBody::Block(self.lower_block(b, scopes))
                    }
                };
                scopes.pop();
                HirMatchArm {
                    pattern,
                    body,
                    span: arm.span,
                }
            })
            .collect();
        HirExpr::Match {
            id: self.fresh_expr_id(),
            scrutinee,
            arms,
            span: m.span,
        }
    }

    /// Lowers one pattern, minting a fresh [`PatternId`] and detecting a
    /// name bound more than once within the *same* pattern tree (`bound`
    /// is reset per-arm by the caller, and threaded through recursive
    /// calls into `Variant` sub-patterns so `Found(user, user)` is
    /// caught across positions, not just siblings at the same level).
    fn lower_pattern(
        &mut self,
        pattern: &ast::Pattern,
        scopes: &mut Scopes,
        bound: &mut HashMap<Symbol, Span>,
    ) -> HirPattern {
        self.lower_pattern_at_depth(pattern, scopes, bound, 0)
    }

    fn lower_pattern_at_depth(
        &mut self,
        pattern: &ast::Pattern,
        scopes: &mut Scopes,
        bound: &mut HashMap<Symbol, Span>,
        depth: usize,
    ) -> HirPattern {
        if depth > crate::limits::MAX_PATTERN_DEPTH {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::PATTERN_TOO_DEEP,
                    self.source,
                    pattern.span(),
                    "pattern is nested too deeply to resolve",
                )
                .with_primary_label("pattern is too complex"),
            );
            return HirPattern::Wildcard {
                id: self.fresh_pattern_id(),
                span: pattern.span(),
            };
        }
        match pattern {
            ast::Pattern::Wildcard { span } => HirPattern::Wildcard {
                id: self.fresh_pattern_id(),
                span: *span,
            },
            ast::Pattern::Ident(ident) => {
                if let Some(&first_span) = bound.get(&ident.symbol) {
                    let text = self.interner.resolve(ident.symbol);
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::DUPLICATE_PATTERN_BINDING,
                            self.source,
                            ident.span,
                            format!("`{text}` is bound more than once in this pattern"),
                        )
                        .with_primary_label("duplicate binding")
                        .with_label(first_span, "first bound here"),
                    );
                } else {
                    bound.insert(ident.symbol, ident.span);
                }
                let local = self.fresh_local();
                scopes.define(ident.symbol, local);
                HirPattern::Bind {
                    id: self.fresh_pattern_id(),
                    local,
                    name: ident.symbol,
                    span: ident.span,
                }
            }
            ast::Pattern::Variant { name, args, span } => {
                let args = args
                    .iter()
                    .map(|a| self.lower_pattern_at_depth(a, scopes, bound, depth + 1))
                    .collect();
                HirPattern::Variant {
                    id: self.fresh_pattern_id(),
                    name: name.symbol,
                    args,
                    span: *span,
                }
            }
            ast::Pattern::Int { value, span } => HirPattern::Int {
                id: self.fresh_pattern_id(),
                value: *value,
                span: *span,
            },
            ast::Pattern::Str { value, span } => HirPattern::Str {
                id: self.fresh_pattern_id(),
                value: value.clone(),
                span: *span,
            },
            ast::Pattern::Char { value, span } => HirPattern::Char {
                id: self.fresh_pattern_id(),
                value: *value,
                span: *span,
            },
            ast::Pattern::Bool { value, span } => HirPattern::Bool {
                id: self.fresh_pattern_id(),
                value: *value,
                span: *span,
            },
        }
    }
}

fn other_item(id: ItemId, name: ast::Ident, span: Span, kind: OtherItemKind) -> OtherItem {
    OtherItem {
        id,
        name: name.symbol,
        span,
        kind,
    }
}

/// A placeholder `ItemId` for an `extend` whose protocol head named no
/// declared protocol (`hir::lower::lower_extend`'s own diagnostic
/// already covers this). Never a real item's id (every real id starts
/// counting from zero and this module's own item count never
/// approaches `u32::MAX`), and never looked up in a merged protocol
/// table by any later stage -- every consumer of `HirExtend::protocol`
/// is expected to skip an extend it can't resolve, the same way a
/// dangling reference elsewhere in this compiler degrades rather than
/// panics.
fn unresolved_protocol_id() -> ItemId {
    ItemId(u32::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::tokenize;
    use crate::parser::Parser;
    use crate::source::SourceMap;

    fn lower(text: &str) -> (HirModule, Vec<Diagnostic>) {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, lex_diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(
            lex_diags.is_empty(),
            "unexpected lexer diagnostics: {lex_diags:?}"
        );
        let (module, parse_diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(
            parse_diags.is_empty(),
            "unexpected parser diagnostics: {parse_diags:?}"
        );
        lower_module(&module, id, &interner)
    }

    #[test]
    fn a_local_record_named_i64_does_not_shadow_the_primitive_in_a_return_type() {
        let (hir, diags) = lower("record i64 { flag: bool } func f() -> i64 { return 1 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        assert!(
            matches!(
                hir.functions[0].return_type,
                Some(HirType::Unresolved { .. })
            ),
            "expected the primitive-shaped Unresolved form, got {:?}",
            hir.functions[0].return_type
        );
    }

    #[test]
    fn a_local_variant_named_bool_does_not_shadow_the_primitive_in_a_param_type() {
        let (hir, diags) = lower("variant bool { A } func f(x: bool) -> i64 { return 1 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        assert!(
            matches!(hir.functions[0].params[0].ty, HirType::Unresolved { .. }),
            "expected the primitive-shaped Unresolved form, got {:?}",
            hir.functions[0].params[0].ty
        );
    }

    #[test]
    fn an_imported_record_named_i64_does_not_shadow_the_primitive_in_a_return_type() {
        let (hir, diags) =
            lower_with_imports("func f() -> i64 { return 1 }", |interner, other_source| {
                let i64_symbol = interner.intern("i64");
                vec![ImportedItem {
                    local_name: i64_symbol,
                    kind: ImportedItemKind::Record {
                        item: ItemId(0),
                        declared_name: interner.intern("Something"),
                        fields: Vec::new(),
                    },
                    import_span: Span::dummy(),
                    local_name_span: Span::dummy(),
                    declared_source: other_source,
                    declared_span: Span::dummy(),
                }]
            });
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        assert!(
            matches!(
                hir.functions[0].return_type,
                Some(HirType::Unresolved { .. })
            ),
            "expected the primitive-shaped Unresolved form, got {:?}",
            hir.functions[0].return_type
        );
    }

    #[test]
    fn a_genuine_aggregate_return_type_still_resolves_to_its_exact_item_id() {
        let (hir, diags) =
            lower("record Point { x: i64 } func f() -> Point { return Point { x: 1 } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let record_id = hir.records[0].id;
        match &hir.functions[0].return_type {
            Some(HirType::Aggregate { item, kind, .. }) => {
                assert_eq!(*item, record_id);
                assert_eq!(*kind, AggregateKind::Record);
            }
            other => panic!("expected an Aggregate return type, got {other:?}"),
        }
    }

    #[test]
    fn resolves_parameter_reference() {
        let (hir, diags) = lower("func f(x: i64) -> i64 { return x }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let tail = hir.functions[0].body.tail.as_deref().unwrap();
        let HirExpr::Return { value, .. } = tail else {
            panic!("expected return")
        };
        assert!(matches!(value.as_deref(), Some(HirExpr::Local { .. })));
    }

    #[test]
    fn resolves_call_to_another_function_declared_later() {
        // Forward reference: `main` calls `helper`, defined afterward.
        let (hir, diags) =
            lower("func main() -> i64 { return helper() } func helper() -> i64 { return 1 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let main_body = &hir.functions[0].body;
        let HirExpr::Return { value, .. } = main_body.tail.as_deref().unwrap() else {
            panic!("expected return")
        };
        let HirExpr::Call { callee, .. } = value.as_deref().unwrap() else {
            panic!("expected call")
        };
        assert!(matches!(**callee, HirExpr::Function { .. }));
    }

    #[test]
    fn unresolved_name_is_a_diagnostic() {
        let (_, diags) = lower("func f() -> i64 { return unknown }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "R0002");
    }

    #[test]
    fn duplicate_function_definition_is_a_diagnostic() {
        let (_, diags) = lower("func f() -> i64 { return 1 } func f() -> i64 { return 2 }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "R0001");
    }

    #[test]
    fn duplicate_across_item_kinds_is_still_a_diagnostic() {
        let (_, diags) = lower("func Point() -> i64 { return 0 } record Point { x: i64 }");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "R0001");
    }

    #[test]
    fn duplicate_parameter_name_is_a_diagnostic_not_silent_shadowing() {
        let (hir, diags) = lower("func f(x: i64, x: i64) -> i64 { return x }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0003");
        // Both parameters still get their own distinct local -- the
        // diagnostic doesn't stop lowering from otherwise producing a
        // normal function.
        assert_eq!(hir.functions[0].params.len(), 2);
        assert_ne!(
            hir.functions[0].params[0].local,
            hir.functions[0].params[1].local
        );
    }

    #[test]
    fn nested_block_shadows_outer_binding() {
        let (hir, diags) =
            lower("func f() -> i64 { value x = 1; value y = { value x = 2; x }; return x + y }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        // Two distinct locals named `x` should have been minted (outer
        // and shadowed inner); the final `return x + y` still resolves
        // to the outer one.
        assert_eq!(hir.functions[0].params.len(), 0);
    }

    #[test]
    fn same_scope_rebinding_shadows_without_a_diagnostic() {
        let (_, diags) = lower("func f() -> i64 { value x = 1; value x = 2; return x }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn match_arm_pattern_binds_a_local_for_its_body() {
        let (_, diags) = lower("func f(x: i64) -> i64 { return match x { n => n, _ => 0 } }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_pattern_binding_does_not_leak_into_another_arm() {
        // `v`, bound in the first arm's pattern, must not be visible in
        // the second arm's body -- each arm gets its own scope.
        let (_, diags) = lower(
            "variant Shape { Circle(i64), Empty } \
             func f(s: Shape) -> i64 { return match s { Circle(v) => v, Empty => v } }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0002");
    }

    #[test]
    fn record_and_variant_items_are_lowered_with_their_full_structure() {
        let (hir, diags) = lower("record Point { x: i64, y: i64 } variant Shape { Circle }");
        assert!(diags.is_empty());
        assert_eq!(hir.records.len(), 1);
        assert_eq!(hir.records[0].fields.len(), 2);
        assert_eq!(hir.variants.len(), 1);
        assert_eq!(hir.variants[0].cases.len(), 1);
        assert!(hir.other_items.is_empty());
    }

    #[test]
    fn uses_and_raises_clauses_are_preserved_not_discarded() {
        let (hir, diags) = lower(
            "func loadUser(id: i64) -> i64 uses Database.Read raises UserNotFound { return id }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        assert_eq!(hir.functions[0].uses.len(), 1);
        assert_eq!(hir.functions[0].uses[0].segments.len(), 2);
        assert_eq!(hir.functions[0].raises.len(), 1);
    }

    #[test]
    fn duplicate_record_field_declaration_is_a_diagnostic() {
        let (hir, diags) = lower("record Point { x: i64, x: i64 }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0004");
        assert_eq!(hir.records[0].fields.len(), 1);
    }

    #[test]
    fn duplicate_variant_case_declaration_is_a_diagnostic() {
        let (hir, diags) = lower("variant Shape { Circle, Circle }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0005");
        assert_eq!(hir.variants[0].cases.len(), 1);
    }

    #[test]
    fn record_literal_resolves_fields_to_declaration_indices() {
        let (hir, diags) = lower(
            "record Point { x: i64, y: i64 } \
             func f() -> i64 { value p = Point { y: 2, x: 1 }; return 0 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let HirStmt::Binding(binding) = &hir.functions[0].body.statements[0] else {
            panic!("expected binding")
        };
        let HirExpr::RecordLiteral { fields, .. } = &binding.value else {
            panic!("expected record literal")
        };
        // Written in source order (y, then x), each resolved to its
        // declaration index (y=1, x=0).
        assert_eq!(fields[0].field_index, 1);
        assert_eq!(fields[1].field_index, 0);
    }

    #[test]
    fn unknown_record_type_is_a_diagnostic() {
        let (_, diags) = lower("func f() { value p = Banana { x: 1 }; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0007");
    }

    #[test]
    fn unknown_field_in_construction_is_a_diagnostic() {
        let (_, diags) =
            lower("record Point { x: i64 } func f() { value p = Point { x: 1, z: 2 }; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0008");
    }

    #[test]
    fn missing_field_in_construction_is_a_diagnostic() {
        let (_, diags) =
            lower("record Point { x: i64, y: i64 } func f() { value p = Point { x: 1 }; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0009");
    }

    #[test]
    fn missing_fields_are_reported_in_declaration_order() {
        // Three missing fields, named so alphabetical/insertion order
        // would disagree with declaration order if either leaked
        // through: declaration order is z, a, m.
        let record = "record Point { z: i64, a: i64, m: i64, x: i64 } ";
        let ctor = "func f() { value p = Point { x: 1 }; }";
        let (_, diags) = lower(&format!("{record}{ctor}"));
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0009");
        assert!(
            diags[0].message.contains("z, a, m"),
            "expected declaration-order field list, got: {}",
            diags[0].message
        );
    }

    #[test]
    fn missing_field_diagnostic_text_is_identical_across_repeated_runs() {
        let text = "record Point { z: i64, a: i64, m: i64, x: i64 } \
                    func f() { value p = Point { x: 1 }; }";
        let first = lower(text).1[0].message.clone();
        for _ in 0..10 {
            let (_, diags) = lower(text);
            assert_eq!(diags[0].message, first);
        }
    }

    #[test]
    fn missing_field_order_is_declaration_order_not_construction_site_order() {
        // The construction site never mentions any of the missing
        // fields, so its own (empty) order can't influence anything;
        // this instead confirms that field declaration order -- not
        // HashMap iteration order, which this test's field names are
        // chosen to disagree with alphabetically -- is what's reported.
        let record = "record Point { z: i64, a: i64, m: i64 } ";
        let ctor = "func f() { value p = Point {}; }";
        let (_, diags) = lower(&format!("{record}{ctor}"));
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert!(
            diags[0].message.contains("z, a, m"),
            "expected declaration-order field list, got: {}",
            diags[0].message
        );
    }

    #[test]
    fn duplicate_field_initializer_is_a_diagnostic() {
        let (_, diags) =
            lower("record Point { x: i64 } func f() { value p = Point { x: 1, x: 2 }; }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0010");
    }

    #[test]
    fn qualified_variant_constructor_resolves_to_a_case_ref() {
        let (hir, diags) = lower(
            "variant Shape { Circle(i64), Empty } \
             func f() -> i64 { value s = Shape.Circle(1); return 0 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let HirStmt::Binding(binding) = &hir.functions[0].body.statements[0] else {
            panic!("expected binding")
        };
        let HirExpr::Call { callee, args, .. } = &binding.value else {
            panic!("expected call")
        };
        assert!(matches!(**callee, HirExpr::CaseRef { case: 0, .. }));
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn qualified_unit_case_resolves_without_a_call() {
        let (hir, diags) = lower(
            "variant Shape { Circle(i64), Empty } \
             func f() -> i64 { value s = Shape.Empty; return 0 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let HirStmt::Binding(binding) = &hir.functions[0].body.statements[0] else {
            panic!("expected binding")
        };
        assert!(matches!(binding.value, HirExpr::CaseRef { case: 1, .. }));
    }

    #[test]
    fn unqualified_unambiguous_constructor_resolves() {
        let (hir, diags) = lower(
            "variant Shape { Circle(i64), Empty } \
             func f() -> i64 { value s = Circle(1); return 0 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let HirStmt::Binding(binding) = &hir.functions[0].body.statements[0] else {
            panic!("expected binding")
        };
        let HirExpr::Call { callee, .. } = &binding.value else {
            panic!("expected call")
        };
        assert!(matches!(**callee, HirExpr::CaseRef { .. }));
    }

    #[test]
    fn ambiguous_unqualified_constructor_is_a_diagnostic() {
        let (_, diags) = lower(
            "variant A { Found(i64) } variant B { Found(i64) } \
             func f() -> i64 { value s = Found(1); return 0 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0006");
    }

    #[test]
    fn qualified_unknown_case_is_a_diagnostic() {
        let (_, diags) = lower(
            "variant Shape { Circle(i64) } \
             func f() -> i64 { value s = Shape.Square; return 0 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0012");
    }

    #[test]
    fn qualified_case_from_a_different_variant_is_a_diagnostic() {
        let (_, diags) = lower(
            "variant A { Found(i64) } variant B { Missing } \
             func f() -> i64 { value s = B.Found; return 0 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0013");
    }

    #[test]
    fn duplicate_pattern_binding_is_a_diagnostic() {
        let (_, diags) = lower(
            "variant Pair { Both(i64, i64) } \
             func f(p: Pair) -> i64 { return match p { Both(a, a) => a } }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0014");
    }

    #[test]
    fn deeply_nested_hand_built_pattern_fails_lowering_with_r0015_not_a_stack_overflow() {
        // The parser's own crate::limits::MAX_PATTERN_DEPTH bound keeps
        // any real parser output shallow enough that lower_pattern's
        // own bound can never fire through the normal pipeline -- so
        // this exercises it the only way possible: a hand-built
        // ast::Pattern that bypasses the parser entirely, the same
        // defense-in-depth posture nir::lower's tests already use for
        // hand-built HIR.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let case_name = interner.intern("Wrap");
        let mut lowering = Lowering {
            source,
            interner: &interner,
            diagnostics: Vec::new(),
            functions_by_name: HashMap::new(),
            type_names: HashMap::new(),
            record_fields: HashMap::new(),
            variant_cases: HashMap::new(),
            case_lookup: HashMap::new(),
            imported_record_field_public: HashMap::new(),
            next_item_id: 0,
            next_local_id: 0,
            next_expr_id: 0,
            next_pattern_id: 0,
            type_param_scope: HashMap::new(),
            next_type_param_id: 0,
        };
        let depth = crate::limits::MAX_PATTERN_DEPTH + 50;
        let mut pattern = ast::Pattern::Wildcard {
            span: Span::dummy(),
        };
        for _ in 0..depth {
            pattern = ast::Pattern::Variant {
                name: ast::Ident {
                    symbol: case_name,
                    span: Span::dummy(),
                },
                args: vec![pattern],
                span: Span::dummy(),
            };
        }
        let mut scopes = Scopes::new();
        let mut bound = HashMap::new();
        // The diagnostic is what signals the real problem -- the
        // deepest call's Wildcard fallback only ever becomes one arg
        // deep inside the still-Variant-shaped result the outer,
        // within-limit levels legitimately produce, exactly like
        // typeck's check_pattern_at_depth.
        let _ = lowering.lower_pattern(&pattern, &mut scopes, &mut bound);
        assert_eq!(
            lowering.diagnostics.len(),
            1,
            "unexpected diagnostics: {:?}",
            lowering.diagnostics
        );
        assert_eq!(lowering.diagnostics[0].code, "R0015");
    }

    #[test]
    fn record_name_still_lowers_cleanly_when_used_as_a_parameter_type() {
        // Regression: pulling record/variant metadata out of
        // `other_items` must not break the item's own name/id still
        // being usable in a type position downstream (typeck rebuilds
        // its own type namespace from `hir.records`/`hir.variants`).
        let (hir, diags) = lower("record Point { x: i64 } func f(p: Point) -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        assert_eq!(hir.records.len(), 1);
        assert_eq!(hir.functions[0].params.len(), 1);
    }

    /// `build_imports` receives the *same* interner the source text is
    /// parsed with, so a symbol it interns for an import's local name
    /// (e.g. `"add"`) is guaranteed to be the same `Symbol` the parsed
    /// source text's own references resolve to -- two separate
    /// `Interner`s would each hand out unrelated ids starting from the
    /// same small integers, so precomputing a symbol from a *different*
    /// interner and passing it in would silently collide with whatever
    /// symbol the real source text happened to get instead.
    fn lower_with_imports(
        text: &str,
        build_imports: impl FnOnce(&mut Interner, SourceId) -> Vec<ImportedItem>,
    ) -> (HirModule, Vec<Diagnostic>) {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let other_source = map.add_file("other.npt", "");
        let mut interner = Interner::new();
        let (tokens, lex_diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(
            lex_diags.is_empty(),
            "unexpected lexer diagnostics: {lex_diags:?}"
        );
        let (module, parse_diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(
            parse_diags.is_empty(),
            "unexpected parser diagnostics: {parse_diags:?}"
        );
        let imports = build_imports(&mut interner, other_source);
        let (hir, _cursor, diags) =
            lower_module_with_imports(&module, id, &interner, IdCursor::default(), imports);
        (hir, diags)
    }

    #[test]
    fn an_imported_function_call_resolves_to_its_real_item_id() {
        let mut map = SourceMap::new();
        let other_source = map.add_file("math.npt", "");
        let mut interner = Interner::new();
        let add_name = interner.intern("add");
        let target = ItemId(42);
        let (hir, _cursor, diags) = {
            let mut m = map;
            let id = m.add_file("t.npt", "func f() -> i64 { return add() }");
            let (tokens, lex_diags) = tokenize(m.get(id).content(), id, &mut interner);
            assert!(lex_diags.is_empty());
            let (module, parse_diags) = Parser::new(tokens, id, &mut interner).parse_module();
            assert!(parse_diags.is_empty());
            lower_module_with_imports(
                &module,
                id,
                &interner,
                IdCursor::default(),
                vec![ImportedItem {
                    local_name: add_name,
                    kind: ImportedItemKind::Function(target),
                    import_span: Span::dummy(),
                    local_name_span: Span::dummy(),
                    declared_source: other_source,
                    declared_span: Span::dummy(),
                }],
            )
        };
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let tail = hir.functions[0].body.tail.as_deref().unwrap();
        let HirExpr::Return { value, .. } = tail else {
            panic!("expected return")
        };
        let HirExpr::Call { callee, .. } = value.as_deref().unwrap() else {
            panic!("expected a call")
        };
        assert!(matches!(**callee, HirExpr::Function { item, .. } if item == target));
    }

    #[test]
    fn two_imports_introducing_the_same_local_name_is_m0007() {
        let (_, diags) =
            lower_with_imports("func f() -> i64 { return 0 }", |interner, other_source| {
                let name = interner.intern("thing");
                vec![
                    ImportedItem {
                        local_name: name,
                        kind: ImportedItemKind::Function(ItemId(1)),
                        import_span: Span::new(0, 1),
                        local_name_span: Span::new(0, 1),
                        declared_source: other_source,
                        declared_span: Span::dummy(),
                    },
                    ImportedItem {
                        local_name: name,
                        kind: ImportedItemKind::Function(ItemId(2)),
                        import_span: Span::new(1, 2),
                        local_name_span: Span::new(1, 2),
                        declared_source: other_source,
                        declared_span: Span::dummy(),
                    },
                ]
            });
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0007");
    }

    #[test]
    fn a_local_declaration_conflicting_with_an_import_is_m0007() {
        let (_, diags) = lower_with_imports(
            "func add() -> i64 { return 0 }",
            |interner, other_source| {
                let name = interner.intern("add");
                vec![ImportedItem {
                    local_name: name,
                    kind: ImportedItemKind::Function(ItemId(1)),
                    import_span: Span::dummy(),
                    local_name_span: Span::dummy(),
                    declared_source: other_source,
                    declared_span: Span::dummy(),
                }]
            },
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0007");
    }

    #[test]
    fn public_function_exposing_a_private_local_record_is_m0012() {
        let (_, diags) = lower(
            "record Secret { x: i64 } \
             public func f(s: Secret) -> i64 { return 0 }",
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0012");
    }

    #[test]
    fn a_private_local_record_named_i64_does_not_leak_through_a_public_param_or_return() {
        // `record i64 { .. }` is a private *local* record -- without the
        // primitive-first rule, a public function's `i64` annotations
        // would look like they leak it, even though they mean the
        // primitive, not the record.
        let (_, diags) = lower(
            "record i64 { flag: bool } \
             public func expose(x: i64) -> i64 { return x }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_private_local_record_named_bool_does_not_leak_through_a_public_field() {
        let (_, diags) = lower(
            "record bool { flag: bool } \
             public record Holder { public active: bool }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn a_private_local_variant_named_i64_does_not_leak_through_a_public_case_payload() {
        let (_, diags) = lower(
            "variant i64 { A } \
             public variant Wrapper { Case(i64) }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn private_function_may_use_a_private_local_record_freely() {
        let (_, diags) = lower(
            "record Secret { x: i64 } \
             func f(s: Secret) -> i64 { return 0 }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    }

    #[test]
    fn constructing_a_private_imported_field_is_m0011() {
        let (_, diags) = lower_with_imports(
            "func f() -> i64 { value p = Point { x: 1, y: 2 }; return 0 }",
            |interner, other_source| {
                let record_name = interner.intern("Point");
                let field_x = interner.intern("x");
                let field_y = interner.intern("y");
                vec![ImportedItem {
                    local_name: record_name,
                    kind: ImportedItemKind::Record {
                        item: ItemId(1),
                        declared_name: record_name,
                        fields: vec![(field_x, 0, true), (field_y, 1, false)],
                    },
                    import_span: Span::dummy(),
                    local_name_span: Span::dummy(),
                    declared_source: other_source,
                    declared_span: Span::dummy(),
                }]
            },
        );
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "M0011");
    }

    // -- Generic parameter lowering (`rfcs/0008`) -----------------------

    #[test]
    fn same_spelled_type_parameters_in_different_declarations_get_distinct_ids() {
        // `first[T]` and `second[T]` are unrelated declarations that
        // just happen to spell their own parameter the same way --
        // `TypeParamId` identity must come from *which declaration*
        // introduced it, never from the spelling alone.
        let (hir, diags) = lower(
            "func first[T](x: T) -> T { return x } \
             func second[T](x: T) -> T { return x }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let ids: Vec<TypeParamId> = hir.functions.iter().map(|f| f.type_params[0].id).collect();
        assert_eq!(ids.len(), 2);
        assert_ne!(
            ids[0], ids[1],
            "each declaration's own T must get its own TypeParamId"
        );
    }

    #[test]
    fn duplicate_type_parameter_name_in_one_function_is_rejected() {
        let (_, diags) = lower("func f[T, T](x: T) -> T { return x }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0016");
    }

    #[test]
    fn duplicate_type_parameter_name_in_one_record_is_rejected() {
        let (_, diags) = lower("record Box[T, T] { payload: T }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0016");
    }

    #[test]
    fn duplicate_type_parameter_name_in_one_variant_is_rejected() {
        let (_, diags) = lower("variant Maybe[T, T] { Some(T), None }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0016");
    }

    #[test]
    fn a_primitive_name_as_a_type_parameter_is_rejected() {
        let (_, diags) = lower("func f[i64](x: i64) -> i64 { return x }");
        assert_eq!(diags.len(), 1, "unexpected diagnostics: {diags:?}");
        assert_eq!(diags[0].code, "R0017");
    }

    #[test]
    fn a_type_parameter_used_outside_its_own_declaration_does_not_leak_across_declarations() {
        // `T` from `first`'s own declaration has no meaning in `second`,
        // which declares no type parameter of its own at all -- `T`
        // there must resolve as an ordinary unresolved name (deferred to
        // typeck's own T0006), never silently reuse `first`'s parameter
        // as if `second` had declared it too.
        let (hir, diags) = lower(
            "func first[T](x: T) -> T { return x } \
             func second(x: T) -> T { return x }",
        );
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let second = &hir.functions[1];
        assert!(
            matches!(second.params[0].ty, HirType::Unresolved { .. }),
            "expected `T` in `second` to be unresolved, not reuse `first`'s parameter: {:?}",
            second.params[0].ty
        );
    }

    #[test]
    fn a_record_with_no_type_parameters_has_an_empty_type_params_list() {
        let (hir, diags) = lower("record Point { x: i64 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        assert!(hir.records[0].type_params.is_empty());
    }

    #[test]
    fn a_generic_record_lowers_its_own_type_parameters() {
        let (hir, diags) = lower("record Box[T] { payload: T }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        assert_eq!(hir.records[0].type_params.len(), 1);
    }

    #[test]
    fn an_applied_type_reference_resolves_to_an_aggregate_type_with_args() {
        let (hir, diags) =
            lower("record Box[T] { payload: T } func f(b: Box[i64]) -> i64 { return 0 }");
        assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
        let f = &hir.functions[0];
        match &f.params[0].ty {
            HirType::Aggregate { args, .. } => assert_eq!(args.len(), 1),
            other => panic!("expected an applied aggregate type, got {other:?}"),
        }
    }
}
