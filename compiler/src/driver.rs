//! Sequences the compiler stages (lex -> parse -> resolve -> typeck -> nir)
//! behind the operations the CLI exposes. Each stage accumulates
//! diagnostics from every stage before it, so `check`, `ir`, and `run`
//! all report lexer/parser/resolver/type errors together rather than
//! stopping at the first one.

use std::collections::HashMap;
use std::path::Path;

use crate::diagnostics::Diagnostic;
use crate::hir::{self, HirModule, ItemRegistry, LocalId};
use crate::interpreter::{Interpreter, InterpreterError, Value};
use crate::lexer::{self, Token};
use crate::nir::{self, Module as NirModule};
use crate::parser::Parser;
use crate::project::{self, CompiledProject};
use crate::source::{SourceId, SourceMap, Span};
use crate::symbol::Interner;
use crate::syntax::ast;
use crate::typeck;
use crate::types::{Evidence, Ty};

pub struct LexOutput {
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn lex(map: &SourceMap, source: SourceId, interner: &mut Interner) -> LexOutput {
    let (tokens, diagnostics) = lexer::tokenize(map.get(source).content(), source, interner);
    LexOutput {
        tokens,
        diagnostics,
    }
}

pub struct ParseOutput {
    pub module: ast::Module,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse(map: &SourceMap, source: SourceId, interner: &mut Interner) -> ParseOutput {
    let lexed = lex(map, source, interner);
    let mut diagnostics = lexed.diagnostics;
    let (module, parse_diags) = Parser::new(lexed.tokens, source, interner).parse_module();
    diagnostics.extend(parse_diags);
    ParseOutput {
        module,
        diagnostics,
    }
}

pub struct CheckOutput {
    pub hir: HirModule,
    pub local_types: HashMap<LocalId, Ty>,
    pub expr_types: HashMap<hir::ExprId, Ty>,
    pub pattern_case: HashMap<hir::PatternId, (hir::ItemId, usize)>,
    /// See [`typeck::TypeckResult::call_type_args`].
    pub call_type_args: HashMap<hir::ExprId, Vec<Ty>>,
    /// See [`typeck::TypeckResult::call_evidence`].
    pub call_evidence: HashMap<hir::ExprId, Vec<Evidence>>,
    /// See [`typeck::TypeckResult::protocol_call_evidence`].
    pub protocol_call_evidence: HashMap<hir::ExprId, Evidence>,
    /// `resourceck`'s own authoritative cleanup plan (`rfcs/0011`) --
    /// `nir::lower` consumes this directly as the single source of
    /// truth for resource cleanup, rather than re-inferring it.
    pub cleanup_edges:
        std::collections::BTreeMap<hir::ExprId, Vec<crate::resourceck::CleanupAction>>,
    /// See [`crate::resourceck::ResourceCheckResult::consume_sites`].
    pub consume_sites: std::collections::BTreeMap<hir::ExprId, crate::resourceck::ConsumeInfo>,
    /// See [`crate::resourceck::ResourceCheckResult::defer_plans`].
    pub defer_plans: std::collections::BTreeMap<hir::ExprId, crate::resourceck::CheckedDeferPlan>,
    /// See [`crate::resourceck::ResourceCheckResult::observations`].
    pub observations:
        std::collections::BTreeMap<hir::ObservationId, crate::resourceck::CheckedObservation>,
    /// See [`crate::resourceck::ResourceCheckResult::observation_exits`].
    pub observation_exits:
        std::collections::BTreeMap<hir::ExprId, Vec<crate::resourceck::ObservationExit>>,
    /// The span of every `import` this source declared, in source order.
    ///
    /// Single-file compilation resolves no imports at all --
    /// `hir::lower_module` drops them, and nothing downstream records
    /// that one was ever written. The native backend still has to refuse
    /// a source that declares one (`rfcs/0014`) rather than compiling a
    /// program whose author expected another module to be part of it,
    /// and this is the only place that evidence survives.
    pub import_spans: Vec<Span>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn check(map: &SourceMap, source: SourceId, interner: &mut Interner) -> CheckOutput {
    let parsed = parse(map, source, interner);
    let mut diagnostics = parsed.diagnostics;
    let (hir, resolve_diags) = hir::lower_module(&parsed.module, source, interner);
    diagnostics.extend(resolve_diags);
    let typeck_result = typeck::check_module(&hir, source, interner, typeck::EntryMain::ByName);
    diagnostics.extend(typeck_result.diagnostics);
    let resourceck_result = crate::resourceck::check_module(
        &hir,
        &typeck_result.local_types,
        &typeck_result.expr_types,
        interner,
        &crate::resourceck::AffineContext {
            aggregate_field_types: &typeck_result.aggregate_field_types,
            declared_resources: &typeck_result.declared_resources,
            item_type_params: &typeck_result.item_type_params,
            field_projections: &typeck_result.field_projections,
        },
    );
    diagnostics.extend(resourceck_result.diagnostics);
    let import_spans = parsed
        .module
        .items
        .iter()
        .filter_map(|item| match item {
            ast::Item::Import(import) => Some(import.span),
            _ => None,
        })
        .collect();
    CheckOutput {
        hir,
        local_types: typeck_result.local_types,
        expr_types: typeck_result.expr_types,
        pattern_case: typeck_result.pattern_case,
        call_type_args: typeck_result.call_type_args,
        call_evidence: typeck_result.call_evidence,
        protocol_call_evidence: typeck_result.protocol_call_evidence,
        cleanup_edges: resourceck_result.cleanup_edges,
        consume_sites: resourceck_result.consume_sites,
        defer_plans: resourceck_result.defer_plans,
        observations: resourceck_result.observations,
        observation_exits: resourceck_result.observation_exits,
        import_spans,
        diagnostics,
    }
}

pub enum IrOutput {
    /// The program type-checked cleanly, every function lowered to NIR
    /// (atomically -- `nir::lower_module`), and the result passed the
    /// NIR verifier: this is never a partial or internally inconsistent
    /// module. `registry` is built with an empty module-path map --
    /// single-file compilation has no project-level module path at all,
    /// so every item's canonical qualified name is just its own
    /// declared name (`rfcs/0007`).
    Ready {
        nir: NirModule,
        registry: ItemRegistry,
    },
    /// Lexing, parsing, resolution, or type-checking failed (NIR
    /// lowering never ran), lowering itself failed, or lowering
    /// succeeded but produced NIR the verifier rejected. Either way,
    /// there is no NIR safe to run.
    Diagnostics(Vec<Diagnostic>),
}

pub fn ir(map: &SourceMap, source: SourceId, interner: &mut Interner) -> IrOutput {
    ir_with_imports(map, source, interner).0
}

/// Exactly [`ir`], plus the one piece of evidence neither NIR nor HIR
/// carries: where the source declared each `import`. Only
/// [`build_native`] needs it, and only to refuse a native build that
/// spans more than one module; nothing about `ir`'s own behavior
/// changes.
fn ir_with_imports(
    map: &SourceMap,
    source: SourceId,
    interner: &mut Interner,
) -> (IrOutput, Vec<Span>) {
    let mut checked = check(map, source, interner);
    let imports = std::mem::take(&mut checked.import_spans);
    if !checked.diagnostics.is_empty() {
        return (IrOutput::Diagnostics(checked.diagnostics), imports);
    }
    let nir_module = match nir::lower_module(
        &checked.hir,
        &checked.local_types,
        &checked.expr_types,
        &checked.pattern_case,
        &checked.call_type_args,
        &checked.call_evidence,
        &checked.protocol_call_evidence,
        &checked.cleanup_edges,
        &checked.consume_sites,
        &checked.defer_plans,
        &checked.observations,
        &checked.observation_exits,
        interner,
        source,
    ) {
        Ok(nir_module) => nir_module,
        Err(diagnostics) => return (IrOutput::Diagnostics(diagnostics), imports),
    };
    let registry = hir::registry::build(&checked.hir, &HashMap::new());
    // A module lowering itself considers well-formed is still checked
    // independently before interpretation ever sees it: the verifier
    // does not trust lowering's own bookkeeping, so a bug in `lower.rs`
    // surfaces as a diagnostic here rather than a panic or silent
    // misbehavior in the interpreter.
    let verify_diagnostics = nir::verify_module(&nir_module, source, interner, &registry);
    if !verify_diagnostics.is_empty() {
        return (IrOutput::Diagnostics(verify_diagnostics), imports);
    }
    (
        IrOutput::Ready {
            nir: nir_module,
            registry,
        },
        imports,
    )
}

pub enum NativeOutput {
    /// The executable was written to the requested path, and every
    /// stage before that succeeded.
    Built,
    /// Nothing was written. Some stage -- any stage, from lexing to the
    /// system linker -- refused, and every later one was skipped.
    Diagnostics(Vec<Diagnostic>),
}

/// Compiles `source` to a native executable at `output`
/// (`rfcs/0014`).
///
/// This is [`ir`]'s pipeline with two more stages on the end: native
/// capability validation, then Cranelift and the system linker. It
/// shares those earlier stages rather than repeating them, so `check`,
/// `ir`, `run` and `build` all agree by construction about what a
/// program means.
///
/// There is no interpreter fallback. A program the native backend
/// cannot compile is refused with a diagnostic naming why; running it
/// is still `napitia run`'s job, and that path is unchanged.
pub fn build_native(
    map: &SourceMap,
    source: SourceId,
    interner: &mut Interner,
    output: &Path,
) -> NativeOutput {
    let (compiled, imports) = ir_with_imports(map, source, interner);
    let (nir, registry) = match compiled {
        IrOutput::Diagnostics(diagnostics) => return NativeOutput::Diagnostics(diagnostics),
        IrOutput::Ready { nir, registry } => (nir, registry),
    };
    let diagnostics =
        crate::native::build_executable(&nir, source, interner, &registry, &imports, output);
    if diagnostics.is_empty() {
        NativeOutput::Built
    } else {
        NativeOutput::Diagnostics(diagnostics)
    }
}

pub enum RunOutput {
    /// Nothing ran: compilation failed at some stage before or during
    /// NIR lowering.
    Diagnostics(Vec<Diagnostic>),
    Result(Result<Value, InterpreterError>),
}

pub fn run(map: &SourceMap, source: SourceId, interner: &mut Interner, entry: &str) -> RunOutput {
    match ir(map, source, interner) {
        IrOutput::Diagnostics(diags) => RunOutput::Diagnostics(diags),
        IrOutput::Ready { nir, .. } => {
            let result = Interpreter::new(&nir).run(entry, interner);
            RunOutput::Result(result)
        }
    }
}

pub fn check_project(
    manifest_path: &Path,
    map: &mut SourceMap,
    interner: &mut Interner,
) -> Vec<Diagnostic> {
    match project::compile_project(manifest_path, map, interner) {
        Ok(_) => Vec::new(),
        Err(diagnostics) => diagnostics,
    }
}

pub enum ProjectIrOutput {
    Ready {
        nir: NirModule,
        registry: ItemRegistry,
    },
    Diagnostics(Vec<Diagnostic>),
}

pub fn ir_project(
    manifest_path: &Path,
    map: &mut SourceMap,
    interner: &mut Interner,
) -> ProjectIrOutput {
    match project::compile_project(manifest_path, map, interner) {
        Ok(CompiledProject { nir, registry, .. }) => ProjectIrOutput::Ready { nir, registry },
        Err(diagnostics) => ProjectIrOutput::Diagnostics(diagnostics),
    }
}

pub enum ProjectRunOutput {
    Diagnostics(Vec<Diagnostic>),
    Result(Result<Value, InterpreterError>),
}

pub fn run_project(
    manifest_path: &Path,
    map: &mut SourceMap,
    interner: &mut Interner,
) -> ProjectRunOutput {
    match project::compile_project(manifest_path, map, interner) {
        Ok(CompiledProject {
            nir, entry_item, ..
        }) => ProjectRunOutput::Result(Interpreter::new(&nir).run_item(entry_item)),
        Err(diagnostics) => ProjectRunOutput::Diagnostics(diagnostics),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn main_calling_a_function_with_an_unsupported_construct_fails_before_interpretation() {
        // `main` never itself uses an unsupported construct, but the
        // function it calls does. This must fail at compile time (as a
        // diagnostic) rather than lowering `main` alone, running it, and
        // only then discovering `helper` doesn't exist -- which is
        // exactly the failure mode "no partial NIR" rules out: a `Call`
        // in a successfully-lowered function must never reference a
        // function that was silently left out.
        let mut map = SourceMap::new();
        let source = map.add_file(
            "t.npt",
            "func helper(x: i64) -> i64 { value r = 0..x; return x } \
             func main() -> i64 { return helper(1) }",
        );
        let mut interner = Interner::new();

        match run(&map, source, &mut interner, "main") {
            RunOutput::Diagnostics(diagnostics) => {
                assert!(
                    diagnostics.iter().any(|d| d.code == "T0007"),
                    "expected a T0007 diagnostic, got {diagnostics:?}"
                );
            }
            RunOutput::Result(result) => {
                panic!("expected compilation to fail, but it ran and produced {result:?}")
            }
        }
    }
}
