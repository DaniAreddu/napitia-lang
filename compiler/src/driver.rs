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
use crate::source::{SourceId, SourceMap};
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
    );
    diagnostics.extend(resourceck_result.diagnostics);
    CheckOutput {
        hir,
        local_types: typeck_result.local_types,
        expr_types: typeck_result.expr_types,
        pattern_case: typeck_result.pattern_case,
        call_type_args: typeck_result.call_type_args,
        call_evidence: typeck_result.call_evidence,
        protocol_call_evidence: typeck_result.protocol_call_evidence,
        cleanup_edges: resourceck_result.cleanup_edges,
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
    let checked = check(map, source, interner);
    if !checked.diagnostics.is_empty() {
        return IrOutput::Diagnostics(checked.diagnostics);
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
        interner,
        source,
    ) {
        Ok(nir_module) => nir_module,
        Err(diagnostics) => return IrOutput::Diagnostics(diagnostics),
    };
    let registry = hir::registry::build(&checked.hir, &HashMap::new());
    // A module lowering itself considers well-formed is still checked
    // independently before interpretation ever sees it: the verifier
    // does not trust lowering's own bookkeeping, so a bug in `lower.rs`
    // surfaces as a diagnostic here rather than a panic or silent
    // misbehavior in the interpreter.
    let verify_diagnostics = nir::verify_module(&nir_module, source, interner, &registry);
    if !verify_diagnostics.is_empty() {
        return IrOutput::Diagnostics(verify_diagnostics);
    }
    IrOutput::Ready {
        nir: nir_module,
        registry,
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
