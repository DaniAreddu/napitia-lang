//! Sequences the compiler stages (lex -> parse -> resolve -> typeck -> nir)
//! behind the operations the CLI exposes. Each stage accumulates
//! diagnostics from every stage before it, so `check`, `ir`, and `run`
//! all report lexer/parser/resolver/type errors together rather than
//! stopping at the first one.

use std::collections::HashMap;

use crate::diagnostics::Diagnostic;
use crate::hir::{self, HirModule, LocalId};
use crate::interpreter::{Interpreter, InterpreterError, Value};
use crate::lexer::{self, Token};
use crate::nir::{self, Module as NirModule};
use crate::parser::Parser;
use crate::source::{SourceId, SourceMap};
use crate::symbol::Interner;
use crate::syntax::ast;
use crate::typeck;
use crate::types::Ty;

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
    pub diagnostics: Vec<Diagnostic>,
}

pub fn check(map: &SourceMap, source: SourceId, interner: &mut Interner) -> CheckOutput {
    let parsed = parse(map, source, interner);
    let mut diagnostics = parsed.diagnostics;
    let (hir, resolve_diags) = hir::lower_module(&parsed.module, source, interner);
    diagnostics.extend(resolve_diags);
    let typeck_result = typeck::check_module(&hir, source, interner);
    diagnostics.extend(typeck_result.diagnostics);
    CheckOutput {
        hir,
        local_types: typeck_result.local_types,
        expr_types: typeck_result.expr_types,
        diagnostics,
    }
}

pub enum IrOutput {
    /// The program type-checked cleanly and every function lowered to
    /// NIR -- lowering is atomic (`nir::lower_module`), so this is never
    /// a partial module.
    Ready { nir: NirModule },
    /// Lexing, parsing, resolution, or type-checking failed (NIR
    /// lowering never ran), or lowering itself failed. Either way,
    /// there is no NIR to run.
    Diagnostics(Vec<Diagnostic>),
}

pub fn ir(map: &SourceMap, source: SourceId, interner: &mut Interner) -> IrOutput {
    let checked = check(map, source, interner);
    if !checked.diagnostics.is_empty() {
        return IrOutput::Diagnostics(checked.diagnostics);
    }
    match nir::lower_module(
        &checked.hir,
        &checked.local_types,
        &checked.expr_types,
        interner,
        source,
    ) {
        Ok(nir_module) => IrOutput::Ready { nir: nir_module },
        Err(diagnostics) => IrOutput::Diagnostics(diagnostics),
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
        IrOutput::Ready { nir } => {
            let result = Interpreter::new(&nir).run(entry, interner);
            RunOutput::Result(result)
        }
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
            "func helper(x: i64) -> i64 { return match x { _ => 0 } } \
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
