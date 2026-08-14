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
        diagnostics,
    }
}

pub enum IrOutput {
    /// The program type-checked cleanly; `skipped` names any function
    /// that used a construct NIR lowering doesn't support yet (`match`,
    /// field access) and was left out of `nir`.
    Ready {
        nir: NirModule,
        skipped: Vec<String>,
    },
    /// Lexing, parsing, resolution, or type-checking failed; NIR
    /// lowering never ran.
    Diagnostics(Vec<Diagnostic>),
}

pub fn ir(map: &SourceMap, source: SourceId, interner: &mut Interner) -> IrOutput {
    let checked = check(map, source, interner);
    if !checked.diagnostics.is_empty() {
        return IrOutput::Diagnostics(checked.diagnostics);
    }
    let (nir_module, skipped) = nir::lower_module(&checked.hir, &checked.local_types, interner);
    IrOutput::Ready {
        nir: nir_module,
        skipped,
    }
}

pub enum RunOutput {
    Diagnostics(Vec<Diagnostic>),
    /// The entry function itself couldn't be lowered to NIR.
    EntryNotSupported(Vec<String>),
    Result(Result<Value, InterpreterError>),
}

pub fn run(map: &SourceMap, source: SourceId, interner: &mut Interner, entry: &str) -> RunOutput {
    match ir(map, source, interner) {
        IrOutput::Diagnostics(diags) => RunOutput::Diagnostics(diags),
        IrOutput::Ready { nir, skipped } => {
            let entry_prefix = format!("{entry}:");
            if skipped.iter().any(|s| s.starts_with(&entry_prefix)) {
                return RunOutput::EntryNotSupported(skipped);
            }
            let result = Interpreter::new(&nir).run(entry, interner);
            RunOutput::Result(result)
        }
    }
}
