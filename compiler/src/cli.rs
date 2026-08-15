//! Command-line entry point. Kept free of compiler logic: it only parses
//! arguments and delegates to [`crate::driver`].

use std::process::ExitCode;

use crate::diagnostics::{self, Diagnostic};
use crate::driver::{self, IrOutput, RunOutput};
use crate::interpreter::Value;
use crate::lexer::Token;
use crate::source::{SourceId, SourceMap};
use crate::symbol::Interner;

const USAGE: &str = "\
Usage: napitia <command> <file>

Commands:
    lex <file>      Tokenize a .npt file and print its tokens
    parse <file>    Parse a .npt file and print its AST
    check <file>    Type-check a .npt file and report every diagnostic
    ir <file>       Print the typed Napitia IR (NIR) for a file
    run <file>      Compile and execute a file's `main` function

Options:
    -h, --help      Print this help message
    --version       Print version information
";

/// Exit code for a usage error (bad arguments, unreadable file) as
/// opposed to a compilation error reported through diagnostics (`1`).
const USAGE_ERROR: u8 = 2;

pub fn run(args: Vec<String>) -> ExitCode {
    let mut args = args.into_iter().skip(1);

    match args.next().as_deref() {
        None | Some("-h") | Some("--help") => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Some("--version") => {
            println!("napitia {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Some(command) => {
            let command = command.to_string();
            let Some(path) = args.next() else {
                eprintln!("error: missing <file> argument for `{command}`\n");
                eprint!("{USAGE}");
                return ExitCode::from(USAGE_ERROR);
            };
            dispatch(&command, &path)
        }
    }
}

fn dispatch(command: &str, path: &str) -> ExitCode {
    if !matches!(command, "lex" | "parse" | "check" | "ir" | "run") {
        eprintln!("error: unknown command `{command}`\n");
        eprint!("{USAGE}");
        return ExitCode::from(USAGE_ERROR);
    }

    let content = match std::fs::read_to_string(path) {
        Ok(content) => content,
        Err(err) => {
            eprintln!("error: could not read `{path}`: {err}");
            return ExitCode::from(USAGE_ERROR);
        }
    };

    let mut map = SourceMap::new();
    let source = map.add_file(path.to_string(), content);
    let mut interner = Interner::new();

    match command {
        "lex" => lex_command(&map, source, &mut interner),
        "parse" => parse_command(&map, source, &mut interner),
        "check" => check_command(&map, source, &mut interner),
        "ir" => ir_command(&map, source, &mut interner),
        "run" => run_command(&map, source, &mut interner),
        _ => unreachable!("validated above"),
    }
}

fn lex_command(map: &SourceMap, source: SourceId, interner: &mut Interner) -> ExitCode {
    let output = driver::lex(map, source, interner);
    for token in &output.tokens {
        println!("{}", format_token(token, interner));
    }
    print_diagnostics(&output.diagnostics, map);
    exit_for(&output.diagnostics)
}

fn parse_command(map: &SourceMap, source: SourceId, interner: &mut Interner) -> ExitCode {
    let output = driver::parse(map, source, interner);
    if output.diagnostics.is_empty() {
        println!("{:#?}", output.module);
    }
    print_diagnostics(&output.diagnostics, map);
    exit_for(&output.diagnostics)
}

fn check_command(map: &SourceMap, source: SourceId, interner: &mut Interner) -> ExitCode {
    let output = driver::check(map, source, interner);
    if output.diagnostics.is_empty() {
        println!("no errors");
    }
    print_diagnostics(&output.diagnostics, map);
    exit_for(&output.diagnostics)
}

fn ir_command(map: &SourceMap, source: SourceId, interner: &mut Interner) -> ExitCode {
    match driver::ir(map, source, interner) {
        IrOutput::Diagnostics(diagnostics) => {
            print_diagnostics(&diagnostics, map);
            exit_for(&diagnostics)
        }
        IrOutput::Ready { nir } => {
            print!("{}", crate::nir::print_module(&nir, interner));
            ExitCode::SUCCESS
        }
    }
}

fn run_command(map: &SourceMap, source: SourceId, interner: &mut Interner) -> ExitCode {
    match driver::run(map, source, interner, "main") {
        RunOutput::Diagnostics(diagnostics) => {
            print_diagnostics(&diagnostics, map);
            exit_for(&diagnostics)
        }
        RunOutput::Result(Ok(value)) => {
            println!("{}", format_value(&value));
            ExitCode::SUCCESS
        }
        RunOutput::Result(Err(err)) => {
            eprintln!("error: runtime error: {err:?}");
            ExitCode::from(1)
        }
    }
}

fn format_token(token: &Token, interner: &Interner) -> String {
    let description = match &token.kind {
        crate::lexer::TokenKind::Ident(symbol) => {
            format!("Ident({:?})", interner.resolve(*symbol))
        }
        other => format!("{other:?}"),
    };
    format!("{}..{} {description}", token.span.start, token.span.end)
}

fn format_value(value: &Value) -> String {
    match value {
        Value::Int(v) => v.to_string(),
        Value::Float(v) => v.to_string(),
        Value::Bool(v) => v.to_string(),
        Value::Char(v) => v.to_string(),
        Value::Str(v) => v.clone(),
        Value::Unit => "()".to_string(),
    }
}

fn print_diagnostics(diagnostics: &[Diagnostic], map: &SourceMap) {
    for diagnostic in diagnostics {
        eprint!("{}", diagnostics::render(diagnostic, map));
    }
}

fn exit_for(diagnostics: &[Diagnostic]) -> ExitCode {
    if diagnostics.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}
