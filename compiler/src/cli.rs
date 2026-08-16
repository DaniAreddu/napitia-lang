//! Command-line entry point. Kept free of compiler logic: it only parses
//! arguments and delegates to [`crate::driver`].

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use crate::diagnostics::{self, Diagnostic};
use crate::driver::{self, IrOutput, ProjectIrOutput, ProjectRunOutput, RunOutput};
use crate::interpreter::Value;
use crate::lexer::Token;
use crate::source::{SourceId, SourceMap};
use crate::symbol::Interner;

const MANIFEST_FILE_NAME: &str = "napitia.toml";

const USAGE: &str = "\
Usage: napitia <command> [path]

Commands:
    lex <file>      Tokenize a .npt file and print its tokens
    parse <file>    Parse a .npt file and print its AST
    check [path]    Type-check a file or project and report every diagnostic
    ir [path]       Print the typed Napitia IR (NIR) for a file or project
    run [path]      Compile and execute a file's or project's `main` function

For `check`, `ir`, and `run`: `path` may be a `.npt` file (single-file mode),
a directory containing a `napitia.toml` manifest, or a manifest path
directly. It defaults to the current directory when omitted.

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
            match command.as_str() {
                "lex" | "parse" => {
                    let Some(path) = args.next() else {
                        eprintln!("error: missing <file> argument for `{command}`\n");
                        eprint!("{USAGE}");
                        return ExitCode::from(USAGE_ERROR);
                    };
                    dispatch_single_file(&command, &path)
                }
                "check" | "ir" | "run" => {
                    let path = args.next().unwrap_or_else(|| ".".to_string());
                    dispatch_check_ir_run(&command, &path)
                }
                _ => {
                    eprintln!("error: unknown command `{command}`\n");
                    eprint!("{USAGE}");
                    ExitCode::from(USAGE_ERROR)
                }
            }
        }
    }
}

fn dispatch_single_file(command: &str, path: &str) -> ExitCode {
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

/// Classifies `path` per the CLI's documented rules and dispatches
/// `check`/`ir`/`run` to either legacy single-file compilation or
/// project compilation. A `.npt` path is always single-file, regardless
/// of whether a manifest happens to sit alongside it -- explicit beats
/// implicit.
fn dispatch_check_ir_run(command: &str, path: &str) -> ExitCode {
    let candidate = Path::new(path);

    if candidate.extension().and_then(|ext| ext.to_str()) == Some("npt") {
        return dispatch_single_file(command, path);
    }

    let manifest_path: PathBuf = if candidate.is_dir() {
        candidate.join(MANIFEST_FILE_NAME)
    } else {
        candidate.to_path_buf()
    };

    dispatch_project(command, &manifest_path)
}

fn dispatch_project(command: &str, manifest_path: &Path) -> ExitCode {
    let mut map = SourceMap::new();
    let mut interner = Interner::new();

    match command {
        "check" => {
            let diagnostics = driver::check_project(manifest_path, &mut map, &mut interner);
            if diagnostics.is_empty() {
                println!("no errors");
            }
            print_diagnostics(&diagnostics, &map);
            exit_for(&diagnostics)
        }
        "ir" => match driver::ir_project(manifest_path, &mut map, &mut interner) {
            ProjectIrOutput::Diagnostics(diagnostics) => {
                print_diagnostics(&diagnostics, &map);
                exit_for(&diagnostics)
            }
            ProjectIrOutput::Ready { nir } => {
                print!("{}", crate::nir::print_module(&nir, &interner));
                ExitCode::SUCCESS
            }
        },
        "run" => match driver::run_project(manifest_path, &mut map, &mut interner) {
            ProjectRunOutput::Diagnostics(diagnostics) => {
                print_diagnostics(&diagnostics, &map);
                exit_for(&diagnostics)
            }
            ProjectRunOutput::Result(Ok(value)) => {
                println!("{}", format_value(&value));
                ExitCode::SUCCESS
            }
            ProjectRunOutput::Result(Err(err)) => {
                eprintln!("error: runtime error: {err:?}");
                ExitCode::from(1)
            }
        },
        _ => unreachable!("validated by dispatch_check_ir_run's caller"),
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
        Value::Record { fields, .. } => {
            let rendered: Vec<String> = fields.iter().map(format_value).collect();
            format!("{{{}}}", rendered.join(", "))
        }
        Value::Variant { case, payload, .. } => {
            if payload.is_empty() {
                format!("<case {case}>")
            } else {
                let rendered: Vec<String> = payload.iter().map(format_value).collect();
                format!("<case {case}>({})", rendered.join(", "))
            }
        }
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
