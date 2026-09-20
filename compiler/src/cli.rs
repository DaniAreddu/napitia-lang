//! Command-line entry point. Kept free of compiler logic: it only parses
//! arguments and delegates to [`crate::driver`].

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use crate::diagnostics::{self, Diagnostic};
use crate::driver::{self, IrOutput, NativeOutput, ProjectIrOutput, ProjectRunOutput, RunOutput};
use crate::interpreter::{InterpreterError, Value};
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
    build <file> --output <exe>
                    Compile a .npt file to a native executable

For `check`, `ir`, and `run`: `path` may be a `.npt` file (single-file mode),
a directory containing a `napitia.toml` manifest, or a manifest path
directly. It defaults to the current directory when omitted.

`build` takes a `.npt` file only, and always targets
x86_64-unknown-linux-gnu. It compiles a small scalar subset of the
language ahead of time and refuses everything outside it with a
diagnostic; `run` remains the complete semantic execution path. See
`rfcs/0014-native-aot-preview.md`.

Options:
    -h, --help      Print this help message
    --version       Print version information
";

/// Exit code for a usage error (bad arguments, unreadable file) as
/// opposed to a compilation error reported through diagnostics (`1`).
const USAGE_ERROR: u8 = 2;

/// Exit code a panic leaves behind, matching what the process would
/// have exited with had the panic unwound out of `main` itself. The
/// panic hook has already printed the message by the time this is
/// used; re-panicking here would only print a second, less useful one.
const PANIC_EXIT: u8 = 101;

/// The stack the compiler and interpreter actually run on.
///
/// Every stage recurses on the native stack, and the interpreter
/// recurses once per Napitia call frame, so the binding constraint on
/// what this compiler can accept is whatever stack the platform
/// happens to hand the main thread -- 1 MiB on Windows, which a debug
/// build exhausts after roughly 25 interpreted frames. That is not a
/// limit worth having, and it fails in the worst possible way: the
/// process aborts, with no diagnostic, no exit code anything can act
/// on and nothing on stderr.
///
/// Sizing it here makes the limit this compiler's own choice instead,
/// and the one that actually applies is
/// `crate::limits::MAX_CALL_DEPTH`, which reports an ordinary runtime
/// error. This is provisioned to outlast that budget with room to
/// spare: 512 frames of a debug build measure well under a quarter of
/// it. It is a *reservation*, not an allocation -- pages are committed
/// as they are touched, so an ordinary compile pays for none of it.
const WORKER_STACK_BYTES: usize = 128 * 1024 * 1024;

/// Runs the CLI on a thread whose stack this compiler sizes itself
/// (`WORKER_STACK_BYTES`), falling back to the caller's own thread if
/// one cannot be spawned -- a smaller stack is still better than
/// refusing to run at all.
pub fn run(args: Vec<String>) -> ExitCode {
    let fallback = args.clone();
    match std::thread::Builder::new()
        .name("napitia".to_string())
        .stack_size(WORKER_STACK_BYTES)
        .spawn(move || dispatch(args))
    {
        Ok(worker) => worker.join().unwrap_or(ExitCode::from(PANIC_EXIT)),
        Err(_) => dispatch(fallback),
    }
}

fn dispatch(args: Vec<String>) -> ExitCode {
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
                    if let Some(extra) = args.next() {
                        return unexpected_argument_error(&extra);
                    }
                    dispatch_single_file(&command, &path)
                }
                "check" | "ir" | "run" => {
                    let path = args.next().unwrap_or_else(|| ".".to_string());
                    if let Some(extra) = args.next() {
                        return unexpected_argument_error(&extra);
                    }
                    dispatch_check_ir_run(&command, &path)
                }
                "build" => {
                    let Some(path) = args.next() else {
                        eprintln!("error: missing <file> argument for `build`\n");
                        eprint!("{USAGE}");
                        return ExitCode::from(USAGE_ERROR);
                    };
                    // `--output` is required rather than defaulted: the
                    // one thing a native build does that no other
                    // command does is write a file the user will run,
                    // and guessing where to put it is not this
                    // compiler's decision to make.
                    match args.next().as_deref() {
                        Some("--output") => {}
                        Some(other) => {
                            eprintln!("error: expected `--output <executable>`, found `{other}`\n");
                            eprint!("{USAGE}");
                            return ExitCode::from(USAGE_ERROR);
                        }
                        None => {
                            eprintln!("error: missing `--output <executable>` for `build`\n");
                            eprint!("{USAGE}");
                            return ExitCode::from(USAGE_ERROR);
                        }
                    }
                    let Some(output) = args.next() else {
                        eprintln!("error: `--output` needs a path\n");
                        eprint!("{USAGE}");
                        return ExitCode::from(USAGE_ERROR);
                    };
                    if let Some(extra) = args.next() {
                        return unexpected_argument_error(&extra);
                    }
                    build_command(&path, Path::new(&output))
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

/// An argument beyond what a command accepts must be reported, not
/// silently dropped -- a typo'd extra path/flag would otherwise compile
/// or run something other than what the user actually asked for,
/// without any indication anything was ignored.
fn unexpected_argument_error(extra: &str) -> ExitCode {
    eprintln!("error: unexpected extra argument `{extra}`\n");
    eprint!("{USAGE}");
    ExitCode::from(USAGE_ERROR)
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
            ProjectIrOutput::Ready { nir, registry } => {
                print!("{}", crate::nir::print_module(&nir, &interner, &registry));
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
            ProjectRunOutput::Result(Err(err)) => runtime_failure(&err),
        },
        _ => unreachable!("validated by dispatch_check_ir_run's caller"),
    }
}

/// `napitia build <file.npt> --output <executable>` (`rfcs/0014`).
///
/// Single-file only, and explicitly so: a native build spans exactly
/// one module, and a project path here would have to be refused later
/// anyway, with a worse message.
fn build_command(path: &str, output: &Path) -> ExitCode {
    if Path::new(path).extension().and_then(|ext| ext.to_str()) != Some("npt") {
        eprintln!("error: `build` takes a `.npt` file, not a project path\n");
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

    match driver::build_native(&map, source, &mut interner, output) {
        NativeOutput::Built => ExitCode::SUCCESS,
        NativeOutput::Diagnostics(diagnostics) => {
            print_diagnostics(&diagnostics, &map);
            exit_for(&diagnostics)
        }
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
        IrOutput::Ready { nir, registry } => {
            print!("{}", crate::nir::print_module(&nir, interner, &registry));
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
        RunOutput::Result(Err(err)) => runtime_failure(&err),
    }
}

/// Reports a Napitia runtime failure and decides the process's status.
///
/// One line on standard error, built from nothing but the failure
/// itself: its stable code and its own rendering (`rfcs/0015`). A
/// successful run writes nothing here at all, which is what makes this
/// line the discriminator between "the program failed" and "the program
/// returned a number" -- under `run`, a returned value is printed on
/// standard output and is never a process status.
fn runtime_failure(error: &InterpreterError) -> ExitCode {
    eprintln!("error[{}]: {error}", error.code());
    ExitCode::from(1)
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
        // A resource's own fields live in the interpreter's resource
        // table, not inline in the `Value` (`rfcs/0011`, Blocker 8),
        // and `format_value` has no handle to that table here -- so,
        // like a variant's own case number, this only names the shape,
        // never fabricates field data it cannot see.
        Value::Resource(_) => "<resource>".to_string(),
        // Never actually observable from a top-level `run` result for
        // any program that passed `nir::verify` (`rfcs/0012`) -- a
        // tombstone only ever occupies a field slot inside an aggregate
        // that already moved or dropped it, never a value returned
        // whole. Printed rather than panicking anyway, matching this
        // module's own no-panic-on-unexpected-input rule.
        Value::Moved => "<moved>".to_string(),
        Value::Dropped => "<dropped>".to_string(),
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
