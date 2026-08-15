use std::process::ExitCode;

fn main() -> ExitCode {
    compiler::cli::run(std::env::args().collect())
}
