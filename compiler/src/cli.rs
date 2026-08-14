//! Command-line entry point. Kept free of compiler logic: it only parses
//! arguments and delegates to [`crate::driver`].

use std::process::ExitCode;

pub fn run(_args: Vec<String>) -> ExitCode {
    ExitCode::SUCCESS
}
