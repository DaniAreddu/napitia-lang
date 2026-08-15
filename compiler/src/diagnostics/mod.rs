//! Structured compiler diagnostics.

pub mod diagnostic;
pub mod renderer;

pub use diagnostic::{Diagnostic, Label, Severity};
pub use renderer::render;
