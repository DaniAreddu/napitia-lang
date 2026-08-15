//! The [`Diagnostic`] data model.

use crate::source::{SourceId, Span};

/// How serious a diagnostic is. Ordered from most to least severe so a
/// batch of diagnostics can be sorted or filtered by severity.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Severity {
    Error,
    Warning,
    Note,
    Help,
}

impl Severity {
    pub fn as_str(&self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Note => "note",
            Severity::Help => "help",
        }
    }
}

/// A secondary span pointing at source code relevant to a diagnostic,
/// distinct from the diagnostic's primary span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

impl Label {
    pub fn new(span: Span, message: impl Into<String>) -> Self {
        Label {
            span,
            message: message.into(),
        }
    }
}

/// One structured compiler diagnostic: a severity, a stable error code,
/// a primary source location, a message, and optional secondary labels,
/// a help note, and a general note. Rendering this into human-readable
/// text is [`crate::diagnostics::renderer::render`]'s job — `Diagnostic`
/// itself carries no formatting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: &'static str,
    pub source: SourceId,
    pub primary_span: Span,
    pub message: String,
    /// Text rendered directly under the carets that underline
    /// `primary_span`, e.g. "string starts here". Distinct from
    /// `message`, which is the diagnostic's headline. `None` renders
    /// bare carets with no inline annotation.
    pub primary_label: Option<String>,
    pub labels: Vec<Label>,
    pub help: Option<String>,
    pub note: Option<String>,
}

impl Diagnostic {
    fn new(
        severity: Severity,
        code: &'static str,
        source: SourceId,
        primary_span: Span,
        message: impl Into<String>,
    ) -> Self {
        Diagnostic {
            severity,
            code,
            source,
            primary_span,
            message: message.into(),
            primary_label: None,
            labels: Vec::new(),
            help: None,
            note: None,
        }
    }

    pub fn error(
        code: &'static str,
        source: SourceId,
        span: Span,
        message: impl Into<String>,
    ) -> Self {
        Self::new(Severity::Error, code, source, span, message)
    }

    pub fn warning(
        code: &'static str,
        source: SourceId,
        span: Span,
        message: impl Into<String>,
    ) -> Self {
        Self::new(Severity::Warning, code, source, span, message)
    }

    pub fn with_primary_label(mut self, label: impl Into<String>) -> Self {
        self.primary_label = Some(label.into());
        self
    }

    pub fn with_label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.labels.push(Label::new(span, message));
        self
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.note = Some(note.into());
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::SourceMap;

    #[test]
    fn error_diagnostic_has_no_labels_or_help_by_default() {
        let mut map = SourceMap::new();
        let id = map.add_file("a.npt", "x");
        let diag = Diagnostic::error("N0001", id, Span::new(0, 1), "boom");
        assert_eq!(diag.severity, Severity::Error);
        assert_eq!(diag.code, "N0001");
        assert!(diag.primary_label.is_none());
        assert!(diag.labels.is_empty());
        assert!(diag.help.is_none());
        assert!(diag.note.is_none());
    }

    #[test]
    fn builder_methods_accumulate_labels_help_and_note() {
        let mut map = SourceMap::new();
        let id = map.add_file("a.npt", "xyz");
        let diag = Diagnostic::warning("N0002", id, Span::new(0, 1), "watch out")
            .with_label(Span::new(1, 2), "here too")
            .with_label(Span::new(2, 3), "and here")
            .with_help("try this instead")
            .with_note("for context");
        assert_eq!(diag.labels.len(), 2);
        assert_eq!(diag.help.as_deref(), Some("try this instead"));
        assert_eq!(diag.note.as_deref(), Some("for context"));
    }

    #[test]
    fn severity_ordering_places_error_first() {
        assert!(Severity::Error < Severity::Warning);
        assert!(Severity::Warning < Severity::Note);
        assert!(Severity::Note < Severity::Help);
    }

    #[test]
    fn severity_as_str_matches_conventional_names() {
        assert_eq!(Severity::Error.as_str(), "error");
        assert_eq!(Severity::Warning.as_str(), "warning");
        assert_eq!(Severity::Note.as_str(), "note");
        assert_eq!(Severity::Help.as_str(), "help");
    }
}
