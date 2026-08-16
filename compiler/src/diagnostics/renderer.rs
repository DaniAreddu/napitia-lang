//! Renders diagnostics into human-readable, `rustc`-style text.

use crate::diagnostics::diagnostic::Diagnostic;
use crate::source::{SourceMap, Span};

/// Renders `diagnostic` against `sources` into the multi-line,
/// human-readable form shown in `spec/0003`'s diagnostics examples.
///
/// Rendering is deterministic: the same `(Diagnostic, SourceMap)` pair
/// always produces the same string, which is what makes this usable in
/// golden-output tests. Spans that cross multiple lines are clipped to
/// the remainder of their first line for the caret underline — this is a
/// deliberate simplification, not a bug, until multi-line highlighting is
/// designed.
pub fn render(diagnostic: &Diagnostic, sources: &SourceMap) -> String {
    let file = sources.get(diagnostic.source);
    let primary_loc = file.location(diagnostic.primary_span.start);

    // The gutter is sized to the widest line number that will actually
    // be printed, across every label regardless of which file it names
    // -- a label in a different, shorter file must not misalign the
    // primary block's gutter, and vice versa.
    let gutter_width = std::iter::once(primary_loc.line)
        .chain(
            diagnostic
                .labels
                .iter()
                .map(|label| sources.get(label.source).location(label.span.start).line),
        )
        .map(digit_count)
        .max()
        .unwrap_or(1);

    let mut out = String::new();
    out.push_str(&format!(
        "{}[{}]: {}\n",
        diagnostic.severity.as_str(),
        diagnostic.code,
        diagnostic.message
    ));
    out.push_str(&format!(
        " --> {}:{}:{}\n",
        file.name(),
        primary_loc.line,
        primary_loc.column
    ));

    push_blank_gutter(&mut out, gutter_width);
    push_span_block(
        &mut out,
        sources,
        diagnostic.source,
        diagnostic.primary_span,
        diagnostic.primary_label.as_deref(),
        gutter_width,
    );

    // A label naming a different file than the one just rendered gets
    // its own `--> file:line:col` header first, exactly like switching
    // to a new primary location -- otherwise its line/column would be
    // silently misread against the wrong file's line table.
    let mut current_source = diagnostic.source;
    for label in &diagnostic.labels {
        if label.source != current_source {
            let label_file = sources.get(label.source);
            let label_loc = label_file.location(label.span.start);
            out.push_str(&format!(
                " --> {}:{}:{}\n",
                label_file.name(),
                label_loc.line,
                label_loc.column
            ));
            current_source = label.source;
        }
        push_blank_gutter(&mut out, gutter_width);
        push_span_block(
            &mut out,
            sources,
            label.source,
            label.span,
            Some(&label.message),
            gutter_width,
        );
    }

    push_blank_gutter(&mut out, gutter_width);

    if let Some(help) = &diagnostic.help {
        out.push_str(&format!("{} = help: {}\n", gutter(gutter_width), help));
    }
    if let Some(note) = &diagnostic.note {
        out.push_str(&format!("{} = note: {}\n", gutter(gutter_width), note));
    }

    out
}

fn gutter(width: usize) -> String {
    " ".repeat(width)
}

fn push_blank_gutter(out: &mut String, width: usize) {
    out.push_str(&gutter(width));
    out.push_str(" |\n");
}

fn digit_count(mut n: u32) -> usize {
    if n == 0 {
        return 1;
    }
    let mut count = 0;
    while n > 0 {
        count += 1;
        n /= 10;
    }
    count
}

/// Renders one source line plus, if `label` is present, a caret line
/// underlining `span`'s portion of that line.
fn push_span_block(
    out: &mut String,
    sources: &SourceMap,
    source: crate::source::SourceId,
    span: Span,
    label: Option<&str>,
    gutter_width: usize,
) {
    let file = sources.get(source);
    let loc = file.location(span.start);
    let line_text = file.line_text(loc.line).unwrap_or("");

    out.push_str(&format!(
        "{:>width$} | {}\n",
        loc.line,
        line_text,
        width = gutter_width
    ));

    let Some(label) = label else {
        return;
    };

    let line_span = file.line_span(loc.line).unwrap_or(Span::empty(span.start));
    let clipped_end = span.end.min(line_span.end);
    let carets = file
        .slice(Span::new(span.start, clipped_end.max(span.start)))
        .map(|s| s.chars().count())
        .unwrap_or(0)
        .max(1);
    let indent = loc.column.saturating_sub(1) as usize;

    out.push_str(&format!(
        "{} | {}{} {}\n",
        gutter(gutter_width),
        " ".repeat(indent),
        "^".repeat(carets),
        label
    ));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostics::diagnostic::Diagnostic;
    use crate::source::SourceMap;

    #[test]
    fn renders_header_and_location() {
        let mut map = SourceMap::new();
        let id = map.add_file("a.npt", "value x = 1");
        let diag = Diagnostic::error("N0001", id, Span::new(0, 5), "example message");
        let rendered = render(&diag, &map);
        assert!(rendered.starts_with("error[N0001]: example message\n"));
        assert!(rendered.contains(" --> a.npt:1:1\n"));
    }

    #[test]
    fn renders_caret_line_under_primary_span() {
        let mut map = SourceMap::new();
        let id = map.add_file("a.npt", "value x = 1");
        // "x" is at byte offset 6, one character wide.
        let diag = Diagnostic::error("N0002", id, Span::new(6, 7), "bad binding")
            .with_primary_label("this binding");
        let rendered = render(&diag, &map);
        let lines: Vec<&str> = rendered.lines().collect();
        assert_eq!(lines[3], "1 | value x = 1");
        assert_eq!(lines[4], "  |       ^ this binding");
    }

    #[test]
    fn renders_help_and_note() {
        let mut map = SourceMap::new();
        let id = map.add_file("a.npt", "value x = 1");
        let diag = Diagnostic::error("N0003", id, Span::new(0, 1), "oops")
            .with_help("try again")
            .with_note("for context");
        let rendered = render(&diag, &map);
        assert!(rendered.contains("= help: try again\n"));
        assert!(rendered.contains("= note: for context\n"));
    }

    #[test]
    fn renders_secondary_labels() {
        let mut map = SourceMap::new();
        let id = map.add_file("a.npt", "value x = 1\nvalue y = 2");
        let diag = Diagnostic::error("N0004", id, Span::new(0, 5), "conflict")
            .with_label(Span::new(12, 17), "also defined here");
        let rendered = render(&diag, &map);
        assert!(rendered.contains("1 | value x = 1"));
        assert!(rendered.contains("2 | value y = 2"));
        assert!(rendered.contains("also defined here"));
    }

    #[test]
    fn renders_a_secondary_label_from_a_different_source_file() {
        let mut map = SourceMap::new();
        let importer = map.add_file("importer.npt", "import math.secret;");
        let declaration = map.add_file("math.npt", "func secret() -> i64 { 0 }");
        let diag = Diagnostic::error("M0006", importer, Span::new(7, 18), "item is private")
            .with_label_in(declaration, Span::new(5, 11), "declared here");
        let rendered = render(&diag, &map);
        assert!(
            rendered.contains(" --> importer.npt:1:8\n"),
            "expected the primary header to name importer.npt: {rendered}"
        );
        assert!(
            rendered.contains(" --> math.npt:1:6\n"),
            "expected a second header naming math.npt for the cross-file label: {rendered}"
        );
        assert!(rendered.contains("declared here"));
        assert!(rendered.contains("func secret"));
    }

    #[test]
    fn multi_digit_line_numbers_align_gutter() {
        let mut map = SourceMap::new();
        let mut content = String::new();
        for i in 0..12 {
            content.push_str(&format!("value v{i} = {i}\n"));
        }
        let id = map.add_file("a.npt", content);
        // Line 11 (0-based line index 10) is a two-digit line number.
        let file = map.get(id);
        let span = file.line_span(11).unwrap();
        let diag = Diagnostic::error("N0005", id, span, "example");
        let rendered = render(&diag, &map);
        // The gutter for a two-digit line number is two characters wide.
        assert!(rendered.contains("11 | "));
    }

    #[test]
    fn rendering_is_deterministic() {
        let mut map = SourceMap::new();
        let id = map.add_file("a.npt", "value x = 1");
        let diag = Diagnostic::error("N0006", id, Span::new(0, 1), "same every time");
        assert_eq!(render(&diag, &map), render(&diag, &map));
    }
}
