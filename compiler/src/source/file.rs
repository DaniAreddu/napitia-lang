//! Source file identifiers and immutable storage.

use super::location::{self, Location};
use super::span::Span;

/// Identifies a source file within a [`SourceMap`] for the lifetime of
/// one compilation session. Stable and cheap to copy; carried around
/// instead of a file path so spans stay small.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SourceId(u32);

/// One immutable, UTF-8 source file plus its precomputed line-start
/// table, used to answer line/column queries without rescanning the
/// file on every diagnostic.
#[derive(Debug)]
pub struct SourceFile {
    id: SourceId,
    name: String,
    content: String,
    /// Byte offset of the first byte of each line. Always has at
    /// least one entry (`0`), even for an empty file.
    line_starts: Vec<u32>,
}

impl SourceFile {
    fn new(id: SourceId, name: String, content: String) -> Self {
        let line_starts = compute_line_starts(&content);
        SourceFile {
            id,
            name,
            content,
            line_starts,
        }
    }

    pub fn id(&self) -> SourceId {
        self.id
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn content(&self) -> &str {
        &self.content
    }

    pub fn len(&self) -> u32 {
        self.content.len() as u32
    }

    pub fn is_empty(&self) -> bool {
        self.content.is_empty()
    }

    /// Number of lines in the file. An empty file has one (empty)
    /// line, matching how editors count lines.
    pub fn line_count(&self) -> u32 {
        self.line_starts.len() as u32
    }

    /// The human-readable [`Location`] of a byte offset. Never panics:
    /// an out-of-range offset clamps to the end of the file.
    pub fn location(&self, offset: u32) -> Location {
        location::locate(&self.content, &self.line_starts, offset)
    }

    /// The source text covered by `span`, or `None` if the span falls
    /// outside the file's bounds or does not land on UTF-8 character
    /// boundaries.
    pub fn slice(&self, span: Span) -> Option<&str> {
        if span.end > self.len() {
            return None;
        }
        self.content.get(span.as_range())
    }

    /// The full text of a single 1-based line number, without its
    /// trailing line terminator, or `None` if `line` is out of range.
    pub fn line_text(&self, line: u32) -> Option<&str> {
        let index = line.checked_sub(1)? as usize;
        let start = *self.line_starts.get(index)?;
        let end = self
            .line_starts
            .get(index + 1)
            .copied()
            .unwrap_or(self.len());
        let raw = self.content.get(start as usize..end as usize)?;
        Some(raw.trim_end_matches(['\n', '\r']))
    }

    /// The byte span covering a single 1-based line number, including
    /// its line terminator (if any), or `None` if out of range.
    pub fn line_span(&self, line: u32) -> Option<Span> {
        let index = line.checked_sub(1)? as usize;
        let start = *self.line_starts.get(index)?;
        let end = self
            .line_starts
            .get(index + 1)
            .copied()
            .unwrap_or(self.len());
        Some(Span::new(start, end))
    }
}

fn compute_line_starts(content: &str) -> Vec<u32> {
    let mut starts = vec![0u32];
    let bytes = content.as_bytes();
    for (i, &byte) in bytes.iter().enumerate() {
        if byte == b'\n' {
            let next = (i + 1) as u32;
            if next < content.len() as u32 {
                starts.push(next);
            }
        }
    }
    starts
}

/// Owns every [`SourceFile`] loaded during a compilation session and
/// hands out stable [`SourceId`]s for them.
#[derive(Debug, Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    pub fn new() -> Self {
        SourceMap { files: Vec::new() }
    }

    pub fn add_file(&mut self, name: impl Into<String>, content: impl Into<String>) -> SourceId {
        let id = SourceId(self.files.len() as u32);
        self.files
            .push(SourceFile::new(id, name.into(), content.into()));
        id
    }

    pub fn get(&self, id: SourceId) -> &SourceFile {
        &self.files[id.0 as usize]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_file_assigns_increasing_ids() {
        let mut map = SourceMap::new();
        let a = map.add_file("a.npt", "fn a() {}");
        let b = map.add_file("b.npt", "fn b() {}");
        assert_ne!(a, b);
        assert_eq!(map.get(a).name(), "a.npt");
        assert_eq!(map.get(b).name(), "b.npt");
    }

    #[test]
    fn empty_file_has_one_line_and_zero_length() {
        let mut map = SourceMap::new();
        let id = map.add_file("empty.npt", "");
        let file = map.get(id);
        assert_eq!(file.len(), 0);
        assert!(file.is_empty());
        assert_eq!(file.line_count(), 1);
        assert_eq!(file.line_text(1), Some(""));
    }

    #[test]
    fn multi_line_lf_file_splits_correctly() {
        let mut map = SourceMap::new();
        let id = map.add_file("multi.npt", "let a = 1\nlet b = 2\nlet c = 3");
        let file = map.get(id);
        assert_eq!(file.line_count(), 3);
        assert_eq!(file.line_text(1), Some("let a = 1"));
        assert_eq!(file.line_text(2), Some("let b = 2"));
        assert_eq!(file.line_text(3), Some("let c = 3"));
        assert_eq!(file.line_text(4), None);
    }

    #[test]
    fn crlf_line_endings_do_not_affect_line_count_or_text() {
        let mut map = SourceMap::new();
        let id = map.add_file("crlf.npt", "let a = 1\r\nlet b = 2\r\n");
        let file = map.get(id);
        assert_eq!(file.line_count(), 2);
        assert_eq!(file.line_text(1), Some("let a = 1"));
        assert_eq!(file.line_text(2), Some("let b = 2"));
    }

    #[test]
    fn slice_returns_requested_source_text() {
        let mut map = SourceMap::new();
        let id = map.add_file("s.npt", "let answer = 42");
        let file = map.get(id);
        let span = Span::new(4, 10);
        assert_eq!(file.slice(span), Some("answer"));
    }

    #[test]
    fn slice_out_of_bounds_is_none_not_a_panic() {
        let mut map = SourceMap::new();
        let id = map.add_file("s.npt", "short");
        let file = map.get(id);
        assert_eq!(file.slice(Span::new(0, 999)), None);
    }

    #[test]
    fn location_reports_expected_line_and_column() {
        let mut map = SourceMap::new();
        let id = map.add_file("s.npt", "fn main() {\n    let x = 1\n}");
        let file = map.get(id);
        let offset = file.content().find("let").unwrap() as u32;
        let loc = file.location(offset);
        assert_eq!(loc.line, 2);
        assert_eq!(loc.column, 5);
    }

    #[test]
    fn multi_byte_utf8_file_maps_locations_by_scalar_value() {
        let mut map = SourceMap::new();
        let id = map.add_file("s.npt", "let name = \"café\"\nlet x = 1");
        let file = map.get(id);
        let second_line_offset = file.content().find("let x").unwrap() as u32;
        let loc = file.location(second_line_offset);
        assert_eq!(loc.line, 2);
        assert_eq!(loc.column, 1);
    }
}
