//! Byte-offset source spans.

use std::ops::Range;

/// A half-open byte range `[start, end)` into some source file.
///
/// Spans are always byte offsets, never character or line/column
/// positions. Line/column positions are derived on demand through
/// [`crate::source::SourceMap`] only when a diagnostic needs to be
/// rendered for a human.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    /// Creates a span covering `[start, end)`.
    ///
    /// # Panics
    ///
    /// Panics if `start > end`. Every caller inside the compiler is
    /// expected to already know its span is well-formed; this is an
    /// internal invariant, not a condition user input can trigger.
    pub fn new(start: u32, end: u32) -> Self {
        assert!(start <= end, "span start {start} must not exceed end {end}");
        Span { start, end }
    }

    /// Creates a zero-length span at `offset`, e.g. for an
    /// end-of-file token or a diagnostic that points at an insertion
    /// point rather than a range.
    pub fn empty(offset: u32) -> Self {
        Span {
            start: offset,
            end: offset,
        }
    }

    /// A span with no meaningful source location, for synthesized
    /// nodes that do not correspond to any real input.
    pub fn dummy() -> Self {
        Span { start: 0, end: 0 }
    }

    pub fn len(&self) -> u32 {
        self.end - self.start
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// The smallest span that contains both `self` and `other`.
    pub fn join(&self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    pub fn contains_offset(&self, offset: u32) -> bool {
        self.start <= offset && offset < self.end
    }

    pub fn as_range(&self) -> Range<usize> {
        self.start as usize..self.end as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_builds_expected_range() {
        let span = Span::new(3, 7);
        assert_eq!(span.start, 3);
        assert_eq!(span.end, 7);
        assert_eq!(span.len(), 4);
    }

    #[test]
    #[should_panic]
    fn new_rejects_inverted_range() {
        Span::new(7, 3);
    }

    #[test]
    fn empty_span_has_zero_length() {
        let span = Span::empty(5);
        assert!(span.is_empty());
        assert_eq!(span.len(), 0);
        assert_eq!(span.start, 5);
        assert_eq!(span.end, 5);
    }

    #[test]
    fn join_covers_both_spans() {
        let a = Span::new(2, 5);
        let b = Span::new(10, 12);
        assert_eq!(a.join(b), Span::new(2, 12));
        // Joining is symmetric.
        assert_eq!(b.join(a), Span::new(2, 12));
    }

    #[test]
    fn join_with_overlapping_spans() {
        let a = Span::new(2, 8);
        let b = Span::new(5, 12);
        assert_eq!(a.join(b), Span::new(2, 12));
    }

    #[test]
    fn contains_offset_is_half_open() {
        let span = Span::new(3, 6);
        assert!(!span.contains_offset(2));
        assert!(span.contains_offset(3));
        assert!(span.contains_offset(5));
        assert!(!span.contains_offset(6));
    }

    #[test]
    fn as_range_matches_start_and_end() {
        let span = Span::new(1, 4);
        assert_eq!(span.as_range(), 1usize..4usize);
    }

    #[test]
    fn dummy_span_is_empty_at_origin() {
        let span = Span::dummy();
        assert!(span.is_empty());
        assert_eq!(span.start, 0);
    }
}
