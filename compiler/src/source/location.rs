//! Line/column mapping derived from byte offsets.

/// A human-readable position within a source file. Both `line` and
/// `column` are 1-based, matching how editors and most compiler
/// diagnostics number them. `column` counts Unicode scalar values
/// (`char`s), not bytes, so multi-byte UTF-8 content still lines up
/// with what a human sees.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    pub line: u32,
    pub column: u32,
}

/// Computes the [`Location`] for a byte `offset` into `content`,
/// given `content`'s precomputed line-start table (byte offset of the
/// first byte of each line; `line_starts[0]` is always `0`).
///
/// `offset` is clamped into `content`'s bounds and snapped backward to
/// the nearest UTF-8 character boundary, so an out-of-range or
/// mid-character offset never panics — it degrades to the nearest
/// valid position instead.
pub(super) fn locate(content: &str, line_starts: &[u32], offset: u32) -> Location {
    let len = content.len() as u32;
    let mut offset = offset.min(len);
    while offset > 0 && !content.is_char_boundary(offset as usize) {
        offset -= 1;
    }

    let line_index = match line_starts.binary_search(&offset) {
        Ok(i) => i,
        Err(i) => i - 1,
    };
    let line_start = line_starts[line_index] as usize;
    let column = content[line_start..offset as usize].chars().count() as u32 + 1;

    Location {
        line: line_index as u32 + 1,
        column,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn line_starts_of(content: &str) -> Vec<u32> {
        let mut starts = vec![0];
        for (i, byte) in content.bytes().enumerate() {
            if byte == b'\n' && i + 1 < content.len() {
                starts.push((i + 1) as u32);
            }
        }
        starts
    }

    #[test]
    fn first_line_first_column() {
        let content = "abc\ndef";
        let starts = line_starts_of(content);
        assert_eq!(locate(content, &starts, 0), Location { line: 1, column: 1 });
    }

    #[test]
    fn offset_on_second_line() {
        let content = "abc\ndef";
        let starts = line_starts_of(content);
        // 'd' is the first byte of line 2.
        assert_eq!(locate(content, &starts, 4), Location { line: 2, column: 1 });
        // 'f' is the third character of line 2.
        assert_eq!(locate(content, &starts, 6), Location { line: 2, column: 3 });
    }

    #[test]
    fn multi_byte_utf8_counts_scalar_values_not_bytes() {
        let content = "café\nbar";
        let starts = line_starts_of(content);
        // "café" is 5 bytes ('é' is 2 bytes) but 4 characters, so the
        // newline (byte offset 5) must map to column 5, not 6.
        let newline_offset = content.find('\n').unwrap() as u32;
        assert_eq!(
            locate(content, &starts, newline_offset),
            Location { line: 1, column: 5 }
        );
    }

    #[test]
    fn out_of_bounds_offset_clamps_to_end() {
        let content = "abc";
        let starts = line_starts_of(content);
        let at_end = locate(content, &starts, content.len() as u32);
        let past_end = locate(content, &starts, 999);
        assert_eq!(at_end, past_end);
    }

    #[test]
    fn mid_character_offset_snaps_backward() {
        let content = "é"; // 2 UTF-8 bytes, 1 character.
        let starts = line_starts_of(content);
        // Offset 1 is the middle of 'é'; it must snap back to 0.
        assert_eq!(locate(content, &starts, 1), Location { line: 1, column: 1 });
    }
}
