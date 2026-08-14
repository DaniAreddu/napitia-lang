# Spec 0001: Lexical Grammar

- Status: Partially implemented (Alpha 0.1)

## Implemented features

### Source encoding

Napitia source files are UTF-8. The lexer operates on the raw byte stream
and decodes UTF-8 as it scans; invalid UTF-8 is rejected by the source
manager before lexing begins (see `spec` for the source manager, currently
folded into the compiler's `source` module documentation). All spans are
byte offsets into the original UTF-8 buffer, never character or codepoint
counts.

### Whitespace and newlines

Space (`U+0020`), tab (`U+0009`), `\r`, and `\n` are whitespace and are
not significant to the grammar except as token separators. Both `\n` and
`\r\n` line endings are accepted; the source manager normalizes line
tracking so line numbers are identical regardless of line-ending style. A
bare `\r` not followed by `\n` is treated as whitespace, not an error.

Napitia is not currently whitespace-sensitive (no significant indentation).
This may be revisited; see "Unresolved research questions".

### Comments

- Line comments start with `//` and run to the end of the line (exclusive
  of the terminating newline).
- Block comments are delimited by `/*` and `*/` and **nest**: a `/*` inside
  a block comment opens another nesting level, and the comment only ends
  once every opened level has been closed. An unterminated block comment
  (at any nesting depth) is a lexical error.

Comments are discarded by the lexer; they do not produce tokens.

### Identifiers

An identifier is an ASCII letter or underscore (`XID_Start`-compatible
subset: `[a-zA-Z_]`) followed by zero or more ASCII letters, digits, or
underscores (`[a-zA-Z0-9_]*`). An identifier that exactly matches a
reserved keyword (below) is lexed as that keyword's token, not as an
identifier. Extending identifiers to full Unicode `XID_Start`/`XID_Continue`
is planned; see "Unresolved research questions".

### Keywords

The following are reserved and cannot be used as identifiers:

```text
func value mutable const return
if else while for in loop break continue
true false
record variant match protocol extend with
import module public private
uses raises
as is
unsafe
async await
region
defer
```

`true` and `false` are boolean literal keywords, not general identifiers.

This vocabulary is provisional (`rfcs/0004-language-independence.md`): it
replaces an earlier keyword table that was a near-verbatim copy of Rust's
declaration keywords (`fn`, `let`/`var`, `struct`, `enum`, `trait`,
`impl`, `use`, `pub`). `func` declares a function, `value` an immutable
binding, `mutable` a mutable binding, `record` a product type, `variant`
a sum type, `protocol` a behavioral contract, `extend` a protocol
implementation (or inherent methods), `import` brings a path into scope,
and `uses`/`raises` declare a function's effects/capabilities and typed
errors respectively (see `spec/0002`, `spec/0005`). `with` introduces the
protocol name in an `extend Type with Protocol { ... }` declaration. The
reserved `move`
keyword from the earlier table was dropped: with ownership transfer
inferred by default (`spec/0004`), an explicit move marker is not
currently needed, and reserving one anyway would imply a feature that has
not been designed.

### Integer literals

```text
decimal_digit  = "0".."9"
binary_digit   = "0" | "1"
octal_digit    = "0".."7"
hex_digit      = "0".."9" | "a".."f" | "A".."F"

decimal_int = decimal_digit (decimal_digit | "_")*
binary_int  = "0b" binary_digit (binary_digit | "_")*
octal_int   = "0o" octal_digit (octal_digit | "_")*
hex_int     = "0x" hex_digit (hex_digit | "_")*
```

Underscore separators (`1_000_000`) are permitted between digits in any
base, including immediately after the base prefix is not permitted (a
digit must directly follow `0b`/`0o`/`0x`) and a trailing underscore
immediately before the end of the literal is rejected — an underscore must
always be followed by another digit. Integer literals carry no type suffix
in this milestone; their type is inferred (see `spec/0003-type-system.md`).

A malformed literal (e.g. `0x` with no following hex digit, `0b2`, a
digit invalid for the declared base) is a lexical error, not silently
truncated or reinterpreted as decimal.

### Floating-point literals

```text
float = decimal_int "." decimal_int [exponent]
      | decimal_int exponent

exponent = ("e" | "E") ["+" | "-"] decimal_int
```

A float literal requires at least one digit on both sides of a decimal
point when a point is present (`1.5`, not `1.` or `.5`). Exponent-only
floats without a fractional part (`1e10`) are permitted. Underscore
separators are permitted in the integer, fractional, and exponent digit
groups, following the same rule as integer literals.

### String literals

A string literal is delimited by `"` and may contain any character except
an unescaped `"` or an unescaped raw newline. Supported escape sequences:

```text
\n  \t  \r  \\  \"  \'  \0
```

An unrecognized escape sequence, an unterminated string (EOF or raw
newline before the closing `"`), is a lexical error. The lexer records
both the raw source slice and the decoded literal value (with escapes
resolved) on the token.

### Raw strings

A raw string is written `r"..."` and performs no escape processing at
all — every byte between the quotes (other than the closing `"` itself)
is part of the literal value verbatim, including backslashes. A raw string
containing a literal `"` cannot be expressed in this milestone (no
delimiter-counting `r#"…"#` form yet); see "Unresolved research questions".

### Character literals

A character literal is delimited by `'` and contains exactly one Unicode
scalar value, written either directly or via one of the escapes listed
above for strings. `''` (empty) and literals containing more than one
scalar value are lexical errors.

### Operators and punctuation

```text
+  -  *  /  %
== != < <= > >=
&& || !
&  |  ^  ~  <<  >>
=  +=  -=  *=  /=  %=  &=  |=  ^=  <<=  >>=
..  ..=
->  =>
(  )  [  ]  {  }
,  ;  :  ::  .
```

### End of file

The lexer emits a single, well-formed end-of-file token after the last
real token, rather than signaling end of input out-of-band. This lets the
parser treat "unexpected EOF" as an ordinary unexpected-token diagnostic.

## Accepted design direction

- Full Unicode identifiers (`XID_Start`/`XID_Continue`), not just ASCII.
- Numeric literal type suffixes (e.g. `1u8`, `1.0f32`) once the type system
  supports them without conflicting with inference.
- Delimiter-counting raw strings (`r#"..."#`) so raw strings can contain
  literal `"`.

## Unresolved research questions

- Whether Napitia should ever adopt significant-whitespace blocks (Python
  style) versus staying brace-delimited (current direction: stay
  brace-delimited, for parser and tooling simplicity, but this has not been
  permanently ruled out).
- Whether string interpolation is a lexical feature (distinct token kinds)
  or a purely syntactic/macro feature layered on top of ordinary strings.

## Non-goals

- A textual preprocessor of any kind (`#define`, `#include`, conditional
  compilation via text substitution) is permanently out of scope; see
  RFC 0001.
