# Spec 0002: Syntax

- Status: Partially implemented (Alpha 0.1)

## Implemented features

Grammar below uses EBNF-style notation: `|` alternation, `[...]` optional,
`{...}` zero-or-more, `(...)` grouping. Terminals are quoted or reference
lexical categories from `spec/0001-lexical-grammar.md` (`IDENT`, `INT`,
`FLOAT`, `STRING`, `CHAR`).

### Module

```text
Module = { Item } ;

Item = FunctionDecl
     | StructDecl
     | EnumDecl
     | UseDecl
     ;
```

A source file is one module. Multi-file modules (`module` declarations
spanning files, visibility enforcement across files) are not implemented
in this milestone; `pub`/`private` are parsed but only checked as
placeholders (see `spec/0003`).

### Imports

```text
UseDecl = "use" Path ";" ;
Path    = IDENT { "::" IDENT } ;
```

`use` is parsed but does not yet resolve to real module contents in this
milestone — there is only ever one module (the file being compiled).

### Functions

```text
FunctionDecl = [ "pub" ] "fn" IDENT "(" [ ParamList ] ")" [ "->" Type ] Block ;
ParamList    = Param { "," Param } [ "," ] ;
Param        = IDENT ":" Type ;
```

A function with no `-> Type` has return type `unit`.

### Structs and enums

```text
StructDecl = [ "pub" ] "struct" IDENT "{" [ FieldList ] "}" ;
FieldList  = Field { "," Field } [ "," ] ;
Field      = [ "pub" ] IDENT ":" Type ;

EnumDecl   = [ "pub" ] "enum" IDENT "{" [ VariantList ] "}" ;
VariantList = Variant { "," Variant } [ "," ] ;
Variant    = IDENT [ "(" Type { "," Type } ")" ] ;
```

Structs and enums are parsed and lowered into HIR items in this milestone.
Full type-checking of their construction, field access, and pattern
matching beyond the primitive-typed subset is accepted direction, not
implemented (see `spec/0003-type-system.md`).

### Types

```text
Type = IDENT ;
```

Only named primitive types (`i8`..`usize`, `f32`, `f64`, `bool`, `char`,
`str`, plus user struct/enum names by identifier) are accepted in this
milestone. Generic type arguments, references, and pointer types are not
part of the grammar yet; see "Accepted design direction".

### Statements and blocks

```text
Block = "{" { Statement } [ Expression ] "}" ;

Statement = LetStmt
          | ExprStmt
          | "return" [ Expression ] ";"
          | "break" [ Expression ] ";"
          | "continue" ";"
          | "defer" Expression ";"
          ;

LetStmt  = ("let" | "var") IDENT [ ":" Type ] "=" Expression ";" ;
ExprStmt = Expression ";" ;
```

A block's final expression, if present without a trailing `;`, is the
block's value (tail expression), matching how `if`/`match` produce values.
`let` introduces an immutable binding; `var` introduces a mutable one.
`const` (module-level compile-time constants) is reserved but not
implemented in this milestone.

`defer` is parsed and lowered but not yet executed by the interpreter in
this milestone (no backend runs deferred cleanup yet); see `spec/0004`.

### Expressions

Precedence, lowest to highest (Pratt parser binding powers):

```text
1.  assignment            = += -= *= /= %= &= |= ^= <<= >>=   (right-assoc)
2.  range                 .. ..=
3.  logical or             ||
4.  logical and            &&
5.  bitwise or             |
6.  bitwise xor            ^
7.  bitwise and            &
8.  equality               == !=
9.  comparison              < <= > >=
10. shift                  << >>
11. additive                + -
12. multiplicative           * / %
13. unary (prefix)          - ! ~
14. postfix                 call `f(...)`, field access `.field`, `as Type`
15. primary                 literals, identifiers, `( Expression )`
```

```text
Expression = AssignExpr ;

AssignExpr = RangeExpr [ AssignOp AssignExpr ] ;
AssignOp   = "=" | "+=" | "-=" | "*=" | "/=" | "%="
           | "&=" | "|=" | "^=" | "<<=" | ">>=" ;

BinaryExpr(level) = generated from the precedence table above,
                    each level left-associative unless noted.

UnaryExpr  = ( "-" | "!" | "~" ) UnaryExpr | PostfixExpr ;

PostfixExpr = PrimaryExpr { Call | FieldAccess | AsCast } ;
Call        = "(" [ Expression { "," Expression } [ "," ] ] ")" ;
FieldAccess = "." IDENT ;
AsCast      = "as" Type ;

PrimaryExpr = INT | FLOAT | STRING | CHAR | "true" | "false"
            | IDENT
            | "(" Expression ")"
            | IfExpr
            | MatchExpr
            | BlockExpr
            ;

BlockExpr = Block ;
```

### Control flow

```text
IfExpr    = "if" Expression Block [ "else" (IfExpr | Block) ] ;
WhileStmt = "while" Expression Block ;
LoopStmt  = "loop" Block ;
```

`if`/`else` is an expression (it can produce a value, both arms must agree
on type when used as a value; see `spec/0003`). `while` and `loop` are
statements in this milestone; `loop` supports `break <expr>` producing a
value is accepted direction but not implemented yet — `break` in this
milestone accepts an optional expression syntactically but the checker
requires it to be `unit` until loop-as-expression is implemented.

### Match

```text
MatchExpr = "match" Expression "{" { MatchArm } "}" ;
MatchArm  = Pattern "=>" (Expression "," | Block) ;
Pattern   = IDENT                      (* binds or matches a unit variant *)
          | IDENT "(" PatternList ")"  (* enum variant with payload *)
          | INT | STRING | CHAR | "true" | "false"
          | "_"                        (* wildcard *)
          ;
PatternList = Pattern { "," Pattern } [ "," ] ;
```

`match` is parsed and lowered into HIR/NIR as a chain of equality
comparisons for literal and unit-variant patterns; payload-carrying enum
patterns are parsed but exhaustiveness checking and payload binding are
accepted direction, not implemented in this milestone (see
`spec/0003-type-system.md`).

## Example

```napitia
fn add(left: i64, right: i64) -> i64 {
    return left + right
}

fn main() -> i64 {
    let answer = add(40, 2)

    if answer == 42 {
        return answer
    } else {
        return 0
    }
}
```

## Error recovery

A syntax error does not abort parsing. The parser records a diagnostic and
recovers by skipping tokens up to a synchronization point (`;`, a block
boundary `{`/`}`, or the start of a keyword that can begin an `Item` or
`Statement`), so later, independent errors in the same file are still
reported in one compiler invocation. Recovery inserts an `Error` AST node
in place of the malformed construct so later stages can detect and skip it
without treating a missing node as a silent success.

## Accepted design direction

- Generic type parameters on functions, structs, enums, and traits
  (`fn identity<T>(x: T) -> T`).
- Reference and pointer types, and ownership/borrow annotations, once
  `rfcs/0002-ownership-and-regions.md` is implemented.
- `impl` blocks and `trait` bodies (currently only reserved as keywords).
- `async`/`await` and structured-concurrency syntax.
- `loop { ... break value }` as a value-producing expression.
- Full pattern matching with exhaustiveness checking and variant payload
  binding.

## Unresolved research questions

- Whether `match` arms need explicit braces always, or the current
  "block or comma-terminated expression" split is the right long-term
  shape.
- The precise surface syntax for effects (`spec/0005`) has not been
  designed; `spec/0005` describes the type-level model only.

## Non-goals

- No macro system that operates on raw tokens/text; any future
  metaprogramming operates on typed AST/HIR structures (RFC 0001).
