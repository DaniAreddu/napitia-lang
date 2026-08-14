# Spec 0002: Syntax

- Status: Partially implemented (Alpha 0.1)

The grammar below uses the provisional vocabulary accepted in
`rfcs/0004-language-independence.md`. It replaces an earlier version of
this spec that used Rust's own declaration keywords (`fn`, `let`/`var`,
`struct`, `enum`, `trait`, `impl`, `use`, `pub`) — see RFC 0004 for why
that was a mistake and not merely a style choice.

## Implemented features

Grammar below uses EBNF-style notation: `|` alternation, `[...]` optional,
`{...}` zero-or-more, `(...)` grouping. Terminals are quoted or reference
lexical categories from `spec/0001-lexical-grammar.md` (`IDENT`, `INT`,
`FLOAT`, `STRING`, `CHAR`).

### Module

```text
Module = { Item } ;

Item = FunctionDecl
     | RecordDecl
     | VariantDecl
     | ProtocolDecl
     | ExtendDecl
     | ImportDecl
     ;
```

A source file is one module. Multi-file modules (`module` declarations
spanning files, visibility enforcement across files) are not implemented
in this milestone; `public`/`private` are parsed but only checked as
placeholders (see `spec/0003`).

### Imports

```text
ImportDecl = "import" Path ";" ;
Path       = IDENT { "." IDENT } ;
```

`import` is parsed but does not yet resolve to real module contents in
this milestone — there is only ever one module (the file being compiled).
Paths are dotted (`a.b.c`), not double-colon-separated, matching the
dotted capability paths used by `uses` (see below) rather than Rust's
`::` path syntax.

### Functions

```text
FunctionDecl = [ "public" ] "func" IDENT "(" [ ParamList ] ")"
               [ "->" Type ] [ UsesClause ] [ RaisesClause ] Block ;
ParamList    = Param { "," Param } [ "," ] ;
Param        = IDENT ":" Type ;

UsesClause   = "uses" EffectPath { "," EffectPath } ;
RaisesClause = "raises" IDENT { "," IDENT } ;
EffectPath   = IDENT { "." IDENT } ;
```

A function with no `-> Type` has return type `unit`. `uses`/`raises` are
parsed and attached to the function's AST/HIR node in this milestone, but
are not yet enforced by the type checker (see `spec/0005`,
`rfcs/0003-extensible-effects.md`) — a function's declared effects and
errors are not faked as checked; they are simply not checked yet.

### Records, variants, and protocols

```text
RecordDecl = [ "public" ] "record" IDENT "{" [ FieldList ] "}" ;
FieldList  = Field { "," Field } [ "," ] ;
Field      = [ "public" ] IDENT ":" Type ;

VariantDecl  = [ "public" ] "variant" IDENT "{" [ CaseList ] "}" ;
CaseList     = Case { "," Case } [ "," ] ;
Case         = IDENT [ "(" Type { "," Type } ")" ] ;

ProtocolDecl = [ "public" ] "protocol" IDENT "{" { ProtocolMember } "}" ;
ProtocolMember = "func" IDENT "(" [ ParamList ] ")" [ "->" Type ] ";" ;

ExtendDecl = "extend" IDENT [ "with" Path ] "{" { FunctionDecl } "}" ;
```

`record` is a product type (fields); `variant` is a sum type (a closed set
of cases, optionally carrying payload types). `protocol` declares a
behavioral contract as a set of function signatures with no bodies.
`extend` attaches function bodies to a type, either as a protocol
implementation (`extend Point with Printable { ... }`) or as inherent
functions with no protocol (`extend Point { ... }`).

All four are parsed and lowered into HIR items in this milestone. Full
type-checking of record/variant construction, field access, protocol
conformance, and pattern matching beyond the primitive-typed subset is
accepted direction, not implemented (see `spec/0003-type-system.md`).

### Types

```text
Type = IDENT ;
```

Only named primitive types (`i8`..`usize`, `f32`, `f64`, `bool`, `char`,
`str`, plus user record/variant names by identifier) are accepted in this
milestone. Generic type arguments and any reference/pointer/ownership
annotation types (`owned`, `borrow`, `shared` — see `spec/0004`) are not
part of the grammar yet; see "Accepted design direction".

### Statements and blocks

```text
Block = "{" { Statement } [ Expression ] "}" ;

Statement = BindingStmt
          | ExprStmt
          | "defer" Expression ";"
          | WhileStmt
          | LoopStmt
          ;

BindingStmt = ("value" | "mutable") IDENT [ ":" Type ] "=" Expression ";" ;
ExprStmt    = Expression ";" ;
```

`ExprStmt`'s trailing `;` is optional when `Expression` is an `IfExpr`,
`MatchExpr`, or `BlockExpr` — all three already end in a `}`, so a
statement like `if cond { f() }` does not additionally need a `;` before
the next statement, the same way most brace-delimited languages don't
require one after a brace-terminated statement. A `;` is still accepted
in that position; it is simply not mandatory.

A block's final expression, if present without a trailing `;`, is the
block's value (tail expression), matching how `if`/`match` produce values.
`value` introduces an immutable binding; `mutable` introduces a mutable
one. `const` (module-level compile-time constants) is reserved but not
implemented in this milestone.

`return`, `break`, and `continue` are **expressions**, not dedicated
statements (see "Expressions" below) — this is what lets
`return left + right` appear with no trailing `;` as a block's tail, as
in the example at the end of this document, while still being usable as
an ordinary `ExprStmt` (`return left + right;`) anywhere else. An earlier
version of this grammar modeled them as semicolon-mandatory statements,
which contradicted that same example; this is a correction, not a
redesign of intent.

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
14. postfix                 call `f(...)`, field access `.field`, `as Type`,
                            error-propagation `expr?`
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

PostfixExpr = PrimaryExpr { Call | FieldAccess | AsCast | TryPropagate } ;
Call         = "(" [ Expression { "," Expression } [ "," ] ] ")" ;
FieldAccess  = "." IDENT ;
AsCast       = "as" Type ;
TryPropagate = "?" ;

PrimaryExpr = INT | FLOAT | STRING | CHAR | "true" | "false"
            | IDENT
            | "(" Expression ")"
            | IfExpr
            | MatchExpr
            | BlockExpr
            | ReturnExpr
            | BreakExpr
            | ContinueExpr
            ;

BlockExpr    = Block ;
ReturnExpr   = "return" [ Expression ] ;
BreakExpr    = "break" [ Expression ] ;
ContinueExpr = "continue" ;
```

`ReturnExpr`/`BreakExpr`/`ContinueExpr` have type `never` (`spec/0003`),
which is why they can appear anywhere an ordinary expression can —
including as a binary operand or call argument, which a statement-shaped
`return` could never do — while still working as a block's tail with no
`;`, or as an ordinary `ExprStmt` (`return x;`) elsewhere.

`?` (`TryPropagate`) is parsed as a postfix operator in this milestone.
It is not yet lowered to any behavior — a function's `raises` clause is
not enforced yet (see "Functions" above), so `?` currently parses but the
checker does not yet give it early-return-on-failure semantics. This is
recorded here, not implemented, matching `rfcs/0004`'s note that
`raises`/`?` is the intended primary failure-propagation path but is not
frozen design.

### Control flow

```text
IfExpr    = "if" Expression Block [ "else" (IfExpr | Block) ] ;
WhileStmt = "while" Expression Block ;
LoopStmt  = "loop" Block ;
```

`if`/`else` is an expression (it can produce a value, both arms must agree
on type when used as a value; see `spec/0003`). `while` and `loop` are
statements in this milestone; `loop` supporting `break <expr>` as a
value-producing expression is accepted direction but not implemented
yet — `break` in this milestone accepts an optional expression
syntactically but the checker requires it to be `unit` until
loop-as-expression is implemented.

### Match

```text
MatchExpr = "match" Expression "{" { MatchArm } "}" ;
MatchArm  = Pattern "=>" (Expression "," | Block) ;
Pattern   = IDENT                      (* binds, or matches a payload-less case *)
          | IDENT "(" PatternList ")"  (* variant case with payload *)
          | INT | STRING | CHAR | "true" | "false"
          | "_"                        (* wildcard *)
          ;
PatternList = Pattern { "," Pattern } [ "," ] ;
```

`match` is parsed and lowered into HIR/NIR as a chain of equality
comparisons for literal and payload-less-case patterns; payload-carrying
variant-case patterns are parsed but exhaustiveness checking and payload
binding are accepted direction, not implemented in this milestone (see
`spec/0003-type-system.md`).

## Example

```napitia
func add(left: i64, right: i64) -> i64 {
    return left + right
}

func main() -> i64 {
    value answer = add(40, 2)

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

- Generic type parameters on functions, records, variants, and protocols
  (`func identity<T>(x: T) -> T`).
- `owned`/`borrow`/`shared` type-position annotations at API boundaries,
  once `rfcs/0002-ownership-and-regions.md` is implemented — never
  pervasive lifetime parameters (`rfcs/0004`).
- `uses`/`raises` clauses actually checked against a real effect/error
  system (`spec/0005`, `rfcs/0003`), rather than parsed-and-ignored as in
  this milestone.
- `async`/`await` and structured-concurrency syntax.
- `loop { ... break value }` as a value-producing expression.
- Full pattern matching with exhaustiveness checking and variant-case
  payload binding.

## Unresolved research questions

- Whether `match` arms need explicit braces always, or the current
  "block or comma-terminated expression" split is the right long-term
  shape.
- The precise surface syntax for a fully checked effect/error system has
  not been designed; `uses`/`raises` clauses exist syntactically, but
  `spec/0005`/`rfcs/0003` describe the type-level model as still open, not
  settled.
- Whether `?` needs any additional surface form (e.g. distinguishing
  "propagate the error" from "propagate and also apply a capability")
  once `raises` is actually checked.

## Non-goals

- No macro system that operates on raw tokens/text; any future
  metaprogramming operates on typed AST/HIR structures (RFC 0001).
