# Spec 0002: Syntax

- Status: Partially implemented (Alpha 0.1.1)

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
parsed and preserved on the function's AST/HIR node in this milestone,
but declaring either non-empty is a checked, reported error (see
`spec/0005`, `rfcs/0003-extensible-effects.md`): the type checker does
not yet implement effect/error checking, so it rejects any use of these
clauses outright rather than silently accepting and ignoring them.

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

All four are parsed, name-resolved, and duplicate-checked against a
module-level item in HIR. As of Alpha 0.1.1, `record`/`variant` are
fully implemented end to end (construction, field access, variant
constructors, pattern matching — see below and `spec/0003`); `protocol`/
`extend` remain name/kind-only in HIR (field lists, case payloads are
preserved for `record`/`variant`, but protocol member signatures and
extend bodies are not) — protocol conformance checking is still
accepted direction, not implemented.

A named `record`/`variant` type is nominal (two declarations are
distinct types even with identical fields, compared by declaration
identity, never by name or structure) and `napitia check` accepts it
anywhere a type is expected, including function parameter and return
position. Since Alpha 0.1.1, a named aggregate type has a real NIR
runtime representation (see `spec/0006-napitia-ir.md`) and crosses
function boundaries (parameters, return values, bindings, variant
payloads) exactly like a primitive type — it is no longer rejected at
lowering time.

#### Record construction

```text
RecordLiteral = IDENT "{" [ FieldInit { "," FieldInit } [ "," ] ] "}" ;
FieldInit     = IDENT ":" Expression ;
```

`User { id: 42, enabled: true }` constructs a value of the record named
by the leading identifier. Fields may be written in any order; each
must appear exactly once (a missing, duplicate, or unknown field is a
checked, reported error — `spec/0003`). Field initializers are
evaluated exactly once, in the order written (not declaration order);
runtime layout always follows declaration order regardless.

A record literal is syntactically **disabled** directly in the
condition of `if`/`while` and the scrutinee of `match` (restored inside
parentheses or call arguments), the same way most brace-delimited
languages with struct literals resolve the ambiguity with the
construct's own opening `{`: `if user { }` parses `user` as a plain
identifier condition, never as `user { }` followed by an empty block.

#### Field access

`base.field` (already part of `PostfixExpr`, below) resolves against
the base expression's inferred nominal record type. Field access on a
non-record type, or on a record that doesn't declare that field, is a
checked, reported error. Field *mutation* (`user.age = 20;`) is parsed
as an ordinary assignment but is a dedicated, reported error in this
milestone — see `spec/0003`.

#### Variant constructors

A variant case is constructed by qualifying its variant's name with a
`.` and calling it (or, for a payload-less case, referencing it bare):

```napitia
value found = LookupResult.Found(user);
value missing = LookupResult.Missing;
```

This needs no new grammar at all: `LookupResult.Found(user)` is exactly
`PostfixExpr`'s existing `FieldAccess` followed by `Call` (`Ident` →
`.Found` → `(user)`); the qualified path is intentionally **dotted, not
`::`**, matching this spec's existing stance that Napitia paths are
dotted (`import`/`uses`, above), not double-colon-separated. Name
resolution (not new syntax) recognizes a `Field` whose base names a
declared `variant` and turns it into a constructor reference rather
than an ordinary field access. The qualifier may be omitted
(`Found(user)`) when the case name is unambiguous across every declared
variant in the module; if two variants both declare a case with that
name, the unqualified form is a checked, reported ambiguity error.

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

`defer` is parsed, but using it is a checked, reported error in this
milestone rather than being lowered or executed (no backend runs
deferred cleanup yet); see `spec/0004`.

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
```

`FieldAccess` is fully implemented as of Alpha 0.1.1 (see "Records,
variants, and protocols" above). `AsCast` is still parsed, but using it
remains a checked, reported error: `as` performs no runtime conversion
in this milestone — accepting it silently would let a program
type-check while lying about what it does.

```text
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

`?` (`TryPropagate`) is parsed as a postfix operator in this milestone,
but using it is a checked, reported error rather than being given any
behavior — a function's `raises` clause is not enforced yet (see
"Functions" above), so the checker rejects `?` outright instead of
silently accepting it with no effect. This is recorded here, not
implemented, matching `rfcs/0004`'s note that `raises`/`?` is the
intended primary failure-propagation path but is not frozen design.

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

As of Alpha 0.1.1, `match` is fully checked and executed: pattern-to-
scrutinee compatibility, exhaustiveness (with a concrete missing-pattern
witness), and unreachable-arm detection are all implemented (see
`spec/0003-type-system.md`), and a well-typed `match` lowers to a real
NIR decision tree (`spec/0006-napitia-ir.md`).

A pattern's case name is never qualified (`Found(user)`, not
`LookupResult.Found(user)`) — unlike a constructor *expression*, a
pattern's scrutinee type is always already known, so there is no
ambiguity a qualifier would need to resolve. `match` is syntactically
disabled as a record-literal position for its scrutinee the same way
`if`/`while` conditions are (see "Record construction" above).

Not implemented in this milestone, and not yet part of the grammar at
all (each is a plain, structured "expected a pattern" parse error, not
a silently-accepted-then-ignored construct): pattern guards,
or-patterns, record-destructuring patterns, slice patterns, range
patterns, and mutable pattern bindings.

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
  system (`spec/0005`, `rfcs/0003`), rather than rejected outright as
  unsupported, as in this milestone.
- `async`/`await` and structured-concurrency syntax.
- `loop { ... break value }` as a value-producing expression.
- Pattern guards, or-patterns, record-destructuring patterns, slice
  patterns, and range patterns (see "Match" above — full variant-case
  pattern matching with exhaustiveness checking is implemented as of
  Alpha 0.1.1; these extended pattern forms are not).

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
