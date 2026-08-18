# Spec 0002: Syntax

- Status: Partially implemented (Alpha 0.1.3)

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

A source file is one module — there is no `module` declaration, and one
module never spans multiple files. As of Alpha 0.1.2, a `napitia.toml`
manifest can name a `source-root` and an `entry` file so a compilation
spans every `.npt` file reachable by `import` from the entry module (see
`rfcs/0006` for the full multi-file architecture); legacy single-file
compilation still works unchanged by naming a `.npt` file directly.
`public`/`private` are enforced for real, both within a module (see
`spec/0003`) and across modules: an item, and each record field
independently, is only reachable from another module if it is `public`
*and* that module actually imported it — reachability through some other
already-imported name in the same module is not enough (`rfcs/0006`).

### Imports

```text
ImportDecl = "import" Path [ "as" IDENT ] ";" ;
Path       = IDENT { "." IDENT } ;
```

In project (multi-file) compilation, `import a.b.c;` brings the single
public item `c`, declared in module `a.b`, into the importing module's
own namespace by that unqualified name — every segment before the last is
the module path, the last is the imported item (`rfcs/0006`). An optional
`as <alias>` (Alpha 0.1.3, `rfcs/0007`) binds the item under `<alias>`
instead of `c`: a purely local rename that never changes the item's own
declared name or identity, needed to bring two same-named items from
different modules into one scope at once (`import a.User as A; import
b.User as B;`). There is no wildcard (`import a.*;`), grouped
(`import a.{b, c};`), package-alias, or module-alias (aliasing `a.b`
itself rather than one item in it) form, and no re-export — every one of
these is rejected with a diagnostic. In legacy single-file compilation an
`import` is accepted syntactically but has nothing to resolve against,
since there is only ever the one module being compiled. Paths are dotted
(`a.b.c`), not double-colon-separated, matching the dotted capability
paths used by `uses` (see below) rather than Rust's `::` path syntax.

### Functions

```text
FunctionDecl = [ "public" ] "func" IDENT "(" [ ParamList ] ")"
               [ "->" Type ] [ UsesClause ] [ RaisesClause ] Block ;
ParamList    = Param { "," Param } [ "," ] ;
Param        = IDENT ":" Type ;

UsesClause   = "uses" UsesEntry { "," UsesEntry } ;
UsesEntry    = EffectPath [ "[" Type { "," Type } [ "," ] "]" ] ;
RaisesClause = "raises" IDENT { "," IDENT } ;
EffectPath   = IDENT { "." IDENT } ;
```

A function with no `-> Type` has return type `unit`. A `UsesEntry`
carrying a bracketed type-argument list (`Equal[T]`) is a capability
requirement (`rfcs/0009`), fully implemented as of Alpha 0.1.5 — see
"Protocols and capabilities", below. A bare `UsesEntry` with no type
arguments (`Database.Read`) is instead `spec/0005`'s pre-existing effect
declaration, which remains unimplemented: declaring one is still a
checked, reported error (`rfcs/0003-extensible-effects.md`), exactly as
before this milestone. `raises` likewise remains parsed and preserved but
rejected if non-empty — this milestone changes nothing about error
checking.

### Records, variants, and protocols

```text
RecordDecl = [ "public" ] "record" IDENT "{" [ FieldList ] "}" ;
FieldList  = Field { "," Field } [ "," ] ;
Field      = [ "public" ] IDENT ":" Type ;

VariantDecl  = [ "public" ] "variant" IDENT "{" [ CaseList ] "}" ;
CaseList     = Case { "," Case } [ "," ] ;
Case         = IDENT [ "(" Type { "," Type } ")" ] ;

ProtocolDecl   = [ "public" ] "protocol" IDENT TypeParamList
                 "{" { ProtocolMember } "}" ;
ProtocolMember = "func" IDENT "(" [ ParamList ] ")" [ "->" Type ] ";" ;

ExtendDecl = "extend" [ TypeParamList ] Type [ UsesClause ]
             "{" { FunctionDecl } "}" ;
```

`record` is a product type (fields); `variant` is a sum type (a closed set
of cases, optionally carrying payload types). `protocol` declares a
capability contract (`rfcs/0009`): a name, one or more explicit type
parameters, and a set of method signatures with no bodies — there is no
implicit receiver or `Self`; every method parameter is ordinary and
explicit. `extend` attaches one implementation of a protocol to a
specific (possibly still-generic) instantiation of it: `Type` after
`extend`'s own optional `[T, ...]` type-parameter list is the protocol
name applied to its own type arguments (`Equal[i64]`, or `Equal[Box[T]]`
using the extend's own `T`), and the optional `UsesClause` declares this
extension's own capability requirements (see "Functions", above, for the
same clause on a function). Every function inside an `extend`'s body
implements exactly one of its protocol's declared methods — the body is
that one implementation, not an independent set of inherent functions
with no protocol (there is no `extend` with no protocol at all).

All four are parsed, name-resolved, and duplicate-checked against a
module-level item in HIR. `record`/`variant` are fully implemented end
to end since Alpha 0.1.1 (construction, field access, variant
constructors, pattern matching — see below and `spec/0003`).
`protocol`/`extend` are fully implemented as of Alpha 0.1.5
(`rfcs/0009`): declaration, authority/coherence checking, capability
resolution (`uses`), and an explicit `Protocol[Args].method(...)` call
expression — see "Protocol calls", below, and `spec/0003`/
`spec/0006`/`rfcs/0009` for the full semantic model.

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

#### Protocol calls (Alpha 0.1.5)

```napitia
Equal[i64].equal(21, 21)
```

A protocol method is invoked by qualifying the protocol's name with its
own bracketed type arguments, then a `.` and the method call — again
`PostfixExpr`'s existing `FieldAccess` followed by `Call`, this time on a
type-application base rather than a bare identifier. This is the *only*
call syntax for a protocol method: there is no implicit receiver
(`a.equal(b)` never resolves to a protocol call) and no operator sugar
routing `==`/`<`/etc. through one. Naming a protocol method without
calling it (`Equal.equal`, or `Equal[i64].equal` with no argument list) is
a checked, reported error, not a first-class function value. See
`rfcs/0009-capability-protocols.md` for the full semantic model
(authority, coherence, capability resolution) and `spec/0003`/`spec/0006`
for the type-system and NIR-level detail.

### Types

```text
Type = IDENT [ "[" Type { "," Type } [ "," ] "]" ] ;
```

Named primitive types (`i8`..`usize`, `f32`, `f64`, `bool`, `char`, `str`),
user record/variant names by identifier, and — since Alpha 0.1.4 — an
applied generic type (`Box[i64]`, `Pair[i64, str]`, `Box[Maybe[i64]]`) are
accepted. A trailing comma inside the bracketed argument list is accepted;
an empty `[]` is malformed. Any reference/pointer/ownership annotation
type (`owned`, `borrow`, `shared` — see `spec/0004`) is not part of the
grammar yet; see "Accepted design direction".

### Generics (Alpha 0.1.4)

```text
TypeParamList = "[" IDENT { "," IDENT } [ "," ] "]" ;
```

`func`, `record`, and `variant` may each carry an optional `TypeParamList`
immediately after their name (before `(`/`{`):

```text
func identity[T](value: T) -> T { value }
record Box[T] { value: T }
variant Maybe[T] { Some(T), None }
```

A type application appears in type position (`Box[i64]`, above) and, for
a function name or a bare variant-case reference, in expression position
too:

```text
identity(42);          // inferred
identity[i64](42);     // explicit
value m = Maybe[i64].Some(42);
value n = Maybe[i64].None;
```

`<T>` angle-bracket syntax does not exist; partial, default, or wildcard
type arguments do not exist; a type parameter is never itself generic
(`T[i64]` is rejected). See `rfcs/0008-canonical-generics.md` for the full
semantics (parameter identity, inference, exhaustiveness over an
instantiated payload type, canonical instance identity, and parametric
NIR) and `spec/0003`/`spec/0006` for the type-system and NIR-level detail.

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

- Generic type parameters on `protocol`/`extend` (functions, records, and
  variants gained square-bracket generics in Alpha 0.1.4 — see "Generics"
  above and `rfcs/0008`; protocols remain name/kind-only in HIR, so a
  generic protocol constraint has nothing to attach to yet).
- Protocol/trait-style constraints on a generic type parameter (bounding
  what a `T` may be instantiated with, and what operations become
  provably safe for it) — Alpha 0.1.4's type parameters are entirely
  unconstrained; see `rfcs/0008`'s honest limitations.
- Native-code specialization/monomorphization of a generic instantiation
  — Alpha 0.1.4's NIR stays fully parametric with no backend to
  specialize for yet.
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
