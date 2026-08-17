# RFC 0008: Canonical Generics (Alpha 0.1.4)

- Status: Accepted, implemented in Alpha 0.1.4

## Summary

Alpha 0.1.4 adds square-bracket generic parameters to `func`, `record`, and
`variant` declarations, and explicit or inferred type applications wherever
a generic declaration is referenced. A generic declaration's body is
checked exactly once, symbolically, against its own opaque type
parameters — never re-checked per instantiation — and every instantiation
(a call, a record/variant construction, a bare unit-case reference) is
identified by a single canonical key, `GenericInstanceKey { declaration:
ItemId, arguments: Vec<Ty> }`, reused everywhere from type inference
through NIR lowering and verification.

```napitia
record Box[T] { value: T }

func unwrap[T](box: Box[T]) -> T {
    box.value
}

func main() -> i64 {
    unwrap(Box[i64] { value: 42 })
}
```

## Non-goals (unchanged from prior milestones, plus these)

`<T>` angle-bracket syntax, partial/default/wildcard type arguments,
higher-kinded types, generic methods or local (nested) generic functions,
variance annotations, specialization syntax, and protocol/trait-style
constraints on a type parameter are all out of scope and rejected — either
by the grammar (there is no syntax for them) or by construction (an
unconstrained type parameter has no operations proven safe for it; see
"Checking a generic body" below). Native-code monomorphization does not
exist yet — NIR remains parametric, and the interpreter erases generic
arguments at runtime the same way it always erased nominal identity to a
bare `ItemId`.

## Syntax

```text
func identity[T](value: T) -> T { value }
record Box[T] { value: T }
variant Maybe[T] { Some(T), None }

value b = Box[i64] { value: 42 };          // explicit type application, record construction
value m = Maybe[i64].Some(42);             // explicit type application, variant construction
value n = Maybe[i64].None;                 // explicit type application, unit case
identity(42);                              // inferred from the argument
identity[i64](42);                         // explicit, at a call site
```

A generic parameter list is a comma-separated list of identifiers between
`[` and `]`, immediately after the declaration's name (before `(` for a
function, before `{` for a record/variant). An empty list (`func f[]()`)
is malformed and recovers with a diagnostic rather than being treated as
"not generic" — if a declaration is not generic, the brackets are simply
omitted. A trailing comma (`[T,]`) is accepted, matching every other
comma-separated list in this grammar. A primitive type name (`i64`,
`bool`, ...) is rejected as a parameter name.

A type application (`Box[i64]`, `Pair[i64, str]`) is valid in type
position (a field, parameter, or return type) and, for a function or a
bare variant-case reference, in expression position too
(`identity[i64](42)`, `Maybe[i64].None`) — parsed by the same
`parse_type_arg_list` either way. An empty `[]`, an unclosed `[`, and a
trailing-comma-only list are all malformed and recover with a parser
diagnostic (`P0001`) rather than being silently reinterpreted as
indexing, a comparison chain, or an ordinary call.

## Generic parameter identity

Every declared type parameter gets its own `TypeParamId(u32)`, minted once
per declaration by `hir::lower`. Two declarations that happen to spell
their own parameter the same way — `func first[T](...)` and `func
second[T](...)` — are completely unrelated: each `T` is a distinct
`TypeParamId`, and nothing about one leaks into the other. Concretely,
`second`'s own body has no meaning for `first`'s `T`, and a `T` used
*outside* the declaration that introduced it (e.g. a sibling function
that never declared its own `T`) resolves as an ordinary unresolved name,
deferred to typeck's own `T0006` — it is never silently treated as if the
enclosing scope had declared it.

`hir::lower` rejects, per declaration:

- a duplicate parameter name (`func f[T, T](...)`, `R0016`)
- a primitive name used as a parameter (`func f[i64](...)`, `R0017`)
- a type parameter given its own type arguments (`T[i64]`, `R0018` — a
  parameter is never itself generic)
- a type application nested past `MAX_GENERIC_DEPTH` (`R0019`)
- a value name used where a type was expected in an explicit type
  application, and a type name used where a value was expected
  (`R0020`)

## Type representation

`Ty` gained two variants, alongside the pre-existing `Ty::Named(ItemId,
Symbol)`:

```rust
/// A reference to one of the *enclosing generic declaration's own* type
/// parameters. Rigid and opaque while that declaration's body is being
/// checked: unifies only with another occurrence of the exact same
/// `TypeParamId`. Nominal, matching `Named`'s own identity contract; the
/// `Symbol` is display-only.
Param(TypeParamId, Symbol),

/// A concrete instantiation of a generic declaration: `declaration` is
/// the exact `ItemId` `Named` would otherwise carry, `arguments` is the
/// declaration's own type parameters substituted in declared order.
/// Two `Applied` types are the same type iff they carry the same
/// `declaration` *and* the same `arguments`, compared structurally —
/// `Box[i64] != Box[str]`, `sales.Box[i64] != admin.Box[i64]`, and an
/// alias never affects this since `declaration` is always the canonical
/// `ItemId`. There is no zero-argument `Applied`: a non-generic
/// declaration is always `Named`, and a generic one is never referenced
/// without arguments (`value x: Box;` is rejected, `T0022`).
Applied(ItemId, Vec<Ty>),
```

`PartialEq`/`Hash` are hand-written for both, exactly mirroring `Named`'s
own nominal-by-identity contract. `Box[Maybe[i64]]` is a real, recursively
representable type — `Applied`'s own arguments can themselves be
`Applied`.

`crate::types::generics` centralizes the two operations every
generics-aware stage otherwise risked reimplementing independently:

```rust
pub struct GenericInstanceKey { pub declaration: ItemId, pub arguments: Vec<Ty> }

pub fn substitute(ty: &Ty, subst: &HashMap<TypeParamId, Ty>) -> Ty;
```

`substitute` walks a type replacing every `Ty::Param` present in `subst`,
recursing through `Ty::Applied`'s own argument list (`Box[T]` becomes
`Box[i64]` once `T -> i64` is in `subst`), bounded by `MAX_GENERIC_DEPTH`
the same way every other stage that walks a nested application is.

## Checking a generic body once, symbolically

A generic declaration's own body is type-checked exactly once, using
`Ty::Param` directly for its own parameters — never a fresh inference
variable, and never re-checked per call site. This is what makes
`identity[T](value: T) -> T { value }` valid (pass/return/store/load,
placement in a generic record/variant, extraction, and match dispatch are
all provably safe for *any* `T`) while rejecting, symbolically, before any
instantiation exists, every operation nothing proves safe for an
unconstrained `T`:

```napitia
func add[T](left: T, right: T) -> T { left + right }   // T0027
func same[T](left: T, right: T) -> bool { left == right }  // T0027
```

`T0027` (`UNSUPPORTED_ON_TYPE_PARAMETER`) is reported, before falling to
the ordinary diagnostic that operation would otherwise get, for: equality
and inequality (`==`/`!=`), ordering (`<`/`<=`/`>`/`>=`), arithmetic
(`+`/`-`/`*`/`/`/`%`, via the pre-existing `require_numeric`), bitwise
operators and shifts (via `require_integer`), logical use (`!`, `&&`,
`||`, and any `if`/`while` condition, via `expect_bool`), field access,
and calling a value of type `T`. Plain movement, binding, assignment,
construction, passing as an argument, and returning remain valid for
every one of these — there is nothing to prove for them.

Because a generic body is checked exactly once regardless of how many
call sites instantiate it, this architecture inherently avoids the
classic exponential blow-up naive eager monomorphization would risk: the
compiler never re-enters `add[T]`'s own body per concrete `T`, so the two
budgets below (depth, instance count) are the only limits actually
needed.

## Inference and unification

A call/construction's type arguments are either supplied explicitly
(`identity[i64](42)`, `Box[i64] { value: 42 }`) or inferred from argument
types (`identity(42)`). Record and variant *construction* always requires
explicit type arguments (there is no field/payload-value-based inference
for construction); a function call and a variant *constructor* call (one
with arguments to infer from) both support inference. A bare unit-case
reference (`Maybe[i64].None`) has nothing to infer from, so it always
requires an explicit application too.

Inference mints one fresh `Ty::Var` per declared type parameter, per
call, substitutes it into every parameter type, and unifies each argument
against its (substituted) parameter — never sharing inference state
between calls. `typeck::unify` was extended with exactly one new case for
this milestone:

```rust
(Ty::Applied(a_item, a_args), Ty::Applied(b_item, b_args)) => {
    if a_item != b_item || a_args.len() != b_args.len() {
        return Err((a.clone(), b.clone()));
    }
    for (x, y) in a_args.iter().zip(b_args.iter()) {
        unify_at_depth(ctx, x, y, depth + 1)?;
    }
    Ok(())
}
```

Two applied types unify only when they name the exact same declaration
(nominal) and have the same arity, after which corresponding arguments
unify pairwise, recursively — this is what lets a fresh inference
variable be discovered *inside* an applied argument
(`unify(Box[Var(T)], Box[i64])` binds `T` to `i64`), not just at the top
level, and is the mechanism that makes the worked example at the top of
this document infer `T = i64` and run to `42`. A mismatched declaration or
arity fails immediately and deterministically; recursion is bounded by
`MAX_GENERIC_DEPTH` as defense in depth (a well-typed program's own
nesting is already far shallower, by construction, from `hir::lower`'s
own guard). `TypeContext`'s deep-resolution helper (`deep_resolve`) was
given the same recursive, depth-bounded treatment, so a resolved
`Ty::Applied`'s own arguments are never left with a stale, unresolved
`Ty::Var` chain inside them.

### Occurs-check and transactional unification

Recursing into `Ty::Applied`'s own arguments means a variable can be
found nested arbitrarily deep inside the other side of a unification —
`occurs()` checks, before every bind, whether the variable being bound
already appears (transitively, through the current substitution state)
inside the type it would be bound to, so `unify(Var(v), Box[Var(v)])`
fails outright instead of producing a cyclic substitution that would
later hang whatever tries to resolve it. This also catches an *indirect*
cycle through a merged variable (`v` unified with `w`, then `w` unified
against `Box[v]`): `occurs` resolves at every level of its own recursion,
not just the top the way `TypeContext::resolve` alone does, so it chases
back through `w`'s own slot and finds `w` again.

Recursing into `Ty::Applied`'s arguments also means a single top-level
`unify` call can attempt several nested binds before one of them fails
(`Pair[V, V]` against `Pair[i64, bool]` binds `V = i64` from the first
argument pair, then fails on the second). The public `unify` entry point
is transactional: it checkpoints `TypeContext` (a cheap clone of its
substitution/kind tables — `unify` never allocates a fresh variable
partway through its own recursion, so a checkpoint is never invalidated
by those tables changing length underneath it) before attempting
anything, and restores it on any `Err`, so a failed call can never leave
a partial bind behind regardless of how much of its own recursion
already succeeded.

After unification: `T0025` (`CONFLICTING_INFERRED_ARGUMENTS`) reports two
arguments disagreeing about the same parameter (`choose(1, true)` for
`choose[T](left: T, right: T) -> T`); `T0026`
(`CANNOT_INFER_TYPE_ARGUMENT`) reports a parameter that appears only in
the return type (`func create[T]() -> T;`, which no argument could ever
constrain) and was not supplied explicitly. Explicit type arguments are
always validated for arity (`T0024`) before the values themselves are
checked. There is no speculative expected-return-type inference.

## Generic records and variants

Field access, constructor payload types, match binding types, and
exhaustiveness all use the *instantiated* type, never the declaration's
raw symbolic one. `check_field_access` builds a substitution from a
record's own `type_params` zipped with its `Ty::Applied`'s concrete
arguments (empty for a `Ty::Named` base) before substituting the found
field's declared type; the same substitution shape is used for a
variant's case payload types during construction, pattern-binding, and
exhaustiveness analysis. `Some(inner)` matched against a `Maybe[i64]`
scrutinee gives `inner` exactly the type `i64`, never the declaration's
own `T`.

**Exhaustiveness after generic substitution** required extending
`typeck::exhaustive::VariantSpace` with each variant's own declared
`type_params`, so `space()` (which decides whether a payload position is
a closed, enumerable domain or an open one) substitutes a case's payload
types against the *current scrutinee's* own concrete arguments before
deciding:

```napitia
variant Maybe[T] { Some(T), None }

func inspect(value: Maybe[bool]) -> i64 {
    match value {
        Some(true) => 1,
        Some(false) => 2,
        None => 0,
    }
}
```

is accepted as exhaustive — `Some`'s payload substitutes to the closed,
two-value `bool` space it actually is here, not the declaration's own
unresolved `T`, which no finite set of arms could ever be judged to
cover. A genuinely missing case (`Some(false)` omitted) is still reported
with the concrete witness `Maybe.Some(false)`, and a redundant arm after
both booleans are covered is still flagged unreachable; both properties
hold recursively for a nested generic scrutinee (`Maybe[Maybe[bool]]`)
and through a cross-module import alias (the analysis keys off the
canonical declaration, never the local name a particular match happens to
construct or reference cases through).

A raw reference to a generic declaration with no type arguments at all
(`value x: Box;`) is rejected (`T0022`), and a non-generic declaration
given type arguments (`User[i64]` when `User` is not generic) is rejected
too (`T0022`).

## Canonical generic instance identity

`GenericInstanceKey { declaration, arguments }` is the one canonical
identity for "this generic declaration, instantiated with these exact
type arguments" — used identically by typeck (to budget and dedupe
instances), by NIR lowering (to record a call site's own concrete
arguments), and by the NIR verifier (to validate them). Two aliases of
the same declaration produce the same key (an alias only ever changes a
local spelling, never the canonical `ItemId`, per `rfcs/0007`); two
distinct declarations that happen to share a name and shape (`sales.Box`
and `admin.Box`) never do.

`typeck::Checker::record_generic_instance` is the single place a new
instance is recorded, enforcing `MAX_GENERIC_INSTANCES` (`T0028`,
`GENERIC_INSTANCE_BUDGET_EXCEEDED`) — a budget on the total number of
*distinct* instantiations one compilation may produce, independent of how
many times each is actually used.

## Parametric NIR, never blind cloning

A generic function's body lowers exactly once, with its own parameter
types kept symbolic (`Ty::Param`):

```text
func @core.identity#12[T](%0: T) -> T {
bb0:
    ret %0
}
```

A concrete call records its own canonical type arguments directly on the
instruction:

```text
%1 = call @core.identity#12[i64](%0)
```

`ValueKind::Call`, `RecordCreate`, and `VariantCreate` each carry a
`Vec<Ty>` of concrete type arguments (empty for a non-generic
call/construction); `nir::Function`/`RecordLayout`/`VariantLayout` each
carry their own declared `type_params: Vec<(TypeParamId, Symbol)>`. NIR
lowering reads a call/construction's already-resolved type arguments back
from `typeck::TypeckResult::call_type_args` (keyed by `ExprId`) rather
than re-inferring them, and substitutes them into the callee's/record's/
variant's declared types purely to compute NIR type hints — the body
itself is never re-checked or duplicated. This includes a *bare* unit-case
reference (`Maybe[i64].None`, no call syntax at all): `check_case_ref`
threads its own `ExprId` and records its resolved arguments into
`call_type_args` exactly like every other generic construction site, so
lowering never silently defaults a known-generic construction to an empty
argument list.

All three lowering sites (`lower_call`, `lower_variant_construct` — which
handles the bare unit-case reference above too — and
`lower_record_literal`) read their own call site's type arguments back
through one shared, checked helper, `resolve_call_type_args`: absent
metadata is valid only for a non-generic reference (an empty argument
list); a generic reference with missing metadata, or metadata whose
length doesn't match the declaration's own type parameter count, is a
structured internal-lowering error (the existing `I0002` family) rather
than silently defaulting to empty or being silently truncated by
`Vec::zip` to whichever side happens to be shorter — either of which
would otherwise produce a partially-specialized NIR value with no
diagnostic at all.

The interpreter erases generic arguments at runtime: a `Value::Record`/
`Value::Variant` already carries only an `ItemId` and positional field
values, with no type arguments at all, so `Box[i64]` and `Box[str]`
execute through the identical lowered body and share runtime
representation shape — nominal identity (which record/variant this is)
is preserved by the `ItemId` alone, exactly as it always was for
non-generic types. Two distinct instantiations never accidentally become
runtime-compatible with each other, since the interpreter never inspects
type arguments to decide behavior in the first place — behavior depends
only on the (shared) lowered body and the `ItemId` the value already
carries.

## The NIR verifier

The verifier re-checks every generic-carrying instruction and type
independently of how NIR was built — it never trusts lowering. For
`Call`/`RecordCreate`/`VariantCreate`: type argument count is validated
against the callee's/record's/variant's own declared parameter count
(`V0031`, `GENERIC_ARITY_MISMATCH`) before substitution; the declared
signature/field/payload types are substituted with the supplied
arguments and compared against the instruction's actual operand/result
types exactly like a non-generic instruction's types always were.
`RecordField`/`VariantPayload` (field/payload *access*, as opposed to
construction) derive their own substitution from the base value's own
recorded `Ty::Applied` rather than carrying a separate, redundant type
argument list.

Additional structural checks, all recursive through nested `Ty::Applied`
arguments and bounded by `MAX_GENERIC_DEPTH`:

- `check_no_bad_type` rejects an unresolved `Ty::Var` (`V0012`) or
  `Ty::Error` (`V0013`) found *inside* an applied argument list, not just
  at the top level.
- `check_named_type_identity` rejects a `Ty::Named` for a declaration that
  is actually generic (`V0033`, `UNAPPLIED_GENERIC_TYPE`), a `Ty::Applied`
  whose arity does not match its declaration (`V0031`), and a `Ty::Applied`
  naming a declaration that is not generic at all (`V0031`).
- `check_type_param_scope` rejects a `Ty::Param` appearing anywhere
  outside the one declaration that binds it (`V0032`,
  `ESCAPING_TYPE_PARAMETER`) — a non-generic function's own signature, a
  different declaration's field/payload type, or a call's type arguments
  in a scope that does not itself declare that parameter.
- Every function/record/variant's own declared `type_params` list is
  checked for an internally-duplicated `TypeParamId` (`V0034`,
  `DUPLICATE_TYPE_PARAMETER`), which would otherwise make positional
  substitution ambiguous.

Every type root this verifier inspects — a record field, a variant case
payload, a function parameter or return type, an instruction's declared
result type, and every type argument at a `Call`/`RecordCreate`/
`VariantCreate` use site — goes through one shared helper,
`check_type_root`, so no root can ever drift into checking a different
subset of the above (an earlier version of this verifier ran only
`check_type_param_scope` on use-site type arguments, and never ran a
depth check at all outside that one call site, leaving a
`Ty::Error`/unresolved `Ty::Var`/unknown-declaration/wrong-nested-arity/
over-depth type unchecked at every other root: fields, payloads,
signatures, and instruction result types alike).
`check_type_root` validates depth *first*: past `MAX_GENERIC_DEPTH`, it
reports a dedicated, single diagnostic (`V0035`, `GENERIC_DEPTH_EXCEEDED`)
for the whole root — never one per nested level — and skips the
remaining checks below for that root entirely, rather than falling
through to the silent early return every one of them still falls back to
past this same bound, as defense in depth for any caller that does not
go through `check_type_root`.

A type parameter that is declared but genuinely never occurs in any
field, payload, parameter, or return type (a "phantom" parameter, e.g.
`record Marker[T] { tag: i64 }`) is accepted — the verifier never
requires every declared parameter to actually occur anywhere; it is only
required to be applied consistently at every reference to the
declaration.

Malformed hand-built NIR that exercises any of the above (the only way
most of it is reachable at all — a well-typed program lowered normally
satisfies every one of these by construction) fails with one or more
`V`-code diagnostics and never reaches interpretation, matching every
other structural invariant this verifier already enforced before this
milestone. This never relies on the parser, HIR, type checker, or
lowering having already rejected the type — every one of these roots is
itself a `verify_module` entry point that hand-built NIR reaches
directly, bypassing every earlier stage.

## Infinite generic aggregate layouts

A cycle is detected *after* substituting the concrete type arguments
flowing through each aggregate edge — not by following an applied type's
bare declaration alone, which cannot see a cycle mediated through a
generic parameter:

```napitia
record Box[T] { value: T }
record Node { next: Box[Node] }   // T0020: infinite (Node -> Box[Node] -> Node)
```

`typeck::cycles::check_cycles` traverses *instances*
(`GenericInstanceKey`-shaped: a declaration plus its own concrete
arguments at this point in the traversal), not bare declarations, so the
same declaration instantiated two different ways is correctly treated as
two different graph nodes. Each declaration's own traversal starts from
its "generic self" (`Ty::Param(id)` for each of its own parameters, or no
arguments at all if non-generic), and an edge substitutes the current
instance's own arguments into the field/payload type before following
it — this is what lets `Box[T] { value: T }` alone be correctly judged
non-cyclic (its own field is just `T`, contributing no edge) while
`Node { next: Box[Node] }`'s traversal (which substitutes `T = Node`)
correctly closes the cycle back to `Node` itself. The classic head-only
cases (`Node[T] { next: Node[T] }`, `List[T] { Cons(T, List[T]), Nil }`)
are still caught, immediately, as a self-loop on the starting instance.

A layout that never repeats an *exact* instance but keeps substituting a
growing argument instead (`record Wrap[T] { inner: Wrap[Box[T]] }`) is
exactly as unlayoutable as a literal cycle, and is caught the same
structural way, immediately: a *declaration* (`ItemId`, regardless of its
own current arguments) reappearing anywhere on the currently-active
traversal path is itself the proof of an infinite layout — `Wrap`
reappears the moment its own first field is substituted, at the very
first step, long before any numeric bound would matter. This is
deliberately **not** a depth/length limit on the path itself: an earlier
version of this check used `path.len() >= MAX_GENERIC_DEPTH` as a proxy
for "infinite," which incorrectly rejected every sufficiently long but
genuinely *finite* chain of distinct aggregate declarations —
`MAX_GENERIC_DEPTH` bounds nested type-*application* syntax/substitution
depth (how deeply `Box[Maybe[...]]]` may itself nest), not how many
aggregate declarations a containment graph may legitimately contain. A
chain of over a hundred distinct, non-recurring declarations terminating
in a primitive is accepted regardless of its length; only an actual
declaration recurrence — whether via the exact same instantiation
(`Node` closing back to `Node`) or a different, even strictly larger one
(`Wrap[T]` closing back to `Wrap[Box[T]]`) — is ever reported.

The reported cycle's own starting point is canonicalized to the member
with the smallest `ItemId` (rotating both the displayed path and which
edge is described as "closing" it), so which declaration a cycle is
shown starting from never depends on which one the outer traversal
(declaration order) happened to visit first. The traversal itself is
iterative (an explicit stack, never native recursion), deterministic
(declaration order, never `HashMap` iteration order), and
`Black`-memoized across starting points so the same already-fully-explored
subtree is never re-walked.

## Determinism

Every determinism property established by prior milestones still holds,
extended to the new surface area:

- `GenericInstanceKey`'s structural `Eq`/`Hash` never depend on traversal
  or insertion order.
- Textual NIR's declared/applied type-parameter brackets print in stable
  declaration order, never a `HashMap`'s iteration order, and are
  byte-identical across repeated compiles of the same program.
- The infinite-layout traversal's reported path, and which declaration
  its cycle is canonicalized to start from, are both a deterministic
  function of declaration order, independent of `HashMap` iteration —
  there is no depth-budget diagnostic to be deterministic about, since
  cycle detection is purely structural (see "Infinite generic aggregate
  layouts" above).
- Aliases never appear in generic diagnostics or textual NIR — every name
  comes from `ItemRegistry`'s canonical qualified name, exactly as
  established in `rfcs/0007`.

## Limits

Two shared, named constants in `crate::limits`, enforced independently by
every stage that walks a nested type application (never trusting an
earlier stage to have already bounded the input, since `hir::lower`,
`typeck`, `nir::lower_module`, `nir::verify_module`, and the parser are
all public entry points a caller can invoke directly):

```rust
pub(crate) const MAX_GENERIC_DEPTH: usize = 64;
pub(crate) const MAX_GENERIC_INSTANCES: usize = 4096;
```

`MAX_GENERIC_DEPTH` bounds *nested type-application syntax/substitution
depth* — how many levels deep a single `Ty::Applied` may nest
(`Box[Maybe[i64]]` is two levels) — never the number of distinct
declarations a structure may pass through: parsing a type application
(`parse_type_arg_list`, `P0001`, exercised exactly at the limit and one
past it); `hir::lower`'s own type-application resolution (`R0019`);
`typeck::unify`'s recursion into nested `Ty::Applied` arguments;
`nir::verify`'s `check_type_root` depth check (`V0035`), run over every
type root the verifier inspects — record fields, variant payloads,
function parameters/return types, instruction result types, and use-site
type arguments alike — and every other recursive check in that module;
every recursive display walk in
`nir::printer` and `types::display_ty`. `typeck::cycles`'s infinite-
layout detection (`T0020`) is a deliberate exception: it does *not* use
this constant to bound the number of aggregate declarations a
containment graph may legitimately contain (a long but finite chain of
over a hundred distinct declarations is accepted regardless of its
length) — see "Infinite generic aggregate layouts" above for the
structural (declaration-recurrence) rule it uses instead.
`MAX_GENERIC_INSTANCES` bounds the total number of distinct
`GenericInstanceKey`s one compilation may record (`T0028`).

## Required examples

Ten fixtures exercising the required scenarios end-to-end through the
real `napitia` binary or the interpreter directly (`compiler/tests/`,
`examples/`): generic identity; a generic `Box[T]` inferring its own
`unwrap` call; a generic `Maybe[T]` with an exhaustive `bool` match;
`Box[Maybe[i64]]` nesting; a cross-module generic alias
(`generic_variant_alias_exhaustive`); two same-named generic records from
different modules; invalid generic arity; an inference conflict; an
infinite generic layout; and generic expansion budget protection. At
least one valid end-to-end example (`unwrap(Box[i64] { value: 42 })`,
`identity[i64](42)`) returns `42`.

## Diagnostic codes

New this milestone:

```text
R0016  duplicate type parameter name in one declaration
R0017  primitive name used as a type parameter
R0018  a type parameter given its own type arguments
R0019  type application nested past the generic depth limit
R0020  invalid type application (value used as type, or vice versa)

T0022  type arguments applied to a non-generic declaration, or a raw
       reference to one that is generic
T0023  a generic declaration referenced without required type arguments
T0024  wrong number of (explicit) type arguments
T0025  conflicting inferred type arguments across occurrences
T0026  a type argument could not be inferred from any argument
T0027  an operation not proven safe for an unconstrained type parameter
T0028  the generic instance budget was exceeded
T0020  an infinite generic aggregate layout (shared with the
       pre-existing, non-generic infinite-layout diagnostic)

V0031  generic arity mismatch (a call, construction, or applied type)
V0032  a symbolic type parameter escaping its owning declaration
V0033  a generic declaration referenced without type arguments
V0034  a declaration's own type parameter list contains a duplicate
V0035  a type root (field, payload, parameter, return type, instruction
       result type, or use-site type argument) nested past the generic
       depth limit
```

## Honest limitations

- Type-argument inference from a *bare* integer/float literal argument
  whose own type is still an undefaulted inference variable does not
  resolve (`identity(42)` for `func identity[T](x: T) -> T` reports
  `T0026`, "cannot infer"). This is a pre-existing gap in how literal
  defaulting interacts with generic inference, not introduced by this
  milestone — inferring from an already-concretely-typed argument (a
  parameter, a field, an explicitly-typed local) works correctly, and
  every worked example in this document and the required-examples list
  avoids the bare-literal case (`identity[i64](42)`, or a value already
  constructed as `Box[i64]`).
- A record/variant field or function parameter literally named `value`
  fails to parse (`value` collides with the statement keyword that
  introduces a binding), independent of generics — a pre-existing parser
  gap, not new to this milestone, worked around throughout this
  milestone's own examples/fixtures by using a different field name
  (`payload`) instead.
- No native-code monomorphization exists: NIR remains fully parametric,
  and there is no per-instantiation specialized machine code. The
  `GenericInstanceKey` design is deliberately reusable for a future
  selective-specialization pass, but nothing here implements one.
- Protocols/trait-style constraints on a type parameter do not exist
  (Alpha 0.1.5+); the only operations available on an unconstrained `T`
  are the unconditionally-safe ones listed above.
- `Terminator::Switch`'s textual NIR prints its scrutinee variant as
  `@Variant#id` without a bracketed type-argument suffix, unlike every
  other generic-carrying instruction — an accepted minor display
  simplification (the scrutinee's own value already carries its full
  `Ty::Applied` for verification purposes; only the terminator's printed
  form omits it), not a correctness gap.
