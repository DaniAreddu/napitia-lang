//! The High-level IR (HIR): AST with names resolved to stable IDs.
//!
//! HIR mirrors the AST's shape closely — this milestone lowers AST to
//! HIR and resolves names in the same pass (`lower.rs`) rather than as
//! two separate walks — but replaces every name *reference* with a
//! resolved [`LocalId`] or [`ItemId`], and gives every item a stable ID.
//! There is no global mutable symbol table: resolution state lives in
//! the [`crate::resolve::Scopes`] stack used only while lowering one
//! module.

pub mod lower;
pub mod registry;

pub use lower::{
    IdCursor, ImportedItem, ImportedItemKind, lower_module, lower_module_with_imports,
};
pub use registry::{ItemIdentity, ItemKind, ItemRegistry};

use crate::lexer::IntBase;
use crate::source::{SourceId, Span};
use crate::symbol::Symbol;
use crate::syntax::ast::{AssignOp, BinaryOp, Ident, Path, UnaryOp};

/// Identifies a module-level item (function, record, variant, protocol,
/// extend, or import) for the lifetime of one compilation session.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ItemId(pub(crate) u32);

/// Identifies a local binding (a function parameter, a `value`/`mutable`
/// statement, or a pattern-bound name in a `match` arm) within one
/// function.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub(crate) u32);

/// Identifies one HIR expression (or block, which carries its own
/// `ExprId` for the same reason) for the lifetime of one compilation
/// session. Deliberately not span-based: a synthesized or structurally
/// nested expression can share a span with another node, but two
/// `ExprId`s are never equal, so a map keyed by `ExprId` (`typeck`'s
/// `expr_types`) can't collide the way one keyed by span could.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExprId(pub(crate) u32);

/// Identifies one HIR pattern for the lifetime of one compilation
/// session, the same way [`ExprId`] identifies an expression: never
/// span-based, since a wildcard or binding pattern's span can coincide
/// with another node's, but two `PatternId`s are never equal. This is
/// what lets `typeck` key its per-pattern resolution maps (resolved
/// case/type, per-pattern local bindings) on identity rather than span.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PatternId(pub(crate) u32);

/// Which kind of declaration an [`HirType::Aggregate`] reference
/// resolved to -- carried so a diagnostic can say "record" or "variant"
/// without a second identity lookup.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AggregateKind {
    Record,
    Variant,
}

/// A type reference, resolved against the *declaring* module's own type
/// namespace at HIR-lowering time -- before modules are merged, and
/// never re-derived later from a project-global surface name
/// (`rfcs/0006`'s module-namespace isolation). A name that matched a
/// declared `record`/`variant` in this module's own namespace (declared
/// locally, or reached via a successful `import`) resolves to the exact
/// declaration's `ItemId` here; a name that didn't is left `Unresolved`
/// for typeck to check against the primitive namespace, or reject as
/// genuinely unknown (`T0006`) -- HIR lowering itself has no notion of
/// primitive types.
#[derive(Debug, Clone)]
pub enum HirType {
    Aggregate {
        item: ItemId,
        kind: AggregateKind,
        name: Symbol,
        span: Span,
    },
    Unresolved {
        name: Symbol,
        span: Span,
    },
}

impl HirType {
    pub fn span(&self) -> Span {
        match self {
            HirType::Aggregate { span, .. } | HirType::Unresolved { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct HirModule {
    pub functions: Vec<HirFunction>,
    pub records: Vec<HirRecord>,
    pub variants: Vec<HirVariant>,
    /// `protocol`/`extend`/`import` items. Alpha 0.1 resolves and
    /// duplicate-checks their names but does not lower their bodies
    /// further (`spec/0003`): full support depends on generics and
    /// protocol conformance checking, neither implemented yet.
    pub other_items: Vec<OtherItem>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OtherItemKind {
    Protocol,
    Extend,
    Import,
}

#[derive(Debug, Clone)]
pub struct OtherItem {
    pub id: ItemId,
    pub name: Symbol,
    pub span: Span,
    pub kind: OtherItemKind,
}

/// A resolved `record` declaration: its full field list, in declaration
/// order (the order runtime layout follows), each field's name already
/// checked for duplicates against its siblings.
#[derive(Debug, Clone)]
pub struct HirRecord {
    pub id: ItemId,
    pub name: Symbol,
    pub span: Span,
    /// The module this record was declared in, always the source
    /// `hir::lower_module` (or `lower_module_with_imports`) actually ran
    /// against -- never the source of whatever other module a merged
    /// multi-module compilation happens to be checking a reference from.
    /// Every diagnostic about this record (a field-visibility
    /// violation, a public-API leak) is reported against this source,
    /// not the accessing site's.
    pub source: SourceId,
    /// Whether this record itself may be imported from another module
    /// (`rfcs/0006`); irrelevant to single-file compilation.
    pub public: bool,
    pub fields: Vec<HirField>,
}

#[derive(Debug, Clone)]
pub struct HirField {
    pub name: Symbol,
    pub span: Span,
    /// Whether this field may be read or initialized from outside its
    /// record's own declaring module (`rfcs/0006`); irrelevant to
    /// single-file compilation, where every field is always accessible.
    pub public: bool,
    /// Resolved against this record's own declaring module's namespace
    /// at HIR-lowering time -- see [`HirType`].
    pub ty: HirType,
}

/// A resolved `variant` declaration: its full case list, in declaration
/// order, each case's name already checked for duplicates.
#[derive(Debug, Clone)]
pub struct HirVariant {
    pub id: ItemId,
    pub name: Symbol,
    pub span: Span,
    /// See [`HirRecord::source`].
    pub source: SourceId,
    /// See [`HirRecord::public`].
    pub public: bool,
    pub cases: Vec<HirCase>,
}

#[derive(Debug, Clone)]
pub struct HirCase {
    pub name: Symbol,
    pub span: Span,
    /// Positional payload types, in declaration order; empty for a
    /// payload-less (unit) case.
    pub payload: Vec<HirType>,
}

#[derive(Debug, Clone)]
pub struct HirFunction {
    pub id: ItemId,
    pub name: Symbol,
    pub name_span: Span,
    /// See [`HirRecord::source`].
    pub source: SourceId,
    /// See [`HirRecord::public`].
    pub public: bool,
    pub params: Vec<HirParam>,
    pub return_type: Option<HirType>,
    /// Effect/capability paths from a `uses` clause, preserved as-parsed.
    /// Not semantically checked (`spec/0005`): the checker only reports
    /// a function declaring a non-empty clause as using an unsupported
    /// feature, rather than silently discarding it.
    pub uses: Vec<Path>,
    /// Error names from a `raises` clause, preserved as-parsed. Not
    /// semantically checked (`spec/0005`), same as `uses`.
    pub raises: Vec<Ident>,
    pub body: HirBlock,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct HirParam {
    pub local: LocalId,
    pub name: Symbol,
    pub span: Span,
    pub ty: HirType,
}

#[derive(Debug, Clone)]
pub struct HirBlock {
    pub id: ExprId,
    pub statements: Vec<HirStmt>,
    pub tail: Option<Box<HirExpr>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum HirStmt {
    Binding(HirBinding),
    Expr(HirExpr),
    Defer {
        expr: HirExpr,
        span: Span,
    },
    While {
        condition: Box<HirExpr>,
        body: HirBlock,
        span: Span,
    },
    Loop {
        body: HirBlock,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub struct HirBinding {
    pub local: LocalId,
    pub name: Symbol,
    pub mutable: bool,
    pub ty: Option<HirType>,
    pub value: HirExpr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum HirExpr {
    Int {
        id: ExprId,
        value: u128,
        base: IntBase,
        span: Span,
    },
    Float {
        id: ExprId,
        value: f64,
        span: Span,
    },
    Str {
        id: ExprId,
        value: String,
        span: Span,
    },
    Char {
        id: ExprId,
        value: char,
        span: Span,
    },
    Bool {
        id: ExprId,
        value: bool,
        span: Span,
    },
    /// A resolved reference to a local binding (parameter, `value`/
    /// `mutable` statement, or pattern-bound match name).
    Local {
        id: ExprId,
        local: LocalId,
        name: Symbol,
        span: Span,
    },
    /// A resolved reference to a module-level function.
    Function {
        id: ExprId,
        item: ItemId,
        name: Symbol,
        span: Span,
    },
    /// A resolved reference to a variant case constructor (`Variant.Case`
    /// qualified, or a bare case name unambiguous across the module) --
    /// mirrors `Function` above. Used bare (a payload-less case) it is
    /// itself a complete value; as the callee of `Call` it constructs a
    /// payload-carrying case (`typeck`/`nir::lower` special-case a
    /// `Call` whose callee is a `CaseRef`, the same way they already
    /// special-case one whose callee is `Function`).
    CaseRef {
        id: ExprId,
        variant: ItemId,
        case: usize,
        name: Symbol,
        span: Span,
    },
    Unary {
        id: ExprId,
        op: UnaryOp,
        operand: Box<HirExpr>,
        span: Span,
    },
    Binary {
        id: ExprId,
        op: BinaryOp,
        left: Box<HirExpr>,
        right: Box<HirExpr>,
        span: Span,
    },
    Assign {
        id: ExprId,
        target: Box<HirExpr>,
        op: AssignOp,
        value: Box<HirExpr>,
        span: Span,
    },
    Call {
        id: ExprId,
        callee: Box<HirExpr>,
        args: Vec<HirExpr>,
        span: Span,
    },
    /// Field access. The field name is not resolved against a record
    /// definition in this milestone (`spec/0003`).
    Field {
        id: ExprId,
        base: Box<HirExpr>,
        name: Symbol,
        span: Span,
    },
    Cast {
        id: ExprId,
        expr: Box<HirExpr>,
        ty: HirType,
        span: Span,
    },
    /// Postfix `?`. Parsed and resolved, not yet given propagation
    /// semantics (`spec/0005`).
    Try {
        id: ExprId,
        expr: Box<HirExpr>,
        span: Span,
    },
    If {
        id: ExprId,
        condition: Box<HirExpr>,
        then_branch: HirBlock,
        else_branch: Option<HirElse>,
        span: Span,
    },
    Match {
        id: ExprId,
        scrutinee: Box<HirExpr>,
        arms: Vec<HirMatchArm>,
        span: Span,
    },
    Block(Box<HirBlock>),
    Return {
        id: ExprId,
        value: Option<Box<HirExpr>>,
        span: Span,
    },
    Break {
        id: ExprId,
        value: Option<Box<HirExpr>>,
        span: Span,
    },
    Continue {
        id: ExprId,
        span: Span,
    },
    /// `TypeName { field: expr, ... }`. `fields` preserves **source
    /// order** (the order evaluation actually happens in), each entry
    /// already resolved to its declaration index within `record` --
    /// runtime layout reorders into declaration order at NIR lowering
    /// time, never here.
    RecordLiteral {
        id: ExprId,
        record: ItemId,
        fields: Vec<HirFieldInit>,
        span: Span,
    },
    /// A name that failed to resolve, or an expression the parser could
    /// not build. A diagnostic has already been recorded; later stages
    /// must skip this node rather than type-check it.
    Error {
        id: ExprId,
        span: Span,
    },
}

/// One resolved `field: expr` entry in a [`HirExpr::RecordLiteral`].
#[derive(Debug, Clone)]
pub struct HirFieldInit {
    pub field_index: usize,
    pub value: HirExpr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum HirElse {
    Block(HirBlock),
    If(Box<HirExpr>),
}

#[derive(Debug, Clone)]
pub struct HirMatchArm {
    pub pattern: HirPattern,
    pub body: HirMatchArmBody,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum HirMatchArmBody {
    Expr(HirExpr),
    Block(HirBlock),
}

#[derive(Debug, Clone)]
pub enum HirPattern {
    Wildcard {
        id: PatternId,
        span: Span,
    },
    /// Binds a fresh local for the arm body, *unless* the name resolves
    /// (during `typeck`) to a payload-less variant case in the
    /// scrutinee's own variant type, in which case it matches that case
    /// instead of introducing a binding -- see `typeck`'s pattern
    /// checking. Lowering (both HIR and this pattern's own `local`)
    /// always mints a binding; `typeck` records the alternate
    /// case-match resolution separately when it applies, and NIR
    /// lowering consults that resolution, never `local` directly, to
    /// decide which one actually happened.
    Bind {
        id: PatternId,
        local: LocalId,
        name: Symbol,
        span: Span,
    },
    Variant {
        id: PatternId,
        name: Symbol,
        args: Vec<HirPattern>,
        span: Span,
    },
    Int {
        id: PatternId,
        value: u128,
        span: Span,
    },
    Str {
        id: PatternId,
        value: String,
        span: Span,
    },
    Char {
        id: PatternId,
        value: char,
        span: Span,
    },
    Bool {
        id: PatternId,
        value: bool,
        span: Span,
    },
}

impl HirPattern {
    pub fn id(&self) -> PatternId {
        match self {
            HirPattern::Wildcard { id, .. }
            | HirPattern::Bind { id, .. }
            | HirPattern::Variant { id, .. }
            | HirPattern::Int { id, .. }
            | HirPattern::Str { id, .. }
            | HirPattern::Char { id, .. }
            | HirPattern::Bool { id, .. } => *id,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            HirPattern::Wildcard { span, .. }
            | HirPattern::Bind { span, .. }
            | HirPattern::Variant { span, .. }
            | HirPattern::Int { span, .. }
            | HirPattern::Str { span, .. }
            | HirPattern::Char { span, .. }
            | HirPattern::Bool { span, .. } => *span,
        }
    }
}

impl HirExpr {
    pub fn span(&self) -> Span {
        match self {
            HirExpr::Int { span, .. }
            | HirExpr::Float { span, .. }
            | HirExpr::Str { span, .. }
            | HirExpr::Char { span, .. }
            | HirExpr::Bool { span, .. }
            | HirExpr::Local { span, .. }
            | HirExpr::Function { span, .. }
            | HirExpr::CaseRef { span, .. }
            | HirExpr::Unary { span, .. }
            | HirExpr::Binary { span, .. }
            | HirExpr::Assign { span, .. }
            | HirExpr::Call { span, .. }
            | HirExpr::Field { span, .. }
            | HirExpr::Cast { span, .. }
            | HirExpr::Try { span, .. }
            | HirExpr::If { span, .. }
            | HirExpr::Match { span, .. }
            | HirExpr::Return { span, .. }
            | HirExpr::Break { span, .. }
            | HirExpr::Continue { span, .. }
            | HirExpr::RecordLiteral { span, .. }
            | HirExpr::Error { span, .. } => *span,
            HirExpr::Block(block) => block.span,
        }
    }

    /// The stable identity typeck's `expr_types` (and any other
    /// per-expression map) keys on -- see [`ExprId`] for why this,
    /// rather than `span`, is the right key.
    pub fn id(&self) -> ExprId {
        match self {
            HirExpr::Int { id, .. }
            | HirExpr::Float { id, .. }
            | HirExpr::Str { id, .. }
            | HirExpr::Char { id, .. }
            | HirExpr::Bool { id, .. }
            | HirExpr::Local { id, .. }
            | HirExpr::Function { id, .. }
            | HirExpr::CaseRef { id, .. }
            | HirExpr::Unary { id, .. }
            | HirExpr::Binary { id, .. }
            | HirExpr::Assign { id, .. }
            | HirExpr::Call { id, .. }
            | HirExpr::Field { id, .. }
            | HirExpr::Cast { id, .. }
            | HirExpr::Try { id, .. }
            | HirExpr::If { id, .. }
            | HirExpr::Match { id, .. }
            | HirExpr::Return { id, .. }
            | HirExpr::Break { id, .. }
            | HirExpr::Continue { id, .. }
            | HirExpr::RecordLiteral { id, .. }
            | HirExpr::Error { id, .. } => *id,
            HirExpr::Block(block) => block.id,
        }
    }
}
