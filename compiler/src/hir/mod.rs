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

pub use lower::lower_module;

use crate::lexer::IntBase;
use crate::source::Span;
use crate::symbol::Symbol;
use crate::syntax::ast::{AssignOp, BinaryOp, Ident, Path, Type, UnaryOp};

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

#[derive(Debug, Clone, Default)]
pub struct HirModule {
    pub functions: Vec<HirFunction>,
    /// `record`/`variant`/`protocol`/`extend`/`import` items. Alpha 0.1
    /// resolves and duplicate-checks their names but does not lower
    /// their bodies further (`spec/0003`): full support depends on
    /// generics and protocol conformance checking, neither implemented
    /// yet.
    pub other_items: Vec<OtherItem>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OtherItemKind {
    Record,
    Variant,
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

#[derive(Debug, Clone)]
pub struct HirFunction {
    pub id: ItemId,
    pub name: Symbol,
    pub name_span: Span,
    pub params: Vec<HirParam>,
    pub return_type: Option<Type>,
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
    pub ty: Type,
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
    pub ty: Option<Type>,
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
        ty: Type,
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
    /// A name that failed to resolve, or an expression the parser could
    /// not build. A diagnostic has already been recorded; later stages
    /// must skip this node rather than type-check it.
    Error {
        id: ExprId,
        span: Span,
    },
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
        span: Span,
    },
    /// Binds a fresh local for the arm body. A bare identifier pattern
    /// is always treated as a new binding in this milestone rather than
    /// a payload-less variant match — distinguishing the two requires
    /// resolving against a real variant definition, which is accepted
    /// direction, not implemented (`spec/0003`).
    Bind {
        local: LocalId,
        name: Symbol,
        span: Span,
    },
    Variant {
        name: Symbol,
        args: Vec<HirPattern>,
        span: Span,
    },
    Int {
        value: u128,
        span: Span,
    },
    Str {
        value: String,
        span: Span,
    },
    Char {
        value: char,
        span: Span,
    },
    Bool {
        value: bool,
        span: Span,
    },
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
            | HirExpr::Error { id, .. } => *id,
            HirExpr::Block(block) => block.id,
        }
    }
}
