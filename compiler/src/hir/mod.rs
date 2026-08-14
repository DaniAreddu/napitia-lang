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
use crate::syntax::ast::{AssignOp, BinaryOp, Type, UnaryOp};

/// Identifies a module-level item (function, record, variant, protocol,
/// extend, or import) for the lifetime of one compilation session.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ItemId(pub(crate) u32);

/// Identifies a local binding (a function parameter, a `value`/`mutable`
/// statement, or a pattern-bound name in a `match` arm) within one
/// function.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub(crate) u32);

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
        value: u128,
        base: IntBase,
        span: Span,
    },
    Float {
        value: f64,
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
    /// A resolved reference to a local binding (parameter, `value`/
    /// `mutable` statement, or pattern-bound match name).
    Local {
        local: LocalId,
        name: Symbol,
        span: Span,
    },
    /// A resolved reference to a module-level function.
    Function {
        item: ItemId,
        name: Symbol,
        span: Span,
    },
    Unary {
        op: UnaryOp,
        operand: Box<HirExpr>,
        span: Span,
    },
    Binary {
        op: BinaryOp,
        left: Box<HirExpr>,
        right: Box<HirExpr>,
        span: Span,
    },
    Assign {
        target: Box<HirExpr>,
        op: AssignOp,
        value: Box<HirExpr>,
        span: Span,
    },
    Call {
        callee: Box<HirExpr>,
        args: Vec<HirExpr>,
        span: Span,
    },
    /// Field access. The field name is not resolved against a record
    /// definition in this milestone (`spec/0003`).
    Field {
        base: Box<HirExpr>,
        name: Symbol,
        span: Span,
    },
    Cast {
        expr: Box<HirExpr>,
        ty: Type,
        span: Span,
    },
    /// Postfix `?`. Parsed and resolved, not yet given propagation
    /// semantics (`spec/0005`).
    Try {
        expr: Box<HirExpr>,
        span: Span,
    },
    If {
        condition: Box<HirExpr>,
        then_branch: HirBlock,
        else_branch: Option<HirElse>,
        span: Span,
    },
    Match {
        scrutinee: Box<HirExpr>,
        arms: Vec<HirMatchArm>,
        span: Span,
    },
    Block(Box<HirBlock>),
    Return {
        value: Option<Box<HirExpr>>,
        span: Span,
    },
    Break {
        value: Option<Box<HirExpr>>,
        span: Span,
    },
    Continue {
        span: Span,
    },
    /// A name that failed to resolve, or an expression the parser could
    /// not build. A diagnostic has already been recorded; later stages
    /// must skip this node rather than type-check it.
    Error {
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
            | HirExpr::Continue { span }
            | HirExpr::Error { span } => *span,
            HirExpr::Block(block) => block.span,
        }
    }
}
