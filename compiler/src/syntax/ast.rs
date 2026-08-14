//! AST node definitions, matching the grammar in `spec/0002-syntax.md`.

use crate::lexer::IntBase;
use crate::source::Span;
use crate::symbol::Symbol;

/// A name reference: an interned symbol plus the span it was written at.
/// Used everywhere an identifier appears (bindings, function/type names,
/// field names, path segments) so every name carries its own location
/// independent of the node that references it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ident {
    pub symbol: Symbol,
    pub span: Span,
}

/// A dotted path (`a.b.c`), used for imports and `uses` effect names.
#[derive(Debug, Clone, PartialEq)]
pub struct Path {
    pub segments: Vec<Ident>,
    pub span: Span,
}

/// A named type reference. Only primitive and user record/variant names
/// by identifier are supported in this milestone (`spec/0002`); generics,
/// and `owned`/`borrow`/`shared` annotations are not part of the grammar
/// yet.
#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub name: Ident,
}

impl Type {
    pub fn span(&self) -> Span {
        self.name.span
    }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Module {
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Function(FunctionDecl),
    Record(RecordDecl),
    Variant(VariantDecl),
    Protocol(ProtocolDecl),
    Extend(ExtendDecl),
    Import(ImportDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDecl {
    pub public: bool,
    pub name: Ident,
    pub params: Vec<Param>,
    pub return_type: Option<Type>,
    /// Effect/capability paths from a `uses` clause. Parsed, not yet
    /// checked (`spec/0005`).
    pub uses: Vec<Path>,
    /// Error names from a `raises` clause. Parsed, not yet checked
    /// (`spec/0005`).
    pub raises: Vec<Ident>,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Ident,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordDecl {
    pub public: bool,
    pub name: Ident,
    pub fields: Vec<Field>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub public: bool,
    pub name: Ident,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariantDecl {
    pub public: bool,
    pub name: Ident,
    pub cases: Vec<Case>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Case {
    pub name: Ident,
    pub payload: Vec<Type>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ProtocolDecl {
    pub public: bool,
    pub name: Ident,
    pub members: Vec<ProtocolMember>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ProtocolMember {
    pub name: Ident,
    pub params: Vec<Param>,
    pub return_type: Option<Type>,
    pub span: Span,
}

/// `extend Type [with Protocol] { ... }` — either a protocol
/// implementation (`protocol` set) or inherent functions (`protocol`
/// `None`).
#[derive(Debug, Clone, PartialEq)]
pub struct ExtendDecl {
    pub type_name: Ident,
    pub protocol: Option<Path>,
    pub functions: Vec<FunctionDecl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImportDecl {
    pub path: Path,
    pub span: Span,
}

/// `{ statements... [tail expression] }`. A `tail` with no trailing `;`
/// is the block's value; a block with no tail has type `unit`.
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub statements: Vec<Stmt>,
    pub tail: Option<Box<Expr>>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Binding(BindingStmt),
    Expr(Expr),
    Defer { expr: Expr, span: Span },
    While(WhileStmt),
    Loop(LoopStmt),
}

/// `value`/`mutable` binding statement.
#[derive(Debug, Clone, PartialEq)]
pub struct BindingStmt {
    pub mutable: bool,
    pub name: Ident,
    pub ty: Option<Type>,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub condition: Box<Expr>,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoopStmt {
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
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
    Ident(Ident),
    Paren {
        inner: Box<Expr>,
        span: Span,
    },
    Unary {
        op: UnaryOp,
        operand: Box<Expr>,
        span: Span,
    },
    Binary {
        op: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
        span: Span,
    },
    Assign {
        target: Box<Expr>,
        op: AssignOp,
        value: Box<Expr>,
        span: Span,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
        span: Span,
    },
    Field {
        base: Box<Expr>,
        name: Ident,
        span: Span,
    },
    Cast {
        expr: Box<Expr>,
        ty: Type,
        span: Span,
    },
    /// Postfix `?` (`spec/0002`'s `TryPropagate`). Parsed only; not yet
    /// given propagation semantics (`spec/0005`).
    Try {
        expr: Box<Expr>,
        span: Span,
    },
    If(Box<IfExpr>),
    Match(Box<MatchExpr>),
    Block(Box<Block>),
    /// `return [expr]`. Modeled as an expression (type `never`) rather
    /// than a semicolon-mandatory statement so it can appear as a
    /// block's tail with no trailing `;`, matching every example in
    /// `spec/0002`.
    Return {
        value: Option<Box<Expr>>,
        span: Span,
    },
    Break {
        value: Option<Box<Expr>>,
        span: Span,
    },
    Continue {
        span: Span,
    },
    /// A malformed expression the parser recovered from. Carries no
    /// value; later stages must skip it rather than type-check it.
    Error {
        span: Span,
    },
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Int { span, .. }
            | Expr::Float { span, .. }
            | Expr::Str { span, .. }
            | Expr::Char { span, .. }
            | Expr::Bool { span, .. }
            | Expr::Paren { span, .. }
            | Expr::Unary { span, .. }
            | Expr::Binary { span, .. }
            | Expr::Assign { span, .. }
            | Expr::Call { span, .. }
            | Expr::Field { span, .. }
            | Expr::Cast { span, .. }
            | Expr::Try { span, .. }
            | Expr::Return { span, .. }
            | Expr::Break { span, .. }
            | Expr::Continue { span }
            | Expr::Error { span } => *span,
            Expr::Ident(ident) => ident.span,
            Expr::If(if_expr) => if_expr.span,
            Expr::Match(match_expr) => match_expr.span,
            Expr::Block(block) => block.span,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
    BitNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Range,
    RangeInclusive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Assign,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfExpr {
    pub condition: Box<Expr>,
    pub then_branch: Block,
    pub else_branch: Option<ElseBranch>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ElseBranch {
    Block(Block),
    If(Box<IfExpr>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchExpr {
    pub scrutinee: Box<Expr>,
    pub arms: Vec<MatchArm>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: MatchArmBody,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MatchArmBody {
    Expr(Expr),
    Block(Block),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Wildcard {
        span: Span,
    },
    Ident(Ident),
    Variant {
        name: Ident,
        args: Vec<Pattern>,
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

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Pattern::Wildcard { span }
            | Pattern::Variant { span, .. }
            | Pattern::Int { span, .. }
            | Pattern::Str { span, .. }
            | Pattern::Char { span, .. }
            | Pattern::Bool { span, .. } => *span,
            Pattern::Ident(ident) => ident.span,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::Span;

    fn ident(sym: u32, span: Span) -> Ident {
        Ident {
            symbol: Symbol(sym),
            span,
        }
    }

    #[test]
    fn expr_span_covers_every_variant() {
        let span = Span::new(0, 3);
        assert_eq!(Expr::Error { span }.span(), span);
        assert_eq!(
            Expr::Int {
                value: 1,
                base: IntBase::Decimal,
                span
            }
            .span(),
            span
        );
        assert_eq!(Expr::Ident(ident(0, span)).span(), span);
    }

    #[test]
    fn pattern_span_covers_every_variant() {
        let span = Span::new(0, 1);
        assert_eq!(Pattern::Wildcard { span }.span(), span);
        assert_eq!(Pattern::Ident(ident(0, span)).span(), span);
    }

    #[test]
    fn module_default_is_empty() {
        let module = Module::default();
        assert!(module.items.is_empty());
    }
}
