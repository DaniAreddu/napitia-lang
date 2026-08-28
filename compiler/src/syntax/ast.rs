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

/// A named type reference: a primitive or user record/variant name, with
/// an optional bracketed type-argument list (`Box[i64]`,
/// `Pair[i64, str]`, `Box[Maybe[i64]]` -- `rfcs/0008`). `args` is empty
/// for a plain (non-generic-application) reference; `owned`/`borrow`/
/// `shared` annotations are still not part of the grammar (`spec/0002`).
#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub name: Ident,
    pub args: Vec<Type>,
    /// The full reference's span -- `name`'s own span when there is no
    /// `[...]`, or `name` joined through the closing `]` when there is.
    /// Kept distinct from `name.span` so an arity/application diagnostic
    /// can underline the whole `Name[Args]`, not just `Name`.
    pub span: Span,
}

impl Type {
    pub fn span(&self) -> Span {
        self.span
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
    Resource(ResourceDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDecl {
    pub public: bool,
    pub name: Ident,
    /// `[T, U]` after the function name, if any (`rfcs/0008`). Empty for
    /// an ordinary, non-generic function.
    pub type_params: Vec<Ident>,
    pub params: Vec<Param>,
    pub return_type: Option<Type>,
    /// A `uses` clause's own entries, in source order. Each entry is
    /// either a bare dotted effect path with no bracketed arguments
    /// (`Database.Read` -- `spec/0005`, parsed but never checked; out of
    /// scope for `rfcs/0009`) or a single name with a bracketed
    /// type-argument list (`Equal[T]` -- `rfcs/0009`'s capability
    /// requirement, fully checked). Which of the two a given entry is
    /// isn't decided here; `UsesClause::args` being non-empty is what
    /// distinguishes them everywhere downstream.
    pub uses: Vec<UsesClause>,
    /// Error names from a `raises` clause. Parsed, not yet checked
    /// (`spec/0005`).
    pub raises: Vec<Ident>,
    pub body: Block,
    pub span: Span,
}

/// One entry in a `uses` clause. `Database.Read` (a pre-existing,
/// still-unchecked effect declaration, `spec/0005`) and `Equal[T]` (a
/// `rfcs/0009` capability requirement) share this one production: the
/// only grammatical difference is whether a bracketed type-argument list
/// follows the (always single-segment, for a requirement) name.
#[derive(Debug, Clone, PartialEq)]
pub struct UsesClause {
    pub path: Path,
    /// `[T]` in `Equal[T]` -- empty for a bare effect path.
    pub args: Vec<Type>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Ident,
    pub ty: Type,
    /// Whether this parameter was declared `take file: File` (`rfcs/0011`)
    /// -- an ownership-transferring parameter, moving the caller's own
    /// argument in, rather than an ordinary call-scoped observation.
    /// Meaningless (but harmlessly `false`) for a non-resource type.
    pub take: bool,
    pub span: Span,
}

/// `resource File { descriptor: i64 }` (`rfcs/0011`): an affine,
/// non-copyable nominal aggregate. Reuses `Field`'s own grammar
/// unchanged -- construction (`File { descriptor: 3 }`) is the same
/// `RecordLiteral` production a `record` construction already uses.
/// Deliberately has no `type_params`: generic resources are out of
/// scope this milestone (`rfcs/0011`'s own non-goals).
#[derive(Debug, Clone, PartialEq)]
pub struct ResourceDecl {
    pub public: bool,
    pub name: Ident,
    pub fields: Vec<Field>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordDecl {
    pub public: bool,
    pub name: Ident,
    /// See [`FunctionDecl::type_params`].
    pub type_params: Vec<Ident>,
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
    /// See [`FunctionDecl::type_params`].
    pub type_params: Vec<Ident>,
    pub cases: Vec<Case>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Case {
    pub name: Ident,
    pub payload: Vec<Type>,
    pub span: Span,
}

/// `protocol Equal[T] { func equal(left: T, right: T) -> bool; }`
/// (`rfcs/0009`). A capability protocol, not a Rust trait/Java
/// interface/Go interface: it declares explicit type parameters, its
/// methods are signatures only (no bodies, no default implementation),
/// and there is no implicit receiver or `Self` -- every parameter is
/// ordinary and explicit.
#[derive(Debug, Clone, PartialEq)]
pub struct ProtocolDecl {
    pub public: bool,
    pub name: Ident,
    /// `[T, U]` after the protocol name -- at least one, required
    /// (`rfcs/0009`); a protocol with none is rejected.
    pub type_params: Vec<Ident>,
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

/// `extend Equal[i64] { ... }` or `extend[T] Equal[Box[T]] uses
/// Equal[T] { ... }` (`rfcs/0009`) -- a concrete or conditional
/// implementation of `protocol`'s type argument(s). `type_params` are
/// only ever those explicitly declared in `extend[...]`; an unknown name
/// appearing in `protocol`'s own argument list is never silently treated
/// as an implicit parameter.
#[derive(Debug, Clone, PartialEq)]
pub struct ExtendDecl {
    pub type_params: Vec<Ident>,
    /// The `Equal[i64]`/`Equal[Box[T]]` head: reuses `Type`'s own
    /// name-plus-bracketed-arguments shape, since a protocol reference
    /// here is syntactically identical to a type application.
    pub protocol: Type,
    /// `uses Equal[T], ...` between the head and `{` -- this extension's
    /// own capability requirements, in source order.
    pub uses: Vec<UsesClause>,
    pub functions: Vec<FunctionDecl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImportDecl {
    pub path: Path,
    /// The optional `as <alias>` clause -- a local name for the
    /// importing module only (`rfcs/0007`), carrying its own span
    /// distinct from `path`'s last segment (the imported item's own
    /// declared name).
    pub alias: Option<Ident>,
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
    Defer {
        expr: Expr,
        span: Span,
    },
    /// `drop file;` (`rfcs/0011`): consumes a live resource immediately.
    Drop {
        expr: Expr,
        span: Span,
    },
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
    /// `TypeName { field: expr, ... }`. Only a bare identifier (with an
    /// optional `[Args]` type-application) followed directly by `{` in a
    /// position where struct literals are allowed (see `Parser`'s
    /// `no_struct_literal` flag) parses as this; `{` in every other
    /// postfix/primary position is a block.
    RecordLiteral {
        type_name: Ident,
        /// `[i64]`/`[i64, str]` written directly after `type_name`, if
        /// any (`rfcs/0008`). Empty for a non-generic record.
        type_args: Vec<Type>,
        fields: Vec<FieldInit>,
        span: Span,
    },
    /// An identifier immediately followed by a bracketed type-argument
    /// list in a non-record-literal position (`identity[i64]`,
    /// `Maybe[i64]` as the base of `.Some(...)`) -- `rfcs/0008`. Type
    /// arguments bind tighter than the postfix `.`/`(...)` that follows,
    /// so `Maybe[i64].Some(42)` parses as
    /// `Call(Field(TypeApply(Ident(Maybe), [i64]), Some), [42])`.
    TypeApply {
        base: Box<Expr>,
        args: Vec<Type>,
        span: Span,
    },
    /// `raise <expr>` (`rfcs/0010`). Always type `never`; `expr` must
    /// resolve to one of the current function's own declared `raises`
    /// variants (checked later, not here).
    Raise {
        operand: Box<Expr>,
        span: Span,
    },
    /// `handle <expr> { success ... , failure ... }` (`rfcs/0010`).
    Handle(Box<HandleExpr>),
    /// A malformed expression the parser recovered from. Carries no
    /// value; later stages must skip it rather than type-check it.
    Error {
        span: Span,
    },
}

/// `rfcs/0010`: consumes a fallible expression exhaustively.
#[derive(Debug, Clone, PartialEq)]
pub struct HandleExpr {
    pub operand: Box<Expr>,
    pub arms: Vec<HandleArm>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum HandleArm {
    /// `success <pattern> => <body>` -- exactly one is required per
    /// `handle`; `pattern` is checked later to be a bare bind or `_`.
    Success {
        pattern: Pattern,
        body: MatchArmBody,
        span: Span,
    },
    /// `failure <FailurePattern> => <body>`.
    Failure {
        pattern: FailurePattern,
        body: MatchArmBody,
        span: Span,
    },
}

/// A `handle` failure arm's own pattern -- not an ordinary [`Pattern`]
/// because it must be able to name *which* raised type a case belongs to
/// (`Type.Case`), unlike an ordinary `match`, whose single scrutinee type
/// already pins that down.
#[derive(Debug, Clone, PartialEq)]
pub enum FailurePattern {
    /// `_` -- a final catch-all for every raised case not otherwise
    /// named, binding no value (a raised value's type varies by which
    /// case actually occurred, so there is nothing uniform to bind).
    Wildcard { span: Span },
    /// `ErrorType.Case` or `ErrorType.Case(pattern, ...)`.
    Case {
        error_type: Ident,
        case: Ident,
        args: Vec<Pattern>,
        span: Span,
    },
}

/// One `field: expr` entry in a [`Expr::RecordLiteral`].
#[derive(Debug, Clone, PartialEq)]
pub struct FieldInit {
    pub name: Ident,
    pub value: Expr,
    pub span: Span,
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
            | Expr::RecordLiteral { span, .. }
            | Expr::TypeApply { span, .. }
            | Expr::Raise { span, .. }
            | Expr::Error { span } => *span,
            Expr::Ident(ident) => ident.span,
            Expr::If(if_expr) => if_expr.span,
            Expr::Match(match_expr) => match_expr.span,
            Expr::Block(block) => block.span,
            Expr::Handle(handle_expr) => handle_expr.span,
        }
    }
}

impl HandleArm {
    pub fn span(&self) -> Span {
        match self {
            HandleArm::Success { span, .. } | HandleArm::Failure { span, .. } => *span,
        }
    }
}

impl FailurePattern {
    pub fn span(&self) -> Span {
        match self {
            FailurePattern::Wildcard { span } | FailurePattern::Case { span, .. } => *span,
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
