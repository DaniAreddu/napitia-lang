//! HIR-to-NIR lowering.
//!
//! Every local (parameter, `value`/`mutable` statement) gets a storage
//! slot and is accessed uniformly through `alloc`/`store`/`load`; NIR
//! does not construct phi nodes in this milestone (`spec/0006`). A
//! branching expression used as a value (`if`/`&&`/`||`) instead uses an
//! implicit temporary slot: each arm stores its result into the slot
//! before jumping to a shared merge block, which then loads it — the
//! same effect a phi node would have, without needing one.
//!
//! Lowering assumes its input already passed type-checking, so in the
//! ordinary pipeline (`driver::ir`) it never runs on a program the
//! checker rejected. Even so, lowering is atomic: either every function
//! lowers and the caller gets a complete `Module`, or lowering fails
//! with diagnostics and the caller gets no module at all. There is no
//! partial result -- a `Call` in a successfully-lowered function can
//! never reference a function that lowering silently left out, because
//! there is no way to leave one out and still get a `Module` back.

use std::collections::HashMap;

use super::{BasicBlock, Const, Function, Module, Param, Terminator, ValueId, ValueKind};
use crate::diagnostics::Diagnostic;
use crate::hir::{
    ExprId, HirBlock, HirElse, HirExpr, HirFunction, HirModule, HirStmt, ItemId, LocalId,
};
use crate::source::SourceId;
use crate::symbol::Interner;
use crate::syntax::ast::{self, AssignOp, BinaryOp, UnaryOp};
use crate::types::{Ty, is_numeric, primitive_from_name};

use super::block::BlockId;

mod codes {
    /// A construct reached NIR lowering without the checker having
    /// already rejected it. In the ordinary pipeline this should be
    /// unreachable (`typeck` gates `match`/field access with its own
    /// T0007 first) -- this is lowering's own defense-in-depth, for
    /// direct callers that bypass that gate.
    pub const UNSUPPORTED_IN_NIR: &str = "I0001";
    /// Lowering itself failed to uphold one of its own structural
    /// invariants (e.g. a block was left without a terminator). This
    /// should never happen for any HIR built by `hir::lower_module` --
    /// it is a bug in `nir::lower` itself, reported as a diagnostic
    /// instead of a panic so that even a lowering bug degrades to a
    /// normal compiler error rather than crashing the process.
    pub const INTERNAL_INVARIANT_VIOLATED: &str = "I0002";
}

// Boxed so a single-`Diagnostic` `Err` doesn't force every `LowerResult`
// (including `LowerResult<()>`) to be as large as `Diagnostic` itself.
type LowerResult<T> = Result<T, Box<Diagnostic>>;

/// Lowers every function in `hir` to NIR. Either every function lowers
/// successfully and the whole `Module` is returned, or one or more
/// failed and the *only* thing returned is their diagnostics -- there is
/// no way to get back a `Module` with some functions missing.
pub fn lower_module(
    hir: &HirModule,
    local_types: &HashMap<LocalId, Ty>,
    expr_types: &HashMap<ExprId, Ty>,
    interner: &Interner,
    source: SourceId,
) -> Result<Module, Vec<Diagnostic>> {
    let mut function_sigs = HashMap::new();
    for f in &hir.functions {
        let params = f
            .params
            .iter()
            .map(|p| resolve_named_type(interner, &p.ty))
            .collect();
        let ret = f
            .return_type
            .as_ref()
            .map(|t| resolve_named_type(interner, t))
            .unwrap_or(Ty::Unit);
        function_sigs.insert(f.id, (params, ret));
    }

    let mut lowering = Lowering {
        local_types,
        expr_types,
        interner,
        source,
        function_sigs,
    };
    let mut functions = Vec::new();
    let mut diagnostics = Vec::new();
    for f in &hir.functions {
        match lowering.lower_function(f) {
            Ok(nir_fn) => functions.push(nir_fn),
            Err(diag) => diagnostics.push(*diag),
        }
    }

    if diagnostics.is_empty() {
        Ok(Module { functions })
    } else {
        Err(diagnostics)
    }
}

fn resolve_named_type(interner: &Interner, ty: &ast::Type) -> Ty {
    primitive_from_name(interner.resolve(ty.name.symbol)).unwrap_or(Ty::Error)
}

struct Lowering<'a> {
    local_types: &'a HashMap<LocalId, Ty>,
    expr_types: &'a HashMap<ExprId, Ty>,
    interner: &'a Interner,
    source: SourceId,
    function_sigs: HashMap<ItemId, (Vec<Ty>, Ty)>,
}

#[derive(Copy, Clone)]
struct LoopCtx {
    break_target: BlockId,
    continue_target: BlockId,
}

struct PendingBlock {
    id: BlockId,
    instructions: Vec<crate::nir::Instruction>,
    terminator: Option<Terminator>,
}

/// How a resolved local is represented in NIR. A local that is never
/// reassigned (every parameter; a `value` binding) is just the `ValueId`
/// that first produced it — referencing it needs no `load` at all. Only
/// a `mutable` binding gets a real storage slot (an `alloc`), since only
/// it can ever need a `store` after its initializer.
#[derive(Copy, Clone, Debug)]
enum LocalBinding {
    Direct(ValueId),
    Slot(ValueId),
}

/// The result of lowering one expression: either a real value the
/// current (still-open) block can keep building on, or proof that
/// control already left this block. `return`/`break`/`continue` lower
/// straight to a real NIR terminator rather than a synthetic "unit"
/// instruction, so once one of them fires there is no value left to
/// store, pass as an operand, or branch on -- every caller that
/// receives `Diverged` must stop emitting into the current block and
/// propagate `Diverged` upward immediately, instead of inventing a
/// placeholder value to keep going. This is what makes "no instruction
/// is ever appended after a block's terminator" a property the type
/// system enforces, rather than something callers have to remember to
/// check with `current_terminated()`.
enum LoweredExpr {
    Value(ValueId),
    Diverged,
}

/// Per-function mutable lowering state: value numbering, the
/// in-progress block list, and the active loop's break/continue targets.
struct FnBuilder {
    next_value: u32,
    local_bindings: HashMap<LocalId, LocalBinding>,
    blocks: Vec<PendingBlock>,
    current: BlockId,
    loop_stack: Vec<LoopCtx>,
    /// The enclosing function's declared return type, used to hint a
    /// bare literal in `return <literal>` to the right type instead of
    /// the usual i64/f64 default.
    return_ty: Ty,
}

impl FnBuilder {
    fn new(return_ty: Ty) -> Self {
        let entry = BlockId(0);
        FnBuilder {
            next_value: 0,
            local_bindings: HashMap::new(),
            blocks: vec![PendingBlock {
                id: entry,
                instructions: Vec::new(),
                terminator: None,
            }],
            current: entry,
            loop_stack: Vec::new(),
            return_ty,
        }
    }

    fn fresh_value(&mut self) -> ValueId {
        let id = ValueId(self.next_value);
        self.next_value += 1;
        id
    }

    fn alloc_slot(&mut self, ty: Ty) -> ValueId {
        self.push_value(ty, ValueKind::Alloc)
    }

    fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(PendingBlock {
            id,
            instructions: Vec::new(),
            terminator: None,
        });
        id
    }

    fn switch_to(&mut self, id: BlockId) {
        self.current = id;
    }

    fn current_block_mut(&mut self) -> &mut PendingBlock {
        let idx = self.current.0 as usize;
        &mut self.blocks[idx]
    }

    fn current_terminated(&self) -> bool {
        self.blocks[self.current.0 as usize].terminator.is_some()
    }

    fn push_value(&mut self, ty: Ty, kind: ValueKind) -> ValueId {
        let result = self.fresh_value();
        self.current_block_mut()
            .instructions
            .push(crate::nir::Instruction::Value { result, ty, kind });
        result
    }

    fn push_store(&mut self, slot: ValueId, value: ValueId) {
        self.current_block_mut()
            .instructions
            .push(crate::nir::Instruction::Store { slot, value });
    }

    fn terminate(&mut self, term: Terminator) {
        self.current_block_mut().terminator = Some(term);
    }

    /// Converts every block built so far into its finished form, or
    /// reports the id of the first block still missing a terminator.
    /// Every code path that creates a block is responsible for either
    /// terminating it or (for `while`'s lazily-created loop-body/exit
    /// blocks) never creating it in the first place -- if that
    /// invariant is ever violated despite that, this is where it is
    /// caught, as a `Result` a caller with real source context can turn
    /// into a diagnostic, not a panic on arbitrary user input.
    fn finish_blocks(self) -> Result<Vec<BasicBlock>, BlockId> {
        self.blocks
            .into_iter()
            .map(|b| match b.terminator {
                Some(terminator) => Ok(BasicBlock {
                    id: b.id,
                    instructions: b.instructions,
                    terminator,
                }),
                None => Err(b.id),
            })
            .collect()
    }
}

impl<'a> Lowering<'a> {
    fn lower_function(&mut self, f: &HirFunction) -> LowerResult<Function> {
        let return_type = f
            .return_type
            .as_ref()
            .map(|t| self.resolve_named_type(t))
            .unwrap_or(Ty::Unit);
        let mut fb = FnBuilder::new(return_type.clone());
        let mut params = Vec::new();
        for p in &f.params {
            let ty = self.local_types.get(&p.local).cloned().unwrap_or(Ty::Error);
            let value = fb.fresh_value();
            fb.local_bindings
                .insert(p.local, LocalBinding::Direct(value));
            params.push(Param { value, ty });
        }

        let body_result = self.lower_block_value(&mut fb, &f.body)?;
        if !fb.current_terminated() {
            // `Diverged` always means the block that produced it is
            // already terminated (see `LoweredExpr`), so reaching here
            // means the body itself did produce a real value.
            let LoweredExpr::Value(body_value) = body_result else {
                unreachable!(
                    "internal invariant: a Diverged result always already terminated its block"
                );
            };
            if matches!(return_type, Ty::Unit) {
                fb.terminate(Terminator::Return(None));
            } else {
                fb.terminate(Terminator::Return(Some(body_value)));
            }
        }

        let blocks = fb.finish_blocks().map_err(|block_id| {
            Box::new(Diagnostic::error(
                codes::INTERNAL_INVARIANT_VIOLATED,
                self.source,
                f.name_span,
                format!(
                    "internal error lowering `{}`: block bb{} was never given a terminator",
                    self.interner.resolve(f.name),
                    block_id.0
                ),
            ))
        })?;

        Ok(Function {
            id: f.id,
            name: f.name,
            params,
            return_type,
            blocks,
        })
    }

    fn resolve_named_type(&self, ty: &ast::Type) -> Ty {
        resolve_named_type(self.interner, ty)
    }

    // ---- reading typeck's already-resolved types ----
    //
    // Lowering never re-derives or approximates a type: typeck recorded
    // the final, resolved type of every expression and block it visited
    // (`expr_types`), so picking the right instruction (e.g. `add.i64`
    // vs `add.f64`) is always a lookup by the node's own `ExprId`, never
    // a re-inference.

    fn expr_ty(&self, expr: &HirExpr) -> Ty {
        self.expr_types
            .get(&expr.id())
            .cloned()
            .unwrap_or(Ty::Error)
    }

    /// Builds the diagnostic for a construct that reached lowering
    /// without the checker having already rejected it -- see
    /// `codes::UNSUPPORTED_IN_NIR`.
    fn unsupported(&self, span: crate::source::Span, feature: &str) -> Box<Diagnostic> {
        Box::new(Diagnostic::error(
            codes::UNSUPPORTED_IN_NIR,
            self.source,
            span,
            format!("{feature} cannot be lowered to NIR"),
        ))
    }

    // ---- statement/block lowering ----

    fn lower_block_void(&mut self, fb: &mut FnBuilder, block: &HirBlock) -> LowerResult<()> {
        for stmt in &block.statements {
            self.lower_stmt(fb, stmt)?;
            if fb.current_terminated() {
                return Ok(());
            }
        }
        if let Some(tail) = &block.tail {
            self.lower_expr(fb, tail)?;
        }
        Ok(())
    }

    fn lower_block_value(
        &mut self,
        fb: &mut FnBuilder,
        block: &HirBlock,
    ) -> LowerResult<LoweredExpr> {
        for stmt in &block.statements {
            self.lower_stmt(fb, stmt)?;
            if fb.current_terminated() {
                // A statement already diverged the block; there is
                // nothing left to lower and nowhere left to put another
                // instruction.
                return Ok(LoweredExpr::Diverged);
            }
        }
        match &block.tail {
            Some(tail) => self.lower_expr(fb, tail),
            None => Ok(LoweredExpr::Value(
                fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)),
            )),
        }
    }

    fn lower_stmt(&mut self, fb: &mut FnBuilder, stmt: &HirStmt) -> LowerResult<()> {
        match stmt {
            HirStmt::Binding(b) => {
                let ty = self.local_types.get(&b.local).cloned().unwrap_or(Ty::Error);
                let value = match self.lower_expr_hinted(fb, &b.value, &ty)? {
                    LoweredExpr::Value(v) => v,
                    // The initializer itself diverged (e.g. `value x =
                    // return 1;`): the binding is never actually
                    // created, and the block is already terminated, so
                    // there is nothing left to allocate or store into.
                    LoweredExpr::Diverged => return Ok(()),
                };
                let binding = if b.mutable {
                    let slot = fb.alloc_slot(ty);
                    fb.push_store(slot, value);
                    LocalBinding::Slot(slot)
                } else {
                    LocalBinding::Direct(value)
                };
                fb.local_bindings.insert(b.local, binding);
                Ok(())
            }
            HirStmt::Expr(e) => {
                self.lower_expr(fb, e)?;
                Ok(())
            }
            // Deferred cleanup is not run by this milestone's
            // interpreter yet (spec/0004); its expression is
            // intentionally not lowered rather than run at the wrong
            // time.
            HirStmt::Defer { .. } => Ok(()),
            HirStmt::While {
                condition, body, ..
            } => self.lower_while(fb, condition, body),
            HirStmt::Loop { body, .. } => self.lower_loop(fb, body),
        }
    }

    fn lower_while(
        &mut self,
        fb: &mut FnBuilder,
        condition: &HirExpr,
        body: &HirBlock,
    ) -> LowerResult<()> {
        let header = fb.new_block();
        fb.terminate(Terminator::Branch(header));

        // `loop_body`/`after` are deliberately not created until the
        // condition is known to produce a real value: creating them
        // upfront and then hitting the early `Diverged` return below
        // would leave them permanently unterminated (nothing branches
        // to them, and nothing ever will), which is exactly the
        // "internal invariant: every NIR block must have a terminator"
        // panic this is guarding against. Lowering them lazily means
        // there is simply nothing left dangling on this path.
        fb.switch_to(header);
        let cond_value = match self.lower_expr(fb, condition)? {
            LoweredExpr::Value(v) => v,
            // The condition itself diverged and already gave `header`
            // a real terminator (whatever `return`/`break`/`continue`
            // it lowered to); the loop body and exit block are never
            // reachable, so they are never created at all.
            LoweredExpr::Diverged => return Ok(()),
        };

        let loop_body = fb.new_block();
        let after = fb.new_block();
        fb.terminate(Terminator::CondBranch {
            condition: cond_value,
            then_block: loop_body,
            else_block: after,
        });

        fb.switch_to(loop_body);
        fb.loop_stack.push(LoopCtx {
            break_target: after,
            continue_target: header,
        });
        self.lower_block_void(fb, body)?;
        fb.loop_stack.pop();
        if !fb.current_terminated() {
            fb.terminate(Terminator::Branch(header));
        }

        fb.switch_to(after);
        Ok(())
    }

    fn lower_loop(&mut self, fb: &mut FnBuilder, body: &HirBlock) -> LowerResult<()> {
        let header = fb.new_block();
        let after = fb.new_block();
        fb.terminate(Terminator::Branch(header));

        fb.switch_to(header);
        fb.loop_stack.push(LoopCtx {
            break_target: after,
            continue_target: header,
        });
        self.lower_block_void(fb, body)?;
        fb.loop_stack.pop();
        if !fb.current_terminated() {
            fb.terminate(Terminator::Branch(header));
        }

        fb.switch_to(after);
        Ok(())
    }

    // ---- expression lowering ----

    fn lower_expr(&mut self, fb: &mut FnBuilder, expr: &HirExpr) -> LowerResult<LoweredExpr> {
        match expr {
            HirExpr::Int { value, .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::I64, ValueKind::Const(Const::Int(*value))),
            )),
            HirExpr::Float { value, .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::F64, ValueKind::Const(Const::Float(*value))),
            )),
            HirExpr::Str { value, .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::Str, ValueKind::Const(Const::Str(value.clone()))),
            )),
            HirExpr::Char { value, .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::Char, ValueKind::Const(Const::Char(*value))),
            )),
            HirExpr::Bool { value, .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::Bool, ValueKind::Const(Const::Bool(*value))),
            )),
            HirExpr::Local { local, .. } => {
                let binding = *fb.local_bindings.get(local).expect(
                    "internal invariant: a resolved local is always bound by the time it's read",
                );
                match binding {
                    LocalBinding::Direct(value) => Ok(LoweredExpr::Value(value)),
                    LocalBinding::Slot(slot) => {
                        let ty = self.local_types.get(local).cloned().unwrap_or(Ty::Error);
                        Ok(LoweredExpr::Value(fb.push_value(ty, ValueKind::Load(slot))))
                    }
                }
            }
            HirExpr::Function { .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::Error, ValueKind::Const(Const::Unit)),
            )),
            HirExpr::Unary { op, operand, .. } => self.lower_unary(fb, *op, operand),
            HirExpr::Binary {
                op, left, right, ..
            } => self.lower_binary(fb, *op, left, right),
            HirExpr::Assign {
                target, op, value, ..
            } => self.lower_assign(fb, target, *op, value),
            HirExpr::Call { callee, args, .. } => self.lower_call(fb, callee, args),
            HirExpr::Field { span, .. } => Err(self.unsupported(*span, "field access")),
            HirExpr::Cast { expr, .. } => self.lower_expr(fb, expr),
            HirExpr::Try { expr, .. } => self.lower_expr(fb, expr),
            HirExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let result_ty = self.expr_ty(expr);
                self.lower_if(fb, condition, then_branch, else_branch, result_ty)
            }
            HirExpr::Match { span, .. } => Err(self.unsupported(*span, "match")),
            HirExpr::Block(b) => self.lower_block_value(fb, b),
            HirExpr::Return { value, .. } => {
                let ret_ty = fb.return_ty.clone();
                let v = match value {
                    Some(v) => match self.lower_expr_hinted(fb, v, &ret_ty)? {
                        LoweredExpr::Value(val) => Some(val),
                        // The value being returned already diverged
                        // (e.g. `return return 1`); this outer `return`
                        // never actually executes, and the block is
                        // already terminated by the inner one.
                        LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
                    },
                    None => None,
                };
                fb.terminate(Terminator::Return(v));
                Ok(LoweredExpr::Diverged)
            }
            HirExpr::Break { value, span, .. } => {
                if let Some(v) = value
                    && matches!(self.lower_expr(fb, v)?, LoweredExpr::Diverged)
                {
                    return Ok(LoweredExpr::Diverged);
                }
                let target = fb
                    .loop_stack
                    .last()
                    .map(|c| c.break_target)
                    .ok_or_else(|| self.unsupported(*span, "`break` outside a loop"))?;
                fb.terminate(Terminator::Branch(target));
                Ok(LoweredExpr::Diverged)
            }
            HirExpr::Continue { span, .. } => {
                let target = fb
                    .loop_stack
                    .last()
                    .map(|c| c.continue_target)
                    .ok_or_else(|| self.unsupported(*span, "`continue` outside a loop"))?;
                fb.terminate(Terminator::Branch(target));
                Ok(LoweredExpr::Diverged)
            }
            HirExpr::Error { .. } => Ok(LoweredExpr::Value(
                fb.push_value(Ty::Error, ValueKind::Const(Const::Unit)),
            )),
        }
    }

    /// Lowers `expr`, using `hint` as the type for a bare integer/float
    /// literal (a literal has no type of its own; it takes whatever
    /// the surrounding context already unified it with).
    fn lower_expr_hinted(
        &mut self,
        fb: &mut FnBuilder,
        expr: &HirExpr,
        hint: &Ty,
    ) -> LowerResult<LoweredExpr> {
        match expr {
            HirExpr::Int { value, .. } if is_numeric(hint) => Ok(LoweredExpr::Value(
                fb.push_value(hint.clone(), ValueKind::Const(Const::Int(*value))),
            )),
            HirExpr::Float { value, .. } if is_numeric(hint) => Ok(LoweredExpr::Value(
                fb.push_value(hint.clone(), ValueKind::Const(Const::Float(*value))),
            )),
            _ => self.lower_expr(fb, expr),
        }
    }

    fn lower_unary(
        &mut self,
        fb: &mut FnBuilder,
        op: UnaryOp,
        operand: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        let ty = self.expr_ty(operand);
        let v = match self.lower_expr_hinted(fb, operand, &ty)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        Ok(LoweredExpr::Value(match op {
            UnaryOp::Neg => fb.push_value(ty, ValueKind::Neg(v)),
            UnaryOp::Not | UnaryOp::BitNot => fb.push_value(ty, ValueKind::Not(v)),
        }))
    }

    fn lower_binary(
        &mut self,
        fb: &mut FnBuilder,
        op: BinaryOp,
        left: &HirExpr,
        right: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        match op {
            BinaryOp::And => return self.lower_short_circuit(fb, left, right, false),
            BinaryOp::Or => return self.lower_short_circuit(fb, left, right, true),
            BinaryOp::Range | BinaryOp::RangeInclusive => {
                // Ranges are not lowered further in this milestone (no
                // range value/iteration support yet); evaluate the
                // endpoints for side effects and yield the start value.
                let lv = match self.lower_expr(fb, left)? {
                    LoweredExpr::Value(v) => v,
                    LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
                };
                if matches!(self.lower_expr(fb, right)?, LoweredExpr::Diverged) {
                    return Ok(LoweredExpr::Diverged);
                }
                return Ok(LoweredExpr::Value(lv));
            }
            _ => {}
        }

        // typeck already unified left and right to the same type (or
        // recorded a diagnostic if it couldn't), so either side's
        // resolved expr_type is the operand type -- no need to guess
        // which side "actually" carries it based on which is a literal.
        let operand_ty = self.expr_ty(left);

        let lv = match self.lower_expr_hinted(fb, left, &operand_ty)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        let rv = match self.lower_expr_hinted(fb, right, &operand_ty)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };

        let kind = match op {
            BinaryOp::Add => ValueKind::Add(lv, rv),
            BinaryOp::Sub => ValueKind::Sub(lv, rv),
            BinaryOp::Mul => ValueKind::Mul(lv, rv),
            BinaryOp::Div => ValueKind::Div(lv, rv),
            BinaryOp::Rem => ValueKind::Rem(lv, rv),
            BinaryOp::BitAnd => ValueKind::And(lv, rv),
            BinaryOp::BitOr => ValueKind::Or(lv, rv),
            BinaryOp::BitXor => ValueKind::Xor(lv, rv),
            BinaryOp::Shl => ValueKind::Shl(lv, rv),
            BinaryOp::Shr => ValueKind::Shr(lv, rv),
            BinaryOp::Eq => ValueKind::Eq(lv, rv),
            BinaryOp::Ne => ValueKind::Ne(lv, rv),
            BinaryOp::Lt => ValueKind::Lt(lv, rv),
            BinaryOp::Le => ValueKind::Le(lv, rv),
            BinaryOp::Gt => ValueKind::Gt(lv, rv),
            BinaryOp::Ge => ValueKind::Ge(lv, rv),
            BinaryOp::And | BinaryOp::Or | BinaryOp::Range | BinaryOp::RangeInclusive => {
                unreachable!("handled above")
            }
        };
        let result_ty = match op {
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge => Ty::Bool,
            _ => operand_ty,
        };
        Ok(LoweredExpr::Value(fb.push_value(result_ty, kind)))
    }

    /// Lowers `&&`/`||` with short-circuit evaluation: the right operand
    /// is only evaluated when the left doesn't already decide the
    /// result. `short_on_true` is `true` for `||` (stop as soon as the
    /// left side is true) and `false` for `&&` (stop as soon as it's
    /// false).
    fn lower_short_circuit(
        &mut self,
        fb: &mut FnBuilder,
        left: &HirExpr,
        right: &HirExpr,
        short_on_true: bool,
    ) -> LowerResult<LoweredExpr> {
        let left_value = match self.lower_expr(fb, left)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        let right_block = fb.new_block();
        let after_block = fb.new_block();
        let result_slot = fb.alloc_slot(Ty::Bool);

        fb.push_store(result_slot, left_value);
        let (then_block, else_block) = if short_on_true {
            (after_block, right_block)
        } else {
            (right_block, after_block)
        };
        fb.terminate(Terminator::CondBranch {
            condition: left_value,
            then_block,
            else_block,
        });

        fb.switch_to(right_block);
        // A Diverged right side already terminated `right_block` itself
        // (via whatever return/break/continue it lowered to); there is
        // no value to store and no `after_block` branch to add on top
        // of that.
        if let LoweredExpr::Value(right_value) = self.lower_expr(fb, right)? {
            fb.push_store(result_slot, right_value);
            fb.terminate(Terminator::Branch(after_block));
        }

        fb.switch_to(after_block);
        Ok(LoweredExpr::Value(
            fb.push_value(Ty::Bool, ValueKind::Load(result_slot)),
        ))
    }

    fn lower_assign(
        &mut self,
        fb: &mut FnBuilder,
        target: &HirExpr,
        op: AssignOp,
        value: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        let HirExpr::Local { local, .. } = target else {
            if matches!(self.lower_expr(fb, target)?, LoweredExpr::Diverged) {
                return Ok(LoweredExpr::Diverged);
            }
            if matches!(self.lower_expr(fb, value)?, LoweredExpr::Diverged) {
                return Ok(LoweredExpr::Diverged);
            }
            return Ok(LoweredExpr::Value(
                fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)),
            ));
        };
        // typeck rejects assigning to a binding that isn't `mutable`
        // before NIR lowering ever runs, so a well-typed program's
        // assignment target always has a real slot here.
        let slot = match fb.local_bindings.get(local) {
            Some(LocalBinding::Slot(slot)) => *slot,
            other => panic!(
                "internal invariant: assignment target must be a mutable local's slot, found {other:?}"
            ),
        };
        let target_ty = self.local_types.get(local).cloned().unwrap_or(Ty::Error);
        let value_value = match self.lower_expr_hinted(fb, value, &target_ty)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };

        let final_value = match op {
            AssignOp::Assign => value_value,
            _ => {
                let current = fb.push_value(target_ty.clone(), ValueKind::Load(slot));
                let kind = match op {
                    AssignOp::Add => ValueKind::Add(current, value_value),
                    AssignOp::Sub => ValueKind::Sub(current, value_value),
                    AssignOp::Mul => ValueKind::Mul(current, value_value),
                    AssignOp::Div => ValueKind::Div(current, value_value),
                    AssignOp::Rem => ValueKind::Rem(current, value_value),
                    AssignOp::BitAnd => ValueKind::And(current, value_value),
                    AssignOp::BitOr => ValueKind::Or(current, value_value),
                    AssignOp::BitXor => ValueKind::Xor(current, value_value),
                    AssignOp::Shl => ValueKind::Shl(current, value_value),
                    AssignOp::Shr => ValueKind::Shr(current, value_value),
                    AssignOp::Assign => unreachable!("handled above"),
                };
                fb.push_value(target_ty.clone(), kind)
            }
        };
        fb.push_store(slot, final_value);
        Ok(LoweredExpr::Value(
            fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)),
        ))
    }

    fn lower_call(
        &mut self,
        fb: &mut FnBuilder,
        callee: &HirExpr,
        args: &[HirExpr],
    ) -> LowerResult<LoweredExpr> {
        let HirExpr::Function { item, .. } = callee else {
            if matches!(self.lower_expr(fb, callee)?, LoweredExpr::Diverged) {
                return Ok(LoweredExpr::Diverged);
            }
            for arg in args {
                if matches!(self.lower_expr(fb, arg)?, LoweredExpr::Diverged) {
                    return Ok(LoweredExpr::Diverged);
                }
            }
            return Ok(LoweredExpr::Value(
                fb.push_value(Ty::Error, ValueKind::Const(Const::Unit)),
            ));
        };
        let (param_tys, ret_ty) = self
            .function_sigs
            .get(item)
            .cloned()
            .unwrap_or_else(|| (Vec::new(), Ty::Error));
        let mut arg_values = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            let hint = param_tys.get(i).cloned().unwrap_or(Ty::Error);
            match self.lower_expr_hinted(fb, arg, &hint)? {
                LoweredExpr::Value(v) => arg_values.push(v),
                LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
            }
        }
        Ok(LoweredExpr::Value(
            fb.push_value(ret_ty, ValueKind::Call(*item, arg_values)),
        ))
    }

    fn lower_if(
        &mut self,
        fb: &mut FnBuilder,
        condition: &HirExpr,
        then_branch: &HirBlock,
        else_branch: &Option<HirElse>,
        result_ty: Ty,
    ) -> LowerResult<LoweredExpr> {
        let cond_value = match self.lower_expr(fb, condition)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };

        let then_block = fb.new_block();
        let else_block = fb.new_block();
        let after_block = fb.new_block();
        fb.terminate(Terminator::CondBranch {
            condition: cond_value,
            then_block,
            else_block,
        });

        let result_slot = fb.alloc_slot(result_ty.clone());

        // A `Diverged` branch has already terminated its own block (via
        // whatever return/break/continue it lowered to); there is no
        // value to store into `result_slot` and no `after_block` branch
        // to add on top of that terminator. `reached_after` tracks
        // whether *either* branch actually falls through to
        // `after_block`, since if neither does, `after_block` itself is
        // unreachable dead code with nothing ever stored into
        // `result_slot` -- there is no value to load there, so the
        // whole `if` diverges too.
        fb.switch_to(then_block);
        let mut reached_after = false;
        if let LoweredExpr::Value(then_value) = self.lower_block_value(fb, then_branch)? {
            reached_after = true;
            if else_branch.is_none() {
                // No `else`: typeck gives the whole expression type
                // `unit` regardless of what the then-branch's own tail
                // expression resolves to (spec/0002 -- an `if` without
                // `else` is never used for its value), so the
                // then-branch's real value (whatever type it has) is
                // evaluated for its side effects and then discarded.
                // Storing it into `result_slot` here -- which is always
                // declared `unit` on this path -- would store a value
                // of the wrong type into it.
                let _ = then_value;
                let unit_value = fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit));
                fb.push_store(result_slot, unit_value);
            } else {
                fb.push_store(result_slot, then_value);
            }
            fb.terminate(Terminator::Branch(after_block));
        }

        fb.switch_to(else_block);
        match else_branch {
            Some(HirElse::Block(b)) => {
                if let LoweredExpr::Value(else_value) = self.lower_block_value(fb, b)? {
                    fb.push_store(result_slot, else_value);
                    fb.terminate(Terminator::Branch(after_block));
                    reached_after = true;
                }
            }
            Some(HirElse::If(inner)) => {
                if let LoweredExpr::Value(else_value) = self.lower_expr(fb, inner)? {
                    fb.push_store(result_slot, else_value);
                    fb.terminate(Terminator::Branch(after_block));
                    reached_after = true;
                }
            }
            None => {
                let unit_value = fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit));
                fb.push_store(result_slot, unit_value);
                fb.terminate(Terminator::Branch(after_block));
                reached_after = true;
            }
        }

        if !reached_after {
            // `after_block` has no predecessor and was never given a
            // terminator; a self-branch keeps it structurally valid
            // (every block still has exactly one terminator, targeting
            // a block that exists) without claiming it produces a
            // value or is ever actually reached.
            fb.switch_to(after_block);
            fb.terminate(Terminator::Branch(after_block));
            return Ok(LoweredExpr::Diverged);
        }

        fb.switch_to(after_block);
        Ok(LoweredExpr::Value(
            fb.push_value(result_ty, ValueKind::Load(result_slot)),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::lower_module as lower_hir;
    use crate::lexer::tokenize;
    use crate::nir::Instruction;
    use crate::parser::Parser;
    use crate::source::SourceMap;
    use crate::typeck::check_module;

    fn lower(text: &str) -> Module {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(
            diags.is_empty(),
            "unexpected resolve diagnostics: {diags:?}"
        );
        let result = check_module(&hir, id, &interner);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected type errors: {:?}",
            result.diagnostics
        );
        lower_module(&hir, &result.local_types, &result.expr_types, &interner, id)
            .expect("expected lowering to succeed")
    }

    /// Like `lower`, but also runs the module through the NIR verifier
    /// (using the same interner/source lowering itself used, unlike a
    /// fresh throwaway one) and returns its diagnostics -- for tests
    /// that need to assert the *verifier* accepts what was produced.
    fn lower_and_verify(text: &str) -> Vec<Diagnostic> {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(
            diags.is_empty(),
            "unexpected resolve diagnostics: {diags:?}"
        );
        let result = check_module(&hir, id, &interner);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected type errors: {:?}",
            result.diagnostics
        );
        let module = lower_module(&hir, &result.local_types, &result.expr_types, &interner, id)
            .expect("expected lowering to succeed");
        crate::nir::verify_module(&module, id, &interner)
    }

    #[test]
    fn simple_function_lowers_with_no_skips() {
        let module = lower("func add(left: i64, right: i64) -> i64 { return left + right }");
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].params.len(), 2);
    }

    #[test]
    fn literal_takes_its_type_from_typeck_not_a_re_derived_default() {
        // `1`'s type comes from expr_types (typeck already unified it
        // with `x: i32`), not NIR re-inferring it as i64 by default.
        let module = lower("func f(x: i32) -> i32 { return x + 1 }");
        let add_ty = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| match i {
                Instruction::Value {
                    ty,
                    kind: ValueKind::Add(..),
                    ..
                } => Some(ty.clone()),
                _ => None,
            })
            .expect("expected an add instruction");
        assert_eq!(add_ty, Ty::I32);
    }

    #[test]
    fn every_block_has_a_terminator() {
        let module = lower("func f(x: i64) -> i64 { if x > 0 { return 1 } else { return 0 } }");
        for block in &module.functions[0].blocks {
            // Just accessing the field is enough: BasicBlock::terminator
            // is not an Option, so a missing terminator would already
            // have failed to compile/construct.
            let _ = &block.terminator;
        }
    }

    #[test]
    fn finish_blocks_reports_a_missing_terminator_instead_of_panicking() {
        // Every real HIR program this session's fixes could reach is
        // covered by the dedicated CFG tests above; this exercises
        // FnBuilder in isolation to confirm the underlying invariant
        // check itself is a structured error, not a panic, in case a
        // future construct manages to violate it in some other way.
        let mut fb = FnBuilder::new(Ty::Unit);
        // Leaves the entry block (bb0) terminated but this new block
        // (bb1) permanently without one.
        let _dangling = fb.new_block();
        fb.terminate(Terminator::Return(None));
        assert!(
            fb.finish_blocks().is_err(),
            "a block with no terminator must be reported, not silently accepted"
        );
    }

    #[test]
    fn if_expression_lowers_with_cond_branch_and_merge_block() {
        let module = lower("func f(x: bool) -> i64 { return if x { 1 } else { 2 } }");
        let blocks = &module.functions[0].blocks;
        assert!(
            blocks.len() >= 4,
            "expected entry + then + else + merge blocks"
        );
    }

    #[test]
    fn if_where_both_branches_diverge_has_no_orphaned_unterminated_block() {
        // Both branches of this `if` return, so its merge block has no
        // predecessor and nothing is ever stored into its result slot --
        // every block must still end in exactly one terminator, and none
        // may load from a slot nothing ever wrote to.
        let module = lower("func f(x: bool) -> i64 { if x { return 1 } else { return 2 } }");
        for block in &module.functions[0].blocks {
            let _ = &block.terminator;
        }
        let has_load_from_result_slot = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Load(_),
                        ..
                    }
                )
            });
        assert!(
            !has_load_from_result_slot,
            "an unreachable merge block must never load a value nothing stored"
        );
    }

    #[test]
    fn while_loop_lowers_with_header_body_and_exit_blocks() {
        let module =
            lower("func f() -> i64 { mutable x = 0; while x < 10 { x = x + 1; } return x }");
        assert!(module.functions[0].blocks.len() >= 3);
    }

    #[test]
    fn while_with_a_diverging_condition_lowers_without_orphaned_blocks() {
        // The condition itself always diverges (`return;`), so the loop
        // body and exit blocks are never reachable at all -- lowering
        // must not create them and then leave them without a
        // terminator. `lower()` panics if `finish_blocks` ever finds an
        // untermined block, so simply succeeding is most of this test;
        // the block-count and verifier checks pin down that this
        // particular CFG shape (one block, no dangling successors) is
        // what actually gets produced.
        let module = lower("func main() { while { return; } {} }");
        // bb0 (entry, branches straight to the header) + bb1 (header,
        // terminated by the diverging `return;`) -- and nothing else:
        // the loop body/exit blocks must never be created at all, not
        // created and then left orphaned.
        assert_eq!(
            module.functions[0].blocks.len(),
            2,
            "unexpected block set: {:?}",
            module.functions[0].blocks
        );
        let diagnostics = lower_and_verify("func main() { while { return; } {} }");
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn if_without_else_discards_the_then_value_and_stores_unit() {
        // The then-branch produces an `i64`, but an `if` without `else`
        // is always `unit`-typed (spec/0002); storing the then-branch's
        // real value into the unit-declared merge slot would be a type
        // mismatch the verifier must never see in valid NIR.
        let diagnostics = lower_and_verify("func main() { if true { 1 } }");
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn choose_never_join_is_symmetric_regardless_of_which_branch_diverges() {
        for text in [
            "func choose(flag: bool) -> i64 { if flag { return 1 } else { 2 } } \
             func main() -> i64 { return choose(false) }",
            "func choose(flag: bool) -> i64 { if flag { 2 } else { return 1 } } \
             func main() -> i64 { return choose(true) }",
        ] {
            let diagnostics = lower_and_verify(text);
            assert!(
                diagnostics.is_empty(),
                "unexpected diagnostics for {text:?}: {diagnostics:?}"
            );
        }
    }

    #[test]
    fn a_binding_whose_initializer_diverges_never_gets_a_slot_or_store() {
        // `x`'s initializer diverges before the binding ever completes,
        // so lowering must never allocate a slot for it or store into
        // one -- and the unreachable `x = 2; return x;` after it must
        // never be lowered either.
        let module = lower("func f() -> i64 { mutable x = return 1; x = 2; return x }");
        let has_alloc_or_store = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Alloc,
                        ..
                    } | Instruction::Store { .. }
                )
            });
        assert!(!has_alloc_or_store);
    }

    #[test]
    fn recursive_call_lowers_to_a_call_instruction() {
        let module =
            lower("func fact(n: i64) -> i64 { if n == 0 { return 1 } return n * fact(n - 1) }");
        let has_call = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Call(..),
                        ..
                    }
                )
            });
        assert!(has_call);
    }

    #[test]
    fn mutable_binding_uses_a_slot_immutable_binding_does_not() {
        let module = lower("func f() -> i64 { value a = 1; mutable b = 2; return a + b }");
        let allocs = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .filter(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Alloc,
                        ..
                    }
                )
            })
            .count();
        // Only `b` (mutable) should have allocated a slot; `a` (value)
        // is referenced directly with no alloc/load round-trip.
        assert_eq!(allocs, 1);
    }

    #[test]
    fn match_expression_fails_lowering_not_silently_wrong() {
        // `match` is now rejected by the type checker itself (T0007)
        // before a program ever reaches NIR lowering, so this bypasses
        // check_module's diagnostics gate to exercise NIR's own
        // defense-in-depth: lowering must still refuse to guess at NIR
        // for a construct it cannot represent, rather than silently
        // emitting something wrong, if it is ever handed one directly --
        // and it must fail atomically (no partial `Module` at all), not
        // return a module missing just this one function.
        let text = "func f(x: i64) -> i64 { return match x { _ => 0 } }";
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty());
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty());
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(diags.is_empty());
        let result = check_module(&hir, id, &interner);
        let outcome = lower_module(&hir, &result.local_types, &result.expr_types, &interner, id);
        let Err(diagnostics) = outcome else {
            panic!(
                "expected lowering to fail, got {:?}",
                outcome.ok().map(|_| ())
            );
        };
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, "I0001");
        assert!(diagnostics[0].message.contains("match"));
    }

    #[test]
    fn one_function_failing_to_lower_fails_the_whole_module_atomically() {
        // `add` alone would lower cleanly, but `bad` (bypassing typeck's
        // gate, as above) cannot. Lowering must not return a `Module`
        // containing just `add` -- either everything lowers, or nothing
        // does.
        let text = "func add(left: i64, right: i64) -> i64 { return left + right } \
                    func bad(x: i64) -> i64 { return match x { _ => 0 } }";
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty());
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty());
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(diags.is_empty());
        let result = check_module(&hir, id, &interner);
        let outcome = lower_module(&hir, &result.local_types, &result.expr_types, &interner, id);
        assert!(
            outcome.is_err(),
            "expected the whole module to fail lowering"
        );
    }

    #[test]
    fn short_circuit_and_does_not_evaluate_right_side_unconditionally() {
        let module = lower("func f(a: bool, b: bool) -> bool { return a && b }");
        // A branch must exist: short-circuiting is implemented via
        // control flow, not a plain eager `and` instruction.
        let has_condbr = module.functions[0]
            .blocks
            .iter()
            .any(|b| matches!(b.terminator, Terminator::CondBranch { .. }));
        assert!(has_condbr);
    }
}
