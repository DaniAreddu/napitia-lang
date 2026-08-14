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
//! Lowering assumes its input already passed type-checking. `match` and
//! field-access expressions are not lowered yet (`spec/0003`'s explicit
//! scope limits) — a function using either is skipped, reported back to
//! the caller by name rather than silently producing wrong NIR.

use std::collections::HashMap;

use super::{BasicBlock, Const, Function, Module, Param, Terminator, ValueId, ValueKind};
use crate::hir::{
    ExprId, HirBlock, HirElse, HirExpr, HirFunction, HirModule, HirStmt, ItemId, LocalId,
};
use crate::symbol::Interner;
use crate::syntax::ast::{self, AssignOp, BinaryOp, UnaryOp};
use crate::types::{Ty, is_numeric, primitive_from_name};

use super::block::BlockId;

type LowerResult<T> = Result<T, String>;

/// Lowers every function in `hir` to NIR. Returns the successfully
/// lowered functions plus a human-readable reason for each function that
/// was skipped (named by its source function, e.g. `"main: match is not
/// yet lowered to NIR"`).
pub fn lower_module(
    hir: &HirModule,
    local_types: &HashMap<LocalId, Ty>,
    expr_types: &HashMap<ExprId, Ty>,
    interner: &Interner,
) -> (Module, Vec<String>) {
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
        function_sigs,
    };
    let mut functions = Vec::new();
    let mut skipped = Vec::new();
    for f in &hir.functions {
        match lowering.lower_function(f) {
            Ok(nir_fn) => functions.push(nir_fn),
            Err(reason) => skipped.push(format!("{}: {reason}", interner.resolve(f.name))),
        }
    }

    (Module { functions }, skipped)
}

fn resolve_named_type(interner: &Interner, ty: &ast::Type) -> Ty {
    primitive_from_name(interner.resolve(ty.name.symbol)).unwrap_or(Ty::Error)
}

struct Lowering<'a> {
    local_types: &'a HashMap<LocalId, Ty>,
    expr_types: &'a HashMap<ExprId, Ty>,
    interner: &'a Interner,
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

    fn finish_blocks(self) -> Vec<BasicBlock> {
        self.blocks
            .into_iter()
            .map(|b| BasicBlock {
                id: b.id,
                instructions: b.instructions,
                terminator: b
                    .terminator
                    .expect("internal invariant: every NIR block must have a terminator"),
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

        let body_value = self.lower_block_value(&mut fb, &f.body)?;
        if !fb.current_terminated() {
            if matches!(return_type, Ty::Unit) {
                fb.terminate(Terminator::Return(None));
            } else {
                fb.terminate(Terminator::Return(Some(body_value)));
            }
        }

        Ok(Function {
            id: f.id,
            name: f.name,
            params,
            return_type,
            blocks: fb.finish_blocks(),
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

    fn lower_block_value(&mut self, fb: &mut FnBuilder, block: &HirBlock) -> LowerResult<ValueId> {
        for stmt in &block.statements {
            self.lower_stmt(fb, stmt)?;
            if fb.current_terminated() {
                return Ok(fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)));
            }
        }
        match &block.tail {
            Some(tail) => self.lower_expr(fb, tail),
            None => Ok(fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit))),
        }
    }

    fn lower_stmt(&mut self, fb: &mut FnBuilder, stmt: &HirStmt) -> LowerResult<()> {
        match stmt {
            HirStmt::Binding(b) => {
                let ty = self.local_types.get(&b.local).cloned().unwrap_or(Ty::Error);
                let value = self.lower_expr_hinted(fb, &b.value, &ty)?;
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
        let loop_body = fb.new_block();
        let after = fb.new_block();
        fb.terminate(Terminator::Branch(header));

        fb.switch_to(header);
        let cond_value = self.lower_expr(fb, condition)?;
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

    fn lower_expr(&mut self, fb: &mut FnBuilder, expr: &HirExpr) -> LowerResult<ValueId> {
        match expr {
            HirExpr::Int { value, .. } => {
                Ok(fb.push_value(Ty::I64, ValueKind::Const(Const::Int(*value))))
            }
            HirExpr::Float { value, .. } => {
                Ok(fb.push_value(Ty::F64, ValueKind::Const(Const::Float(*value))))
            }
            HirExpr::Str { value, .. } => {
                Ok(fb.push_value(Ty::Str, ValueKind::Const(Const::Str(value.clone()))))
            }
            HirExpr::Char { value, .. } => {
                Ok(fb.push_value(Ty::Char, ValueKind::Const(Const::Char(*value))))
            }
            HirExpr::Bool { value, .. } => {
                Ok(fb.push_value(Ty::Bool, ValueKind::Const(Const::Bool(*value))))
            }
            HirExpr::Local { local, .. } => {
                let binding = *fb.local_bindings.get(local).expect(
                    "internal invariant: a resolved local is always bound by the time it's read",
                );
                match binding {
                    LocalBinding::Direct(value) => Ok(value),
                    LocalBinding::Slot(slot) => {
                        let ty = self.local_types.get(local).cloned().unwrap_or(Ty::Error);
                        Ok(fb.push_value(ty, ValueKind::Load(slot)))
                    }
                }
            }
            HirExpr::Function { .. } => Ok(fb.push_value(Ty::Error, ValueKind::Const(Const::Unit))),
            HirExpr::Unary { op, operand, .. } => self.lower_unary(fb, *op, operand),
            HirExpr::Binary {
                op, left, right, ..
            } => self.lower_binary(fb, *op, left, right),
            HirExpr::Assign {
                target, op, value, ..
            } => self.lower_assign(fb, target, *op, value),
            HirExpr::Call { callee, args, .. } => self.lower_call(fb, callee, args),
            HirExpr::Field { .. } => Err("field access is not yet lowered to NIR".to_string()),
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
            HirExpr::Match { .. } => Err("match is not yet lowered to NIR".to_string()),
            HirExpr::Block(b) => self.lower_block_value(fb, b),
            HirExpr::Return { value, .. } => {
                let ret_ty = fb.return_ty.clone();
                let v = match value {
                    Some(v) => Some(self.lower_expr_hinted(fb, v, &ret_ty)?),
                    None => None,
                };
                fb.terminate(Terminator::Return(v));
                Ok(fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)))
            }
            HirExpr::Break { value, .. } => {
                if let Some(v) = value {
                    self.lower_expr(fb, v)?;
                }
                let target = fb
                    .loop_stack
                    .last()
                    .map(|c| c.break_target)
                    .ok_or_else(|| "break outside a loop".to_string())?;
                fb.terminate(Terminator::Branch(target));
                Ok(fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)))
            }
            HirExpr::Continue { .. } => {
                let target = fb
                    .loop_stack
                    .last()
                    .map(|c| c.continue_target)
                    .ok_or_else(|| "continue outside a loop".to_string())?;
                fb.terminate(Terminator::Branch(target));
                Ok(fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)))
            }
            HirExpr::Error { .. } => Ok(fb.push_value(Ty::Error, ValueKind::Const(Const::Unit))),
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
    ) -> LowerResult<ValueId> {
        match expr {
            HirExpr::Int { value, .. } if is_numeric(hint) => {
                Ok(fb.push_value(hint.clone(), ValueKind::Const(Const::Int(*value))))
            }
            HirExpr::Float { value, .. } if is_numeric(hint) => {
                Ok(fb.push_value(hint.clone(), ValueKind::Const(Const::Float(*value))))
            }
            _ => self.lower_expr(fb, expr),
        }
    }

    fn lower_unary(
        &mut self,
        fb: &mut FnBuilder,
        op: UnaryOp,
        operand: &HirExpr,
    ) -> LowerResult<ValueId> {
        let ty = self.expr_ty(operand);
        let v = self.lower_expr_hinted(fb, operand, &ty)?;
        Ok(match op {
            UnaryOp::Neg => fb.push_value(ty, ValueKind::Neg(v)),
            UnaryOp::Not | UnaryOp::BitNot => fb.push_value(ty, ValueKind::Not(v)),
        })
    }

    fn lower_binary(
        &mut self,
        fb: &mut FnBuilder,
        op: BinaryOp,
        left: &HirExpr,
        right: &HirExpr,
    ) -> LowerResult<ValueId> {
        match op {
            BinaryOp::And => return self.lower_short_circuit(fb, left, right, false),
            BinaryOp::Or => return self.lower_short_circuit(fb, left, right, true),
            BinaryOp::Range | BinaryOp::RangeInclusive => {
                // Ranges are not lowered further in this milestone (no
                // range value/iteration support yet); evaluate the
                // endpoints for side effects and yield the start value.
                let lv = self.lower_expr(fb, left)?;
                self.lower_expr(fb, right)?;
                return Ok(lv);
            }
            _ => {}
        }

        // typeck already unified left and right to the same type (or
        // recorded a diagnostic if it couldn't), so either side's
        // resolved expr_type is the operand type -- no need to guess
        // which side "actually" carries it based on which is a literal.
        let operand_ty = self.expr_ty(left);

        let lv = self.lower_expr_hinted(fb, left, &operand_ty)?;
        let rv = self.lower_expr_hinted(fb, right, &operand_ty)?;

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
        Ok(fb.push_value(result_ty, kind))
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
    ) -> LowerResult<ValueId> {
        let left_value = self.lower_expr(fb, left)?;
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
        let right_value = self.lower_expr(fb, right)?;
        if !fb.current_terminated() {
            fb.push_store(result_slot, right_value);
            fb.terminate(Terminator::Branch(after_block));
        }

        fb.switch_to(after_block);
        Ok(fb.push_value(Ty::Bool, ValueKind::Load(result_slot)))
    }

    fn lower_assign(
        &mut self,
        fb: &mut FnBuilder,
        target: &HirExpr,
        op: AssignOp,
        value: &HirExpr,
    ) -> LowerResult<ValueId> {
        let HirExpr::Local { local, .. } = target else {
            self.lower_expr(fb, target)?;
            self.lower_expr(fb, value)?;
            return Ok(fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)));
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
        let value_value = self.lower_expr_hinted(fb, value, &target_ty)?;

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
        Ok(fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit)))
    }

    fn lower_call(
        &mut self,
        fb: &mut FnBuilder,
        callee: &HirExpr,
        args: &[HirExpr],
    ) -> LowerResult<ValueId> {
        let HirExpr::Function { item, .. } = callee else {
            self.lower_expr(fb, callee)?;
            for arg in args {
                self.lower_expr(fb, arg)?;
            }
            return Ok(fb.push_value(Ty::Error, ValueKind::Const(Const::Unit)));
        };
        let (param_tys, ret_ty) = self
            .function_sigs
            .get(item)
            .cloned()
            .unwrap_or_else(|| (Vec::new(), Ty::Error));
        let mut arg_values = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            let hint = param_tys.get(i).cloned().unwrap_or(Ty::Error);
            arg_values.push(self.lower_expr_hinted(fb, arg, &hint)?);
        }
        Ok(fb.push_value(ret_ty, ValueKind::Call(*item, arg_values)))
    }

    fn lower_if(
        &mut self,
        fb: &mut FnBuilder,
        condition: &HirExpr,
        then_branch: &HirBlock,
        else_branch: &Option<HirElse>,
        result_ty: Ty,
    ) -> LowerResult<ValueId> {
        let cond_value = self.lower_expr(fb, condition)?;

        let then_block = fb.new_block();
        let else_block = fb.new_block();
        let after_block = fb.new_block();
        fb.terminate(Terminator::CondBranch {
            condition: cond_value,
            then_block,
            else_block,
        });

        let result_slot = fb.alloc_slot(result_ty.clone());

        fb.switch_to(then_block);
        let then_value = self.lower_block_value(fb, then_branch)?;
        if !fb.current_terminated() {
            fb.push_store(result_slot, then_value);
            fb.terminate(Terminator::Branch(after_block));
        }

        fb.switch_to(else_block);
        match else_branch {
            Some(HirElse::Block(b)) => {
                let else_value = self.lower_block_value(fb, b)?;
                if !fb.current_terminated() {
                    fb.push_store(result_slot, else_value);
                    fb.terminate(Terminator::Branch(after_block));
                }
            }
            Some(HirElse::If(inner)) => {
                let else_value = self.lower_expr(fb, inner)?;
                if !fb.current_terminated() {
                    fb.push_store(result_slot, else_value);
                    fb.terminate(Terminator::Branch(after_block));
                }
            }
            None => {
                let unit_value = fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit));
                fb.push_store(result_slot, unit_value);
                fb.terminate(Terminator::Branch(after_block));
            }
        }

        fb.switch_to(after_block);
        Ok(fb.push_value(result_ty, ValueKind::Load(result_slot)))
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

    fn lower(text: &str) -> (Module, Vec<String>) {
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
        lower_module(&hir, &result.local_types, &result.expr_types, &interner)
    }

    #[test]
    fn simple_function_lowers_with_no_skips() {
        let (module, skipped) =
            lower("func add(left: i64, right: i64) -> i64 { return left + right }");
        assert!(skipped.is_empty());
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].params.len(), 2);
    }

    #[test]
    fn literal_takes_its_type_from_typeck_not_a_re_derived_default() {
        // `1`'s type comes from expr_types (typeck already unified it
        // with `x: i32`), not NIR re-inferring it as i64 by default.
        let (module, skipped) = lower("func f(x: i32) -> i32 { return x + 1 }");
        assert!(skipped.is_empty());
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
        let (module, skipped) =
            lower("func f(x: i64) -> i64 { if x > 0 { return 1 } else { return 0 } }");
        assert!(skipped.is_empty());
        for block in &module.functions[0].blocks {
            // Just accessing the field is enough: BasicBlock::terminator
            // is not an Option, so a missing terminator would already
            // have failed to compile/construct.
            let _ = &block.terminator;
        }
    }

    #[test]
    fn if_expression_lowers_with_cond_branch_and_merge_block() {
        let (module, skipped) = lower("func f(x: bool) -> i64 { return if x { 1 } else { 2 } }");
        assert!(skipped.is_empty());
        let blocks = &module.functions[0].blocks;
        assert!(
            blocks.len() >= 4,
            "expected entry + then + else + merge blocks"
        );
    }

    #[test]
    fn while_loop_lowers_with_header_body_and_exit_blocks() {
        let (module, skipped) =
            lower("func f() -> i64 { mutable x = 0; while x < 10 { x = x + 1; } return x }");
        assert!(skipped.is_empty());
        assert!(module.functions[0].blocks.len() >= 3);
    }

    #[test]
    fn recursive_call_lowers_to_a_call_instruction() {
        let (module, skipped) =
            lower("func fact(n: i64) -> i64 { if n == 0 { return 1 } return n * fact(n - 1) }");
        assert!(skipped.is_empty());
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
        let (module, skipped) =
            lower("func f() -> i64 { value a = 1; mutable b = 2; return a + b }");
        assert!(skipped.is_empty());
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
    fn match_expression_is_skipped_not_silently_wrong() {
        // `match` is now rejected by the type checker itself (T0007)
        // before a program ever reaches NIR lowering, so this bypasses
        // check_module's diagnostics gate to exercise NIR's own
        // defense-in-depth: lowering must still refuse to guess at NIR
        // for a construct it cannot represent, rather than silently
        // emitting something wrong, if it is ever handed one directly.
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
        let (module, skipped) =
            lower_module(&hir, &result.local_types, &result.expr_types, &interner);
        assert!(module.functions.is_empty());
        assert_eq!(skipped.len(), 1);
        assert!(skipped[0].contains("match"));
    }

    #[test]
    fn short_circuit_and_does_not_evaluate_right_side_unconditionally() {
        let (module, skipped) = lower("func f(a: bool, b: bool) -> bool { return a && b }");
        assert!(skipped.is_empty());
        // A branch must exist: short-circuiting is implemented via
        // control flow, not a plain eager `and` instruction.
        let has_condbr = module.functions[0]
            .blocks
            .iter()
            .any(|b| matches!(b.terminator, Terminator::CondBranch { .. }));
        assert!(has_condbr);
    }
}
