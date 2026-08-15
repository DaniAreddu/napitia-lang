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

use super::{
    BasicBlock, CaseLayout, Const, Function, Module, Param, RecordLayout, Terminator, ValueId,
    ValueKind, VariantLayout,
};
use crate::diagnostics::Diagnostic;
use crate::hir::{
    ExprId, HirBlock, HirElse, HirExpr, HirFieldInit, HirFunction, HirMatchArm, HirMatchArmBody,
    HirModule, HirPattern, HirStmt, ItemId, LocalId, PatternId,
};
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
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
    pattern_case: &HashMap<PatternId, (ItemId, usize)>,
    interner: &Interner,
    source: SourceId,
) -> Result<Module, Vec<Diagnostic>> {
    // The same module-level type namespace typeck itself builds
    // (`typeck::check_module`): primitives plus every declared
    // `record`/`variant` name. Without this, a legitimately-declared
    // named type would have no way to resolve to anything here and
    // would silently fall back to `Ty::Error` -- exactly the kind of
    // "unknown type becomes Error with no diagnostic" bug this whole
    // pass exists to close.
    let type_names: HashMap<Symbol, ItemId> = hir
        .records
        .iter()
        .map(|r| (r.name, r.id))
        .chain(hir.variants.iter().map(|v| (v.name, v.id)))
        .collect();

    let mut record_layouts: HashMap<ItemId, RecordLayout> = HashMap::new();
    let mut record_order: Vec<ItemId> = Vec::new();
    for r in &hir.records {
        let fields = r
            .fields
            .iter()
            .map(|f| (f.name, resolve_named_type(interner, &type_names, &f.ty)))
            .collect();
        record_order.push(r.id);
        record_layouts.insert(
            r.id,
            RecordLayout {
                name: r.name,
                fields,
            },
        );
    }
    let mut variant_layouts: HashMap<ItemId, VariantLayout> = HashMap::new();
    let mut variant_order: Vec<ItemId> = Vec::new();
    for v in &hir.variants {
        let cases = v
            .cases
            .iter()
            .map(|c| CaseLayout {
                name: c.name,
                payload: c
                    .payload
                    .iter()
                    .map(|t| resolve_named_type(interner, &type_names, t))
                    .collect(),
            })
            .collect();
        variant_order.push(v.id);
        variant_layouts.insert(
            v.id,
            VariantLayout {
                name: v.name,
                cases,
            },
        );
    }

    let mut function_sigs = HashMap::new();
    for f in &hir.functions {
        let params = f
            .params
            .iter()
            .map(|p| resolve_named_type(interner, &type_names, &p.ty))
            .collect();
        let ret = f
            .return_type
            .as_ref()
            .map(|t| resolve_named_type(interner, &type_names, t))
            .unwrap_or(Ty::Unit);
        function_sigs.insert(f.id, (params, ret));
    }

    let mut lowering = Lowering {
        local_types,
        expr_types,
        pattern_case,
        interner,
        source,
        type_names,
        records: record_layouts,
        variants: variant_layouts,
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

    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }

    let records = record_order
        .into_iter()
        .map(|id| (id, lowering.records.remove(&id).expect("just inserted")))
        .collect();
    let variants = variant_order
        .into_iter()
        .map(|id| (id, lowering.variants.remove(&id).expect("just inserted")))
        .collect();

    Ok(Module {
        functions,
        records,
        variants,
    })
}

/// Resolves a written type name the same way `typeck::resolve_named_type`
/// does: primitives first, then declared `record`/`variant` names,
/// nominally by `ItemId`. Unlike typeck, an unknown name here is never
/// reachable in the ordinary pipeline (typeck already rejected it with
/// its own diagnostic before lowering ever ran), so falling back to
/// `Ty::Error` is only ever exercised by a direct caller that bypasses
/// that gate -- the same defense-in-depth posture as the rest of this
/// module.
fn resolve_named_type(
    interner: &Interner,
    type_names: &HashMap<Symbol, ItemId>,
    ty: &ast::Type,
) -> Ty {
    let text = interner.resolve(ty.name.symbol);
    if let Some(prim) = primitive_from_name(text) {
        return prim;
    }
    if let Some(&item) = type_names.get(&ty.name.symbol) {
        return Ty::Named(item, ty.name.symbol);
    }
    Ty::Error
}

struct Lowering<'a> {
    local_types: &'a HashMap<LocalId, Ty>,
    expr_types: &'a HashMap<ExprId, Ty>,
    pattern_case: &'a HashMap<PatternId, (ItemId, usize)>,
    interner: &'a Interner,
    source: SourceId,
    type_names: HashMap<Symbol, ItemId>,
    records: HashMap<ItemId, RecordLayout>,
    variants: HashMap<ItemId, VariantLayout>,
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
#[derive(Copy, Clone, Debug, PartialEq)]
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
        debug_assert!(
            !self.current_terminated(),
            "internal invariant: appended a value to block {:?} after it was already terminated",
            self.current
        );
        let result = self.fresh_value();
        self.current_block_mut()
            .instructions
            .push(crate::nir::Instruction::Value { result, ty, kind });
        result
    }

    fn push_store(&mut self, slot: ValueId, value: ValueId) {
        debug_assert!(
            !self.current_terminated(),
            "internal invariant: appended a store to block {:?} after it was already terminated",
            self.current
        );
        self.current_block_mut()
            .instructions
            .push(crate::nir::Instruction::Store { slot, value });
    }

    /// Sets the current block's terminator. This is the one place a
    /// block transitions from "still being built" to "closed" --
    /// `push_value`/`push_store` refuse (in debug builds) to append
    /// anything to a block afterward, so every lowering path must emit
    /// all of a block's instructions before calling this, never after.
    fn terminate(&mut self, term: Terminator) {
        debug_assert!(
            !self.current_terminated(),
            "internal invariant: block {:?} was terminated twice",
            self.current
        );
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
        resolve_named_type(self.interner, &self.type_names, ty)
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
    fn unsupported(&self, span: Span, feature: &str) -> Box<Diagnostic> {
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
            // typeck rejects a non-empty `defer` outright (T0007) before
            // lowering ever runs in the normal pipeline. A direct caller
            // that bypasses that gate must not have it silently
            // dropped (which would run the enclosing block as though
            // the `defer` had never been written at all) -- this
            // milestone's interpreter has nowhere correct to run
            // deferred cleanup (spec/0004), so it is rejected here too.
            HirStmt::Defer { span, .. } => Err(self.unsupported(*span, "`defer`")),
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
            // typeck rejects a function name used outside of a call
            // position outright (T0010) before lowering ever runs in
            // the normal pipeline. A direct caller bypassing that gate
            // must not get a fabricated `Ty::Error` placeholder value
            // in its place -- functions are not first-class values in
            // this milestone at all.
            HirExpr::Function { name, span, .. } => {
                let text = self.interner.resolve(*name);
                Err(self.unsupported(*span, &format!("using `{text}` as a first-class value")))
            }
            // A bare (uncalled) case reference: `typeck` already
            // confirmed this case carries no payload (else it recorded
            // `Ty::Error` and this is unreachable for a well-typed
            // program) -- constructs the unit case directly, with no
            // fabricated payload.
            HirExpr::CaseRef { variant, case, .. } => Ok(LoweredExpr::Value(fb.push_value(
                self.expr_ty(expr),
                ValueKind::VariantCreate {
                    variant: *variant,
                    case: *case,
                    payload: Vec::new(),
                },
            ))),
            HirExpr::Unary { op, operand, .. } => self.lower_unary(fb, *op, operand),
            HirExpr::Binary {
                op,
                left,
                right,
                span,
                ..
            } => self.lower_binary(fb, *op, left, right, *span),
            HirExpr::Assign {
                target, op, value, ..
            } => self.lower_assign(fb, target, *op, value),
            HirExpr::Call { callee, args, .. } => self.lower_call(fb, callee, args, expr),
            HirExpr::Field { base, name, .. } => self.lower_field(fb, base, *name, expr),
            // typeck rejects both of these outright (T0007) before
            // lowering ever runs in the normal pipeline. A direct
            // caller bypassing that gate must not get identity lowering
            // in their place: `as` performs no runtime conversion at
            // all in this milestone, and `?` has no propagation
            // semantics -- silently forwarding the unconverted /
            // unpropagated inner value would let either "succeed" while
            // lying about what it does.
            HirExpr::Cast { span, .. } => Err(self.unsupported(*span, "casts (`as`)")),
            HirExpr::Try { span, .. } => Err(self.unsupported(*span, "postfix `?`")),
            HirExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let result_ty = self.expr_ty(expr);
                self.lower_if(fb, condition, then_branch, else_branch, result_ty)
            }
            HirExpr::Match {
                scrutinee, arms, ..
            } => {
                let result_ty = self.expr_ty(expr);
                self.lower_match(fb, scrutinee, arms, result_ty)
            }
            HirExpr::Block(b) => self.lower_block_value(fb, b),
            HirExpr::RecordLiteral { record, fields, .. } => {
                self.lower_record_literal(fb, *record, fields, expr)
            }
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
                // typeck rejects any value-carrying `break` outright
                // (T0007) regardless of the value's type, before
                // lowering ever runs in the normal pipeline. A direct
                // caller bypassing that gate must not have the value
                // silently evaluated and discarded as though it were an
                // ordinary valueless `break` -- loop-as-expression has
                // no lowering at all yet.
                if value.is_some() {
                    return Err(
                        self.unsupported(*span, "`break` with a value (loop-as-expression)")
                    );
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
        span: Span,
    ) -> LowerResult<LoweredExpr> {
        match op {
            BinaryOp::And => return self.lower_short_circuit(fb, left, right, false),
            BinaryOp::Or => return self.lower_short_circuit(fb, left, right, true),
            // typeck rejects every range expression outright (T0007)
            // before lowering ever runs in the normal pipeline. A
            // direct caller bypassing that gate must not get "lowered
            // to its left endpoint" in its place -- there is no range
            // value or iteration support at all in this milestone, so
            // silently keeping just one side would misrepresent what
            // the expression means, not merely leave it unsupported.
            BinaryOp::Range | BinaryOp::RangeInclusive => {
                return Err(self.unsupported(span, "range expressions (`..`/`..=`)"));
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
        call_expr: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        if let HirExpr::CaseRef { variant, case, .. } = callee {
            return self.lower_variant_construct(fb, *variant, *case, args, call_expr);
        }

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

    fn lower_variant_construct(
        &mut self,
        fb: &mut FnBuilder,
        variant: ItemId,
        case: usize,
        args: &[HirExpr],
        call_expr: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        let payload_tys = self
            .variants
            .get(&variant)
            .map(|v| v.cases[case].payload.clone())
            .unwrap_or_default();
        let mut payload = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            let hint = payload_tys.get(i).cloned().unwrap_or(Ty::Error);
            match self.lower_expr_hinted(fb, arg, &hint)? {
                LoweredExpr::Value(v) => payload.push(v),
                LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
            }
        }
        Ok(LoweredExpr::Value(fb.push_value(
            self.expr_ty(call_expr),
            ValueKind::VariantCreate {
                variant,
                case,
                payload,
            },
        )))
    }

    /// `TypeName { field: expr, ... }`. Each field is evaluated exactly
    /// once, in **source order** (`fields` is already in that order --
    /// see `HirExpr::RecordLiteral`'s doc comment), then reordered into
    /// **declaration order** for `record.create` -- runtime layout
    /// always follows declaration order, independent of how the
    /// construction site wrote them.
    fn lower_record_literal(
        &mut self,
        fb: &mut FnBuilder,
        record: ItemId,
        fields: &[HirFieldInit],
        literal_expr: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        let field_count = self
            .records
            .get(&record)
            .map(|r| r.fields.len())
            .unwrap_or(fields.len());
        let mut by_index: Vec<Option<ValueId>> = vec![None; field_count];
        for f in fields {
            let hint = self
                .records
                .get(&record)
                .and_then(|r| r.fields.get(f.field_index))
                .map(|(_, ty)| ty.clone())
                .unwrap_or(Ty::Error);
            match self.lower_expr_hinted(fb, &f.value, &hint)? {
                LoweredExpr::Value(v) => {
                    if let Some(slot) = by_index.get_mut(f.field_index) {
                        *slot = Some(v);
                    }
                }
                // A diverging initializer means the whole construction
                // never completes; no field written after it in source
                // order is lowered as reachable work.
                LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
            }
        }
        let ordered: Vec<ValueId> = by_index
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                v.unwrap_or_else(|| {
                    panic!(
                        "internal invariant: record construction reached NIR lowering missing \
                         field {i}; typeck/hir::lower must have already rejected it"
                    )
                })
            })
            .collect();
        Ok(LoweredExpr::Value(fb.push_value(
            self.expr_ty(literal_expr),
            ValueKind::RecordCreate(record, ordered),
        )))
    }

    fn lower_field(
        &mut self,
        fb: &mut FnBuilder,
        base: &HirExpr,
        name: Symbol,
        field_expr: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        let base_value = match self.lower_expr(fb, base)? {
            LoweredExpr::Value(v) => v,
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        let base_ty = self.expr_ty(base);
        let Ty::Named(record, _) = base_ty else {
            return Err(self.unsupported(field_expr.span(), "field access on a non-record type"));
        };
        let field_index = self
            .records
            .get(&record)
            .and_then(|r| r.fields.iter().position(|(n, _)| *n == name))
            .ok_or_else(|| {
                self.unsupported(field_expr.span(), "field access on an unknown field")
            })?;
        Ok(LoweredExpr::Value(fb.push_value(
            self.expr_ty(field_expr),
            ValueKind::RecordField {
                base: base_value,
                record,
                field: field_index,
            },
        )))
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

        // `result_ty` is typeck's already-resolved never-join of both
        // branches (spec/0003): the condition itself already produced a
        // real value above, so the only way this whole `if` can be
        // `never` is if both branches diverge. When that's the case
        // there is nothing to merge -- no result slot and no
        // `after_block` are ever created, since each branch's own
        // terminator (whatever `return`/nested-diverging-`if` it
        // lowers to) already leaves a complete, valid CFG on its own.
        if result_ty == Ty::Never {
            fb.terminate(Terminator::CondBranch {
                condition: cond_value,
                then_block,
                else_block,
            });

            fb.switch_to(then_block);
            let then_result = self.lower_block_value(fb, then_branch)?;

            fb.switch_to(else_block);
            let else_result = match else_branch {
                Some(HirElse::Block(b)) => self.lower_block_value(fb, b)?,
                Some(HirElse::If(inner)) => self.lower_expr(fb, inner)?,
                // An else-less `if` always types as `unit` (see below),
                // never `never` -- typeck cannot have produced this
                // combination.
                None => unreachable!(
                    "internal invariant: an else-less `if` is always unit-typed, not never"
                ),
            };
            debug_assert!(
                matches!(then_result, LoweredExpr::Diverged)
                    && matches!(else_result, LoweredExpr::Diverged),
                "internal invariant: typeck reported this `if` as `never`, so both branches \
                 must diverge"
            );
            return Ok(LoweredExpr::Diverged);
        }

        // At least one branch is required to produce a real value of
        // `result_ty` here (typeck already ruled out "both diverge"
        // above). The slot and merge block belong to whichever block
        // is current before the branch -- allocating the slot here
        // both keeps it dominating both `then_block` and `else_block`
        // (required by the verifier) and keeps every instruction
        // belonging to this block emitted before it acquires its
        // terminator (spec/0006): nothing may be appended afterward.
        let result_slot = fb.alloc_slot(result_ty.clone());
        let after_block = fb.new_block();
        fb.terminate(Terminator::CondBranch {
            condition: cond_value,
            then_block,
            else_block,
        });

        fb.switch_to(then_block);
        if let LoweredExpr::Value(then_value) = self.lower_block_value(fb, then_branch)? {
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
                }
            }
            Some(HirElse::If(inner)) => {
                if let LoweredExpr::Value(else_value) = self.lower_expr(fb, inner)? {
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
        Ok(LoweredExpr::Value(
            fb.push_value(result_ty, ValueKind::Load(result_slot)),
        ))
    }

    // ---- match lowering: a decision tree over a pattern matrix ----
    //
    // Mirrors the same recursive specialize/default structure
    // `typeck::exhaustive` uses for its analysis (see RFC 0005's "Match
    // lowering"), but building real NIR blocks instead of checking
    // coverage. A "row" carries one pattern slot per currently pending
    // occurrence (the original scrutinee, plus one fresh occurrence per
    // payload position introduced by descending into a `Variant`
    // pattern) -- `PatternSlot::Wildcard` pads a row that doesn't
    // itself constrain a newly-introduced occurrence (a wildcard/
    // binding/unit-case row matches every payload position trivially),
    // keeping every row in one matrix the same length.

    fn lower_match(
        &mut self,
        fb: &mut FnBuilder,
        scrutinee: &HirExpr,
        arms: &[HirMatchArm],
        result_ty: Ty,
    ) -> LowerResult<LoweredExpr> {
        let scrutinee_value = match self.lower_expr(fb, scrutinee)? {
            LoweredExpr::Value(v) => v,
            // A diverging scrutinee is evaluated exactly once, before
            // any pattern could ever be tested -- the whole match is
            // `never`, and no arm is lowered as reachable work.
            LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
        };
        let scrutinee_ty = self.expr_ty(scrutinee);

        let rows: Vec<MatrixRow> = arms
            .iter()
            .enumerate()
            .map(|(i, arm)| MatrixRow {
                arm_index: i,
                patterns: vec![PatternSlot::Real(&arm.pattern)],
                bindings: Vec::new(),
            })
            .collect();
        let occurrences = vec![Occurrence {
            value: scrutinee_value,
            ty: scrutinee_ty,
        }];

        if result_ty == Ty::Never {
            // Every arm diverges (typeck already proved this); no
            // result slot or merge block is ever created -- each arm's
            // own terminator is already a complete CFG on its own.
            self.lower_decision(fb, rows, occurrences, arms, None)?;
            return Ok(LoweredExpr::Diverged);
        }

        // The slot and merge block belong to the block current before
        // any branching starts, so they dominate every arm -- the same
        // discipline `lower_if` already uses for its own result slot.
        let result_slot = fb.alloc_slot(result_ty.clone());
        let after_block = fb.new_block();
        self.lower_decision(
            fb,
            rows,
            occurrences,
            arms,
            Some((result_slot, after_block)),
        )?;

        fb.switch_to(after_block);
        Ok(LoweredExpr::Value(
            fb.push_value(result_ty, ValueKind::Load(result_slot)),
        ))
    }

    fn lower_decision<'h>(
        &mut self,
        fb: &mut FnBuilder,
        rows: Vec<MatrixRow<'h>>,
        occurrences: Vec<Occurrence>,
        arms: &'h [HirMatchArm],
        merge: Option<(ValueId, BlockId)>,
    ) -> LowerResult<()> {
        if occurrences.is_empty() {
            let Some(winner) = rows.first() else {
                return Err(self.internal_error(
                    "a match's decision tree ran out of candidate arms with no winner",
                ));
            };
            for (local, value) in &winner.bindings {
                fb.local_bindings
                    .insert(*local, LocalBinding::Direct(*value));
            }
            let arm = &arms[winner.arm_index];
            let result = match &arm.body {
                HirMatchArmBody::Expr(e) => self.lower_expr(fb, e)?,
                HirMatchArmBody::Block(b) => self.lower_block_value(fb, b)?,
            };
            if let LoweredExpr::Value(v) = result
                && let Some((slot, after)) = merge
            {
                fb.push_store(slot, v);
                fb.terminate(Terminator::Branch(after));
            }
            return Ok(());
        }

        if matches!(&occurrences[0].ty, Ty::Named(item, _) if self.variants.contains_key(item)) {
            self.lower_variant_switch(fb, rows, occurrences, arms, merge)
        } else if matches!(&occurrences[0].ty, Ty::Bool) {
            // `bool` is a closed two-constructor domain (like a
            // variant's finite case set), so it is switched on
            // directly rather than through the open-domain literal
            // chain below -- an exhaustive `match true { true => ..,
            // false => .. }` (no wildcard at all) would otherwise have
            // no catch-all to terminate that chain's recursion on.
            self.lower_bool_switch(fb, rows, occurrences, arms, merge)
        } else {
            self.lower_literal_chain(fb, rows, occurrences, arms, merge)
        }
    }

    fn lower_bool_switch<'h>(
        &mut self,
        fb: &mut FnBuilder,
        rows: Vec<MatrixRow<'h>>,
        occurrences: Vec<Occurrence>,
        arms: &'h [HirMatchArm],
        merge: Option<(ValueId, BlockId)>,
    ) -> LowerResult<()> {
        let occ = occurrences[0].clone();
        let rest_occ = occurrences[1..].to_vec();

        let any_real_test = rows.iter().any(|r| {
            matches!(
                self.classify(&r.patterns[0]),
                Classified::Literal(LiteralTest::Bool(_))
            )
        });
        if !any_real_test {
            let mut new_rows = Vec::with_capacity(rows.len());
            for r in rows {
                let mut bindings = r.bindings;
                if let Classified::Bind(local) = self.classify(&r.patterns[0]) {
                    bindings.push((local, occ.value));
                }
                new_rows.push(MatrixRow {
                    arm_index: r.arm_index,
                    patterns: r.patterns[1..].to_vec(),
                    bindings,
                });
            }
            return self.lower_decision(fb, new_rows, rest_occ, arms, merge);
        }

        let then_block = fb.new_block();
        let else_block = fb.new_block();
        fb.terminate(Terminator::CondBranch {
            condition: occ.value,
            then_block,
            else_block,
        });

        for (value, block) in [(true, then_block), (false, else_block)] {
            fb.switch_to(block);
            let mut new_rows = Vec::new();
            for r in &rows {
                match self.classify(&r.patterns[0]) {
                    Classified::Literal(LiteralTest::Bool(b)) if b == value => {
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns: r.patterns[1..].to_vec(),
                            bindings: r.bindings.clone(),
                        });
                    }
                    Classified::Literal(LiteralTest::Bool(_)) => {}
                    Classified::Bind(local) => {
                        let mut bindings = r.bindings.clone();
                        bindings.push((local, occ.value));
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns: r.patterns[1..].to_vec(),
                            bindings,
                        });
                    }
                    Classified::Wildcard => {
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns: r.patterns[1..].to_vec(),
                            bindings: r.bindings.clone(),
                        });
                    }
                    _ => {}
                }
            }
            if new_rows.is_empty() {
                return Err(
                    self.internal_error("a match's bool switch left a branch with no covering arm")
                );
            }
            self.lower_decision(fb, new_rows, rest_occ.clone(), arms, merge)?;
        }
        Ok(())
    }

    fn lower_variant_switch<'h>(
        &mut self,
        fb: &mut FnBuilder,
        rows: Vec<MatrixRow<'h>>,
        occurrences: Vec<Occurrence>,
        arms: &'h [HirMatchArm],
        merge: Option<(ValueId, BlockId)>,
    ) -> LowerResult<()> {
        let occ = occurrences[0].clone();
        let rest_occ = occurrences[1..].to_vec();
        let Ty::Named(variant_item, _) = occ.ty.clone() else {
            return Err(self.internal_error("expected a variant-typed occurrence"));
        };

        let any_real_test = rows
            .iter()
            .any(|r| matches!(self.classify(&r.patterns[0]), Classified::Case { .. }));
        if !any_real_test {
            let mut new_rows = Vec::with_capacity(rows.len());
            for r in rows {
                let mut bindings = r.bindings;
                if let Classified::Bind(local) = self.classify(&r.patterns[0]) {
                    bindings.push((local, occ.value));
                }
                new_rows.push(MatrixRow {
                    arm_index: r.arm_index,
                    patterns: r.patterns[1..].to_vec(),
                    bindings,
                });
            }
            return self.lower_decision(fb, new_rows, rest_occ, arms, merge);
        }

        let num_cases = self
            .variants
            .get(&variant_item)
            .map(|v| v.cases.len())
            .unwrap_or(0);
        let case_blocks: Vec<BlockId> = (0..num_cases).map(|_| fb.new_block()).collect();
        fb.terminate(Terminator::Switch {
            scrutinee: occ.value,
            variant: variant_item,
            cases: case_blocks.clone(),
        });

        for (case_index, case_block) in case_blocks.iter().enumerate() {
            fb.switch_to(*case_block);
            let payload_types = self.variants[&variant_item].cases[case_index]
                .payload
                .clone();
            let arity = payload_types.len();

            let mut new_rows: Vec<MatrixRow<'h>> = Vec::new();
            for r in &rows {
                let rest: Vec<PatternSlot<'h>> = r.patterns[1..].to_vec();
                match self.classify(&r.patterns[0]) {
                    Classified::Case {
                        variant,
                        case,
                        args,
                    } if variant == variant_item && case == case_index => {
                        let mut patterns: Vec<PatternSlot<'h>> =
                            args.iter().map(PatternSlot::Real).collect();
                        patterns.resize(arity, PatternSlot::Wildcard);
                        patterns.extend(rest);
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns,
                            bindings: r.bindings.clone(),
                        });
                    }
                    Classified::Case { .. } => {}
                    Classified::Bind(local) => {
                        let mut bindings = r.bindings.clone();
                        bindings.push((local, occ.value));
                        let mut patterns = vec![PatternSlot::Wildcard; arity];
                        patterns.extend(rest);
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns,
                            bindings,
                        });
                    }
                    Classified::Wildcard => {
                        let mut patterns = vec![PatternSlot::Wildcard; arity];
                        patterns.extend(rest);
                        new_rows.push(MatrixRow {
                            arm_index: r.arm_index,
                            patterns,
                            bindings: r.bindings.clone(),
                        });
                    }
                    // A literal pattern against a variant-typed
                    // occurrence is rejected by typeck (T0021,
                    // incompatible pattern) before lowering ever runs
                    // in the normal pipeline; excluded here rather than
                    // panicking, matching this module's defense-in-depth
                    // posture for a direct caller that bypasses typeck.
                    Classified::Literal(_) => {}
                }
            }
            if new_rows.is_empty() {
                return Err(self.internal_error(
                    "a match's decision tree left a variant case with no covering arm",
                ));
            }

            let mut payload_occurrences = Vec::with_capacity(arity);
            for (i, ty) in payload_types.iter().enumerate() {
                let v = fb.push_value(
                    ty.clone(),
                    ValueKind::VariantPayload {
                        base: occ.value,
                        variant: variant_item,
                        case: case_index,
                        index: i,
                    },
                );
                payload_occurrences.push(Occurrence {
                    value: v,
                    ty: ty.clone(),
                });
            }

            let mut new_occurrences = payload_occurrences;
            new_occurrences.extend(rest_occ.clone());
            self.lower_decision(fb, new_rows, new_occurrences, arms, merge)?;
        }
        Ok(())
    }

    fn lower_literal_chain<'h>(
        &mut self,
        fb: &mut FnBuilder,
        rows: Vec<MatrixRow<'h>>,
        occurrences: Vec<Occurrence>,
        arms: &'h [HirMatchArm],
        merge: Option<(ValueId, BlockId)>,
    ) -> LowerResult<()> {
        let occ = occurrences[0].clone();
        let rest_occ = occurrences[1..].to_vec();

        let Some(first) = rows.first() else {
            return Err(self.internal_error("a match's literal chain ran out of candidate arms"));
        };
        match self.classify(&first.patterns[0]) {
            Classified::Wildcard => {
                let new_rows = vec![MatrixRow {
                    arm_index: first.arm_index,
                    patterns: first.patterns[1..].to_vec(),
                    bindings: first.bindings.clone(),
                }];
                self.lower_decision(fb, new_rows, rest_occ, arms, merge)
            }
            Classified::Bind(local) => {
                let mut bindings = first.bindings.clone();
                bindings.push((local, occ.value));
                let new_rows = vec![MatrixRow {
                    arm_index: first.arm_index,
                    patterns: first.patterns[1..].to_vec(),
                    bindings,
                }];
                self.lower_decision(fb, new_rows, rest_occ, arms, merge)
            }
            Classified::Literal(lit) => {
                let const_value = literal_const(fb, &lit, &occ.ty);
                let eq = fb.push_value(Ty::Bool, ValueKind::Eq(occ.value, const_value));
                let then_block = fb.new_block();
                let else_block = fb.new_block();
                fb.terminate(Terminator::CondBranch {
                    condition: eq,
                    then_block,
                    else_block,
                });

                let mut then_rows = Vec::new();
                for r in &rows {
                    match self.classify(&r.patterns[0]) {
                        Classified::Literal(l2) if literal_eq(&lit, &l2) => {
                            then_rows.push(MatrixRow {
                                arm_index: r.arm_index,
                                patterns: r.patterns[1..].to_vec(),
                                bindings: r.bindings.clone(),
                            });
                        }
                        Classified::Wildcard => {
                            then_rows.push(MatrixRow {
                                arm_index: r.arm_index,
                                patterns: r.patterns[1..].to_vec(),
                                bindings: r.bindings.clone(),
                            });
                        }
                        Classified::Bind(local) => {
                            let mut bindings = r.bindings.clone();
                            bindings.push((local, occ.value));
                            then_rows.push(MatrixRow {
                                arm_index: r.arm_index,
                                patterns: r.patterns[1..].to_vec(),
                                bindings,
                            });
                        }
                        _ => {}
                    }
                }
                fb.switch_to(then_block);
                self.lower_decision(fb, then_rows, rest_occ.clone(), arms, merge)?;

                let else_rows: Vec<MatrixRow<'h>> = rows
                    .into_iter()
                    .filter(|r| {
                        !matches!(self.classify(&r.patterns[0]), Classified::Literal(l2) if literal_eq(&lit, &l2))
                    })
                    .collect();
                fb.switch_to(else_block);
                if else_rows.is_empty() {
                    return Err(self.internal_error(
                        "a match's literal chain ran out of rows without a catch-all",
                    ));
                }
                let mut all_occ = vec![occ];
                all_occ.extend(rest_occ);
                self.lower_decision(fb, else_rows, all_occ, arms, merge)
            }
            Classified::Case { .. } => Err(self
                .internal_error("a variant pattern was tested against a non-variant occurrence")),
        }
    }

    fn classify<'h>(&self, slot: &PatternSlot<'h>) -> Classified<'h> {
        let pattern = match slot {
            PatternSlot::Wildcard => return Classified::Wildcard,
            PatternSlot::Real(p) => *p,
        };
        match pattern {
            HirPattern::Wildcard { .. } => Classified::Wildcard,
            HirPattern::Bind { id, local, .. } => match self.pattern_case.get(id) {
                Some(&(variant, case)) => Classified::Case {
                    variant,
                    case,
                    args: &[],
                },
                None => Classified::Bind(*local),
            },
            HirPattern::Variant { id, args, .. } => match self.pattern_case.get(id) {
                Some(&(variant, case)) => Classified::Case {
                    variant,
                    case,
                    args,
                },
                // Unresolved (typeck-unreachable for a valid program):
                // treated as matching nothing, defensively.
                None => Classified::Case {
                    variant: ItemId(u32::MAX),
                    case: usize::MAX,
                    args,
                },
            },
            HirPattern::Int { value, .. } => Classified::Literal(LiteralTest::Int(*value)),
            HirPattern::Str { value, .. } => Classified::Literal(LiteralTest::Str(value)),
            HirPattern::Char { value, .. } => Classified::Literal(LiteralTest::Char(*value)),
            HirPattern::Bool { value, .. } => Classified::Literal(LiteralTest::Bool(*value)),
        }
    }

    fn internal_error(&self, message: &str) -> Box<Diagnostic> {
        Box::new(Diagnostic::error(
            codes::INTERNAL_INVARIANT_VIOLATED,
            self.source,
            Span::dummy(),
            message.to_string(),
        ))
    }
}

/// One pattern slot in a decision-tree matrix row: either a real
/// surface pattern, or a synthetic filler for a newly-introduced
/// occurrence that a wildcard/binding/unit-case row doesn't itself
/// constrain -- keeps every row in one matrix the same length (see
/// `Lowering::lower_decision`'s doc comment).
#[derive(Clone, Copy)]
enum PatternSlot<'h> {
    Real(&'h HirPattern),
    Wildcard,
}

#[derive(Clone)]
struct Occurrence {
    value: ValueId,
    ty: Ty,
}

struct MatrixRow<'h> {
    arm_index: usize,
    patterns: Vec<PatternSlot<'h>>,
    bindings: Vec<(LocalId, ValueId)>,
}

enum Classified<'h> {
    Wildcard,
    Bind(LocalId),
    Case {
        variant: ItemId,
        case: usize,
        args: &'h [HirPattern],
    },
    Literal(LiteralTest<'h>),
}

enum LiteralTest<'h> {
    Int(u128),
    Str(&'h str),
    Char(char),
    Bool(bool),
}

fn literal_eq(a: &LiteralTest, b: &LiteralTest) -> bool {
    match (a, b) {
        (LiteralTest::Int(x), LiteralTest::Int(y)) => x == y,
        (LiteralTest::Str(x), LiteralTest::Str(y)) => x == y,
        (LiteralTest::Char(x), LiteralTest::Char(y)) => x == y,
        (LiteralTest::Bool(x), LiteralTest::Bool(y)) => x == y,
        _ => false,
    }
}

fn literal_const(fb: &mut FnBuilder, lit: &LiteralTest, ty: &Ty) -> ValueId {
    match lit {
        LiteralTest::Int(v) => fb.push_value(ty.clone(), ValueKind::Const(Const::Int(*v))),
        LiteralTest::Str(s) => {
            fb.push_value(ty.clone(), ValueKind::Const(Const::Str((*s).to_string())))
        }
        LiteralTest::Char(c) => fb.push_value(ty.clone(), ValueKind::Const(Const::Char(*c))),
        LiteralTest::Bool(b) => fb.push_value(ty.clone(), ValueKind::Const(Const::Bool(*b))),
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
        lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &interner,
            id,
        )
        .expect("expected lowering to succeed")
    }

    /// Like `lower`, but for a program that type-checks cleanly and is
    /// expected to *fail* lowering (e.g. a named aggregate type in an
    /// executable signature) -- returns whatever `lower_module` actually
    /// produces instead of asserting success.
    fn lower_result(text: &str) -> Result<Module, Vec<Diagnostic>> {
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
        lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &interner,
            id,
        )
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
        let module = lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &interner,
            id,
        )
        .expect("expected lowering to succeed");
        crate::nir::verify_module(&module, id, &interner)
    }

    #[test]
    fn a_named_return_type_lowers_and_verifies_cleanly() {
        // Alpha 0.1.1: records now have a real aggregate runtime
        // representation, so a named type in a function signature is
        // no longer rejected -- it lowers and verifies like any other
        // type.
        let text = "record Point { x: i64 } func identity(p: Point) -> Point { p } \
                    func main() -> i64 { 42 }";
        let diagnostics = lower_and_verify(text);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn a_named_parameter_type_lowers_successfully() {
        let text = "record Point { x: i64 } func describe(p: Point) -> i64 { 0 } \
                    func main() -> i64 { 42 }";
        assert!(lower_result(text).is_ok());
    }

    #[test]
    fn variant_names_also_resolve_and_lower_successfully() {
        let text = "variant Shape { Circle } \
                    func describe(s: Shape) -> i64 { 0 } \
                    func main() -> i64 { 42 }";
        assert!(lower_result(text).is_ok());
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

    /// Item 1: an ordinary value-producing `if/else` allocates exactly
    /// one result slot, stores each branch's value into that same slot,
    /// and loads that same slot's value back at the merge point -- the
    /// three instructions must agree on one `ValueId`, not merely exist
    /// somewhere in the function.
    #[test]
    fn if_else_with_real_values_allocates_stores_and_loads_the_same_slot() {
        let module = lower("func f(x: bool) -> i64 { return if x { 1 } else { 2 } }");
        let instructions: Vec<&Instruction> = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .collect();

        let allocs: Vec<ValueId> = instructions
            .iter()
            .filter_map(|i| match i {
                Instruction::Value {
                    result,
                    kind: ValueKind::Alloc,
                    ty: Ty::I64,
                } => Some(*result),
                _ => None,
            })
            .collect();
        assert_eq!(
            allocs.len(),
            1,
            "expected exactly one i64 result slot, found {instructions:?}"
        );
        let slot = allocs[0];

        let stores: Vec<&Instruction> = instructions
            .iter()
            .filter(|i| matches!(i, Instruction::Store { slot: s, .. } if *s == slot))
            .copied()
            .collect();
        assert_eq!(
            stores.len(),
            2,
            "expected one store per branch into the result slot, found {instructions:?}"
        );

        let loads_result_slot = instructions.iter().any(|i| {
            matches!(
                i,
                Instruction::Value { kind: ValueKind::Load(s), .. } if *s == slot
            )
        });
        assert!(
            loads_result_slot,
            "expected the merge block to load the result slot, found {instructions:?}"
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

    /// Items 5 & 6: a fully diverging `if` produces no result slot at
    /// all -- no `alloc` (of `never` or of anything else attributable
    /// to the `if`'s result), no `store` of a fabricated value, and no
    /// `load` -- and lowers to exactly the entry, then, and else
    /// blocks; no extra merge block is created to be immediately
    /// unreachable.
    #[test]
    fn if_where_both_branches_diverge_allocates_no_result_slot() {
        let module = lower("func f(x: bool) -> i64 { if x { return 1 } else { return 2 } }");
        let blocks = &module.functions[0].blocks;
        assert_eq!(
            blocks.len(),
            3,
            "expected exactly entry + then + else, no merge block: {blocks:?}"
        );

        let instructions: Vec<&Instruction> = blocks.iter().flat_map(|b| &b.instructions).collect();
        assert!(
            !instructions.iter().any(|i| matches!(
                i,
                Instruction::Value {
                    kind: ValueKind::Alloc,
                    ..
                }
            )),
            "a fully diverging `if` must not allocate any result slot: {instructions:?}"
        );
        assert!(
            !instructions
                .iter()
                .any(|i| matches!(i, Instruction::Store { .. })),
            "a fully diverging `if` must not store a fabricated merge value: {instructions:?}"
        );
        assert!(
            !instructions.iter().any(|i| matches!(
                i,
                Instruction::Value {
                    kind: ValueKind::Load(_),
                    ..
                }
            )),
            "a fully diverging `if` must not load a result nothing produced: {instructions:?}"
        );
    }

    /// Item 5 (propagation): when a fully diverging `if` is used as a
    /// statement rather than the function's tail, `LoweredExpr::Diverged`
    /// must stop the surrounding block from lowering anything after it
    /// -- if it didn't, the `99` tail below would still appear as a
    /// `const.i64` instruction in the output.
    #[test]
    fn a_fully_diverging_if_statement_makes_the_rest_of_the_block_unreachable() {
        let module =
            lower("func f(flag: bool) -> i64 { if flag { return 1 } else { return 2 } 99 }");
        let has_99 = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Const(Const::Int(99)),
                        ..
                    }
                )
            });
        assert!(
            !has_99,
            "code after a fully diverging `if` statement must never be lowered"
        );
    }

    /// Item 8: the verifier independently accepts every CFG shape this
    /// fix produces -- real values, an else-less `if`, and a fully
    /// diverging `if` alike.
    #[test]
    fn the_verifier_accepts_every_if_lowering_shape() {
        for text in [
            "func f(x: bool) -> i64 { return if x { 1 } else { 2 } }",
            "func main() { if true { 1 } }",
            "func f(x: bool) -> i64 { if x { return 1 } else { return 2 } }",
            "func f(x: bool) -> i64 { if x { return 1 } else { return 2 } return 0 }",
        ] {
            let diagnostics = lower_and_verify(text);
            assert!(
                diagnostics.is_empty(),
                "unexpected diagnostics for {text:?}: {diagnostics:?}"
            );
        }
    }

    /// Item 9: the builder's own append-after-terminate guard (the
    /// safeguard `fix(nir): enforce block termination invariants` adds
    /// right at the `FnBuilder` API boundary) must actually fire if a
    /// future lowering bug reintroduces this shape -- exercised here by
    /// calling the builder directly, bypassing all real lowering.
    #[test]
    #[should_panic(expected = "already terminated")]
    fn appending_a_value_after_terminate_is_caught_by_the_builder_invariant() {
        let mut fb = FnBuilder::new(Ty::Unit);
        fb.terminate(Terminator::Return(None));
        fb.push_value(Ty::Unit, ValueKind::Const(Const::Unit));
    }

    #[test]
    #[should_panic(expected = "already terminated")]
    fn appending_a_store_after_terminate_is_caught_by_the_builder_invariant() {
        let mut fb = FnBuilder::new(Ty::Unit);
        let slot = fb.alloc_slot(Ty::I64);
        let value = fb.push_value(Ty::I64, ValueKind::Const(Const::Int(1)));
        fb.terminate(Terminator::Return(None));
        fb.push_store(slot, value);
    }

    #[test]
    #[should_panic(expected = "terminated twice")]
    fn terminating_a_block_twice_is_caught_by_the_builder_invariant() {
        let mut fb = FnBuilder::new(Ty::Unit);
        fb.terminate(Terminator::Return(None));
        fb.terminate(Terminator::Return(None));
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

    /// Runs the full pipeline through `check_module` but, unlike `lower`
    /// or `lower_result`, does *not* assert that typeck's own
    /// diagnostics are empty -- typeck already gates every construct
    /// tested here with its own diagnostic before lowering would
    /// normally ever run, so this deliberately bypasses that gate to
    /// exercise NIR's own defense-in-depth for a direct caller that
    /// skips typeck entirely (e.g. a tool driving `hir`/`nir` directly).
    fn lower_bypassing_typeck(text: &str) -> Result<Module, Vec<Diagnostic>> {
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
        lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &interner,
            id,
        )
    }

    fn assert_fails_with_i0001(text: &str, expect_in_message: &str) {
        let Err(diagnostics) = lower_bypassing_typeck(text) else {
            panic!("expected lowering to fail for: {text:?}");
        };
        assert!(
            diagnostics.iter().any(|d| d.code == "I0001"),
            "expected an I0001 diagnostic for {text:?}, got {diagnostics:?}"
        );
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains(expect_in_message)),
            "expected a diagnostic mentioning {expect_in_message:?} for {text:?}, got {diagnostics:?}"
        );
    }

    #[test]
    fn match_expression_now_lowers_successfully() {
        // Alpha 0.1.1: `match` has real NIR lowering (a decision tree
        // over `variant.switch`/`condbr`), so it no longer fails with
        // I0001.
        let module = lower("func f(x: i64) -> i64 { return match x { _ => 0 } }");
        assert_eq!(module.functions.len(), 1);
    }

    #[test]
    fn cast_fails_lowering_instead_of_forwarding_the_unconverted_value() {
        // Must never be lowered as identity: `as` performs no runtime
        // conversion in this milestone, so silently forwarding the
        // inner value would let a cast "succeed" while lying about what
        // it does.
        assert_fails_with_i0001("func f() -> f64 { value x = 1; return x as f64 }", "as");
    }

    #[test]
    fn postfix_try_fails_lowering_instead_of_forwarding_the_inner_value() {
        assert_fails_with_i0001("func f(x: i64) -> i64 { return x? }", "?");
    }

    #[test]
    fn range_expression_fails_lowering_instead_of_becoming_its_left_endpoint() {
        // Must never be lowered as "just the left endpoint": that would
        // silently misrepresent what the expression means, not merely
        // leave it unsupported.
        assert_fails_with_i0001("func f() { value r = 1..10; }", "range");
    }

    #[test]
    fn inclusive_range_expression_fails_lowering() {
        assert_fails_with_i0001("func f() { value r = 1..=10; }", "range");
    }

    #[test]
    fn defer_fails_lowering_instead_of_being_silently_dropped() {
        assert_fails_with_i0001("func f() { value x = 1; defer x + 1; }", "defer");
    }

    #[test]
    fn function_used_as_a_value_fails_lowering_instead_of_a_fabricated_error_value() {
        assert_fails_with_i0001(
            "func add(a: i64, b: i64) -> i64 { return a + b } \
             func f() -> i64 { value g = add; return g }",
            "add",
        );
    }

    #[test]
    fn break_with_a_value_fails_lowering_instead_of_discarding_it_silently() {
        assert_fails_with_i0001("func f() { loop { break 1; } }", "break");
    }

    #[test]
    fn break_with_a_unit_value_still_fails_lowering() {
        // Not just a non-unit value: *every* value-carrying break must
        // fail, regardless of the value's own type.
        assert_fails_with_i0001("func f() { loop { break {}; } }", "break");
    }

    #[test]
    fn one_function_failing_to_lower_fails_the_whole_module_atomically() {
        // `add` alone would lower cleanly, but `bad` (bypassing typeck's
        // gate, as above) cannot. Lowering must not return a `Module`
        // containing just `add` -- either everything lowers, or nothing
        // does.
        let text = "func add(left: i64, right: i64) -> i64 { return left + right } \
                    func bad(x: i64) -> i64 { return x? }";
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
        let outcome = lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &interner,
            id,
        );
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
