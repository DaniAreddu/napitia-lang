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
    BasicBlock, CaseLayout, Const, ExtendLayout, Function, Module, Param, ProtocolLayout,
    ProtocolMethodLayout, RecordLayout, Terminator, ValueId, ValueKind, VariantLayout,
};
use crate::diagnostics::Diagnostic;
use crate::hir::{
    ExprId, HirBlock, HirElse, HirExpr, HirFieldInit, HirFunction, HirMatchArm, HirMatchArmBody,
    HirModule, HirPattern, HirStmt, ItemId, LocalId, PatternId,
};
use crate::limits::MAX_PATTERN_DEPTH;
use crate::source::{SourceId, Span};
use crate::symbol::{Interner, Symbol};
use crate::syntax::ast::{AssignOp, BinaryOp, UnaryOp};
use crate::types::{CapabilityRequirement, Evidence, Ty, is_numeric, primitive_from_name};

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
    call_type_args: &HashMap<ExprId, Vec<Ty>>,
    call_evidence: &HashMap<ExprId, Vec<Evidence>>,
    protocol_call_evidence: &HashMap<ExprId, Evidence>,
    interner: &Interner,
    source: SourceId,
) -> Result<Module, Vec<Diagnostic>> {
    // Every module-level item's ItemId must be globally unique across
    // records, variants, and functions alike -- not just unique within
    // its own kind. hir::lower's own name resolution already keeps this
    // true for any HIR it produces, but this is a public entry point a
    // caller can invoke directly with a hand-built HirModule bypassing
    // that guarantee. Without this check, a duplicate id would make
    // record_layouts/variant_layouts silently overwrite the first
    // entry on insert, then panic on the second of two removals below
    // ("just inserted" no longer holds); a cross-kind collision would
    // let records/variants/function_sigs disagree about what the same
    // id names. Checked here, before any layout is built or any
    // function is lowered, so a malformed module fails atomically
    // rather than reaching either failure mode.
    let identity_diagnostics = validate_item_identities(hir, interner, source);
    if !identity_diagnostics.is_empty() {
        return Err(identity_diagnostics);
    }

    let mut record_layouts: HashMap<ItemId, RecordLayout> = HashMap::new();
    let mut record_order: Vec<ItemId> = Vec::new();
    for r in &hir.records {
        let fields = r
            .fields
            .iter()
            .map(|f| (f.name, resolve_named_type(interner, &f.ty)))
            .collect();
        record_order.push(r.id);
        record_layouts.insert(
            r.id,
            RecordLayout {
                name: r.name,
                type_params: r.type_params.iter().map(|p| (p.id, p.name)).collect(),
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
                    .map(|t| resolve_named_type(interner, t))
                    .collect(),
            })
            .collect();
        variant_order.push(v.id);
        variant_layouts.insert(
            v.id,
            VariantLayout {
                name: v.name,
                type_params: v.type_params.iter().map(|p| (p.id, p.name)).collect(),
                cases,
            },
        );
    }

    let mut function_sigs = HashMap::new();
    let mut function_requirements: HashMap<ItemId, Vec<CapabilityRequirement>> = HashMap::new();
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
        let type_params = f.type_params.iter().map(|p| p.id).collect();
        function_sigs.insert(f.id, (type_params, params, ret));
        function_requirements.insert(
            f.id,
            f.requirements
                .iter()
                .map(|r| resolve_requirement(interner, r))
                .collect(),
        );
    }

    // Every declared protocol's layout, in declaration order -- built
    // once, up front, since an extend's own method table (below) needs
    // to look a protocol's method names up by index.
    let mut protocols: Vec<(ItemId, ProtocolLayout)> = Vec::with_capacity(hir.protocols.len());
    for p in &hir.protocols {
        let methods = p
            .methods
            .iter()
            .map(|m| ProtocolMethodLayout {
                name: m.name,
                params: m
                    .params
                    .iter()
                    .map(|t| resolve_named_type(interner, t))
                    .collect(),
                return_type: m
                    .return_type
                    .as_ref()
                    .map(|t| resolve_named_type(interner, t))
                    .unwrap_or(Ty::Unit),
            })
            .collect();
        protocols.push((
            p.id,
            ProtocolLayout {
                name: p.name,
                type_params: p.type_params.iter().map(|tp| (tp.id, tp.name)).collect(),
                methods,
            },
        ));
    }

    // Every accepted extend's layout, in declaration order. `nir::lower`
    // trusts that every extend it sees here already passed `typeck`'s
    // authority/overlap/completeness validation (this module's own
    // "input already passed type-checking" contract, see its own module
    // doc) -- an unauthorized or incomplete extend never reaches here at
    // all in the ordinary pipeline. Each extend method is registered
    // exactly like an ordinary function (sharing the extend's own
    // `type_params`/`requirements`) and lowered the same way, below.
    let mut extends: Vec<(ItemId, ExtendLayout)> = Vec::with_capacity(hir.extends.len());
    let mut function_named_type_params: HashMap<ItemId, Vec<(crate::hir::TypeParamId, Symbol)>> =
        HashMap::new();
    for e in &hir.extends {
        let extend_type_params: Vec<crate::hir::TypeParamId> =
            e.type_params.iter().map(|p| p.id).collect();
        let extend_named_type_params: Vec<(crate::hir::TypeParamId, Symbol)> =
            e.type_params.iter().map(|p| (p.id, p.name)).collect();
        for m in &e.methods {
            function_named_type_params.insert(m.id, extend_named_type_params.clone());
        }
        let protocol_arguments: Vec<Ty> = e
            .protocol_arguments
            .iter()
            .map(|t| resolve_named_type(interner, t))
            .collect();
        let requirements: Vec<CapabilityRequirement> = e
            .requirements
            .iter()
            .map(|r| resolve_requirement(interner, r))
            .collect();
        let proto_method_names: Vec<Symbol> = protocols
            .iter()
            .find(|(id, _)| *id == e.protocol)
            .map(|(_, layout)| layout.methods.iter().map(|m| m.name).collect())
            .unwrap_or_default();
        let mut methods_by_index: Vec<Option<ItemId>> = vec![None; proto_method_names.len()];
        for m in &e.methods {
            function_sigs.insert(
                m.id,
                (
                    extend_type_params.clone(),
                    m.params
                        .iter()
                        .map(|p| resolve_named_type(interner, &p.ty))
                        .collect(),
                    m.return_type
                        .as_ref()
                        .map(|t| resolve_named_type(interner, t))
                        .unwrap_or(Ty::Unit),
                ),
            );
            function_requirements.insert(m.id, requirements.clone());
            if let Some(index) = proto_method_names.iter().position(|n| *n == m.name) {
                methods_by_index[index] = Some(m.id);
            }
        }
        let mut methods = Vec::with_capacity(methods_by_index.len());
        for (index, method_id) in methods_by_index.into_iter().enumerate() {
            match method_id {
                Some(id) => methods.push(id),
                None => {
                    return Err(vec![Diagnostic::error(
                        codes::INTERNAL_INVARIANT_VIOLATED,
                        source,
                        e.span,
                        format!(
                            "extend for protocol method index {index} has no implementing function; typeck should have already rejected this incomplete extend"
                        ),
                    )]);
                }
            }
        }
        extends.push((
            e.id,
            ExtendLayout {
                protocol: e.protocol,
                type_params: extend_named_type_params,
                protocol_arguments,
                requirements,
                methods,
            },
        ));
    }

    let mut lowering = Lowering {
        local_types,
        expr_types,
        pattern_case,
        call_type_args,
        call_evidence,
        protocol_call_evidence,
        interner,
        source,
        records: record_layouts,
        variants: variant_layouts,
        function_sigs,
        function_requirements,
        function_named_type_params,
    };
    let mut functions = Vec::new();
    let mut diagnostics = Vec::new();
    for f in &hir.functions {
        match lowering.lower_function(f) {
            Ok(nir_fn) => functions.push(nir_fn),
            Err(diag) => diagnostics.push(*diag),
        }
    }
    for e in &hir.extends {
        for m in &e.methods {
            match lowering.lower_function(m) {
                Ok(nir_fn) => functions.push(nir_fn),
                Err(diag) => diagnostics.push(*diag),
            }
        }
    }

    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }

    // `record_order`/`variant_order` were built by pushing each item's
    // id exactly once per item in `hir.records`/`hir.variants`, and the
    // identity validation above already rejected any duplicate id
    // within either kind -- so every id removed here is guaranteed to
    // still be present, exactly once. Returned as a diagnostic instead
    // of an `.expect()` panic anyway: this function's own atomicity
    // guarantee should never depend on a caller trusting that an
    // earlier check in this same function was never changed to miss a
    // case, the same defense-in-depth posture the rest of this module
    // already takes toward every other stage's guarantees.
    let mut records = Vec::with_capacity(record_order.len());
    for id in record_order {
        let Some(layout) = lowering.records.remove(&id) else {
            return Err(vec![*lowering.internal_error(&format!(
                "record layout for {id:?} was not built during lowering"
            ))]);
        };
        records.push((id, layout));
    }
    let mut variants = Vec::with_capacity(variant_order.len());
    for id in variant_order {
        let Some(layout) = lowering.variants.remove(&id) else {
            return Err(vec![*lowering.internal_error(&format!(
                "variant layout for {id:?} was not built during lowering"
            ))]);
        };
        variants.push((id, layout));
    }

    Ok(Module {
        functions,
        records,
        variants,
        protocols,
        extends,
    })
}

/// Which kind of module-level item an `ItemId` names, for a collision
/// diagnostic to describe accurately.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ItemKind {
    Record,
    Variant,
    Function,
    Protocol,
    Extend,
}

impl ItemKind {
    fn describe(self) -> &'static str {
        match self {
            ItemKind::Protocol => "protocol",
            ItemKind::Extend => "extend",
            ItemKind::Record => "record",
            ItemKind::Variant => "variant",
            ItemKind::Function => "function",
        }
    }
}

/// Checks that every record/variant/function's `ItemId` is unique
/// across the whole module -- not merely unique within its own kind.
/// Visits records, then variants, then functions, each in their own
/// declaration order (never a `HashMap`'s iteration order), so the
/// diagnostics this produces are identical across repeated runs.
fn validate_item_identities(
    hir: &HirModule,
    interner: &Interner,
    source: SourceId,
) -> Vec<Diagnostic> {
    let mut seen: HashMap<ItemId, ItemKind> = HashMap::new();
    let mut diagnostics = Vec::new();
    let mut check = |id: ItemId, kind: ItemKind, name: Symbol, span: Span| {
        let text = interner.resolve(name);
        match seen.get(&id) {
            Some(&existing) if existing == kind => {
                diagnostics.push(Diagnostic::error(
                    codes::INTERNAL_INVARIANT_VIOLATED,
                    source,
                    span,
                    format!(
                        "{} `{text}` reuses an id already used by another {} in this module",
                        kind.describe(),
                        kind.describe()
                    ),
                ));
            }
            Some(&existing) => {
                diagnostics.push(Diagnostic::error(
                    codes::INTERNAL_INVARIANT_VIOLATED,
                    source,
                    span,
                    format!(
                        "{} `{text}` reuses an id already used by a {} in this module",
                        kind.describe(),
                        existing.describe()
                    ),
                ));
            }
            None => {
                seen.insert(id, kind);
            }
        }
    };
    for r in &hir.records {
        check(r.id, ItemKind::Record, r.name, r.span);
    }
    for v in &hir.variants {
        check(v.id, ItemKind::Variant, v.name, v.span);
    }
    for f in &hir.functions {
        check(f.id, ItemKind::Function, f.name, f.name_span);
    }
    for p in &hir.protocols {
        check(p.id, ItemKind::Protocol, p.name, p.name_span);
    }
    for e in &hir.extends {
        // An extend has no name of its own; its own protocol's name is
        // used only for this diagnostic's own text, never as this
        // extend's identity. An extend whose protocol reference never
        // resolved (`hir::lower` already reported that separately) has
        // no name to borrow here, so its own id-collision check is
        // skipped rather than fabricating one.
        if let Some(protocol_name) = hir
            .protocols
            .iter()
            .find(|p| p.id == e.protocol)
            .map(|p| p.name)
        {
            check(e.id, ItemKind::Extend, protocol_name, e.span);
        }
        for m in &e.methods {
            check(m.id, ItemKind::Function, m.name, m.name_span);
        }
    }
    diagnostics
}

/// Converts a type reference already resolved by `hir::lower` against
/// its *declaring module's own* namespace (see [`crate::hir::HirType`])
/// into `Ty` -- an aggregate reference is already an exact `ItemId` by
/// this point, no lookup needed. Unlike typeck, an `Unresolved` name
/// that also isn't a primitive is never reachable in the ordinary
/// pipeline (typeck already rejected it with its own `T0006` diagnostic
/// before lowering ever ran), so falling back to `Ty::Error` here is
/// only ever exercised by a direct caller that bypasses that gate -- the
/// same defense-in-depth posture as the rest of this module.
fn resolve_named_type(interner: &Interner, ty: &crate::hir::HirType) -> Ty {
    resolve_named_type_at_depth(interner, ty, 0)
}

/// `depth` bounds recursion into nested `Ty::Applied` arguments the same
/// way every other stage that walks a type application does
/// (`crate::limits::MAX_GENERIC_DEPTH`) -- `nir::lower_module` is a
/// public entry point a direct caller can invoke with hand-built HIR
/// that bypasses `hir::lower`'s own depth guard (R0019) entirely, so
/// this cannot simply trust that earlier stage to have already bounded
/// the input.
fn resolve_named_type_at_depth(interner: &Interner, ty: &crate::hir::HirType, depth: usize) -> Ty {
    if depth > crate::limits::MAX_GENERIC_DEPTH {
        return Ty::Error;
    }
    match ty {
        crate::hir::HirType::Aggregate {
            item, name, args, ..
        } => {
            if args.is_empty() {
                Ty::Named(*item, *name)
            } else {
                // A generic declaration's own layout keeps its field/
                // payload/parameter types *symbolic* (one canonical
                // schema, never duplicated per instantiation, `rfcs/0008`)
                // -- but a reference *to* that declaration (a parameter
                // typed `Box[i64]`, say) is always a concrete application,
                // resolved recursively the same way `hir::lower`/`typeck`
                // already do.
                Ty::Applied(
                    *item,
                    args.iter()
                        .map(|a| resolve_named_type_at_depth(interner, a, depth + 1))
                        .collect(),
                )
            }
        }
        crate::hir::HirType::Param { id, name, .. } => Ty::Param(*id, *name),
        crate::hir::HirType::Unresolved { name, .. } => {
            let text = interner.resolve(*name);
            primitive_from_name(text).unwrap_or(Ty::Error)
        }
    }
}

/// Converts one HIR-level capability requirement (`rfcs/0009`) into its
/// canonical form, the same "read back what typeck already resolved,
/// never re-validate" discipline `resolve_named_type` follows -- typeck
/// already rejected an unknown protocol or wrong arity; this module
/// never runs at all for a program that didn't already pass that check
/// (`nir::lower`'s own module doc).
fn resolve_requirement(
    interner: &Interner,
    requirement: &crate::hir::HirCapabilityRequirement,
) -> crate::types::CapabilityRequirement {
    crate::types::CapabilityRequirement::new(
        requirement.protocol,
        requirement
            .arguments
            .iter()
            .map(|a| resolve_named_type(interner, a))
            .collect(),
    )
}

struct Lowering<'a> {
    local_types: &'a HashMap<LocalId, Ty>,
    expr_types: &'a HashMap<ExprId, Ty>,
    pattern_case: &'a HashMap<PatternId, (ItemId, usize)>,
    /// Every generic call/construction's own concrete type arguments, as
    /// `typeck` resolved them, keyed by that expression's `ExprId`
    /// (`rfcs/0008`) -- read back here rather than re-inferred, the same
    /// "typeck already decided, lowering only reads it back" discipline
    /// `expr_types`/`local_types` already follow.
    call_type_args: &'a HashMap<ExprId, Vec<Ty>>,
    /// Every call's own resolved capability evidence (`rfcs/0009`), one
    /// entry per requirement the callee declares, in that same order --
    /// read back here, never re-resolved (mirrors `call_type_args`).
    call_evidence: &'a HashMap<ExprId, Vec<Evidence>>,
    /// Every explicit protocol-call expression's own resolved evidence,
    /// keyed by that call's own `ExprId` (`rfcs/0009`).
    protocol_call_evidence: &'a HashMap<ExprId, Evidence>,
    interner: &'a Interner,
    source: SourceId,
    records: HashMap<ItemId, RecordLayout>,
    variants: HashMap<ItemId, VariantLayout>,
    /// `(this function's own generic parameters, its param types, its
    /// return type)`. The parameter/return types may reference the
    /// first element via `Ty::Param`; a call site substitutes its own
    /// `call_type_args` for them (`rfcs/0008`).
    function_sigs: HashMap<ItemId, (Vec<crate::hir::TypeParamId>, Vec<Ty>, Ty)>,
    /// Every function/extend method's own capability requirements
    /// (`rfcs/0009`), in declared order -- a `Call` targeting one of
    /// these carries exactly this many evidence entries.
    function_requirements: HashMap<ItemId, Vec<CapabilityRequirement>>,
    /// An extend method's own *displayed* generic parameters -- always
    /// its owning extend's own `type_params` (never empty the way its
    /// own `HirFunction::type_params` is), keyed by the method's own
    /// `ItemId`. Absent (falls back to `f.type_params` directly) for an
    /// ordinary function, which owns its parameters itself.
    function_named_type_params: HashMap<ItemId, Vec<(crate::hir::TypeParamId, Symbol)>>,
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

        // An extend method's own `f.type_params` is always empty (see
        // `HirFunction::type_params`'s own doc comment): its real
        // generic parameters are its *owning extend's* own, looked up
        // here by name rather than assumed empty, so a conditional
        // extend's NIR function still carries its own `[T]` correctly.
        let type_params = self
            .function_named_type_params
            .get(&f.id)
            .cloned()
            .unwrap_or_else(|| f.type_params.iter().map(|p| (p.id, p.name)).collect());
        let requirements = self
            .function_requirements
            .get(&f.id)
            .cloned()
            .unwrap_or_default();
        Ok(Function {
            id: f.id,
            name: f.name,
            type_params,
            requirements,
            params,
            return_type,
            blocks,
        })
    }

    fn resolve_named_type(&self, ty: &crate::hir::HirType) -> Ty {
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
            // program) -- routed through the same lower_variant_construct
            // a `Variant.Case(...)` call goes through, with an empty
            // argument list, so an unknown variant, an invalid case
            // index, and (via the existing arity check) a bare
            // reference to a case that actually carries a payload are
            // all rejected the same one way, not by a second,
            // independently-drifting implementation here.
            HirExpr::CaseRef { variant, case, .. } => {
                self.lower_variant_construct(fb, *variant, *case, &[], expr)
            }
            // There are no first-class/dynamic protocol methods in
            // Alpha 0.1.5 (`rfcs/0009`); typeck already rejects a bare
            // (uncalled) reference outright before lowering ever runs
            // in the normal pipeline.
            HirExpr::ProtocolMethodRef { name, span, .. } => {
                let text = self.interner.resolve(*name);
                Err(self.unsupported(
                    *span,
                    &format!("using protocol method `{text}` as a first-class value"),
                ))
            }
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
        if let HirExpr::ProtocolMethodRef {
            protocol,
            arguments,
            method,
            ..
        } = callee
        {
            return self.lower_protocol_call(fb, *protocol, arguments, *method, args, call_expr);
        }

        let HirExpr::Function { item, .. } = callee else {
            // typeck already rejects a call whose callee doesn't
            // resolve to an actual function (Napitia has no first-class
            // function values); reaching here means a caller lowered
            // hand-built HIR bypassing that check. The callee and
            // arguments are still checked for their own divergence (a
            // diverging callee/argument really would make the whole
            // call unreachable), but the call itself must never
            // fabricate a successful `Ty::Error`/`Const::Unit` result --
            // that would silently invent a value nothing in the source
            // actually produced.
            if matches!(self.lower_expr(fb, callee)?, LoweredExpr::Diverged) {
                return Ok(LoweredExpr::Diverged);
            }
            for arg in args {
                if matches!(self.lower_expr(fb, arg)?, LoweredExpr::Diverged) {
                    return Ok(LoweredExpr::Diverged);
                }
            }
            return Err(self.internal_error("call target does not resolve to a function"));
        };
        let (type_params, param_tys, _ret_ty) = self
            .function_sigs
            .get(item)
            .cloned()
            .unwrap_or_else(|| (Vec::new(), Vec::new(), Ty::Error));
        // Resolved once by `typeck` (inferred or explicit) and read back
        // here, never re-inferred -- the same "typeck already decided"
        // discipline every other type in this module already follows
        // (`rfcs/0008`). Empty for a non-generic call.
        let type_args = self.resolve_call_type_args(call_expr.id(), &type_params, "a call")?;
        let subst: HashMap<crate::hir::TypeParamId, Ty> = type_params
            .into_iter()
            .zip(type_args.iter().cloned())
            .collect();
        let mut arg_values = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            let hint = param_tys
                .get(i)
                .map(|t| crate::types::substitute(t, &subst))
                .unwrap_or(Ty::Error);
            match self.lower_expr_hinted(fb, arg, &hint)? {
                LoweredExpr::Value(v) => arg_values.push(v),
                LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
            }
        }
        let requirements = self
            .function_requirements
            .get(item)
            .cloned()
            .unwrap_or_default();
        let evidence = self.resolve_call_evidence(call_expr.id(), &requirements, "a call")?;
        Ok(LoweredExpr::Value(fb.push_value(
            self.expr_ty(call_expr),
            ValueKind::Call(*item, type_args, arg_values, evidence),
        )))
    }

    /// Lowers an explicit protocol-call expression,
    /// `Protocol[Args].method(..)` (`rfcs/0009`) -- `typeck` already
    /// resolved exactly which extension (or forwarded requirement)
    /// answers this specific call (`protocol_call_evidence`); lowering
    /// only ever reads that back, never re-resolves it.
    fn lower_protocol_call(
        &mut self,
        fb: &mut FnBuilder,
        protocol: ItemId,
        arguments: &[crate::hir::HirType],
        method: usize,
        args: &[HirExpr],
        call_expr: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        let resolved_arguments: Vec<Ty> = arguments
            .iter()
            .map(|a| self.resolve_named_type(a))
            .collect();
        let mut arg_values = Vec::with_capacity(args.len());
        for arg in args {
            match self.lower_expr(fb, arg)? {
                LoweredExpr::Value(v) => arg_values.push(v),
                LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
            }
        }
        let Some(evidence) = self.protocol_call_evidence.get(&call_expr.id()).cloned() else {
            return Err(self.internal_error(
                "protocol call has no recorded call-site evidence from typeck's capability solver",
            ));
        };
        Ok(LoweredExpr::Value(fb.push_value(
            self.expr_ty(call_expr),
            ValueKind::ProtocolCall {
                protocol,
                arguments: resolved_arguments,
                method,
                evidence,
                args: arg_values,
            },
        )))
    }

    fn lower_variant_construct(
        &mut self,
        fb: &mut FnBuilder,
        variant: ItemId,
        case: usize,
        args: &[HirExpr],
        call_expr: &HirExpr,
    ) -> LowerResult<LoweredExpr> {
        // A well-typed program always has a real entry here (typeck
        // already validated the variant and case); a caller that lowers
        // hand-built HIR bypassing typeck must get a structured
        // diagnostic instead of an out-of-bounds panic or a fabricated
        // payload-type hint for an unknown case.
        let (type_params, payload_tys) = match self.variants.get(&variant).and_then(|v| {
            let ids: Vec<crate::hir::TypeParamId> =
                v.type_params.iter().map(|(id, _)| *id).collect();
            v.cases.get(case).map(|c| (ids, c.payload.clone()))
        }) {
            Some(found) => found,
            None => {
                return Err(self.internal_error(&format!(
                    "variant construction references unknown variant/case ({variant:?}, {case})"
                )));
            }
        };
        // Resolved once by `typeck` and read back here, never re-inferred
        // (`rfcs/0008`) -- empty for a non-generic variant. This also
        // covers a *bare* unit-case reference (`Maybe[i64].None`, no call
        // syntax at all), which lowers through this same function.
        let type_args =
            self.resolve_call_type_args(call_expr.id(), &type_params, "a variant construction")?;
        let subst: HashMap<crate::hir::TypeParamId, Ty> = type_params
            .into_iter()
            .zip(type_args.iter().cloned())
            .collect();
        // The complete shape is validated before a single argument is
        // evaluated: too few arguments would otherwise leave `payload`
        // shorter than the case's declared arity, and too many would
        // leave it longer, either way fabricating a `variant.create`
        // whose payload count doesn't match its own declared case.
        if args.len() != payload_tys.len() {
            return Err(self.internal_error(&format!(
                "variant construction for case {case} of {variant:?} has {} argument(s), expected {}",
                args.len(),
                payload_tys.len()
            )));
        }
        let mut payload = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            let hint = payload_tys
                .get(i)
                .map(|t| crate::types::substitute(t, &subst))
                .unwrap_or(Ty::Error);
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
                type_args,
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
        // typeck/hir::lower already reject a source-level unknown
        // record, out-of-range/duplicate field index, or missing field;
        // reaching any of these means a caller lowered a
        // HirExpr::RecordLiteral built by hand (or otherwise bypassing
        // those checks). The complete shape is validated up front,
        // before a single field is evaluated, so lowering never
        // silently drops an out-of-range field into nowhere or lets a
        // duplicate index overwrite an earlier field's already-lowered
        // value in its temporary slot -- either would fabricate a
        // `record.create` that doesn't reflect what was actually
        // written.
        let Some(layout) = self.records.get(&record) else {
            return Err(self.internal_error(&format!(
                "record construction references unknown record {record:?}"
            )));
        };
        let field_count = layout.fields.len();
        let mut seen = vec![false; field_count];
        for f in fields {
            let Some(slot_seen) = seen.get_mut(f.field_index) else {
                return Err(self.internal_error(&format!(
                    "record construction's field index {} is out of range for {record:?}'s {field_count} declared field(s)",
                    f.field_index
                )));
            };
            if *slot_seen {
                return Err(self.internal_error(&format!(
                    "record construction reuses field index {} more than once",
                    f.field_index
                )));
            }
            *slot_seen = true;
        }
        if let Some(missing) = seen.iter().position(|&s| !s) {
            return Err(
                self.internal_error(&format!("record construction is missing field {missing}"))
            );
        }

        // Resolved once by `typeck` and read back here, never re-inferred
        // (`rfcs/0008`) -- empty for a non-generic record. Generic record
        // construction always supplies this explicitly (`Box[i64] { .. }`),
        // so it is never itself inferred the way a call's can be.
        let type_params: Vec<crate::hir::TypeParamId> = self.records[&record]
            .type_params
            .iter()
            .map(|(id, _)| *id)
            .collect();
        let type_args =
            self.resolve_call_type_args(literal_expr.id(), &type_params, "a record construction")?;
        let subst: HashMap<crate::hir::TypeParamId, Ty> = type_params
            .into_iter()
            .zip(type_args.iter().cloned())
            .collect();

        let mut by_index: Vec<Option<ValueId>> = vec![None; field_count];
        for f in fields {
            let declared = self.records[&record].fields[f.field_index].1.clone();
            let hint = crate::types::substitute(&declared, &subst);
            match self.lower_expr_hinted(fb, &f.value, &hint)? {
                LoweredExpr::Value(v) => by_index[f.field_index] = Some(v),
                // A diverging initializer means the whole construction
                // never completes; no field written after it in source
                // order is lowered as reachable work.
                LoweredExpr::Diverged => return Ok(LoweredExpr::Diverged),
            }
        }
        let ordered: Vec<ValueId> = by_index
            .into_iter()
            .map(|v| v.expect("every index was already proven present above"))
            .collect();
        Ok(LoweredExpr::Value(fb.push_value(
            self.expr_ty(literal_expr),
            ValueKind::RecordCreate(record, type_args, ordered),
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
        // A generic record's own body (e.g. `unwrap[T](box: Box[T]) ->
        // T { box.value }`) accesses a field whose base is symbolically
        // typed `Box[T]` (`Ty::Applied`), never `Ty::Named` -- checked
        // once, symbolically, the same way every other operation on an
        // unconstrained type parameter is (`rfcs/0008`). Field lookup
        // itself only ever needs the declaration's own (unsubstituted)
        // field list, never the concrete/symbolic arguments, so both
        // forms resolve identically here.
        let record = match base_ty {
            Ty::Named(record, _) => record,
            Ty::Applied(record, _) => record,
            _ => {
                return Err(
                    self.unsupported(field_expr.span(), "field access on a non-record type")
                );
            }
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
            self.lower_decision(fb, rows, occurrences, arms, None, 0)?;
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
            0,
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
        depth: usize,
    ) -> LowerResult<()> {
        // Each round trip through lower_decision and one of
        // lower_bool_switch/lower_variant_switch/lower_literal_chain
        // consumes exactly one occurrence position -- one nesting
        // level of the pattern(s) being decided between -- on this
        // pass's own native call stack. typeck's check_pattern already
        // keeps every pattern the normal pipeline produces shallow
        // enough that this can never fire there, but lower_module is a
        // public entry point a direct caller can invoke with hand-built
        // HIR bypassing typeck entirely, so this needs its own
        // independent bound too, matching hir::lower_pattern's and
        // typeck::is_useful's -- all sharing crate::limits::MAX_PATTERN_DEPTH.
        if depth > MAX_PATTERN_DEPTH {
            return Err(self.internal_error("match decision tree is nested too deeply to lower"));
        }
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

        // A generic variant's scrutinee/occurrence is `Ty::Applied`, not
        // `Ty::Named` -- `Maybe[bool]` must still dispatch to the same
        // variant-switch lowering a non-generic variant's `Ty::Named`
        // does, or it falls through to the literal chain below and
        // fails the instant it meets its first `Some`/`None` pattern
        // (`rfcs/0008`).
        let scrutinee_variant = match &occurrences[0].ty {
            Ty::Named(item, _) | Ty::Applied(item, _) => Some(*item),
            _ => None,
        };
        if scrutinee_variant.is_some_and(|item| self.variants.contains_key(&item)) {
            self.lower_variant_switch(fb, rows, occurrences, arms, merge, depth)
        } else if matches!(&occurrences[0].ty, Ty::Bool) {
            // `bool` is a closed two-constructor domain (like a
            // variant's finite case set), so it is switched on
            // directly rather than through the open-domain literal
            // chain below -- an exhaustive `match true { true => ..,
            // false => .. }` (no wildcard at all) would otherwise have
            // no catch-all to terminate that chain's recursion on.
            self.lower_bool_switch(fb, rows, occurrences, arms, merge, depth)
        } else {
            self.lower_literal_chain(fb, rows, occurrences, arms, merge, depth)
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_bool_switch<'h>(
        &mut self,
        fb: &mut FnBuilder,
        rows: Vec<MatrixRow<'h>>,
        occurrences: Vec<Occurrence>,
        arms: &'h [HirMatchArm],
        merge: Option<(ValueId, BlockId)>,
        depth: usize,
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
            return self.lower_decision(fb, new_rows, rest_occ, arms, merge, depth + 1);
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
            self.lower_decision(fb, new_rows, rest_occ.clone(), arms, merge, depth + 1)?;
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_variant_switch<'h>(
        &mut self,
        fb: &mut FnBuilder,
        rows: Vec<MatrixRow<'h>>,
        occurrences: Vec<Occurrence>,
        arms: &'h [HirMatchArm],
        merge: Option<(ValueId, BlockId)>,
        depth: usize,
    ) -> LowerResult<()> {
        let occ = occurrences[0].clone();
        let rest_occ = occurrences[1..].to_vec();
        let (variant_item, concrete_args): (ItemId, Vec<Ty>) = match occ.ty.clone() {
            Ty::Named(item, _) => (item, Vec::new()),
            Ty::Applied(item, args) => (item, args),
            _ => return Err(self.internal_error("expected a variant-typed occurrence")),
        };
        let payload_subst: HashMap<crate::hir::TypeParamId, Ty> = self
            .variants
            .get(&variant_item)
            .map(|v| v.type_params.iter().map(|(id, _)| *id).collect::<Vec<_>>())
            .into_iter()
            .flatten()
            .zip(concrete_args.iter().cloned())
            .collect();

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
            return self.lower_decision(fb, new_rows, rest_occ, arms, merge, depth + 1);
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
            // The declaration's own *symbolic* payload shape (may
            // contain `Ty::Param`), substituted with this occurrence's
            // own concrete type arguments before use -- otherwise a
            // `Some[T]` payload's sub-occurrence would keep the
            // unconstrained `Ty::Param(T)` as its own type, and the next
            // `lower_decision` call would fail to recognize it as e.g.
            // `bool` and route it to the wrong lowering strategy
            // (`rfcs/0008`).
            let payload_types: Vec<Ty> = self.variants[&variant_item].cases[case_index]
                .payload
                .iter()
                .map(|t| crate::types::substitute(t, &payload_subst))
                .collect();
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
                        // typeck's check_pattern (fix for malformed
                        // variant-pattern arity) already rejects an
                        // args-count/declared-arity mismatch before the
                        // normal pipeline ever reaches lowering -- but a
                        // caller that hand-builds HIR and calls this
                        // module directly could still hand it one.
                        // `Vec::resize` would otherwise silently
                        // truncate extra sub-patterns (arity too small)
                        // or accept too few as if the rest were
                        // wildcards (arity too large), fabricating a
                        // decision tree that doesn't match what was
                        // actually written; a structured diagnostic is
                        // required instead, matching this function's
                        // existing unknown-case check just above.
                        if args.len() != arity {
                            return Err(self.internal_error(&format!(
                                "variant pattern for case {case_index} of {variant_item:?} has {} sub-pattern(s), expected {arity}",
                                args.len()
                            )));
                        }
                        let mut patterns: Vec<PatternSlot<'h>> =
                            args.iter().map(PatternSlot::Real).collect();
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
            self.lower_decision(fb, new_rows, new_occurrences, arms, merge, depth + 1)?;
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_literal_chain<'h>(
        &mut self,
        fb: &mut FnBuilder,
        rows: Vec<MatrixRow<'h>>,
        occurrences: Vec<Occurrence>,
        arms: &'h [HirMatchArm],
        merge: Option<(ValueId, BlockId)>,
        depth: usize,
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
                self.lower_decision(fb, new_rows, rest_occ, arms, merge, depth + 1)
            }
            Classified::Bind(local) => {
                let mut bindings = first.bindings.clone();
                bindings.push((local, occ.value));
                let new_rows = vec![MatrixRow {
                    arm_index: first.arm_index,
                    patterns: first.patterns[1..].to_vec(),
                    bindings,
                }];
                self.lower_decision(fb, new_rows, rest_occ, arms, merge, depth + 1)
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
                self.lower_decision(fb, then_rows, rest_occ.clone(), arms, merge, depth + 1)?;

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
                self.lower_decision(fb, else_rows, all_occ, arms, merge, depth + 1)
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

    /// Reads `expr_id`'s already-resolved type arguments back from
    /// typeck's `call_type_args` (never re-inferred here, matching every
    /// other type this module reads back rather than re-derives,
    /// `rfcs/0008`) -- the single place all three generic-carrying
    /// lowering sites (a call, a variant construction -- including a
    /// *bare* unit case, which lowers through the same function -- and a
    /// record construction) go through, so none of them can drift into
    /// silently defaulting to an empty argument list on their own.
    ///
    /// Absent metadata is only ever valid when `declared` is empty (a
    /// non-generic reference: no type arguments were ever going to
    /// exist). For a generic reference, missing metadata, or metadata
    /// whose length doesn't match `declared`, means typeck failed to
    /// validate/infer this site's type arguments before lowering ever
    /// saw it -- or a caller lowered hand-built HIR bypassing typeck
    /// entirely -- and is reported as a structured internal-lowering
    /// error, never silently truncated through `Vec::zip` (which would
    /// otherwise just drop the extra/missing arguments with no
    /// diagnostic at all) and never producing a partially-specialized
    /// `Call`/`RecordCreate`/`VariantCreate`.
    fn resolve_call_type_args(
        &self,
        expr_id: ExprId,
        declared: &[crate::hir::TypeParamId],
        what: &str,
    ) -> LowerResult<Vec<Ty>> {
        match self.call_type_args.get(&expr_id) {
            None if declared.is_empty() => Ok(Vec::new()),
            None => Err(self.internal_error(&format!(
                "{what} is generic (declaring {} type parameter(s)) but has no recorded call-site type arguments",
                declared.len()
            ))),
            Some(args) if args.len() == declared.len() => Ok(args.clone()),
            Some(args) => Err(self.internal_error(&format!(
                "{what} declares {} type parameter(s) but has {} recorded call-site type argument(s)",
                declared.len(),
                args.len()
            ))),
        }
    }

    /// Reads `expr_id`'s already-resolved capability evidence back from
    /// typeck's `call_evidence` (`rfcs/0009`), never re-resolved here --
    /// mirrors `resolve_call_type_args` exactly: absent metadata for a
    /// callee with no requirements is a valid empty list; anything else
    /// missing or wrong-arity is a structured internal-lowering error,
    /// never a silent default or a truncating zip.
    fn resolve_call_evidence(
        &self,
        expr_id: ExprId,
        requirements: &[CapabilityRequirement],
        what: &str,
    ) -> LowerResult<Vec<Evidence>> {
        match self.call_evidence.get(&expr_id) {
            None if requirements.is_empty() => Ok(Vec::new()),
            None => Err(self.internal_error(&format!(
                "{what} declares {} capability requirement(s) but has no recorded call-site evidence",
                requirements.len()
            ))),
            Some(evidence) if evidence.len() == requirements.len() => Ok(evidence.clone()),
            Some(evidence) => Err(self.internal_error(&format!(
                "{what} declares {} capability requirement(s) but has {} recorded call-site evidence entries",
                requirements.len(),
                evidence.len()
            ))),
        }
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
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
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
            &result.call_type_args,
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
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
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
            &result.call_type_args,
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
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
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
            &result.call_type_args,
            &interner,
            id,
        )
        .expect("expected lowering to succeed");
        crate::nir::verify_module(&module, id, &interner, &crate::hir::ItemRegistry::default())
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
    fn record_create_orders_fields_by_declaration_not_construction_site() {
        // Written `y` first, `x` second; declaration order is `x, y`.
        let module = lower(
            "record Point { x: i64, y: i64 } \
             func f() -> i64 { value p = Point { y: 2, x: 1 }; return p.x }",
        );
        let instructions: Vec<&Instruction> = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .collect();
        let (record, args) = instructions
            .iter()
            .find_map(|i| match i {
                Instruction::Value {
                    kind: ValueKind::RecordCreate(record, _, args),
                    ..
                } => Some((*record, args.clone())),
                _ => None,
            })
            .expect("expected a record.create instruction");
        // The two const instructions, in source order, produced `2`
        // then `1`; record.create's args must be reordered so the
        // first arg is `x`'s value (1) and the second is `y`'s (2).
        let const_values: HashMap<ValueId, i128> = instructions
            .iter()
            .filter_map(|i| match i {
                Instruction::Value {
                    result,
                    kind: ValueKind::Const(Const::Int(v)),
                    ..
                } => Some((*result, *v as i128)),
                _ => None,
            })
            .collect();
        assert_eq!(args.len(), 2);
        assert_eq!(const_values[&args[0]], 1, "expected x's value first");
        assert_eq!(const_values[&args[1]], 2, "expected y's value second");
        let _ = record;
    }

    #[test]
    fn record_field_initializers_evaluate_exactly_once_in_source_order() {
        let module = lower(
            "record Pair { a: i64, b: i64 } \
             func f() -> i64 { value p = Pair { b: 2, a: 1 }; return p.a }",
        );
        let const_count = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .filter(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Const(Const::Int(_)),
                        ..
                    }
                )
            })
            .count();
        assert_eq!(
            const_count, 2,
            "each field initializer must be evaluated exactly once"
        );
    }

    #[test]
    fn record_field_access_lowers_to_a_resolved_projection() {
        let module = lower(
            "record Point { x: i64, y: i64 } \
             func f() -> i64 { value p = Point { x: 1, y: 2 }; return p.y }",
        );
        let has_field_projection = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::RecordField { field: 1, .. },
                        ..
                    }
                )
            });
        assert!(
            has_field_projection,
            "expected a record.field projection at declaration index 1 (y)"
        );
    }

    #[test]
    fn variant_construction_lowers_explicitly() {
        let module = lower(
            "variant Shape { Circle(i64), Empty } \
             func f() -> i64 { value s = Shape.Circle(7); return 0 }",
        );
        let has_variant_create = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::VariantCreate { case: 0, .. },
                        ..
                    }
                )
            });
        assert!(has_variant_create, "expected a variant.create for case 0");
    }

    #[test]
    fn unit_case_construction_allocates_no_payload() {
        let module = lower(
            "variant Shape { Circle(i64), Empty } \
             func f() -> i64 { value s = Shape.Empty; return 0 }",
        );
        let payload_len = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| match i {
                Instruction::Value {
                    kind:
                        ValueKind::VariantCreate {
                            case: 1, payload, ..
                        },
                    ..
                } => Some(payload.len()),
                _ => None,
            })
            .expect("expected a variant.create for the unit case");
        assert_eq!(payload_len, 0);
    }

    #[test]
    fn variant_match_lowers_to_a_deterministic_switch() {
        let text = "variant Shape { Circle(i64), Square(i64) } \
                     func f(s: Shape) -> i64 { return match s { Circle(v) => v, Square(v) => v } }";
        let a = lower(text);
        let b = lower(text);
        let switches_of = |m: &Module| -> Vec<(ItemId, usize)> {
            m.functions[0]
                .blocks
                .iter()
                .filter_map(|blk| match &blk.terminator {
                    Terminator::Switch { variant, cases, .. } => Some((*variant, cases.len())),
                    _ => None,
                })
                .collect()
        };
        assert_eq!(
            switches_of(&a),
            switches_of(&b),
            "switch lowering must be deterministic across runs"
        );
        assert_eq!(switches_of(&a).len(), 1);
        assert_eq!(switches_of(&a)[0].1, 2, "expected one target per case");
    }

    #[test]
    fn nested_variant_pattern_lowers_to_nested_switches() {
        let text = "variant Inner { X, Y } \
                     variant Outer { A(Inner), B } \
                     func f(o: Outer) -> i64 { \
                         return match o { A(X) => 1, A(Y) => 2, B => 3 } \
                     }";
        let module = lower(text);
        let switch_count = module.functions[0]
            .blocks
            .iter()
            .filter(|b| matches!(b.terminator, Terminator::Switch { .. }))
            .count();
        assert_eq!(
            switch_count, 2,
            "expected one switch for Outer and one for the nested Inner pattern"
        );
    }

    #[test]
    fn fully_diverging_match_allocates_no_result_slot() {
        let text = "variant Shape { Circle, Empty } \
                     func f(s: Shape) -> i64 { \
                         match s { Circle => return 1, Empty => return 2 } \
                     }";
        let module = lower(text);
        let has_alloc = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| {
                matches!(
                    i,
                    Instruction::Value {
                        kind: ValueKind::Alloc,
                        ..
                    }
                )
            });
        assert!(
            !has_alloc,
            "a fully diverging match must not allocate a result slot"
        );
        let diagnostics = lower_and_verify(text);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn value_producing_match_allocates_exactly_one_result_slot() {
        let text = "variant Shape { Circle(i64), Empty } \
                     func f(s: Shape) -> i64 { return match s { Circle(v) => v, Empty => 0 } }";
        let module = lower(text);
        let alloc_count = module.functions[0]
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
        assert_eq!(alloc_count, 1);
        let diagnostics = lower_and_verify(text);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
    }

    #[test]
    fn payload_bindings_dominate_their_arm_body() {
        // Exercised through the verifier's own dominance analysis: a
        // payload extracted in a case's block, used in that same arm's
        // body (however deeply nested), must never be flagged as a
        // dominance violation.
        let text = "variant Shape { Circle(i64) } \
                     func f(s: Shape) -> i64 { \
                         return match s { Circle(v) => if v > 0 { v } else { 0 - v } } \
                     }";
        let diagnostics = lower_and_verify(text);
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
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
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
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
    fn record_construction_missing_a_field_fails_lowering_with_i0002_not_a_panic() {
        // hir::lower itself diagnoses a missing field (R0009) but does
        // not synthesize one, so a caller that lowers past *that*
        // diagnostic too (not just typeck's, unlike every other test in
        // this module) reaches NIR lowering with a genuinely incomplete
        // field list. Must fail atomically with a structured
        // diagnostic, never panic and never fabricate the missing
        // field's value.
        let text = "record Point { x: i64, y: i64 } \
                    func f() { value p = Point { x: 1 }; }";
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "unexpected lexer diagnostics: {diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "unexpected parser diagnostics: {diags:?}");
        let (hir, resolve_diags) = lower_hir(&module, id, &interner);
        assert!(
            resolve_diags.iter().any(|d| d.code == "R0009"),
            "expected a missing-field diagnostic from hir::lower: {resolve_diags:?}"
        );
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        let outcome = lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &interner,
            id,
        );
        let Err(diagnostics) = outcome else {
            panic!("expected lowering to fail for a record literal missing a field")
        };
        assert!(
            diagnostics.iter().any(|d| d.code == "I0002"),
            "expected an I0002 diagnostic, got {diagnostics:?}"
        );
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains("missing field")),
            "expected a diagnostic mentioning the missing field, got {diagnostics:?}"
        );
    }

    #[test]
    fn variant_pattern_arity_mismatch_fails_lowering_with_i0002_not_a_silent_truncation() {
        // typeck reports T0002 for this arity mismatch and the normal
        // driver never lowers past it, but a caller that lowers anyway
        // (bypassing that diagnostic gate, like every test in this
        // module using `lower_bypassing_typeck`) must not have the
        // extra sub-pattern silently dropped by a bare `Vec::resize` --
        // it must fail atomically with a structured diagnostic instead.
        let text = "variant Pair { Two(i64, i64) } \
                    func f(p: Pair) -> i64 { return match p { Two(a, b, c) => a } }";
        assert_fails_with_i0002(text, "sub-pattern");
    }

    fn assert_fails_with_i0002(text: &str, expect_in_message: &str) {
        let Err(diagnostics) = lower_bypassing_typeck(text) else {
            panic!("expected lowering to fail for: {text:?}");
        };
        assert!(
            diagnostics.iter().any(|d| d.code == "I0002"),
            "expected an I0002 diagnostic for {text:?}, got {diagnostics:?}"
        );
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains(expect_in_message)),
            "expected a diagnostic mentioning {expect_in_message:?} for {text:?}, got {diagnostics:?}"
        );
    }

    /// A trivial, otherwise-valid `HirFunction` (no params, no return
    /// type, an empty body) -- only its own `id`/`name` matter for the
    /// item-identity tests below, which fail before this function's
    /// body is ever lowered.
    fn minimal_function(id: ItemId, name: Symbol, source: SourceId) -> HirFunction {
        HirFunction {
            id,
            name,
            name_span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            params: vec![],
            return_type: None,
            uses: vec![],
            raises: vec![],
            body: HirBlock {
                id: ExprId(0),
                statements: vec![],
                tail: None,
                span: Span::dummy(),
            },
            span: Span::dummy(),
        }
    }

    fn minimal_record(id: ItemId, name: Symbol, source: SourceId) -> crate::hir::HirRecord {
        crate::hir::HirRecord {
            id,
            name,
            span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            fields: vec![],
        }
    }

    fn minimal_variant(id: ItemId, name: Symbol, source: SourceId) -> crate::hir::HirVariant {
        crate::hir::HirVariant {
            id,
            name,
            span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            cases: vec![],
        }
    }

    #[allow(clippy::type_complexity)]
    fn empty_maps() -> (
        HashMap<LocalId, Ty>,
        HashMap<ExprId, Ty>,
        HashMap<PatternId, (ItemId, usize)>,
    ) {
        (HashMap::new(), HashMap::new(), HashMap::new())
    }

    /// A trivial function whose body's tail is `tail_expr` -- used by
    /// the bare-`CaseRef` tests below, which need a real function body
    /// to place a hand-built `HirExpr::CaseRef` in.
    fn function_with_tail(
        id: ItemId,
        name: Symbol,
        tail_expr: HirExpr,
        source: SourceId,
    ) -> HirFunction {
        HirFunction {
            id,
            name,
            name_span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            params: vec![],
            return_type: None,
            uses: vec![],
            raises: vec![],
            body: HirBlock {
                id: ExprId(100),
                statements: vec![],
                tail: Some(Box::new(tail_expr)),
                span: Span::dummy(),
            },
            span: Span::dummy(),
        }
    }

    fn case_ref(variant: ItemId, case: usize, name: Symbol) -> HirExpr {
        HirExpr::CaseRef {
            id: ExprId(0),
            variant,
            case,
            name,
            type_args: Vec::new(),
            span: Span::dummy(),
        }
    }

    #[test]
    fn bare_case_ref_to_an_unknown_variant_fails_lowering_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let f = interner.intern("f");
        let case_name = interner.intern("Empty");
        let unknown_variant = ItemId(0);
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function_with_tail(
                ItemId(1),
                f,
                case_ref(unknown_variant, 0, case_name),
                source,
            )],
            records: vec![],
            variants: vec![],
            other_items: vec![],
        };
        let mut expr_types = HashMap::new();
        expr_types.insert(ExprId(0), Ty::Named(unknown_variant, case_name));
        let local_types = HashMap::new();
        let pattern_case = HashMap::new();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a bare case ref to an unknown variant to fail lowering")
        };
        assert!(diagnostics.iter().any(|d| d.code == "I0002"));
    }

    #[test]
    fn bare_case_ref_with_an_invalid_case_index_fails_lowering_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let f = interner.intern("f");
        let variant_sym = interner.intern("Shape");
        let case_name = interner.intern("Empty");
        let variant_item = ItemId(0);
        let variant = minimal_variant(variant_item, variant_sym, source);
        // Case index 7 does not exist -- the variant declares no cases
        // at all.
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function_with_tail(
                ItemId(1),
                f,
                case_ref(variant_item, 7, case_name),
                source,
            )],
            records: vec![],
            variants: vec![variant],
            other_items: vec![],
        };
        let mut expr_types = HashMap::new();
        expr_types.insert(ExprId(0), Ty::Named(variant_item, variant_sym));
        let local_types = HashMap::new();
        let pattern_case = HashMap::new();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a bare case ref with an invalid case index to fail lowering")
        };
        assert!(diagnostics.iter().any(|d| d.code == "I0002"));
    }

    #[test]
    fn bare_case_ref_to_a_payload_carrying_case_fails_lowering_not_a_panic() {
        // `Shape.Circle` written bare (no call parens) against a case
        // that actually carries a payload must be rejected, not
        // silently construct it with an empty payload.
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let f = interner.intern("f");
        let variant_sym = interner.intern("Shape");
        let case_name = interner.intern("Circle");
        let variant_item = ItemId(0);
        let variant = crate::hir::HirVariant {
            id: variant_item,
            name: variant_sym,
            span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            cases: vec![crate::hir::HirCase {
                name: case_name,
                span: Span::dummy(),
                payload: vec![crate::hir::HirType::Unresolved {
                    name: interner.intern("i64"),
                    span: Span::dummy(),
                }],
            }],
        };
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function_with_tail(
                ItemId(1),
                f,
                case_ref(variant_item, 0, case_name),
                source,
            )],
            records: vec![],
            variants: vec![variant],
            other_items: vec![],
        };
        let mut expr_types = HashMap::new();
        expr_types.insert(ExprId(0), Ty::Named(variant_item, variant_sym));
        let local_types = HashMap::new();
        let pattern_case = HashMap::new();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a bare case ref to a payload-carrying case to fail lowering")
        };
        assert!(diagnostics.iter().any(|d| d.code == "I0002"));
    }

    #[test]
    fn duplicate_record_id_fails_lowering_atomically_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![],
            records: vec![
                minimal_record(ItemId(0), a, source),
                minimal_record(ItemId(0), b, source),
            ],
            variants: vec![],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a duplicate record id to fail lowering")
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert_eq!(diagnostics[0].code, "I0002");
        assert!(diagnostics[0].message.contains("record"));
    }

    #[test]
    fn duplicate_variant_id_fails_lowering_atomically_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![],
            records: vec![],
            variants: vec![
                minimal_variant(ItemId(0), a, source),
                minimal_variant(ItemId(0), b, source),
            ],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a duplicate variant id to fail lowering")
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert_eq!(diagnostics[0].code, "I0002");
        assert!(diagnostics[0].message.contains("variant"));
    }

    #[test]
    fn duplicate_function_id_fails_lowering_atomically_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let f = interner.intern("f");
        let g = interner.intern("g");
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![
                minimal_function(ItemId(0), f, source),
                minimal_function(ItemId(0), g, source),
            ],
            records: vec![],
            variants: vec![],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a duplicate function id to fail lowering")
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert_eq!(diagnostics[0].code, "I0002");
        assert!(diagnostics[0].message.contains("function"));
    }

    #[test]
    fn record_variant_id_collision_fails_lowering_atomically_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![],
            records: vec![minimal_record(ItemId(0), a, source)],
            variants: vec![minimal_variant(ItemId(0), b, source)],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a record/variant id collision to fail lowering")
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert_eq!(diagnostics[0].code, "I0002");
        assert!(
            diagnostics[0].message.contains("record") && diagnostics[0].message.contains("variant")
        );
    }

    #[test]
    fn function_aggregate_id_collision_fails_lowering_atomically_not_a_panic() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let f = interner.intern("f");
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![minimal_function(ItemId(0), f, source)],
            records: vec![minimal_record(ItemId(0), a, source)],
            variants: vec![],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &HashMap::new(),
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!("expected a function/record id collision to fail lowering")
        };
        assert_eq!(
            diagnostics.len(),
            1,
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert_eq!(diagnostics[0].code, "I0002");
        assert!(
            diagnostics[0].message.contains("function")
                && diagnostics[0].message.contains("record")
        );
    }

    #[test]
    fn multiple_id_collisions_produce_deterministic_diagnostics_in_declaration_order() {
        let mut interner = Interner::new();
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let a = interner.intern("A");
        let b = interner.intern("B");
        let c = interner.intern("C");
        let d = interner.intern("D");
        // Two independent collisions: records 0/0, then variants 1/1.
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![],
            records: vec![
                minimal_record(ItemId(0), a, source),
                minimal_record(ItemId(0), b, source),
            ],
            variants: vec![
                minimal_variant(ItemId(1), c, source),
                minimal_variant(ItemId(1), d, source),
            ],
            other_items: vec![],
        };
        let (local_types, expr_types, pattern_case) = empty_maps();
        let build = || {
            lower_module(
                &module,
                &local_types,
                &expr_types,
                &pattern_case,
                &HashMap::new(),
                &interner,
                source,
            )
        };
        let Err(first) = build() else {
            panic!("expected multiple id collisions to fail lowering")
        };
        assert_eq!(first.len(), 2, "unexpected diagnostics: {first:?}");
        assert!(first.iter().all(|d| d.code == "I0002"));
        // Declaration order (records before variants), run twice to
        // confirm it is the same order every time -- never a HashMap's
        // iteration order.
        let Err(second) = build() else {
            panic!("expected the second run to fail lowering too")
        };
        let first_messages: Vec<&str> = first.iter().map(|d| d.message.as_str()).collect();
        let second_messages: Vec<&str> = second.iter().map(|d| d.message.as_str()).collect();
        assert_eq!(first_messages, second_messages);
        assert!(first_messages[0].contains("record"));
        assert!(first_messages[1].contains("variant"));
    }

    /// Builds a `Lowering` directly (bypassing the whole lex/parse/hir/
    /// typeck pipeline entirely, not just typeck's diagnostic gate) so a
    /// single aggregate-lowering method can be exercised with an
    /// out-of-range index no real frontend ever produces -- the only way
    /// to reach these defense-in-depth paths at all, since `hir::lower`'s
    /// own name resolution never emits a case/field index outside its
    /// declaration's real range.
    fn direct_lowering<'a>(
        source: SourceId,
        interner: &'a Interner,
        local_types: &'a HashMap<LocalId, Ty>,
        expr_types: &'a HashMap<ExprId, Ty>,
        pattern_case: &'a HashMap<PatternId, (ItemId, usize)>,
        records: HashMap<ItemId, RecordLayout>,
        variants: HashMap<ItemId, VariantLayout>,
    ) -> Lowering<'a> {
        Lowering {
            local_types,
            expr_types,
            pattern_case,
            interner,
            source,
            records,
            variants,
            function_sigs: HashMap::new(),
            call_type_args: Box::leak(Box::new(HashMap::new())),
        }
    }

    /// Like `direct_lowering`, but with a caller-supplied `function_sigs`
    /// and `call_type_args`, for tests that need to control exactly what
    /// generic call-site metadata (or lack of it) a direct lowering call
    /// sees.
    #[allow(clippy::too_many_arguments)]
    fn direct_lowering_with_generics<'a>(
        source: SourceId,
        interner: &'a Interner,
        local_types: &'a HashMap<LocalId, Ty>,
        expr_types: &'a HashMap<ExprId, Ty>,
        pattern_case: &'a HashMap<PatternId, (ItemId, usize)>,
        records: HashMap<ItemId, RecordLayout>,
        variants: HashMap<ItemId, VariantLayout>,
        function_sigs: HashMap<ItemId, (Vec<crate::hir::TypeParamId>, Vec<Ty>, Ty)>,
        call_type_args: &'a HashMap<ExprId, Vec<Ty>>,
    ) -> Lowering<'a> {
        Lowering {
            local_types,
            expr_types,
            pattern_case,
            interner,
            source,
            records,
            variants,
            function_sigs,
            call_type_args,
        }
    }

    #[test]
    fn a_generic_call_missing_its_recorded_type_arguments_fails_with_i0002_not_a_panic() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let callee_item = ItemId(0);
        let t = crate::hir::TypeParamId(0);
        let mut function_sigs = HashMap::new();
        function_sigs.insert(
            callee_item,
            (
                vec![t],
                vec![Ty::Param(t, interner.intern("T"))],
                Ty::Param(t, interner.intern("T")),
            ),
        );
        let g_name = interner.intern("g");
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
            function_sigs,
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let callee = HirExpr::Function {
            id: ExprId(0),
            item: callee_item,
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        let call_expr = HirExpr::Call {
            id: ExprId(1),
            callee: Box::new(callee.clone()),
            args: Vec::new(),
            span: Span::dummy(),
        };
        let result = lowering.lower_call(&mut fb, &callee, &[], &call_expr);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for a generic call with no recorded type arguments")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_generic_call_with_the_wrong_number_of_recorded_type_arguments_fails_with_i0002() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let callee_item = ItemId(0);
        let t = crate::hir::TypeParamId(0);
        let mut function_sigs = HashMap::new();
        function_sigs.insert(
            callee_item,
            (
                vec![t],
                vec![Ty::Param(t, interner.intern("T"))],
                Ty::Param(t, interner.intern("T")),
            ),
        );
        let g_name = interner.intern("g");
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_expr_id = ExprId(1);
        let mut call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        // `g` declares one type parameter; two are recorded here.
        call_type_args.insert(call_expr_id, vec![Ty::I64, Ty::Bool]);
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
            function_sigs,
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let callee = HirExpr::Function {
            id: ExprId(0),
            item: callee_item,
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        let call_expr = HirExpr::Call {
            id: call_expr_id,
            callee: Box::new(callee.clone()),
            args: Vec::new(),
            span: Span::dummy(),
        };
        let result = lowering.lower_call(&mut fb, &callee, &[], &call_expr);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for a call with mismatched type-argument arity")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_generic_variant_construction_missing_its_recorded_type_arguments_fails_with_i0002() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let variant_item = ItemId(0);
        let t = crate::hir::TypeParamId(0);
        let mut variants = HashMap::new();
        variants.insert(
            variant_item,
            VariantLayout {
                name: interner.intern("Maybe"),
                type_params: vec![(t, interner.intern("T"))],
                cases: vec![CaseLayout {
                    name: interner.intern("Some"),
                    payload: vec![Ty::Param(t, interner.intern("T"))],
                }],
            },
        );
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            variants,
            HashMap::new(),
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let arg = HirExpr::Int {
            id: ExprId(1),
            value: 1,
            base: crate::lexer::IntBase::Decimal,
            span: Span::dummy(),
        };
        let args = vec![arg];
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_variant_construct(&mut fb, variant_item, 0, &args, &probe);
        let Err(diagnostic) = result else {
            panic!(
                "expected lowering to fail for a generic variant construction with no recorded type arguments"
            )
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_bare_generic_unit_case_missing_its_recorded_type_arguments_fails_with_i0002() {
        // The same lowering path a `Some(...)` call goes through above,
        // exercised via a *bare* unit-case reference instead (no call
        // syntax, empty argument list) -- `Maybe[i64].None` must be
        // rejected here exactly the same way, never silently defaulting
        // to an empty (and therefore wrong-arity) type-argument list.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let variant_item = ItemId(0);
        let t = crate::hir::TypeParamId(0);
        let mut variants = HashMap::new();
        variants.insert(
            variant_item,
            VariantLayout {
                name: interner.intern("Maybe"),
                type_params: vec![(t, interner.intern("T"))],
                cases: vec![CaseLayout {
                    name: interner.intern("None"),
                    payload: vec![],
                }],
            },
        );
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            variants,
            HashMap::new(),
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_variant_construct(&mut fb, variant_item, 0, &[], &probe);
        let Err(diagnostic) = result else {
            panic!(
                "expected lowering to fail for a bare generic unit case with no recorded type arguments"
            )
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_generic_record_construction_with_the_wrong_number_of_recorded_type_arguments_fails() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let record_item = ItemId(0);
        let t = crate::hir::TypeParamId(0);
        let mut records = HashMap::new();
        records.insert(
            record_item,
            RecordLayout {
                name: interner.intern("Box"),
                type_params: vec![(t, interner.intern("T"))],
                fields: vec![(interner.intern("value"), Ty::Param(t, interner.intern("T")))],
            },
        );
        let (local_types, expr_types, pattern_case) = empty_maps();
        let literal_expr_id = ExprId(1);
        let mut call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        // `Box` declares one type parameter; two are recorded here.
        call_type_args.insert(literal_expr_id, vec![Ty::I64, Ty::Bool]);
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            records,
            HashMap::new(),
            HashMap::new(),
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let init = HirFieldInit {
            field_index: 0,
            value: HirExpr::Int {
                id: ExprId(2),
                value: 1,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            },
            span: Span::dummy(),
        };
        let probe = HirExpr::Bool {
            id: literal_expr_id,
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_record_literal(&mut fb, record_item, &[init], &probe);
        let Err(diagnostic) = result else {
            panic!(
                "expected lowering to fail for a record construction with mismatched type-argument arity"
            )
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn a_non_generic_call_missing_type_argument_metadata_still_lowers() {
        // No declared type parameters at all -- absent call_type_args
        // metadata is exactly the valid, expected case here (an empty
        // argument list), never an error.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let callee_item = ItemId(0);
        let mut function_sigs = HashMap::new();
        function_sigs.insert(callee_item, (Vec::new(), Vec::new(), Ty::I64));
        let g_name = interner.intern("g");
        let (local_types, expr_types, pattern_case) = empty_maps();
        let call_type_args: HashMap<ExprId, Vec<Ty>> = HashMap::new();
        let mut lowering = direct_lowering_with_generics(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
            function_sigs,
            &call_type_args,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let callee = HirExpr::Function {
            id: ExprId(0),
            item: callee_item,
            name: g_name,
            type_args: Vec::new(),
            span: Span::dummy(),
        };
        let call_expr = HirExpr::Call {
            id: ExprId(1),
            callee: Box::new(callee.clone()),
            args: Vec::new(),
            span: Span::dummy(),
        };
        let result = lowering.lower_call(&mut fb, &callee, &[], &call_expr);
        assert!(
            result.is_ok(),
            "a non-generic call must lower cleanly with no recorded type arguments: {result:?}"
        );
    }

    #[test]
    fn direct_variant_construction_with_an_unknown_case_index_fails_with_i0002_not_a_panic() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let variant_item = ItemId(0);
        let mut variants = HashMap::new();
        variants.insert(
            variant_item,
            VariantLayout {
                name: interner.intern("V"),
                type_params: Vec::new(),
                cases: vec![CaseLayout {
                    name: interner.intern("A"),
                    payload: vec![Ty::I64],
                }],
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            variants,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        // Case index 7 does not exist on a variant with a single case.
        let result = lowering.lower_variant_construct(&mut fb, variant_item, 7, &[], &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for an unknown case index")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn direct_record_construction_with_an_out_of_range_field_index_fails_with_i0002_not_a_panic() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let record_item = ItemId(0);
        let mut records = HashMap::new();
        records.insert(
            record_item,
            RecordLayout {
                name: interner.intern("Point"),
                type_params: Vec::new(),
                fields: vec![(interner.intern("x"), Ty::I64)],
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            records,
            HashMap::new(),
        );
        let mut fb = FnBuilder::new(Ty::I64);
        // Field index 9 does not exist on a record with a single field
        // -- rejected up front, before its initializer is ever
        // evaluated, rather than silently dropped into nowhere.
        let bad_init = HirFieldInit {
            field_index: 9,
            value: HirExpr::Bool {
                id: ExprId(1),
                value: true,
                span: Span::dummy(),
            },
            span: Span::dummy(),
        };
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_record_literal(&mut fb, record_item, &[bad_init], &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for an out-of-range field index")
        };
        assert_eq!(diagnostic.code, "I0002");
        assert!(
            diagnostic.message.contains("out of range"),
            "expected an out-of-range diagnostic, got: {}",
            diagnostic.message
        );
    }

    #[test]
    fn all_valid_record_fields_plus_one_out_of_range_field_fails_atomically() {
        // Every genuinely declared field is present and correct; the
        // one extra field beyond the record's own layout must still
        // reject the whole construction, not just be ignored while the
        // rest lowers successfully.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let record_item = ItemId(0);
        let mut records = HashMap::new();
        records.insert(
            record_item,
            RecordLayout {
                name: interner.intern("Point"),
                type_params: Vec::new(),
                fields: vec![
                    (interner.intern("x"), Ty::I64),
                    (interner.intern("y"), Ty::I64),
                ],
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            records,
            HashMap::new(),
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let init = |field_index: usize, id: u32| HirFieldInit {
            field_index,
            value: HirExpr::Int {
                id: ExprId(id),
                value: 1,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            },
            span: Span::dummy(),
        };
        let fields = vec![init(0, 1), init(1, 2), init(2, 3)];
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_record_literal(&mut fb, record_item, &fields, &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for an extra out-of-range field")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn duplicate_field_index_with_every_other_field_present_fails_atomically() {
        // Every field index the record actually declares is covered --
        // 0 is just covered twice, at the cost of 1 never being
        // written -- so this can't be caught as "missing" without also
        // catching the duplicate itself; the second write to index 0
        // must never silently overwrite the first's already-lowered
        // value in its temporary slot.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let record_item = ItemId(0);
        let mut records = HashMap::new();
        records.insert(
            record_item,
            RecordLayout {
                name: interner.intern("Point"),
                type_params: Vec::new(),
                fields: vec![
                    (interner.intern("x"), Ty::I64),
                    (interner.intern("y"), Ty::I64),
                ],
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            records,
            HashMap::new(),
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let init = |field_index: usize, id: u32| HirFieldInit {
            field_index,
            value: HirExpr::Int {
                id: ExprId(id),
                value: 1,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            },
            span: Span::dummy(),
        };
        let fields = vec![init(0, 1), init(0, 2)];
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_record_literal(&mut fb, record_item, &fields, &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for a duplicate field index")
        };
        assert_eq!(diagnostic.code, "I0002");
        assert!(
            diagnostic.message.contains("more than once"),
            "expected a duplicate-index diagnostic, got: {}",
            diagnostic.message
        );
    }

    #[test]
    fn unknown_record_id_fails_lowering_instead_of_using_the_provided_field_count() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let interner = Interner::new();
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_record_literal(&mut fb, ItemId(0), &[], &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for an unknown record")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn too_many_variant_payload_arguments_fails_lowering_instead_of_a_longer_payload() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let variant_item = ItemId(0);
        let mut variants = HashMap::new();
        variants.insert(
            variant_item,
            VariantLayout {
                name: interner.intern("V"),
                type_params: Vec::new(),
                cases: vec![CaseLayout {
                    name: interner.intern("A"),
                    payload: vec![Ty::I64],
                }],
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            variants,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let arg = |id: u32| HirExpr::Int {
            id: ExprId(id),
            value: 1,
            base: crate::lexer::IntBase::Decimal,
            span: Span::dummy(),
        };
        let args = vec![arg(1), arg(2)];
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_variant_construct(&mut fb, variant_item, 0, &args, &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for too many payload arguments")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn too_few_variant_payload_arguments_fails_lowering_instead_of_a_shorter_payload() {
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let variant_item = ItemId(0);
        let mut variants = HashMap::new();
        variants.insert(
            variant_item,
            VariantLayout {
                name: interner.intern("V"),
                type_params: Vec::new(),
                cases: vec![CaseLayout {
                    name: interner.intern("A"),
                    payload: vec![Ty::I64, Ty::I64],
                }],
            },
        );
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            variants,
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let args = vec![HirExpr::Int {
            id: ExprId(1),
            value: 1,
            base: crate::lexer::IntBase::Decimal,
            span: Span::dummy(),
        }];
        let probe = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_variant_construct(&mut fb, variant_item, 0, &args, &probe);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for too few payload arguments")
        };
        assert_eq!(diagnostic.code, "I0002");
    }

    #[test]
    fn deeply_nested_hand_built_match_pattern_fails_lowering_with_i0002_not_a_stack_overflow() {
        // The parser's own crate::limits::MAX_PATTERN_DEPTH bound keeps
        // any real parser output shallow enough that lower_decision's
        // own bound can never fire through the normal pipeline
        // (typeck's matching bound also stops it before NIR lowering is
        // ever reached) -- so this exercises it the only way possible:
        // a hand-built HirModule that bypasses the parser, hir::lower,
        // and typeck entirely, calling the public nir::lower_module
        // entry point a direct caller would, and asserting the whole
        // module fails atomically rather than calling only the private
        // lower_match helper.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let wrap_name = interner.intern("Wrap");
        let leaf_name = interner.intern("Leaf");
        let variant_item = ItemId(0);
        let variant_sym = interner.intern("Rec");
        let variant_ty_name = crate::hir::HirType::Aggregate {
            item: variant_item,
            kind: crate::hir::AggregateKind::Variant,
            name: variant_sym,
            args: Vec::new(),
            span: Span::dummy(),
        };
        let i64_name = crate::hir::HirType::Unresolved {
            name: interner.intern("i64"),
            span: Span::dummy(),
        };
        let variant = crate::hir::HirVariant {
            id: variant_item,
            name: variant_sym,
            span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            cases: vec![
                crate::hir::HirCase {
                    name: wrap_name,
                    span: Span::dummy(),
                    payload: vec![variant_ty_name.clone()],
                },
                crate::hir::HirCase {
                    name: leaf_name,
                    span: Span::dummy(),
                    payload: vec![],
                },
            ],
        };

        let depth = MAX_PATTERN_DEPTH + 50;
        let mut pattern_case = HashMap::new();
        let mut pattern = HirPattern::Wildcard {
            id: PatternId(0),
            span: Span::dummy(),
        };
        for i in 0..depth {
            let id = PatternId(i as u32 + 1);
            pattern_case.insert(id, (variant_item, 0usize));
            pattern = HirPattern::Variant {
                id,
                name: wrap_name,
                args: vec![pattern],
                span: Span::dummy(),
            };
        }

        let param_local = LocalId(0);
        let scrutinee_id = ExprId(0);
        let scrutinee = HirExpr::Local {
            id: scrutinee_id,
            local: param_local,
            name: variant_sym,
            span: Span::dummy(),
        };
        let arms = vec![HirMatchArm {
            pattern,
            body: HirMatchArmBody::Expr(HirExpr::Int {
                id: ExprId(1),
                value: 0,
                base: crate::lexer::IntBase::Decimal,
                span: Span::dummy(),
            }),
            span: Span::dummy(),
        }];
        let match_expr = HirExpr::Match {
            id: ExprId(2),
            scrutinee: Box::new(scrutinee),
            arms,
            span: Span::dummy(),
        };
        let function = HirFunction {
            id: ItemId(1),
            name: interner.intern("f"),
            name_span: Span::dummy(),
            source,
            public: true,
            type_params: Vec::new(),
            params: vec![crate::hir::HirParam {
                local: param_local,
                name: variant_sym,
                span: Span::dummy(),
                ty: variant_ty_name,
            }],
            return_type: Some(i64_name),
            uses: vec![],
            raises: vec![],
            body: HirBlock {
                id: ExprId(3),
                statements: vec![],
                tail: Some(Box::new(match_expr)),
                span: Span::dummy(),
            },
            span: Span::dummy(),
        };
        let module = HirModule {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![function],
            records: vec![],
            variants: vec![variant],
            other_items: vec![],
        };

        let mut local_types = HashMap::new();
        local_types.insert(param_local, Ty::Named(variant_item, variant_sym));
        let mut expr_types = HashMap::new();
        expr_types.insert(scrutinee_id, Ty::Named(variant_item, variant_sym));

        let call_type_args = HashMap::new();
        let result = lower_module(
            &module,
            &local_types,
            &expr_types,
            &pattern_case,
            &call_type_args,
            &interner,
            source,
        );
        let Err(diagnostics) = result else {
            panic!(
                "expected the whole module to fail lowering for a match nested past the depth limit"
            )
        };
        assert!(
            diagnostics.iter().any(|d| d.code == "I0002"),
            "expected an I0002 diagnostic, got {diagnostics:?}"
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
    fn calling_a_non_function_value_fails_lowering_instead_of_a_fabricated_error_value() {
        // typeck already rejects a call whose callee isn't an actual
        // function reference; reaching lower_call with one anyway (a
        // hand-built HirExpr::Call over a plain Local, bypassing
        // typeck) must fail atomically rather than silently return a
        // fabricated Ty::Error/Const::Unit value as if the call had
        // "succeeded".
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let mut interner = Interner::new();
        let x_name = interner.intern("x");
        let local_types = HashMap::new();
        let expr_types = HashMap::new();
        let pattern_case = HashMap::new();
        let mut lowering = direct_lowering(
            source,
            &interner,
            &local_types,
            &expr_types,
            &pattern_case,
            HashMap::new(),
            HashMap::new(),
        );
        let mut fb = FnBuilder::new(Ty::I64);
        let placeholder = fb.push_value(Ty::I64, ValueKind::Alloc);
        fb.local_bindings
            .insert(LocalId(0), LocalBinding::Direct(placeholder));
        let callee = HirExpr::Local {
            id: ExprId(1),
            local: LocalId(0),
            name: x_name,
            span: Span::dummy(),
        };
        let call_expr = HirExpr::Bool {
            id: ExprId(0),
            value: true,
            span: Span::dummy(),
        };
        let result = lowering.lower_call(&mut fb, &callee, &[], &call_expr);
        let Err(diagnostic) = result else {
            panic!("expected lowering to fail for a call to a non-function value")
        };
        assert_eq!(diagnostic.code, "I0002");
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
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        let outcome = lower_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
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

    // -- Generic lowering (`rfcs/0008`) ---------------------------------

    #[test]
    fn a_generic_function_lowers_exactly_once_with_symbolic_param_types() {
        // `identity[T]` must lower to one `Function` whose own parameter
        // is typed by its own `Ty::Param`, never a per-call-site clone.
        let module = lower(
            "func identity[T](x: T) -> T { return x } \
             func main() -> i64 { return identity[i64](1) + identity[i64](2) }",
        );
        assert_eq!(
            module
                .functions
                .iter()
                .filter(|f| f.params.len() == 1)
                .count(),
            1,
            "identity must lower exactly once regardless of how many call sites instantiate it"
        );
        let identity = module
            .functions
            .iter()
            .find(|f| f.params.len() == 1)
            .unwrap();
        assert!(matches!(identity.params[0].ty, Ty::Param(..)));
        assert!(matches!(identity.return_type, Ty::Param(..)));
        assert_eq!(identity.type_params.len(), 1);
    }

    #[test]
    fn a_call_to_a_generic_function_records_its_own_concrete_type_arguments() {
        let module = lower(
            "func identity[T](x: T) -> T { return x } func main() -> i64 { return identity[i64](42) }",
        );
        let main = module
            .functions
            .iter()
            .find(|f| f.params.is_empty())
            .unwrap();
        let call_type_args = main
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| {
                if let Instruction::Value {
                    kind: ValueKind::Call(_, type_args, _),
                    ..
                } = i
                {
                    Some(type_args.clone())
                } else {
                    None
                }
            });
        assert_eq!(call_type_args, Some(vec![Ty::I64]));
    }

    #[test]
    fn a_generic_record_construction_records_its_own_concrete_type_arguments() {
        let module = lower(
            "record Box[T] { payload: T } \
             func main() -> i64 { value b = Box[i64] { payload: 42 }; return b.payload }",
        );
        let main = module
            .functions
            .iter()
            .find(|f| f.params.is_empty())
            .unwrap();
        let create_type_args = main
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| {
                if let Instruction::Value {
                    kind: ValueKind::RecordCreate(_, type_args, _),
                    ..
                } = i
                {
                    Some(type_args.clone())
                } else {
                    None
                }
            });
        assert_eq!(create_type_args, Some(vec![Ty::I64]));
    }

    #[test]
    fn a_generic_variant_construction_records_its_own_concrete_type_arguments() {
        let module = lower(
            "variant Maybe[T] { Some(T), None } \
             func main() -> i64 { \
                 return match Maybe[i64].Some(42) { \
                     Some(n) => n, \
                     None => 0, \
                 } \
             }",
        );
        let main = module
            .functions
            .iter()
            .find(|f| f.params.is_empty())
            .unwrap();
        let create_type_args = main
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| {
                if let Instruction::Value {
                    kind: ValueKind::VariantCreate { type_args, .. },
                    ..
                } = i
                {
                    Some(type_args.clone())
                } else {
                    None
                }
            });
        assert_eq!(create_type_args, Some(vec![Ty::I64]));
    }

    #[test]
    fn a_bare_generic_unit_case_records_its_own_concrete_type_arguments() {
        // Regression: `Maybe[i64].None` (no call syntax at all) must
        // still record its type argument -- `check_case_ref` threading
        // its own `ExprId` into `call_type_args` is what this exercises.
        let module = lower(
            "variant Maybe[T] { Some(T), None } \
             func main() -> i64 { \
                 return match Maybe[i64].None { \
                     Some(n) => n, \
                     None => 0, \
                 } \
             }",
        );
        let main = module
            .functions
            .iter()
            .find(|f| f.params.is_empty())
            .unwrap();
        let create_type_args = main
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| {
                if let Instruction::Value {
                    kind: ValueKind::VariantCreate { type_args, .. },
                    ..
                } = i
                {
                    Some(type_args.clone())
                } else {
                    None
                }
            });
        assert_eq!(
            create_type_args,
            Some(vec![Ty::I64]),
            "a bare generic unit case must not silently default to an empty type argument list"
        );
    }
}
