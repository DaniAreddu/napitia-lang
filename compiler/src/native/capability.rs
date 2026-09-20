//! The native capability validator: the gate between verified NIR and
//! Cranelift.
//!
//! This pass answers exactly one question -- *is this whole reachable
//! program inside the native subset?* -- and answers it exhaustively,
//! before a single Cranelift instruction is built. That ordering is the
//! point: [`super::lower`] never has to decide what to do with a
//! construct it cannot compile, because it never sees one.
//!
//! # What this pass is not
//!
//! It is not a second NIR verifier. [`crate::nir::verify_module`] has
//! already run and already owns every structural and typing invariant
//! NIR has. Where this pass notices such a violation anyway -- it is a
//! public function and a caller may hand it hand-built NIR that never
//! went through the verifier -- it reports
//! [`super::codes::UNVERIFIED_NIR`] and refuses,
//! rather than guessing at a repair or walking off the end of
//! something. A resource is *unsupported*; a dangling block target is
//! *malformed*; the two never share a code.
//!
//! # Reachability policy
//!
//! The backend validates, and then compiles, exactly the code it would
//! execute:
//!
//! * a function is reachable when `main` reaches it through a chain of
//!   direct calls;
//! * a block is reachable when that function's own entry block
//!   (`bb0`) reaches it through terminator edges.
//!
//! Nothing outside that set is validated, lowered, consulted for a call
//! edge, or allowed to define a value, a slot or a type that reachable
//! code generation can see. An unsupported instruction sitting in a
//! block no path reaches, or in a function `main` never calls, is
//! therefore not an error -- it is dead code, exactly as it is for the
//! interpreter, which never executes it either. Everything the backend
//! *does* reach is checked completely before any of it is compiled.
//!
//! # Arithmetic
//!
//! Every operator this pass accepts is one the native backend
//! reproduces *exactly*, over the operator's whole input domain, as the
//! interpreter already implements it (see [`super::Scalar`] for why
//! that forces a 128-bit integer representation). Four operators are
//! rejected instead of approximated:
//!
//! * `div` and `rem`, because the interpreter answers a zero divisor
//!   with `InterpreterError::DivisionByZero` -- a *runtime error value*
//!   -- and Alpha 0.2.0 has no native runtime facility to raise, report
//!   or carry one. A hardware trap is not the same behavior, and
//!   silently emitting one would be exactly the kind of borrowed host
//!   semantics this backend refuses.
//! * `shl` and `shr`, for the same reason: the interpreter rejects an
//!   out-of-range shift amount with a runtime error
//!   (`i128::checked_shl`/`checked_shr` plus an explicit `u32`
//!   conversion), where the hardware would silently mask the amount
//!   instead.
//!
//! Every other accepted operator -- `add`, `sub`, `mul`, `neg`, `not`,
//! bitwise `and`/`or`/`xor`, and the six comparisons -- agrees with the
//! interpreter on every input, with no exceptional case at all.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::diagnostics::Diagnostic;
use crate::hir::{ItemId, ItemRegistry};
use crate::nir::{
    BasicBlock, BlockId, Const, Function, Instruction, Module, OwnershipMode, Terminator, ValueId,
    ValueKind,
};
use crate::source::{SourceId, Span};
use crate::symbol::Interner;
use crate::types::{Ty, display_ty};

use super::{Scalar, TARGET_TRIPLE, codes, scalar_of};

/// One refusal, behind a pointer.
///
/// A [`Diagnostic`] is a large value, and the helpers below return one
/// only on the path that gives up -- so it travels boxed rather than
/// widening every successful return to its size.
type Refusal = Box<Diagnostic>;

/// The name of the function the native entry wrapper calls. Matches
/// `typeck::EntryMain::ByName`, which is how single-file compilation --
/// the only mode `napitia build` accepts -- already identifies the
/// entry point.
pub const ENTRY_NAME: &str = "main";

/// What [`validate`] hands to code generation: the exact, ordered set
/// of things to compile.
///
/// Every order in here is derived from semantic identity
/// ([`ItemId`]/[`BlockId`]), never from the position an item happened to
/// occupy in a `Vec`, so reversing `Module::functions` or a function's
/// own `blocks` changes nothing about what is emitted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativePlan {
    /// The single `main` this build compiles an entry wrapper around.
    pub entry: ItemId,
    /// `main`'s own result: [`Scalar::Int`] or [`Scalar::Unit`], never
    /// anything else.
    pub entry_result: Scalar,
    /// Every function reachable from [`NativePlan::entry`] through
    /// direct calls, in ascending [`ItemId`] order, `entry` included.
    pub functions: Vec<ItemId>,
    /// For each entry of [`NativePlan::functions`], the blocks reachable
    /// from that function's own `bb0`, in ascending [`BlockId`] order.
    pub reachable_blocks: BTreeMap<ItemId, Vec<BlockId>>,
}

/// Validates `module` against the native subset, targeting `target`.
///
/// `imports` carries the span of every `import` declaration the source
/// itself wrote. Single-file compilation resolves no imports at all, so
/// nothing about the NIR records that one was written -- and a native
/// build must still refuse it rather than quietly compiling a program
/// whose author expected another module to be part of it.
///
/// Returns the compilation plan, or every reason the program is outside
/// the subset, in a deterministic order: target, then module-level
/// facts, then the entry contract, then each reachable function in
/// ascending [`ItemId`] order, then call-graph cycles.
pub fn validate(
    module: &Module,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
    target: &str,
    imports: &[Span],
) -> Result<NativePlan, Vec<Diagnostic>> {
    // A different target is not a partial failure to compile *this*
    // program -- nothing below it would be meaningful, since every
    // decision this pass makes is a decision about one specific
    // machine.
    if target != TARGET_TRIPLE {
        return Err(vec![
            Diagnostic::error(
                codes::UNSUPPORTED_TARGET,
                source,
                Span::dummy(),
                format!("the native backend cannot target `{target}`"),
            )
            .with_help(format!(
                "Alpha 0.2.0 compiles for `{TARGET_TRIPLE}` and nothing else"
            )),
        ]);
    }

    let mut validator = Validator {
        source,
        interner,
        registry,
        functions: BTreeMap::new(),
        diagnostics: Vec::new(),
    };

    for function in &module.functions {
        if validator.functions.insert(function.id, function).is_some() {
            let name = validator.name(function.id);
            validator.diagnostics.push(validator.unverified(
                function.id,
                format!(
                    "two functions in this module share the id {}",
                    function.id.0
                ),
                format!("`{name}` reuses another function's id"),
            ));
        }
    }
    if !validator.diagnostics.is_empty() {
        return Err(validator.diagnostics);
    }

    if let Some(span) = imports.iter().min().copied() {
        validator.diagnostics.push(
            Diagnostic::error(
                codes::MULTI_MODULE_BUILD,
                source,
                span,
                "the native backend compiles one module at a time; this source declares an import",
            )
            .with_primary_label("no native build spans more than one module")
            .with_help("`napitia check`, `napitia ir` and `napitia run` still accept this program"),
        );
    }

    let entry = match validator.find_entry() {
        Ok(entry) => entry,
        Err(diagnostic) => {
            validator.diagnostics.push(*diagnostic);
            return Err(validator.diagnostics);
        }
    };

    // Reachability, the call graph and per-function validation all walk
    // the same deterministic traversal, so a diagnostic's position in
    // the output never depends on how the module was stored.
    let mut reachable_blocks: BTreeMap<ItemId, Vec<BlockId>> = BTreeMap::new();
    let mut callees: BTreeMap<ItemId, Vec<ItemId>> = BTreeMap::new();
    // A function whose blocks cannot even be keyed has already been
    // reported, by the walk below, for the one reason that matters;
    // validating a body nothing could index would only say it again.
    let mut unkeyed: BTreeSet<ItemId> = BTreeSet::new();
    let mut reached: BTreeSet<ItemId> = BTreeSet::new();
    let mut queue: VecDeque<ItemId> = VecDeque::new();
    reached.insert(entry);
    queue.push_back(entry);
    while let Some(id) = queue.pop_front() {
        let Some(function) = validator.functions.get(&id).copied() else {
            continue;
        };
        let blocks = match validator.blocks_by_id(function) {
            Ok(blocks) => blocks,
            Err(diagnostic) => {
                validator.diagnostics.push(*diagnostic);
                unkeyed.insert(id);
                reachable_blocks.insert(id, Vec::new());
                callees.insert(id, Vec::new());
                continue;
            }
        };
        let reachable = validator.reachable_blocks(&blocks);
        let direct = direct_callees(&blocks, &reachable);
        for callee in &direct {
            // A callee this module does not define is reported by
            // `validate_function`, which can name the calling
            // instruction; it contributes no node to the graph.
            if validator.functions.contains_key(callee) && reached.insert(*callee) {
                queue.push_back(*callee);
            }
        }
        reachable_blocks.insert(id, reachable);
        callees.insert(id, direct);
    }

    let functions: Vec<ItemId> = reached.iter().copied().collect();

    for id in &functions {
        if unkeyed.contains(id) {
            continue;
        }
        let Some(function) = validator.functions.get(id).copied() else {
            continue;
        };
        let blocks = reachable_blocks.get(id).cloned().unwrap_or_default();
        validator.validate_function(function, *id == entry, &blocks);
    }

    validator.report_cycles(&functions, &callees);

    if !validator.diagnostics.is_empty() {
        return Err(validator.diagnostics);
    }

    // Only ever read after the entry's own signature was accepted,
    // which is exactly what makes this classification total.
    let entry_result = validator
        .functions
        .get(&entry)
        .and_then(|function| scalar_of(&function.return_type))
        .unwrap_or(Scalar::Unit);

    Ok(NativePlan {
        entry,
        entry_result,
        functions,
        reachable_blocks,
    })
}

struct Validator<'a> {
    source: SourceId,
    interner: &'a Interner,
    registry: &'a ItemRegistry,
    functions: BTreeMap<ItemId, &'a Function>,
    diagnostics: Vec<Diagnostic>,
}

impl<'a> Validator<'a> {
    /// Where to point a diagnostic about `id`. Prefers the item's own
    /// declaration site; falls back to the build's own source with no
    /// span for an id no registry entry covers (only reachable from
    /// hand-built NIR), in which case the message itself carries the
    /// NIR identity instead.
    fn site(&self, id: ItemId) -> (SourceId, Span) {
        match self.registry.get(id) {
            Some(identity) => (identity.source, identity.span),
            None => (self.source, Span::dummy()),
        }
    }

    fn name(&self, id: ItemId) -> String {
        self.registry.qualified_name(id, self.interner)
    }

    fn ty_name(&self, ty: &Ty) -> String {
        display_ty(ty, self.interner)
    }

    /// A diagnostic about `id` in this pass's own layer.
    fn about(&self, code: &'static str, id: ItemId, message: String, label: String) -> Diagnostic {
        let (source, span) = self.site(id);
        Diagnostic::error(code, source, span, message).with_primary_label(label)
    }

    /// A diagnostic for structure the NIR verifier owns. Always says so:
    /// a user whose program produced one is looking at a compiler
    /// defect, not at a feature this milestone left out.
    fn unverified(&self, id: ItemId, message: String, label: String) -> Diagnostic {
        self.about(codes::UNVERIFIED_NIR, id, message, label)
            .with_note(
                "this NIR did not pass `nir::verify`; the native backend never generates code for it",
            )
    }

    /// The single function named `main`, or why there isn't one.
    fn find_entry(&self) -> Result<ItemId, Refusal> {
        let mut found: Vec<ItemId> = Vec::new();
        for (id, function) in &self.functions {
            if self.interner.resolve(function.name) == ENTRY_NAME {
                found.push(*id);
            }
        }
        // `self.functions` is a `BTreeMap`, so `found` is already in
        // ascending id order: which declaration a duplicate diagnostic
        // points at does not depend on storage order.
        match found.as_slice() {
            [] => Err(Box::new(
                Diagnostic::error(
                    codes::MISSING_ENTRY,
                    self.source,
                    Span::dummy(),
                    format!(
                        "a native build needs a `{ENTRY_NAME}` function, and this module has none"
                    ),
                )
                .with_help(format!(
                    "declare `func {ENTRY_NAME}() -> i64` or `func {ENTRY_NAME}() -> unit`"
                )),
            )),
            [single] => Ok(*single),
            [first, second, ..] => {
                let (source, span) = self.site(*second);
                let (first_source, first_span) = self.site(*first);
                Err(Box::new(
                    Diagnostic::error(
                        codes::DUPLICATE_ENTRY,
                        source,
                        span,
                        format!("this module declares more than one `{ENTRY_NAME}` function"),
                    )
                    .with_primary_label("a native build has exactly one entry point")
                    .with_label_in(
                        first_source,
                        first_span,
                        "already declared here",
                    ),
                ))
            }
        }
    }

    /// `function`'s blocks keyed by id, or the verifier-layer reason
    /// they cannot be keyed at all.
    fn blocks_by_id(
        &self,
        function: &'a Function,
    ) -> Result<BTreeMap<BlockId, &'a BasicBlock>, Refusal> {
        let name = self.name(function.id);
        let mut blocks: BTreeMap<BlockId, &BasicBlock> = BTreeMap::new();
        for block in &function.blocks {
            if blocks.insert(block.id, block).is_some() {
                return Err(Box::new(self.unverified(
                    function.id,
                    format!("function `{name}` declares bb{} twice", block.id.0),
                    "duplicate block id".to_string(),
                )));
            }
        }
        if !blocks.contains_key(&BlockId(0)) {
            return Err(Box::new(self.unverified(
                function.id,
                format!("function `{name}` has no entry block bb0"),
                "no entry block".to_string(),
            )));
        }
        Ok(blocks)
    }

    /// The blocks `bb0` reaches, ascending. A target no block defines is
    /// simply not followed -- `validate_function` reports it from the
    /// terminator that named it, where the message can say which block
    /// the dangling edge left.
    fn reachable_blocks(&self, blocks: &BTreeMap<BlockId, &'a BasicBlock>) -> Vec<BlockId> {
        let mut reached: BTreeSet<BlockId> = BTreeSet::new();
        let mut queue: VecDeque<BlockId> = VecDeque::new();
        if blocks.contains_key(&BlockId(0)) {
            reached.insert(BlockId(0));
            queue.push_back(BlockId(0));
        }
        while let Some(id) = queue.pop_front() {
            let Some(block) = blocks.get(&id) else {
                continue;
            };
            for target in terminator_targets(&block.terminator) {
                if blocks.contains_key(&target) && reached.insert(target) {
                    queue.push_back(target);
                }
            }
        }
        reached.into_iter().collect()
    }

    /// Validates one reachable function, recording at most one
    /// diagnostic for it.
    ///
    /// One is the right number: this pass is a gate, not an incremental
    /// checker. A function that uses a resource fails for one reason,
    /// and listing every instruction that touches that resource would
    /// bury it. The early return is only ever taken on a path that has
    /// already recorded a diagnostic, so a function that validates
    /// cleanly has had *every* reachable instruction, terminator and
    /// type examined.
    fn validate_function(&mut self, function: &'a Function, is_entry: bool, reachable: &[BlockId]) {
        if let Some(diagnostic) = self.check_module_origin(function) {
            self.diagnostics.push(diagnostic);
            return;
        }
        if let Some(diagnostic) = self.check_signature(function, is_entry) {
            self.diagnostics.push(diagnostic);
            return;
        }
        if let Some(diagnostic) = self.check_body(function, reachable) {
            self.diagnostics.push(diagnostic);
        }
    }

    /// A reachable function declared in another file means the NIR was
    /// built by project compilation, which `napitia build` does not
    /// accept.
    fn check_module_origin(&self, function: &'a Function) -> Option<Diagnostic> {
        let identity = self.registry.get(function.id)?;
        if identity.source == self.source {
            return None;
        }
        let name = self.name(function.id);
        Some(
            self.about(
                codes::MULTI_MODULE_BUILD,
                function.id,
                format!("`{name}` is declared in another module than the one being built"),
                "no native build spans more than one module".to_string(),
            )
            .with_help("`napitia build` compiles a single `.npt` file"),
        )
    }

    fn check_signature(&self, function: &'a Function, is_entry: bool) -> Option<Diagnostic> {
        let name = self.name(function.id);
        if !function.type_params.is_empty() {
            return Some(self.about(
                codes::GENERIC_CODE,
                function.id,
                format!("`{name}` is generic, and the native backend does not monomorphize"),
                "generic function".to_string(),
            ));
        }
        if !function.requirements.is_empty() {
            return Some(self.about(
                codes::CAPABILITY_DISPATCH,
                function.id,
                format!("`{name}` declares a capability requirement, which dispatches indirectly"),
                "`uses` requirement".to_string(),
            ));
        }
        if !function.raises.is_empty() {
            return Some(self.about(
                codes::FALLIBLE_FUNCTION,
                function.id,
                format!(
                    "`{name}` declares raised errors, and there is no native typed-failure runtime"
                ),
                "`raises` clause".to_string(),
            ));
        }
        if is_entry {
            if !function.params.is_empty() {
                return Some(self.about(
                    codes::ENTRY_PARAMETERS,
                    function.id,
                    format!(
                        "`{name}` must take no parameters, found {}",
                        function.params.len()
                    ),
                    "the native entry point receives no arguments".to_string(),
                ));
            }
            if !matches!(
                scalar_of(&function.return_type),
                Some(Scalar::Int) | Some(Scalar::Unit)
            ) {
                return Some(
                    self.about(
                        codes::ENTRY_RETURN_TYPE,
                        function.id,
                        format!(
                            "`{name}` returns `{}`, which the native entry point cannot produce",
                            self.ty_name(&function.return_type)
                        ),
                        "native `main` returns `i64` or `unit`".to_string(),
                    )
                    .with_help("an `i64` result becomes the process exit status; `unit` exits 0"),
                );
            }
        }
        for param in &function.params {
            if param.take {
                return Some(self.about(
                    codes::UNSUPPORTED_INSTRUCTION,
                    function.id,
                    format!(
                        "`{name}` declares a `take` parameter, which transfers resource ownership"
                    ),
                    "no resource is natively lowered".to_string(),
                ));
            }
            if scalar_of(&param.ty).is_none() {
                return Some(self.unsupported_type(function.id, &param.ty, "a parameter of"));
            }
        }
        if scalar_of(&function.return_type).is_none() {
            return Some(self.unsupported_type(
                function.id,
                &function.return_type,
                "the result of",
            ));
        }
        None
    }

    fn unsupported_type(&self, id: ItemId, ty: &Ty, position: &str) -> Diagnostic {
        let name = self.name(id);
        self.about(
            codes::UNSUPPORTED_TYPE,
            id,
            format!(
                "`{}` is not a type the native backend represents, and it is {position} `{name}`",
                self.ty_name(ty)
            ),
            "native code uses `i64`, `bool` and `unit`".to_string(),
        )
    }

    /// Walks every reachable block of `function`, in ascending block
    /// order, and returns the first reason it cannot be compiled.
    fn check_body(&self, function: &'a Function, reachable: &[BlockId]) -> Option<Diagnostic> {
        // Rebuilt rather than threaded through from the reachability
        // walk: a `BTreeMap` of shared references is cheap, and the
        // alternative is a borrow that has to outlive what it came
        // from. It has already succeeded once for this function, so the
        // error arm here is unreachable in practice and still handled.
        let blocks = match self.blocks_by_id(function) {
            Ok(blocks) => blocks,
            Err(diagnostic) => return Some(*diagnostic),
        };

        let types = match self.value_types(function, reachable, &blocks) {
            Ok(types) => types,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let slots = self.alloc_slots(reachable, &blocks);

        for id in reachable {
            let Some(block) = blocks.get(id) else {
                continue;
            };
            for instruction in &block.instructions {
                if let Some(diagnostic) =
                    self.check_instruction(function, *id, instruction, &types, &slots)
                {
                    return Some(diagnostic);
                }
            }
            if let Some(diagnostic) =
                self.check_terminator(function, *id, &block.terminator, &types, &slots, &blocks)
            {
                return Some(diagnostic);
            }
        }

        self.check_slot_initialization(function, reachable, &blocks, &slots)
    }

    /// Every value a reachable block defines, with its declared type.
    ///
    /// Built from reachable blocks and parameters only. A value defined
    /// in an unreachable block is deliberately absent: the verifier's
    /// dominance rule means no reachable block can use one, and leaving
    /// it out is what makes "unreachable NIR never contaminates
    /// reachable code generation" a structural fact rather than a
    /// promise.
    fn value_types(
        &self,
        function: &'a Function,
        reachable: &[BlockId],
        blocks: &BTreeMap<BlockId, &'a BasicBlock>,
    ) -> Result<BTreeMap<ValueId, Ty>, Refusal> {
        let name = self.name(function.id);
        let mut types: BTreeMap<ValueId, Ty> = BTreeMap::new();
        let mut define = |value: ValueId, ty: Ty| -> Result<(), Refusal> {
            if types.insert(value, ty).is_some() {
                return Err(Box::new(self.unverified(
                    function.id,
                    format!("function `{name}` defines %{} more than once", value.0),
                    "duplicate value definition".to_string(),
                )));
            }
            Ok(())
        };
        for param in &function.params {
            define(param.value, param.ty.clone())?;
        }
        for id in reachable {
            let Some(block) = blocks.get(id) else {
                continue;
            };
            for instruction in &block.instructions {
                if let Instruction::Value { result, ty, .. } = instruction {
                    define(*result, ty.clone())?;
                }
            }
        }
        Ok(types)
    }

    /// The results of every reachable `alloc`: the only values that may
    /// appear in a slot position, and the only ones that may not appear
    /// anywhere else.
    fn alloc_slots(
        &self,
        reachable: &[BlockId],
        blocks: &BTreeMap<BlockId, &'a BasicBlock>,
    ) -> BTreeSet<ValueId> {
        let mut slots = BTreeSet::new();
        for id in reachable {
            let Some(block) = blocks.get(id) else {
                continue;
            };
            for instruction in &block.instructions {
                if let Instruction::Value {
                    result,
                    kind: ValueKind::Alloc,
                    ..
                } = instruction
                {
                    slots.insert(*result);
                }
            }
        }
        slots
    }

    /// Classifies one operand used as an ordinary value.
    fn operand(
        &self,
        function: &'a Function,
        block: BlockId,
        value: ValueId,
        types: &BTreeMap<ValueId, Ty>,
        slots: &BTreeSet<ValueId>,
    ) -> Result<Scalar, Refusal> {
        let name = self.name(function.id);
        if slots.contains(&value) {
            return Err(Box::new(self.about(
                codes::SLOT_USED_AS_VALUE,
                function.id,
                format!(
                    "function `{name}`: bb{} uses the slot %{} as a value",
                    block.0, value.0
                ),
                "a slot is only ever stored into or loaded from".to_string(),
            )));
        }
        let Some(ty) = types.get(&value) else {
            return Err(Box::new(self.unverified(
                function.id,
                format!(
                    "function `{name}`: bb{} uses %{}, which no reachable instruction defines",
                    block.0, value.0
                ),
                "undefined value".to_string(),
            )));
        };
        match scalar_of(ty) {
            Some(scalar) => Ok(scalar),
            None => Err(Box::new(self.unsupported_type(
                function.id,
                ty,
                "used inside",
            ))),
        }
    }

    fn check_instruction(
        &self,
        function: &'a Function,
        block: BlockId,
        instruction: &Instruction,
        types: &BTreeMap<ValueId, Ty>,
        slots: &BTreeSet<ValueId>,
    ) -> Option<Diagnostic> {
        let name = self.name(function.id);
        match instruction {
            Instruction::Value { result, ty, kind } => {
                self.check_value(function, block, *result, ty, kind, types, slots)
            }
            Instruction::Store { slot, value, mode } => {
                if !matches!(mode, OwnershipMode::Observe) {
                    return Some(self.about(
                        codes::UNSUPPORTED_INSTRUCTION,
                        function.id,
                        format!(
                            "function `{name}`: bb{} stores by transferring ownership",
                            block.0
                        ),
                        "no resource is natively lowered".to_string(),
                    ));
                }
                if !slots.contains(slot) {
                    return Some(self.unverified(
                        function.id,
                        format!(
                            "function `{name}`: bb{} stores into %{}, which no reachable `alloc` produced",
                            block.0, slot.0
                        ),
                        "unknown slot".to_string(),
                    ));
                }
                let stored = match self.operand(function, block, *value, types, slots) {
                    Ok(scalar) => scalar,
                    Err(diagnostic) => return Some(*diagnostic),
                };
                let slot_scalar = types.get(slot).and_then(scalar_of);
                if slot_scalar != Some(stored) {
                    return Some(self.unverified(
                        function.id,
                        format!(
                            "function `{name}`: bb{} stores a {} into a slot that is not one",
                            block.0,
                            stored.as_str()
                        ),
                        "slot type mismatch".to_string(),
                    ));
                }
                None
            }
            // Everything below exists only to serve a feature the
            // native subset does not include. None of it is lowered
            // approximately, erased, or replaced by a unit value.
            Instruction::Drop { .. } => Some(self.unsupported_instruction(
                function.id,
                block,
                "drops a resource",
                "resources are not natively lowered",
            )),
            Instruction::DecomposeVariant { .. } => Some(self.unsupported_instruction(
                function.id,
                block,
                "takes a variant apart",
                "variants are not natively lowered",
            )),
            Instruction::StorePlace { .. } => Some(self.unsupported_instruction(
                function.id,
                block,
                "reinitializes an aggregate's field",
                "aggregates are not natively lowered",
            )),
            Instruction::EndObserve { .. } => Some(self.unsupported_instruction(
                function.id,
                block,
                "ends a scoped observation",
                "observations are not natively lowered",
            )),
        }
    }

    fn unsupported_instruction(
        &self,
        id: ItemId,
        block: BlockId,
        what: &str,
        why: &str,
    ) -> Diagnostic {
        let name = self.name(id);
        self.about(
            codes::UNSUPPORTED_INSTRUCTION,
            id,
            format!("function `{name}`: bb{} {what}", block.0),
            why.to_string(),
        )
        .with_help("`napitia run` executes this program with the interpreter, unchanged")
    }

    /// Exhaustive over [`ValueKind`]: every variant is named, so a
    /// future NIR instruction cannot become natively supported by
    /// falling through a wildcard.
    #[allow(clippy::too_many_arguments)]
    fn check_value(
        &self,
        function: &'a Function,
        block: BlockId,
        result: ValueId,
        ty: &Ty,
        kind: &ValueKind,
        types: &BTreeMap<ValueId, Ty>,
        slots: &BTreeSet<ValueId>,
    ) -> Option<Diagnostic> {
        let name = self.name(function.id);
        let operand = |value: ValueId| self.operand(function, block, value, types, slots);
        let mismatch = |what: &str| {
            Some(self.unverified(
                function.id,
                format!("function `{name}`: bb{}'s %{} {what}", block.0, result.0),
                "operand type mismatch".to_string(),
            ))
        };

        // A result this backend cannot represent is reported before the
        // operation itself: the type is the root cause, and naming the
        // operation instead would send a reader looking in the wrong
        // place.
        let Some(result_scalar) = scalar_of(ty) else {
            return Some(self.unsupported_type(function.id, ty, "produced inside"));
        };

        match kind {
            ValueKind::Alloc => None,
            ValueKind::Const(constant) => match constant {
                Const::Int(_) if result_scalar == Scalar::Int => None,
                Const::Bool(_) if result_scalar == Scalar::Bool => None,
                Const::Unit if result_scalar == Scalar::Unit => None,
                Const::Int(_) | Const::Bool(_) | Const::Unit => {
                    mismatch("is a constant declared with a type it is not")
                }
                Const::Float(_) => Some(self.unsupported_constant(function.id, block, "a float")),
                Const::Char(_) => Some(self.unsupported_constant(function.id, block, "a char")),
                Const::Str(_) => Some(self.unsupported_constant(function.id, block, "a string")),
            },
            ValueKind::Load(slot) => {
                if !slots.contains(slot) {
                    return Some(self.unverified(
                        function.id,
                        format!(
                            "function `{name}`: bb{} loads %{}, which no reachable `alloc` produced",
                            block.0, slot.0
                        ),
                        "unknown slot".to_string(),
                    ));
                }
                if types.get(slot).and_then(scalar_of) != Some(result_scalar) {
                    return mismatch("loads a slot of another type");
                }
                None
            }
            ValueKind::Add(a, b) | ValueKind::Sub(a, b) | ValueKind::Mul(a, b) => {
                self.binary_int(operand, mismatch, result_scalar, *a, *b)
            }
            ValueKind::And(a, b) | ValueKind::Or(a, b) | ValueKind::Xor(a, b) => {
                self.binary_int(operand, mismatch, result_scalar, *a, *b)
            }
            // See this module's own documentation: the interpreter
            // answers the exceptional case with a runtime error, and
            // Alpha 0.2.0 has no native facility that can.
            ValueKind::Div(_, _) => Some(self.unsupported_operator(function.id, block, "div")),
            ValueKind::Rem(_, _) => Some(self.unsupported_operator(function.id, block, "rem")),
            ValueKind::Shl(_, _) => Some(self.unsupported_operator(function.id, block, "shl")),
            ValueKind::Shr(_, _) => Some(self.unsupported_operator(function.id, block, "shr")),
            ValueKind::Neg(a) => {
                let scalar = match operand(*a) {
                    Ok(scalar) => scalar,
                    Err(diagnostic) => return Some(*diagnostic),
                };
                if scalar != Scalar::Int || result_scalar != Scalar::Int {
                    return mismatch("negates something that is not an `i64`");
                }
                None
            }
            ValueKind::Not(a) => {
                let scalar = match operand(*a) {
                    Ok(scalar) => scalar,
                    Err(diagnostic) => return Some(*diagnostic),
                };
                if scalar != result_scalar || scalar == Scalar::Unit {
                    return mismatch("applies `not` to something it cannot invert");
                }
                None
            }
            ValueKind::Eq(a, b) | ValueKind::Ne(a, b) => {
                let (left, right) = match (operand(*a), operand(*b)) {
                    (Ok(left), Ok(right)) => (left, right),
                    (Err(diagnostic), _) | (_, Err(diagnostic)) => return Some(*diagnostic),
                };
                if left != right || result_scalar != Scalar::Bool {
                    return mismatch("compares operands it cannot compare");
                }
                None
            }
            ValueKind::Lt(a, b)
            | ValueKind::Le(a, b)
            | ValueKind::Gt(a, b)
            | ValueKind::Ge(a, b) => {
                let (left, right) = match (operand(*a), operand(*b)) {
                    (Ok(left), Ok(right)) => (left, right),
                    (Err(diagnostic), _) | (_, Err(diagnostic)) => return Some(*diagnostic),
                };
                if left != right || result_scalar != Scalar::Bool {
                    return mismatch("compares operands it cannot compare");
                }
                // The interpreter's own ordering answers `unit < unit`
                // with a runtime error rather than a value, so there is
                // nothing here to reproduce faithfully.
                if left == Scalar::Unit {
                    return Some(self.unsupported_operator(
                        function.id,
                        block,
                        "ordered comparison of `unit`",
                    ));
                }
                None
            }
            ValueKind::Call(callee, type_args, args, evidence) => self.check_call(
                function,
                block,
                result,
                result_scalar,
                *callee,
                type_args,
                args,
                evidence,
                types,
                slots,
            ),
            ValueKind::ProtocolCall { .. } => Some(
                self.about(
                    codes::CAPABILITY_DISPATCH,
                    function.id,
                    format!(
                        "function `{name}`: bb{} dispatches through capability evidence",
                        block.0
                    ),
                    "the native backend emits direct calls only".to_string(),
                )
                .with_help("`napitia run` executes this program with the interpreter, unchanged"),
            ),
            ValueKind::RecordCreate(_, _, _) => Some(self.unsupported_instruction(
                function.id,
                block,
                "constructs a record",
                "records are not natively lowered",
            )),
            ValueKind::RecordField { .. } => Some(self.unsupported_instruction(
                function.id,
                block,
                "reads a record field",
                "records are not natively lowered",
            )),
            ValueKind::VariantCreate { .. } => Some(self.unsupported_instruction(
                function.id,
                block,
                "constructs a variant",
                "variants are not natively lowered",
            )),
            ValueKind::VariantPayload { .. } => Some(self.unsupported_instruction(
                function.id,
                block,
                "reads a variant payload",
                "variants are not natively lowered",
            )),
            ValueKind::Move { .. } => Some(self.unsupported_instruction(
                function.id,
                block,
                "moves a resource",
                "resources are not natively lowered",
            )),
            ValueKind::DeferCapture { .. } => Some(self.unsupported_instruction(
                function.id,
                block,
                "captures a resource for a `defer`",
                "deferred cleanup is not natively lowered",
            )),
            ValueKind::PlaceRead { .. } => Some(self.unsupported_instruction(
                function.id,
                block,
                "reads an aggregate place",
                "aggregates are not natively lowered",
            )),
            ValueKind::ObservePlace { .. } => Some(self.unsupported_instruction(
                function.id,
                block,
                "begins a scoped observation",
                "observations are not natively lowered",
            )),
        }
    }

    fn binary_int(
        &self,
        operand: impl Fn(ValueId) -> Result<Scalar, Refusal>,
        mismatch: impl Fn(&str) -> Option<Diagnostic>,
        result_scalar: Scalar,
        a: ValueId,
        b: ValueId,
    ) -> Option<Diagnostic> {
        let (left, right) = match (operand(a), operand(b)) {
            (Ok(left), Ok(right)) => (left, right),
            (Err(diagnostic), _) | (_, Err(diagnostic)) => return Some(*diagnostic),
        };
        if left != Scalar::Int || right != Scalar::Int || result_scalar != Scalar::Int {
            return mismatch("combines operands that are not both `i64`");
        }
        None
    }

    fn unsupported_constant(&self, id: ItemId, block: BlockId, what: &str) -> Diagnostic {
        let name = self.name(id);
        self.about(
            codes::UNSUPPORTED_TYPE,
            id,
            format!("function `{name}`: bb{} builds {what} constant", block.0),
            "native code uses `i64`, `bool` and `unit`".to_string(),
        )
    }

    fn unsupported_operator(&self, id: ItemId, block: BlockId, operator: &str) -> Diagnostic {
        let name = self.name(id);
        self.about(
            codes::UNSUPPORTED_OPERATOR,
            id,
            format!("function `{name}`: bb{} uses `{operator}`", block.0),
            "this operator's exceptional case has no native behavior yet".to_string(),
        )
        .with_note(
            "the interpreter answers it with a runtime error, and Alpha 0.2.0 has no native runtime to raise one",
        )
        .with_help("`napitia run` executes this program with the interpreter, unchanged")
    }

    #[allow(clippy::too_many_arguments)]
    fn check_call(
        &self,
        function: &'a Function,
        block: BlockId,
        result: ValueId,
        result_scalar: Scalar,
        callee: ItemId,
        type_args: &[Ty],
        args: &[ValueId],
        evidence: &[crate::types::Evidence],
        types: &BTreeMap<ValueId, Ty>,
        slots: &BTreeSet<ValueId>,
    ) -> Option<Diagnostic> {
        let name = self.name(function.id);
        if !type_args.is_empty() {
            return Some(self.about(
                codes::GENERIC_CODE,
                function.id,
                format!(
                    "function `{name}`: bb{} calls a generic function with type arguments",
                    block.0
                ),
                "the native backend does not monomorphize".to_string(),
            ));
        }
        if !evidence.is_empty() {
            return Some(self.about(
                codes::CAPABILITY_DISPATCH,
                function.id,
                format!(
                    "function `{name}`: bb{} supplies capability evidence to a call",
                    block.0
                ),
                "the native backend emits direct calls only".to_string(),
            ));
        }
        let Some(target) = self.functions.get(&callee) else {
            return Some(
                self.about(
                    codes::UNKNOWN_CALLEE,
                    function.id,
                    format!(
                        "function `{name}`: bb{} calls function id {}, which this module does not define",
                        block.0, callee.0
                    ),
                    "every native callee is compiled alongside its caller".to_string(),
                )
                .with_help("the native backend has no FFI"),
            );
        };
        let target_name = self.name(callee);
        if args.len() != target.params.len() {
            return Some(self.about(
                codes::CALL_SIGNATURE_MISMATCH,
                function.id,
                format!(
                    "function `{name}`: bb{} passes {} argument(s) to `{target_name}`, which takes {}",
                    block.0,
                    args.len(),
                    target.params.len()
                ),
                "direct calls match their callee exactly".to_string(),
            ));
        }
        for (index, (arg, param)) in args.iter().zip(&target.params).enumerate() {
            let actual = match self.operand(function, block, *arg, types, slots) {
                Ok(scalar) => scalar,
                Err(diagnostic) => return Some(*diagnostic),
            };
            let expected = scalar_of(&param.ty);
            if Some(actual) != expected {
                return Some(self.about(
                    codes::CALL_SIGNATURE_MISMATCH,
                    function.id,
                    format!(
                        "function `{name}`: bb{} passes a `{}` as argument {} of `{target_name}`, which expects `{}`",
                        block.0,
                        actual.as_str(),
                        index,
                        self.ty_name(&param.ty),
                    ),
                    "direct calls match their callee exactly".to_string(),
                ));
            }
        }
        if scalar_of(&target.return_type) != Some(result_scalar) {
            return Some(self.about(
                codes::CALL_SIGNATURE_MISMATCH,
                function.id,
                format!(
                    "function `{name}`: bb{}'s %{} takes the result of `{target_name}` as a type it does not return",
                    block.0, result.0
                ),
                "direct calls match their callee exactly".to_string(),
            ));
        }
        None
    }

    /// Exhaustive over [`Terminator`].
    #[allow(clippy::too_many_arguments)]
    fn check_terminator(
        &self,
        function: &'a Function,
        block: BlockId,
        terminator: &Terminator,
        types: &BTreeMap<ValueId, Ty>,
        slots: &BTreeSet<ValueId>,
        blocks: &BTreeMap<BlockId, &'a BasicBlock>,
    ) -> Option<Diagnostic> {
        let name = self.name(function.id);
        let dangling = |target: BlockId| {
            Some(self.unverified(
                function.id,
                format!(
                    "function `{name}`: bb{} branches to bb{}, which it does not declare",
                    block.0, target.0
                ),
                "unknown branch target".to_string(),
            ))
        };
        match terminator {
            Terminator::Return(value) => {
                let declared = scalar_of(&function.return_type);
                match value {
                    Some(value) => {
                        let actual = match self.operand(function, block, *value, types, slots) {
                            Ok(scalar) => scalar,
                            Err(diagnostic) => return Some(*diagnostic),
                        };
                        if Some(actual) != declared {
                            return Some(self.unverified(
                                function.id,
                                format!(
                                    "function `{name}`: bb{} returns a `{}` from a function declared `{}`",
                                    block.0,
                                    actual.as_str(),
                                    self.ty_name(&function.return_type)
                                ),
                                "return type mismatch".to_string(),
                            ));
                        }
                        None
                    }
                    None => {
                        if declared != Some(Scalar::Unit) {
                            return Some(self.unverified(
                                function.id,
                                format!(
                                    "function `{name}`: bb{} returns no value from a function declared `{}`",
                                    block.0,
                                    self.ty_name(&function.return_type)
                                ),
                                "return type mismatch".to_string(),
                            ));
                        }
                        None
                    }
                }
            }
            Terminator::Branch(target) => {
                if !blocks.contains_key(target) {
                    return dangling(*target);
                }
                None
            }
            Terminator::CondBranch {
                condition,
                then_block,
                else_block,
            } => {
                let scalar = match self.operand(function, block, *condition, types, slots) {
                    Ok(scalar) => scalar,
                    Err(diagnostic) => return Some(*diagnostic),
                };
                if scalar != Scalar::Bool {
                    return Some(self.unverified(
                        function.id,
                        format!(
                            "function `{name}`: bb{} branches on a `{}`",
                            block.0,
                            scalar.as_str()
                        ),
                        "a condition is a `bool`".to_string(),
                    ));
                }
                for target in [then_block, else_block] {
                    if !blocks.contains_key(target) {
                        return dangling(*target);
                    }
                }
                None
            }
            Terminator::Switch { .. } => Some(self.unsupported_terminator(
                function.id,
                block,
                "switches on a variant case",
                "variants are not natively lowered",
            )),
            Terminator::Invoke { .. } => Some(self.unsupported_terminator(
                function.id,
                block,
                "invokes a fallible function",
                "there is no native typed-failure runtime",
            )),
            Terminator::Raise { .. } => Some(self.unsupported_terminator(
                function.id,
                block,
                "raises an error",
                "there is no native typed-failure runtime",
            )),
        }
    }

    fn unsupported_terminator(
        &self,
        id: ItemId,
        block: BlockId,
        what: &str,
        why: &str,
    ) -> Diagnostic {
        let name = self.name(id);
        self.about(
            codes::UNSUPPORTED_TERMINATOR,
            id,
            format!("function `{name}`: bb{} {what}", block.0),
            why.to_string(),
        )
        .with_help("`napitia run` executes this program with the interpreter, unchanged")
    }

    /// Requires every reachable `load` to be preceded, on *every* path
    /// that reaches it, by a `store` to that same slot.
    ///
    /// This is not pedantry. The interpreter models a slot as an entry
    /// in its own value table that `alloc` seeds with `Value::Unit`, so
    /// a load with no preceding store reads a unit -- while Cranelift's
    /// SSA builder answers an undefined variable by silently
    /// materializing a zero. Those are two different answers, and
    /// neither is a value this backend is willing to invent. Lowering
    /// rejects the program instead.
    ///
    /// A forward, path-intersecting analysis: a slot counts as stored at
    /// a block's entry only when every predecessor agrees. Non-entry
    /// blocks start optimistic (every slot) and only ever shrink, so the
    /// fixpoint is reached in at most `blocks * slots` narrowing steps.
    fn check_slot_initialization(
        &self,
        function: &'a Function,
        reachable: &[BlockId],
        blocks: &BTreeMap<BlockId, &'a BasicBlock>,
        slots: &BTreeSet<ValueId>,
    ) -> Option<Diagnostic> {
        if slots.is_empty() {
            return None;
        }
        // Membership is asked once per edge, so it is worth a set: a
        // linear scan of `reachable` here would make this pass
        // quadratic in the size of a function, which is the wrong shape
        // for something whose job includes not hanging.
        let live: BTreeSet<BlockId> = reachable.iter().copied().collect();
        let mut predecessors: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
        for id in reachable {
            let Some(block) = blocks.get(id) else {
                continue;
            };
            for target in terminator_targets(&block.terminator) {
                if live.contains(&target) {
                    predecessors.entry(target).or_default().insert(*id);
                }
            }
        }

        let mut entry_state: BTreeMap<BlockId, BTreeSet<ValueId>> = BTreeMap::new();
        for id in reachable {
            let state = if *id == BlockId(0) {
                BTreeSet::new()
            } else {
                slots.clone()
            };
            entry_state.insert(*id, state);
        }

        let mut changed = true;
        while changed {
            changed = false;
            for id in reachable {
                if *id == BlockId(0) {
                    continue;
                }
                let Some(preds) = predecessors.get(id) else {
                    // Unreachable from `bb0` by definition, so it is not
                    // in `reachable`; a block with no predecessor other
                    // than the entry cannot occur here.
                    continue;
                };
                let mut incoming: Option<BTreeSet<ValueId>> = None;
                for pred in preds {
                    let out = match entry_state.get(pred) {
                        Some(state) => stores_after(state, blocks.get(pred).copied()),
                        None => continue,
                    };
                    incoming = Some(match incoming {
                        Some(current) => current.intersection(&out).copied().collect(),
                        None => out,
                    });
                }
                let incoming = incoming.unwrap_or_default();
                if let Some(existing) = entry_state.get_mut(id)
                    && *existing != incoming
                {
                    *existing = incoming;
                    changed = true;
                }
            }
        }

        let name = self.name(function.id);
        for id in reachable {
            let Some(block) = blocks.get(id) else {
                continue;
            };
            let mut stored = entry_state.get(id).cloned().unwrap_or_default();
            for instruction in &block.instructions {
                match instruction {
                    Instruction::Value {
                        kind: ValueKind::Load(slot),
                        ..
                    } => {
                        if !stored.contains(slot) {
                            return Some(
                                self.about(
                                    codes::UNINITIALIZED_SLOT_LOAD,
                                    function.id,
                                    format!(
                                        "function `{name}`: bb{} loads %{} on a path that never stored it",
                                        id.0, slot.0
                                    ),
                                    "the native backend never invents a slot's first value"
                                        .to_string(),
                                ),
                            );
                        }
                    }
                    Instruction::Store { slot, .. } => {
                        stored.insert(*slot);
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// Reports each cycle in the reachable direct-call graph once, at
    /// the cycle's own canonical representative: the smallest
    /// [`ItemId`] in it. Cycles are found as strongly connected
    /// components, so a cycle is detected for what it is rather than
    /// inferred from how deep a traversal happened to go.
    fn report_cycles(&mut self, functions: &[ItemId], callees: &BTreeMap<ItemId, Vec<ItemId>>) {
        let mut edges: BTreeMap<ItemId, Vec<ItemId>> = BTreeMap::new();
        let present: BTreeSet<ItemId> = functions.iter().copied().collect();
        for id in functions {
            let mut targets: Vec<ItemId> = callees
                .get(id)
                .map(|targets| {
                    targets
                        .iter()
                        .copied()
                        .filter(|target| present.contains(target))
                        .collect()
                })
                .unwrap_or_default();
            targets.sort_unstable();
            targets.dedup();
            edges.insert(*id, targets);
        }

        for component in strongly_connected_components(functions, &edges) {
            let is_cycle = component.len() > 1
                || component
                    .first()
                    .is_some_and(|id| edges.get(id).is_some_and(|targets| targets.contains(id)));
            if !is_cycle {
                continue;
            }
            let Some(root) = component.first().copied() else {
                continue;
            };
            let members: Vec<String> = component.iter().map(|id| self.name(*id)).collect();
            let description = if component.len() == 1 {
                format!("`{}` calls itself", members.join(""))
            } else {
                format!("`{}` call each other", members.join("`, `"))
            };
            self.diagnostics.push(
                self.about(
                    codes::RECURSIVE_CALL_GRAPH,
                    root,
                    format!(
                        "the native backend cannot compile a recursive call graph: {description}"
                    ),
                    "recursion is not natively lowered".to_string(),
                )
                .with_help("`napitia run` executes this program with the interpreter, unchanged"),
            );
        }
    }
}

/// The slots `block` has definitely stored by the time it ends, given
/// what was definitely stored when it began.
fn stores_after(entry: &BTreeSet<ValueId>, block: Option<&BasicBlock>) -> BTreeSet<ValueId> {
    let mut state = entry.clone();
    let Some(block) = block else {
        return state;
    };
    for instruction in &block.instructions {
        if let Instruction::Store { slot, .. } = instruction {
            state.insert(*slot);
        }
    }
    state
}

/// Every block one terminator can transfer control to.
///
/// Exhaustive over [`Terminator`]. Unsupported terminators still
/// contribute their edges: reachability is about which blocks the
/// program could enter, which is a separate question from whether this
/// backend can compile what it finds there.
fn terminator_targets(terminator: &Terminator) -> Vec<BlockId> {
    match terminator {
        Terminator::Return(_) | Terminator::Raise { .. } => Vec::new(),
        Terminator::Branch(target) => vec![*target],
        Terminator::CondBranch {
            then_block,
            else_block,
            ..
        } => vec![*then_block, *else_block],
        Terminator::Switch { cases, .. } => cases.clone(),
        Terminator::Invoke {
            ok_target,
            err_targets,
            ..
        } => {
            let mut targets = vec![*ok_target];
            targets.extend(err_targets.iter().map(|target| target.target));
            targets
        }
    }
}

/// Every function called directly from a reachable block, in the order
/// the instructions appear under an ascending block walk.
fn direct_callees(blocks: &BTreeMap<BlockId, &BasicBlock>, reachable: &[BlockId]) -> Vec<ItemId> {
    let mut callees = Vec::new();
    for id in reachable {
        let Some(block) = blocks.get(id) else {
            continue;
        };
        for instruction in &block.instructions {
            if let Instruction::Value {
                kind: ValueKind::Call(callee, ..),
                ..
            } = instruction
            {
                callees.push(*callee);
            }
        }
        // An `invoke` is rejected as a terminator, but its callee is
        // still an edge of the real call graph, and leaving it out
        // would let a recursion cycle hide behind one.
        if let Terminator::Invoke { callee, .. } = &block.terminator {
            callees.push(*callee);
        }
    }
    callees
}

/// Tarjan's strongly connected components, iteratively.
///
/// Iterative on purpose: a deep call graph must not be able to exhaust
/// the native stack inside a pass whose whole job is to reject programs
/// safely. `nodes` is already ascending and every adjacency list is
/// sorted, so the components -- and the order they are returned in --
/// are a function of the graph alone.
fn strongly_connected_components(
    nodes: &[ItemId],
    edges: &BTreeMap<ItemId, Vec<ItemId>>,
) -> Vec<Vec<ItemId>> {
    let mut index: BTreeMap<ItemId, usize> = BTreeMap::new();
    let mut lowlink: BTreeMap<ItemId, usize> = BTreeMap::new();
    let mut on_stack: BTreeSet<ItemId> = BTreeSet::new();
    let mut stack: Vec<ItemId> = Vec::new();
    let mut counter = 0usize;
    let mut components: Vec<Vec<ItemId>> = Vec::new();

    for root in nodes {
        if index.contains_key(root) {
            continue;
        }
        let mut work: Vec<(ItemId, usize)> = vec![(*root, 0)];
        while let Some((node, next_child)) = work.pop() {
            if next_child == 0 {
                index.insert(node, counter);
                lowlink.insert(node, counter);
                counter += 1;
                stack.push(node);
                on_stack.insert(node);
            }
            let adjacent = edges
                .get(&node)
                .map_or(&[][..], |targets| targets.as_slice());
            let mut descended = false;
            for position in next_child..adjacent.len() {
                let Some(child) = adjacent.get(position).copied() else {
                    continue;
                };
                if !index.contains_key(&child) {
                    work.push((node, position + 1));
                    work.push((child, 0));
                    descended = true;
                    break;
                }
                if on_stack.contains(&child)
                    && let (Some(child_index), Some(node_low)) =
                        (index.get(&child).copied(), lowlink.get(&node).copied())
                {
                    lowlink.insert(node, node_low.min(child_index));
                }
            }
            if descended {
                continue;
            }
            if index.get(&node).copied() == lowlink.get(&node).copied() {
                let mut component = Vec::new();
                while let Some(member) = stack.pop() {
                    on_stack.remove(&member);
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                component.sort_unstable();
                components.push(component);
            }
            if let Some((parent, _)) = work.last().copied()
                && let (Some(parent_low), Some(node_low)) =
                    (lowlink.get(&parent).copied(), lowlink.get(&node).copied())
            {
                lowlink.insert(parent, parent_low.min(node_low));
            }
        }
    }

    components.sort_by_key(|component| component.first().copied());
    components
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::{self, IrOutput};
    use crate::source::SourceMap;

    /// One compiled, verified single-file program, kept together so a
    /// test can validate it and render whatever it refuses.
    struct Compiled {
        module: Module,
        registry: ItemRegistry,
        source: SourceId,
        interner: Interner,
        map: SourceMap,
    }

    /// Compiles `text` all the way through `nir::verify`, exactly as
    /// `napitia build` does before the native backend is reached.
    fn compile(text: &str) -> Compiled {
        let mut map = SourceMap::new();
        let source = map.add_file("native.npt", text);
        let mut interner = Interner::new();
        match driver::ir(&map, source, &mut interner) {
            IrOutput::Ready { nir, registry } => Compiled {
                module: nir,
                registry,
                source,
                interner,
                map,
            },
            IrOutput::Diagnostics(diagnostics) => {
                let codes: Vec<&str> = diagnostics.iter().map(|d| d.code).collect();
                panic!("this fixture must compile and verify cleanly, got {codes:?}")
            }
        }
    }

    impl Compiled {
        fn validate(&self) -> Result<NativePlan, Vec<Diagnostic>> {
            self.validate_for(TARGET_TRIPLE, &[])
        }

        fn validate_for(
            &self,
            target: &str,
            imports: &[Span],
        ) -> Result<NativePlan, Vec<Diagnostic>> {
            validate(
                &self.module,
                self.source,
                &self.interner,
                &self.registry,
                target,
                imports,
            )
        }

        fn codes(&self) -> Vec<&'static str> {
            match self.validate() {
                Ok(_) => Vec::new(),
                Err(diagnostics) => diagnostics.iter().map(|d| d.code).collect(),
            }
        }

        fn rendered(&self) -> String {
            match self.validate() {
                Ok(_) => String::new(),
                Err(diagnostics) => diagnostics
                    .iter()
                    .map(|d| crate::diagnostics::render(d, &self.map))
                    .collect(),
            }
        }
    }

    fn accepts(text: &str) -> NativePlan {
        let compiled = compile(text);
        match compiled.validate() {
            Ok(plan) => plan,
            Err(diagnostics) => {
                let codes: Vec<&str> = diagnostics.iter().map(|d| d.code).collect();
                panic!("expected the native subset to accept this program, got {codes:?}")
            }
        }
    }

    fn rejects(text: &str) -> Vec<&'static str> {
        let codes = compile(text).codes();
        assert!(
            !codes.is_empty(),
            "expected the native subset to reject this program"
        );
        codes
    }

    // -- acceptance -----------------------------------------------------

    /// Every natively supported instruction, terminator and type in one
    /// program: `i64`/`bool`/`unit` values, constants, slots, all the
    /// accepted arithmetic and bitwise operators, all six comparisons,
    /// both `if` arms, a loop with a backedge, a chain of direct calls,
    /// scalar parameters and scalar results.
    const EVERY_SUPPORTED_CONSTRUCT: &str = "
        func add(a: i64, b: i64) -> i64 { return a + b; }
        func twice(x: i64) -> i64 { return add(x, x); }
        func pick(flag: bool, a: i64, b: i64) -> i64 {
            if flag { return a; }
            return b;
        }
        func nothing() -> unit { return; }
        func main() -> i64 {
            mutable total = 0;
            mutable index = 0;
            while index < 4 {
                total = total + twice(index);
                index = index + 1;
            }
            value bits = (total & 12) | (total ^ 3);
            value inverted = ~bits;
            value negated = -bits;
            value ordered = (total <= 40) == !(total > 40);
            value different = (total >= 0) != (total < 0);
            nothing();
            return pick(ordered, total - negated, inverted) * 2 + pick(different, 1, 0);
        }
    ";

    #[test]
    fn every_supported_construct_validates() {
        let plan = accepts(EVERY_SUPPORTED_CONSTRUCT);
        assert_eq!(plan.entry_result, Scalar::Int);
        assert_eq!(
            plan.functions.len(),
            5,
            "every declared function is reachable from `main` here"
        );
    }

    #[test]
    fn a_unit_returning_main_validates() {
        let plan = accepts(
            "func nothing() -> unit { return; } func main() -> unit { nothing(); return; }",
        );
        assert_eq!(plan.entry_result, Scalar::Unit);
        assert_eq!(plan.functions.len(), 2);
    }

    #[test]
    fn a_bool_local_and_a_bool_parameter_validate() {
        accepts(
            "func flip(x: bool) -> bool { return !x; } \
             func main() -> i64 { value b = flip(true); if b { return 1; } return 0; }",
        );
    }

    // -- storage order --------------------------------------------------

    /// Reversing how the module stores its functions, and how each
    /// function stores its blocks, changes nothing: every order this
    /// pass produces comes from `ItemId`/`BlockId`, never from a vector
    /// position.
    #[test]
    fn reversed_function_and_block_storage_produce_an_identical_plan() {
        let forward = compile(EVERY_SUPPORTED_CONSTRUCT);
        let mut reversed = compile(EVERY_SUPPORTED_CONSTRUCT);
        reversed.module.functions.reverse();
        for function in &mut reversed.module.functions {
            function.blocks.reverse();
        }

        let expected = forward.validate().expect("the forward module validates");
        let actual = reversed
            .validate()
            .expect("reversing storage must not change acceptance");
        assert_eq!(expected, actual);
    }

    /// The same program, with its entry block stored last, still starts
    /// at `bb0`.
    #[test]
    fn an_entry_block_stored_last_is_still_the_entry_block() {
        let mut compiled = compile(EVERY_SUPPORTED_CONSTRUCT);
        for function in &mut compiled.module.functions {
            if function.blocks.len() > 1 {
                function.blocks.rotate_left(1);
            }
        }
        compiled
            .validate()
            .expect("the entry block is bb0 wherever it is stored");
    }

    // -- reachability policy --------------------------------------------

    /// A function `main` never calls is dead code: it is not validated,
    /// not compiled, and cannot make an otherwise-supported program
    /// fail. Exactly what the interpreter does with it -- nothing.
    #[test]
    fn an_unreachable_function_using_a_resource_does_not_fail_the_build() {
        let plan = accepts(
            "
            resource File { descriptor: i64 }
            func open() -> File { return File { descriptor: 1 }; }
            func unused() -> i64 {
                value file = open();
                value d = file.descriptor;
                drop file;
                return d;
            }
            func main() -> i64 { return 7; }
            ",
        );
        assert_eq!(
            plan.functions.len(),
            1,
            "only `main` is reachable, so only `main` is compiled"
        );
    }

    /// The same construct, in a function `main` does reach, is refused.
    #[test]
    fn a_reachable_nested_function_using_a_resource_fails_the_build() {
        let codes = rejects(
            "
            resource File { descriptor: i64 }
            func open() -> File { return File { descriptor: 1 }; }
            func used() -> i64 {
                value file = open();
                value d = file.descriptor;
                drop file;
                return d;
            }
            func main() -> i64 { return used(); }
            ",
        );
        assert!(
            codes.contains(&codes::UNSUPPORTED_TYPE)
                || codes.contains(&codes::UNSUPPORTED_INSTRUCTION),
            "a reachable resource must be refused, got {codes:?}"
        );
    }

    // -- the entry contract ---------------------------------------------

    #[test]
    fn a_module_without_main_is_refused() {
        let compiled = compile("func helper() -> i64 { return 1; }");
        assert_eq!(compiled.codes(), vec![codes::MISSING_ENTRY]);
    }

    #[test]
    fn a_main_returning_something_else_is_refused() {
        let compiled = compile("func main() -> bool { return true; }");
        assert_eq!(compiled.codes(), vec![codes::ENTRY_RETURN_TYPE]);
    }

    // -- unsupported language features ----------------------------------

    #[test]
    fn a_resource_program_is_refused() {
        let codes = rejects(
            "
            resource File { descriptor: i64 }
            func open(descriptor: i64) -> File { return File { descriptor: descriptor }; }
            func inspect(file: File) -> i64 { return file.descriptor; }
            func main() -> i64 {
                value file = open(3);
                value result = inspect(file);
                drop file;
                return result;
            }
            ",
        );
        assert!(
            codes.iter().all(|code| *code == codes::UNSUPPORTED_TYPE),
            "{codes:?}"
        );
    }

    #[test]
    fn an_observation_is_refused() {
        let codes = rejects(
            "
            resource File { descriptor: i64 }
            func inspect(file: File) -> i64 { return file.descriptor; }
            func read(take file: File) -> i64 {
                mutable result = 0;
                observe file as view { result = inspect(view); }
                drop file;
                return result;
            }
            func main() -> i64 { return read(File { descriptor: 7 }); }
            ",
        );
        assert!(!codes.is_empty(), "{codes:?}");
    }

    #[test]
    fn a_defer_is_refused() {
        let codes = rejects(
            "
            resource File { descriptor: i64 }
            func open(descriptor: i64) -> File { return File { descriptor: descriptor }; }
            func inspect(file: File) -> i64 { return file.descriptor; }
            func close(file: File) -> unit { }
            func main() -> i64 {
                value file = open(9);
                defer close(file);
                return inspect(file);
            }
            ",
        );
        assert!(!codes.is_empty(), "{codes:?}");
    }

    #[test]
    fn a_record_is_refused() {
        let codes = rejects(
            "
            record User { id: i64 }
            func identifier(user: User) -> i64 { return user.id; }
            func main() -> i64 { return identifier(User { id: 4 }); }
            ",
        );
        assert!(codes.contains(&codes::UNSUPPORTED_TYPE), "{codes:?}");
    }

    #[test]
    fn a_variant_is_refused() {
        let codes = rejects(
            "
            variant Answer { Yes, No }
            func pick(answer: Answer) -> i64 {
                return match answer { Yes => 1, No => 0, };
            }
            func main() -> i64 { return pick(Answer.Yes); }
            ",
        );
        assert!(codes.contains(&codes::UNSUPPORTED_TYPE), "{codes:?}");
    }

    #[test]
    fn a_string_is_refused() {
        let codes = rejects(
            "func main() -> i64 { value s = \"hi\"; if s == \"hi\" { return 1; } return 0; }",
        );
        assert!(codes.contains(&codes::UNSUPPORTED_TYPE), "{codes:?}");
    }

    #[test]
    fn a_generic_function_is_refused() {
        let codes = rejects(
            "func identity[T](x: T) -> T { return x } \
             func main() -> i64 { return identity[i64](42) }",
        );
        assert!(codes.contains(&codes::GENERIC_CODE), "{codes:?}");
    }

    #[test]
    fn a_protocol_call_is_refused() {
        let codes = rejects(
            "
            protocol Equal[T] { func equal(left: T, right: T) -> bool; }
            extend Equal[i64] { func equal(left: i64, right: i64) -> bool { return left == right } }
            func main() -> i64 { if Equal[i64].equal(21, 21) { return 1; } return 0; }
            ",
        );
        assert!(codes.contains(&codes::CAPABILITY_DISPATCH), "{codes:?}");
    }

    #[test]
    fn a_typed_failure_is_refused() {
        let codes = rejects(
            "
            variant Failure { Missing }
            func risky(flag: bool) -> i64 raises Failure {
                if flag { raise Failure.Missing; }
                return 1;
            }
            func main() -> i64 {
                return handle risky(false) {
                    success got => got,
                    failure Failure.Missing => 0,
                };
            }
            ",
        );
        assert!(
            codes.contains(&codes::FALLIBLE_FUNCTION)
                || codes.contains(&codes::UNSUPPORTED_TERMINATOR),
            "{codes:?}"
        );
    }

    // -- arithmetic this backend will not approximate ---------------------

    #[test]
    fn division_remainder_and_shifts_are_refused_by_name() {
        for source in [
            "func main() -> i64 { value a = 9; value b = 2; return a / b; }",
            "func main() -> i64 { value a = 9; value b = 2; return a % b; }",
            "func main() -> i64 { value a = 9; value b = 2; return a << b; }",
            "func main() -> i64 { value a = 9; value b = 2; return a >> b; }",
        ] {
            assert_eq!(
                compile(source).codes(),
                vec![codes::UNSUPPORTED_OPERATOR],
                "{source}"
            );
        }
    }

    // -- the call graph ---------------------------------------------------

    #[test]
    fn self_recursion_is_refused() {
        let codes = rejects(
            "
            func countdown(n: i64) -> i64 {
                if n <= 0 { return 0; }
                return countdown(n - 1);
            }
            func main() -> i64 { return countdown(3); }
            ",
        );
        assert_eq!(codes, vec![codes::RECURSIVE_CALL_GRAPH]);
    }

    #[test]
    fn mutual_recursion_is_refused_once_for_the_whole_cycle() {
        let codes = rejects(
            "
            func even(n: i64) -> bool {
                if n <= 0 { return true; }
                return odd(n - 1);
            }
            func odd(n: i64) -> bool {
                if n <= 0 { return false; }
                return even(n - 1);
            }
            func main() -> i64 { if even(4) { return 1; } return 0; }
            ",
        );
        assert_eq!(
            codes,
            vec![codes::RECURSIVE_CALL_GRAPH],
            "one cycle, one diagnostic"
        );
    }

    // -- module and target ------------------------------------------------

    #[test]
    fn an_import_is_refused_even_though_single_file_compilation_ignores_it() {
        let compiled = compile("import models.user.User;\nfunc main() -> i64 { return 1; }");
        let codes: Vec<&str> = match compiled.validate_for(TARGET_TRIPLE, &[Span::new(0, 24)]) {
            Ok(_) => Vec::new(),
            Err(diagnostics) => diagnostics.iter().map(|d| d.code).collect(),
        };
        assert_eq!(codes, vec![codes::MULTI_MODULE_BUILD]);
    }

    #[test]
    fn another_target_triple_is_refused_before_anything_else_is_examined() {
        let compiled = compile("func main() -> i64 { return 1; }");
        let diagnostics = compiled
            .validate_for("aarch64-apple-darwin", &[])
            .expect_err("only one triple is supported");
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, codes::UNSUPPORTED_TARGET);
    }

    // -- determinism -------------------------------------------------------

    #[test]
    fn the_same_program_is_refused_with_byte_identical_output_every_time() {
        let source = "
            resource File { descriptor: i64 }
            func open(descriptor: i64) -> File { return File { descriptor: descriptor }; }
            func inspect(file: File) -> i64 { return file.descriptor; }
            func main() -> i64 {
                value file = open(3);
                value result = inspect(file);
                drop file;
                return result;
            }
        ";
        let first = compile(source).rendered();
        let second = compile(source).rendered();
        assert!(!first.is_empty());
        assert_eq!(first, second);
    }
}

#[cfg(test)]
mod hand_built_tests {
    use super::*;
    use crate::nir::{Param, verify_module};
    use crate::source::SourceMap;
    use crate::symbol::Symbol;

    fn value(result: u32, ty: Ty, kind: ValueKind) -> Instruction {
        Instruction::Value {
            result: ValueId(result),
            ty,
            kind,
        }
    }

    fn int(result: u32, literal: u128) -> Instruction {
        value(result, Ty::I64, ValueKind::Const(Const::Int(literal)))
    }

    fn boolean(result: u32, literal: bool) -> Instruction {
        value(result, Ty::Bool, ValueKind::Const(Const::Bool(literal)))
    }

    fn block(id: u32, instructions: Vec<Instruction>, terminator: Terminator) -> BasicBlock {
        BasicBlock {
            id: BlockId(id),
            instructions,
            terminator,
        }
    }

    fn func(
        id: u32,
        name: Symbol,
        params: Vec<Ty>,
        return_type: Ty,
        blocks: Vec<BasicBlock>,
    ) -> Function {
        Function {
            id: ItemId(id),
            name,
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: params
                .into_iter()
                .enumerate()
                .map(|(index, ty)| Param {
                    value: ValueId(index as u32),
                    ty,
                    take: false,
                })
                .collect(),
            return_type,
            raises: Vec::new(),
            blocks,
        }
    }

    fn module(functions: Vec<Function>) -> Module {
        Module {
            functions,
            ..Module::default()
        }
    }

    /// Validates hand-built NIR the way a caller who skipped the
    /// verifier would: nothing here has a registry entry, so every
    /// diagnostic has to identify itself by NIR identity alone.
    fn codes_of(module: &Module, interner: &Interner) -> Vec<&'static str> {
        let mut map = SourceMap::new();
        let source = map.add_file("hand-built.npt", "\n");
        match validate(
            module,
            source,
            interner,
            &ItemRegistry::default(),
            TARGET_TRIPLE,
            &[],
        ) {
            Ok(_) => Vec::new(),
            Err(diagnostics) => diagnostics.iter().map(|d| d.code).collect(),
        }
    }

    /// What `nir::verify` makes of the same module. Used to prove which
    /// layer owns a given defect: malformed NIR must be rejected here,
    /// before the native backend is ever consulted.
    fn verifier_codes(module: &Module, interner: &Interner) -> Vec<&'static str> {
        let mut map = SourceMap::new();
        let source = map.add_file("hand-built.npt", "\n");
        verify_module(module, source, interner, &ItemRegistry::default())
            .iter()
            .map(|d| d.code)
            .collect()
    }

    /// `func main() -> i64 { return <literal> }`, the smallest thing the
    /// native subset accepts, as a starting point to perturb.
    fn minimal_main(interner: &mut Interner) -> Function {
        let main = interner.intern("main");
        func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![int(0, 1)],
                Terminator::Return(Some(ValueId(0))),
            )],
        )
    }

    #[test]
    fn the_smallest_accepted_module_is_accepted_by_both_layers() {
        let mut interner = Interner::new();
        let built = module(vec![minimal_main(&mut interner)]);
        assert!(verifier_codes(&built, &interner).is_empty());
        assert!(codes_of(&built, &interner).is_empty());
    }

    // -- entry contract, unreachable from ordinary source -----------------

    #[test]
    fn a_main_declaring_parameters_is_refused() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let built = module(vec![func(
            0,
            main,
            vec![Ty::I64],
            Ty::I64,
            vec![block(0, Vec::new(), Terminator::Return(Some(ValueId(0))))],
        )]);
        assert_eq!(codes_of(&built, &interner), vec![codes::ENTRY_PARAMETERS]);
    }

    #[test]
    fn two_functions_named_main_are_refused_once() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let first = func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![int(0, 1)],
                Terminator::Return(Some(ValueId(0))),
            )],
        );
        let second = func(
            1,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![int(0, 2)],
                Terminator::Return(Some(ValueId(0))),
            )],
        );
        let built = module(vec![first, second]);
        assert_eq!(codes_of(&built, &interner), vec![codes::DUPLICATE_ENTRY]);
    }

    #[test]
    fn a_take_parameter_is_refused_as_an_ownership_transfer() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let helper = interner.intern("helper");
        let mut callee = func(
            1,
            helper,
            vec![Ty::I64],
            Ty::I64,
            vec![block(0, Vec::new(), Terminator::Return(Some(ValueId(0))))],
        );
        if let Some(param) = callee.params.first_mut() {
            param.take = true;
        }
        let caller = func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![
                    int(0, 1),
                    value(
                        1,
                        Ty::I64,
                        ValueKind::Call(ItemId(1), Vec::new(), vec![ValueId(0)], Vec::new()),
                    ),
                ],
                Terminator::Return(Some(ValueId(1))),
            )],
        );
        let built = module(vec![caller, callee]);
        assert_eq!(
            codes_of(&built, &interner),
            vec![codes::UNSUPPORTED_INSTRUCTION]
        );
    }

    // -- the direct-call contract -----------------------------------------

    #[test]
    fn a_call_to_a_function_this_module_does_not_define_is_refused() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![value(
                    0,
                    Ty::I64,
                    ValueKind::Call(ItemId(99), Vec::new(), Vec::new(), Vec::new()),
                )],
                Terminator::Return(Some(ValueId(0))),
            )],
        )]);
        assert_eq!(codes_of(&built, &interner), vec![codes::UNKNOWN_CALLEE]);
        assert!(
            !verifier_codes(&built, &interner).is_empty(),
            "the verifier owns this too, and runs first"
        );
    }

    #[test]
    fn a_call_passing_the_wrong_number_of_arguments_is_refused() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let helper = interner.intern("helper");
        let callee = func(
            1,
            helper,
            vec![Ty::I64],
            Ty::I64,
            vec![block(0, Vec::new(), Terminator::Return(Some(ValueId(0))))],
        );
        let caller = func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![value(
                    0,
                    Ty::I64,
                    ValueKind::Call(ItemId(1), Vec::new(), Vec::new(), Vec::new()),
                )],
                Terminator::Return(Some(ValueId(0))),
            )],
        );
        let built = module(vec![caller, callee]);
        assert_eq!(
            codes_of(&built, &interner),
            vec![codes::CALL_SIGNATURE_MISMATCH]
        );
    }

    #[test]
    fn a_call_passing_an_argument_of_the_wrong_type_is_refused() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let helper = interner.intern("helper");
        let callee = func(
            1,
            helper,
            vec![Ty::I64],
            Ty::I64,
            vec![block(0, Vec::new(), Terminator::Return(Some(ValueId(0))))],
        );
        let caller = func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![
                    boolean(0, true),
                    value(
                        1,
                        Ty::I64,
                        ValueKind::Call(ItemId(1), Vec::new(), vec![ValueId(0)], Vec::new()),
                    ),
                ],
                Terminator::Return(Some(ValueId(1))),
            )],
        );
        let built = module(vec![caller, callee]);
        assert_eq!(
            codes_of(&built, &interner),
            vec![codes::CALL_SIGNATURE_MISMATCH]
        );
    }

    #[test]
    fn a_call_taking_a_result_the_callee_does_not_return_is_refused() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let helper = interner.intern("helper");
        let callee = func(
            1,
            helper,
            Vec::new(),
            Ty::Bool,
            vec![block(
                0,
                vec![boolean(0, true)],
                Terminator::Return(Some(ValueId(0))),
            )],
        );
        let caller = func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![value(
                    0,
                    Ty::I64,
                    ValueKind::Call(ItemId(1), Vec::new(), Vec::new(), Vec::new()),
                )],
                Terminator::Return(Some(ValueId(0))),
            )],
        );
        let built = module(vec![caller, callee]);
        assert_eq!(
            codes_of(&built, &interner),
            vec![codes::CALL_SIGNATURE_MISMATCH]
        );
    }

    // -- malformed NIR belongs to the verifier ----------------------------

    #[test]
    fn a_branch_to_a_block_that_does_not_exist_fails_verification_and_never_reaches_codegen() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(0, Vec::new(), Terminator::Branch(BlockId(7)))],
        )]);
        assert!(
            verifier_codes(&built, &interner).contains(&"V0004"),
            "a dangling target is malformed NIR, and the verifier says so"
        );
        assert_eq!(codes_of(&built, &interner), vec![codes::UNVERIFIED_NIR]);
    }

    #[test]
    fn a_use_of_a_value_nothing_defines_fails_verification_and_never_reaches_codegen() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(0, Vec::new(), Terminator::Return(Some(ValueId(3))))],
        )]);
        assert!(!verifier_codes(&built, &interner).is_empty());
        assert_eq!(codes_of(&built, &interner), vec![codes::UNVERIFIED_NIR]);
    }

    #[test]
    fn a_function_with_no_entry_block_is_refused_without_panicking() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                4,
                vec![int(0, 1)],
                Terminator::Return(Some(ValueId(0))),
            )],
        )]);
        assert_eq!(codes_of(&built, &interner), vec![codes::UNVERIFIED_NIR]);
    }

    // -- slots --------------------------------------------------------------

    #[test]
    fn a_load_with_no_store_on_some_path_is_refused_rather_than_invented() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        // bb0: alloc, branch on a constant into bb1 (stores) or bb2
        // (does not); bb3 loads. One incoming edge never wrote the slot.
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![
                block(
                    0,
                    vec![
                        value(0, Ty::I64, ValueKind::Alloc),
                        boolean(1, true),
                        int(2, 5),
                    ],
                    Terminator::CondBranch {
                        condition: ValueId(1),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                ),
                block(
                    1,
                    vec![Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(2),
                        mode: OwnershipMode::Observe,
                    }],
                    Terminator::Branch(BlockId(3)),
                ),
                block(2, Vec::new(), Terminator::Branch(BlockId(3))),
                block(
                    3,
                    vec![value(3, Ty::I64, ValueKind::Load(ValueId(0)))],
                    Terminator::Return(Some(ValueId(3))),
                ),
            ],
        )]);
        assert_eq!(
            codes_of(&built, &interner),
            vec![codes::UNINITIALIZED_SLOT_LOAD]
        );
    }

    #[test]
    fn a_load_stored_on_every_path_is_accepted() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![
                block(
                    0,
                    vec![
                        value(0, Ty::I64, ValueKind::Alloc),
                        boolean(1, true),
                        int(2, 5),
                    ],
                    Terminator::CondBranch {
                        condition: ValueId(1),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                ),
                block(
                    1,
                    vec![Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(2),
                        mode: OwnershipMode::Observe,
                    }],
                    Terminator::Branch(BlockId(3)),
                ),
                block(
                    2,
                    vec![Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(2),
                        mode: OwnershipMode::Observe,
                    }],
                    Terminator::Branch(BlockId(3)),
                ),
                block(
                    3,
                    vec![value(3, Ty::I64, ValueKind::Load(ValueId(0)))],
                    Terminator::Return(Some(ValueId(3))),
                ),
            ],
        )]);
        assert!(verifier_codes(&built, &interner).is_empty());
        assert!(codes_of(&built, &interner).is_empty());
    }

    #[test]
    fn a_slot_used_as_an_ordinary_value_is_refused() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![
                    value(0, Ty::I64, ValueKind::Alloc),
                    int(1, 3),
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(1),
                        mode: OwnershipMode::Observe,
                    },
                    value(2, Ty::I64, ValueKind::Add(ValueId(0), ValueId(1))),
                ],
                Terminator::Return(Some(ValueId(2))),
            )],
        )]);
        assert_eq!(codes_of(&built, &interner), vec![codes::SLOT_USED_AS_VALUE]);
    }

    #[test]
    fn a_store_that_transfers_ownership_is_refused() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![
                    value(0, Ty::I64, ValueKind::Alloc),
                    int(1, 3),
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(1),
                        mode: OwnershipMode::Transfer,
                    },
                    value(2, Ty::I64, ValueKind::Load(ValueId(0))),
                ],
                Terminator::Return(Some(ValueId(2))),
            )],
        )]);
        assert_eq!(
            codes_of(&built, &interner),
            vec![codes::UNSUPPORTED_INSTRUCTION]
        );
    }

    // -- control-flow shapes ------------------------------------------------

    #[test]
    fn a_diamond_and_a_loop_backedge_are_accepted_by_both_layers() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        // bb0 -> {bb1, bb2} -> bb3 -> (bb3 | bb4), a diamond whose join
        // block loops back on itself before leaving.
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![
                block(
                    0,
                    vec![
                        value(0, Ty::I64, ValueKind::Alloc),
                        int(1, 0),
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(1),
                            mode: OwnershipMode::Observe,
                        },
                        boolean(2, true),
                    ],
                    Terminator::CondBranch {
                        condition: ValueId(2),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                ),
                block(1, Vec::new(), Terminator::Branch(BlockId(3))),
                block(2, Vec::new(), Terminator::Branch(BlockId(3))),
                block(
                    3,
                    vec![
                        value(3, Ty::I64, ValueKind::Load(ValueId(0))),
                        int(4, 4),
                        value(5, Ty::Bool, ValueKind::Lt(ValueId(3), ValueId(4))),
                        value(6, Ty::I64, ValueKind::Add(ValueId(3), ValueId(4))),
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(6),
                            mode: OwnershipMode::Observe,
                        },
                    ],
                    Terminator::CondBranch {
                        condition: ValueId(5),
                        then_block: BlockId(3),
                        else_block: BlockId(4),
                    },
                ),
                block(
                    4,
                    vec![value(7, Ty::I64, ValueKind::Load(ValueId(0)))],
                    Terminator::Return(Some(ValueId(7))),
                ),
            ],
        )]);
        assert!(
            verifier_codes(&built, &interner).is_empty(),
            "{:?}",
            verifier_codes(&built, &interner)
        );
        assert!(codes_of(&built, &interner).is_empty());
    }

    /// An unsupported instruction nothing can execute is dead code, not
    /// an error -- and, crucially, the value it defines never enters the
    /// map reachable code generation reads.
    #[test]
    fn an_unsupported_instruction_in_an_unreachable_block_is_ignored() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![
                block(0, vec![int(0, 1)], Terminator::Return(Some(ValueId(0)))),
                block(
                    1,
                    vec![value(
                        1,
                        Ty::Str,
                        ValueKind::Const(Const::Str("unreachable".to_string())),
                    )],
                    Terminator::Return(Some(ValueId(1))),
                ),
            ],
        )]);
        assert!(codes_of(&built, &interner).is_empty());
    }

    /// Two unreachable blocks that only reach each other: the fixpoint
    /// must not be entered for them at all, and must not spin.
    #[test]
    fn an_unreachable_cycle_neither_fails_nor_hangs() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![
                block(
                    0,
                    vec![
                        value(0, Ty::I64, ValueKind::Alloc),
                        int(1, 1),
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(1),
                            mode: OwnershipMode::Observe,
                        },
                        value(2, Ty::I64, ValueKind::Load(ValueId(0))),
                    ],
                    Terminator::Return(Some(ValueId(2))),
                ),
                block(1, Vec::new(), Terminator::Branch(BlockId(2))),
                block(2, Vec::new(), Terminator::Branch(BlockId(1))),
            ],
        )]);
        assert!(codes_of(&built, &interner).is_empty());
    }

    /// A deep chain of blocks, all reachable, each carrying a slot
    /// store: nothing here recurses on the native stack, so depth is
    /// just work, never a crash.
    #[test]
    fn a_deep_scalar_control_flow_graph_neither_overflows_nor_hangs() {
        const DEPTH: u32 = 400;
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let mut blocks = vec![block(
            0,
            vec![
                value(0, Ty::I64, ValueKind::Alloc),
                int(1, 0),
                Instruction::Store {
                    slot: ValueId(0),
                    value: ValueId(1),
                    mode: OwnershipMode::Observe,
                },
            ],
            Terminator::Branch(BlockId(1)),
        )];
        for index in 1..DEPTH {
            blocks.push(block(
                index,
                vec![value(index + 1, Ty::I64, ValueKind::Load(ValueId(0)))],
                Terminator::Branch(BlockId(index + 1)),
            ));
        }
        blocks.push(block(
            DEPTH,
            vec![value(DEPTH + 1, Ty::I64, ValueKind::Load(ValueId(0)))],
            Terminator::Return(Some(ValueId(DEPTH + 1))),
        ));
        let built = module(vec![func(0, main, Vec::new(), Ty::I64, blocks)]);
        assert!(codes_of(&built, &interner).is_empty());
    }

    /// A long, strictly acyclic call chain: the component search is
    /// iterative, so chain length costs time and nothing else.
    #[test]
    fn a_deep_acyclic_call_chain_is_accepted_without_overflowing() {
        const LENGTH: u32 = 300;
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let step = interner.intern("step");
        let mut functions = vec![func(
            0,
            main,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![value(
                    0,
                    Ty::I64,
                    ValueKind::Call(ItemId(1), Vec::new(), Vec::new(), Vec::new()),
                )],
                Terminator::Return(Some(ValueId(0))),
            )],
        )];
        for index in 1..LENGTH {
            functions.push(func(
                index,
                step,
                Vec::new(),
                Ty::I64,
                vec![block(
                    0,
                    vec![value(
                        0,
                        Ty::I64,
                        ValueKind::Call(ItemId(index + 1), Vec::new(), Vec::new(), Vec::new()),
                    )],
                    Terminator::Return(Some(ValueId(0))),
                )],
            ));
        }
        functions.push(func(
            LENGTH,
            step,
            Vec::new(),
            Ty::I64,
            vec![block(
                0,
                vec![int(0, 1)],
                Terminator::Return(Some(ValueId(0))),
            )],
        ));
        let built = module(functions);
        assert!(codes_of(&built, &interner).is_empty());
    }

    /// Two independent cycles produce exactly two diagnostics, each at
    /// its own cycle's smallest id, in ascending order -- never one per
    /// edge and never one per member.
    #[test]
    fn each_recursion_cycle_is_reported_once_at_its_canonical_root() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let name = interner.intern("f");
        let call = |target: u32| {
            block(
                0,
                vec![value(
                    0,
                    Ty::I64,
                    ValueKind::Call(ItemId(target), Vec::new(), Vec::new(), Vec::new()),
                )],
                Terminator::Return(Some(ValueId(0))),
            )
        };
        let two_calls = |first: u32, second: u32| {
            block(
                0,
                vec![
                    value(
                        0,
                        Ty::I64,
                        ValueKind::Call(ItemId(first), Vec::new(), Vec::new(), Vec::new()),
                    ),
                    value(
                        1,
                        Ty::I64,
                        ValueKind::Call(ItemId(second), Vec::new(), Vec::new(), Vec::new()),
                    ),
                    value(2, Ty::I64, ValueKind::Add(ValueId(0), ValueId(1))),
                ],
                Terminator::Return(Some(ValueId(2))),
            )
        };
        let functions = vec![
            // `main` reaches a self-recursive `f1` and a mutually
            // recursive `f2`/`f3`.
            func(0, main, Vec::new(), Ty::I64, vec![two_calls(1, 2)]),
            func(1, name, Vec::new(), Ty::I64, vec![call(1)]),
            func(2, name, Vec::new(), Ty::I64, vec![call(3)]),
            func(3, name, Vec::new(), Ty::I64, vec![call(2)]),
        ];
        let built = module(functions);
        assert_eq!(
            codes_of(&built, &interner),
            vec![codes::RECURSIVE_CALL_GRAPH, codes::RECURSIVE_CALL_GRAPH]
        );

        // The same graph, stored backwards, reports the same two cycles
        // in the same order.
        let mut reversed = built;
        reversed.functions.reverse();
        assert_eq!(
            codes_of(&reversed, &interner),
            vec![codes::RECURSIVE_CALL_GRAPH, codes::RECURSIVE_CALL_GRAPH]
        );
    }

    /// A cycle only reachable through a function `main` never calls is
    /// not this build's problem: it is never compiled.
    #[test]
    fn a_recursion_cycle_outside_the_reachable_graph_is_ignored() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let name = interner.intern("f");
        let built = module(vec![
            func(
                0,
                main,
                Vec::new(),
                Ty::I64,
                vec![block(
                    0,
                    vec![int(0, 1)],
                    Terminator::Return(Some(ValueId(0))),
                )],
            ),
            func(
                1,
                name,
                Vec::new(),
                Ty::I64,
                vec![block(
                    0,
                    vec![value(
                        0,
                        Ty::I64,
                        ValueKind::Call(ItemId(1), Vec::new(), Vec::new(), Vec::new()),
                    )],
                    Terminator::Return(Some(ValueId(0))),
                )],
            ),
        ]);
        assert!(codes_of(&built, &interner).is_empty());
    }

    #[test]
    fn hand_built_refusals_are_byte_identical_across_repeated_runs() {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let built = module(vec![func(
            0,
            main,
            Vec::new(),
            Ty::Str,
            vec![block(
                0,
                vec![value(
                    0,
                    Ty::Str,
                    ValueKind::Const(Const::Str("nope".to_string())),
                )],
                Terminator::Return(Some(ValueId(0))),
            )],
        )]);
        let render = || {
            let mut map = SourceMap::new();
            let source = map.add_file("hand-built.npt", "\n");
            match validate(
                &built,
                source,
                &interner,
                &ItemRegistry::default(),
                TARGET_TRIPLE,
                &[],
            ) {
                Ok(_) => String::new(),
                Err(diagnostics) => diagnostics
                    .iter()
                    .map(|d| crate::diagnostics::render(d, &map))
                    .collect::<String>(),
            }
        };
        let first = render();
        assert!(first.contains(codes::ENTRY_RETURN_TYPE));
        assert_eq!(first, render());
    }

    // -- unsupported terminators ------------------------------------------
    //
    // None of these three is reachable from ordinary source: a program
    // that could produce one always carries a variant or a fallible
    // signature too, and the type or the signature is refused first, as
    // the root cause it is. Hand-built NIR is the only way to put the
    // terminator itself under test.

    fn refused_terminator(terminator: Terminator, extra: Vec<BasicBlock>) -> Vec<&'static str> {
        let mut interner = Interner::new();
        let main = interner.intern("main");
        let mut blocks = vec![block(0, vec![int(0, 1)], terminator)];
        blocks.extend(extra);
        let built = module(vec![func(0, main, Vec::new(), Ty::I64, blocks)]);
        codes_of(&built, &interner)
    }

    #[test]
    fn a_switch_is_refused() {
        let codes = refused_terminator(
            Terminator::Switch {
                scrutinee: ValueId(0),
                variant: ItemId(9),
                cases: vec![BlockId(1)],
            },
            vec![block(1, Vec::new(), Terminator::Return(Some(ValueId(0))))],
        );
        assert_eq!(codes, vec![codes::UNSUPPORTED_TERMINATOR]);
    }

    #[test]
    fn an_invoke_is_refused() {
        let codes = refused_terminator(
            Terminator::Invoke {
                callee: ItemId(9),
                type_args: Vec::new(),
                args: Vec::new(),
                evidence: Vec::new(),
                ok_slot: ValueId(5),
                ok_target: BlockId(1),
                err_targets: vec![crate::nir::InvokeErrTarget {
                    variant: ItemId(8),
                    slot: ValueId(6),
                    target: BlockId(2),
                }],
            },
            vec![
                block(1, Vec::new(), Terminator::Return(Some(ValueId(0)))),
                block(2, Vec::new(), Terminator::Return(Some(ValueId(0)))),
            ],
        );
        assert_eq!(codes, vec![codes::UNSUPPORTED_TERMINATOR]);
    }

    #[test]
    fn a_raise_is_refused() {
        let codes = refused_terminator(Terminator::Raise { value: ValueId(0) }, Vec::new());
        assert_eq!(codes, vec![codes::UNSUPPORTED_TERMINATOR]);
    }
}
