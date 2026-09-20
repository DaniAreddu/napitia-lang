//! Cranelift lowering for the validated native subset.
//!
//! Everything here may assume [`super::capability`] already ran and
//! accepted the program, which is why this module has no "unsupported,
//! give up" path threaded through code generation. What it does have is
//! a refusal for its own defects: a Cranelift error, or an NIR shape
//! validation should have excluded, becomes a
//! [`super::codes::CODEGEN_FAILED`] diagnostic
//! rather than a panic.
//!
//! # Determinism
//!
//! The same program produces byte-identical object output on the same
//! toolchain, and nothing in here can quietly stop being true of that:
//!
//! * functions are declared, and then defined, in ascending [`ItemId`]
//!   order -- never in the order `Module::functions` happens to store
//!   them;
//! * blocks are created and filled in reverse postorder of a traversal
//!   that visits successors in ascending [`BlockId`] order, so a
//!   function's block *storage* order is irrelevant too;
//! * every map keyed by a NIR identity is a `BTreeMap`, so nothing is
//!   ever iterated in hash order;
//! * symbol names come from an item's own id and declared name, not
//!   from a counter, an address, or a position in a vector.
//!
//! # Representation
//!
//! [`super::Scalar`] records the machine type each Napitia scalar is
//! held in; this module is where those choices are spent. `unit` is
//! represented by no
//! value at all: a `unit` parameter is absent from a native signature,
//! a `unit` result makes the signature return nothing, and a `unit`
//! slot holds no variable. Nothing fabricates a placeholder for it.
//!
//! # The entry wrapper
//!
//! Napitia's own `main` is compiled like any other function, under its
//! own mangled symbol. A separate exported `main` -- the one the C
//! runtime calls -- wraps it, and is the only symbol here that is a
//! documented interface.

use std::collections::{BTreeMap, BTreeSet};
use std::str::FromStr;

use cranelift_codegen::Context;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{AbiParam, Block, InstBuilder, Signature, Value, types};
use cranelift_codegen::isa;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{FuncId, Linkage, Module as _};
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::hir::ItemId;
use crate::nir::{
    BasicBlock, BlockId, Const, Function, Instruction, Module, Terminator, ValueId, ValueKind,
};
use crate::symbol::Interner;

use super::capability::NativePlan;
use super::{ENTRY_SYMBOL, Scalar, scalar_of};

/// The object's own module name. Constant, because it is written into
/// the emitted file and a build must not depend on where it ran.
const OBJECT_NAME: &str = "napitia";

/// A native value, or the deliberate absence of one.
#[derive(Copy, Clone, Debug)]
enum Native {
    /// An `i64`, held in an `I64` (`rfcs/0015`).
    Int(Value),
    /// A `bool`, held in an `I8` that is always `0` or `1`.
    Bool(Value),
    /// A `unit`. One inhabitant, so no bits, no register, no value.
    Unit,
    /// An `alloc` slot. `unit` slots hold no variable, because there is
    /// nothing for them to hold.
    Slot {
        variable: Option<Variable>,
        scalar: Scalar,
    },
}

/// Compiles `plan`'s functions into one ELF object for `target`.
///
/// Returns the object's bytes, or the single reason this backend could
/// not produce them.
pub(super) fn emit_object(
    module: &Module,
    interner: &Interner,
    plan: &NativePlan,
    target: &str,
) -> Result<Vec<u8>, String> {
    let mut flags = settings::builder();
    // A preview compiles for correctness, not speed: the unoptimized
    // output is the one that most obviously corresponds to the NIR it
    // came from, which is what makes a differential test against the
    // interpreter meaningful.
    set_flag(&mut flags, "opt_level", "none")?;
    set_flag(&mut flags, "is_pic", "true")?;

    // Parsed here rather than through `isa::lookup_by_name`, which
    // panics on a triple it cannot parse.
    let triple = target_lexicon::Triple::from_str(target)
        .map_err(|error| format!("`{target}` is not a target triple: {error}"))?;
    let isa = isa::lookup(triple)
        .map_err(|error| format!("no Cranelift backend for `{target}`: {error}"))?
        .finish(settings::Flags::new(flags))
        .map_err(|error| format!("could not configure the `{target}` backend: {error}"))?;
    let frontend_config = isa.frontend_config();
    let builder = ObjectBuilder::new(isa, OBJECT_NAME, cranelift_module::default_libcall_names())
        .map_err(|error| format!("could not start an object for `{target}`: {error}"))?;
    let mut object = ObjectModule::new(builder);

    let functions = index_functions(module, plan);

    // Every function is declared before any body is emitted, so a call
    // never has to care whether its callee has been compiled yet.
    let mut declared: BTreeMap<ItemId, FuncId> = BTreeMap::new();
    for id in plan.functions() {
        let function = lookup(&functions, *id)?;
        let signature = native_signature(&mut object, function)?;
        let symbol = symbol_name(*id, interner.resolve(function.name));
        let func_id = object
            .declare_function(&symbol, Linkage::Local, &signature)
            .map_err(|error| format!("could not declare `{symbol}`: {error}"))?;
        declared.insert(*id, func_id);
    }

    let mut context = object.make_context();
    let mut frontend = FunctionBuilderContext::new();
    for id in plan.functions() {
        let function = lookup(&functions, *id)?;
        let reachable = plan
            .reachable_blocks(*id)
            .ok_or_else(|| format!("no block plan for function id {}", id.0))?;
        context.func.signature = native_signature(&mut object, function)?;
        define_body(
            &mut object,
            &mut context,
            &mut frontend,
            frontend_config,
            &declared,
            &functions,
            function,
            reachable,
        )?;
        let func_id = declared
            .get(id)
            .copied()
            .ok_or_else(|| format!("function id {} was never declared", id.0))?;
        object
            .define_function(func_id, &mut context)
            .map_err(|error| format!("Cranelift rejected function id {}: {error}", id.0))?;
        object.clear_context(&mut context);
    }

    define_entry_wrapper(
        &mut object,
        &mut context,
        &mut frontend,
        frontend_config,
        &declared,
        plan,
    )?;

    object
        .finish()
        .emit()
        .map_err(|error| format!("could not write the object file: {error}"))
}

fn set_flag(flags: &mut settings::Builder, name: &str, value: &str) -> Result<(), String> {
    flags
        .set(name, value)
        .map_err(|error| format!("could not set the Cranelift flag `{name}`: {error}"))
}

/// The symbol one Napitia function is emitted under.
///
/// Built from the item's own id -- globally unique across the module by
/// construction -- plus its declared name, kept readable for anyone
/// reading a disassembly. Sanitizing the name cannot introduce a
/// collision, because the id alone already separates every function.
/// None of these names is a documented interface; only
/// [`ENTRY_SYMBOL`] is.
pub(super) fn symbol_name(id: ItemId, declared: &str) -> String {
    let mut sanitized = String::with_capacity(declared.len());
    for character in declared.chars() {
        if character.is_ascii_alphanumeric() || character == '_' {
            sanitized.push(character);
        } else {
            sanitized.push('_');
        }
    }
    format!("napitia_{}_{}", id.0, sanitized)
}

fn index_functions<'a>(module: &'a Module, plan: &NativePlan) -> BTreeMap<ItemId, &'a Function> {
    let wanted: BTreeSet<ItemId> = plan.functions().iter().copied().collect();
    let mut functions: BTreeMap<ItemId, &Function> = BTreeMap::new();
    for function in &module.functions {
        if wanted.contains(&function.id) {
            functions.insert(function.id, function);
        }
    }
    functions
}

fn lookup<'a>(
    functions: &BTreeMap<ItemId, &'a Function>,
    id: ItemId,
) -> Result<&'a Function, String> {
    functions.get(&id).copied().ok_or_else(|| {
        format!(
            "the plan names function id {}, which the module does not",
            id.0
        )
    })
}

/// The Cranelift type one scalar is held in, or `None` for `unit`,
/// which occupies no ABI position at all.
fn abi_type(scalar: Scalar) -> Option<types::Type> {
    match scalar {
        Scalar::Int => Some(types::I64),
        Scalar::Bool => Some(types::I8),
        Scalar::Unit => None,
    }
}

fn scalar_of_checked(ty: &crate::types::Ty) -> Result<Scalar, String> {
    scalar_of(ty).ok_or_else(|| {
        "capability validation accepted a type the backend cannot represent".to_string()
    })
}

fn native_signature(object: &mut ObjectModule, function: &Function) -> Result<Signature, String> {
    let mut signature = object.make_signature();
    for param in &function.params {
        if let Some(ty) = abi_type(scalar_of_checked(&param.ty)?) {
            signature.params.push(AbiParam::new(ty));
        }
    }
    if let Some(ty) = abi_type(scalar_of_checked(&function.return_type)?) {
        signature.returns.push(AbiParam::new(ty));
    }
    Ok(signature)
}

/// Reverse postorder over `reachable`, visiting successors in ascending
/// block order.
///
/// Emission order matters for more than tidiness: a value defined in
/// one block and used in another is only available once its defining
/// block has been built, and reverse postorder puts every dominator
/// before the blocks it dominates. Ascending block *number* would not:
/// nothing requires NIR to number its blocks in dominator order.
fn reverse_postorder(
    blocks: &BTreeMap<BlockId, &BasicBlock>,
    reachable: &[BlockId],
) -> Result<Vec<BlockId>, String> {
    let live: BTreeSet<BlockId> = reachable.iter().copied().collect();
    let mut postorder: Vec<BlockId> = Vec::new();
    let mut visited: BTreeSet<BlockId> = BTreeSet::new();
    // (block, index of the next successor to descend into)
    let mut work: Vec<(BlockId, usize)> = Vec::new();

    if live.contains(&BlockId(0)) {
        work.push((BlockId(0), 0));
        visited.insert(BlockId(0));
    }
    while let Some((id, next)) = work.pop() {
        // A block the plan calls reachable that the function does not
        // declare is an inconsistency between validation and lowering,
        // not a block with no successors. Reported, never defaulted.
        let Some(block) = blocks.get(&id) else {
            return Err(format!(
                "bb{} is in the plan but the function does not declare it",
                id.0
            ));
        };
        let successors: Vec<BlockId> = {
            let mut targets: Vec<BlockId> = successors_of(&block.terminator)
                .into_iter()
                .filter(|target| live.contains(target))
                .collect();
            targets.sort_unstable();
            targets.dedup();
            targets
        };
        let mut descended = false;
        for position in next..successors.len() {
            let Some(successor) = successors.get(position).copied() else {
                continue;
            };
            if visited.insert(successor) {
                work.push((id, position + 1));
                work.push((successor, 0));
                descended = true;
                break;
            }
        }
        if !descended {
            postorder.push(id);
        }
    }
    postorder.reverse();
    Ok(postorder)
}

fn successors_of(terminator: &Terminator) -> Vec<BlockId> {
    match terminator {
        Terminator::Branch(target) => vec![*target],
        Terminator::CondBranch {
            then_block,
            else_block,
            ..
        } => vec![*then_block, *else_block],
        // Validation has already refused every other terminator in a
        // reachable block, so nothing else can contribute an edge here.
        Terminator::Return(_)
        | Terminator::Switch { .. }
        | Terminator::Invoke { .. }
        | Terminator::Raise { .. } => Vec::new(),
    }
}

#[allow(clippy::too_many_arguments)]
fn define_body(
    object: &mut ObjectModule,
    context: &mut Context,
    frontend: &mut FunctionBuilderContext,
    frontend_config: isa::TargetFrontendConfig,
    declared: &BTreeMap<ItemId, FuncId>,
    functions: &BTreeMap<ItemId, &Function>,
    function: &Function,
    reachable: &[BlockId],
) -> Result<(), String> {
    let mut blocks: BTreeMap<BlockId, &BasicBlock> = BTreeMap::new();
    for block in &function.blocks {
        blocks.entry(block.id).or_insert(block);
    }
    let order = reverse_postorder(&blocks, reachable)?;

    let mut builder = FunctionBuilder::new(&mut context.func, frontend);

    // A dedicated Cranelift entry block, rather than reusing the one
    // for NIR's `bb0`: Cranelift's entry block may have no
    // predecessors, and a loop whose header *is* `bb0` would give it
    // one. The extra jump costs nothing and keeps every NIR block shape
    // legal.
    let prologue = builder.create_block();
    builder.append_block_params_for_function_params(prologue);

    let mut cranelift_blocks: BTreeMap<BlockId, Block> = BTreeMap::new();
    for id in &order {
        cranelift_blocks.insert(*id, builder.create_block());
    }

    let mut lowerer = BodyLowerer {
        builder,
        object,
        declared,
        functions,
        values: BTreeMap::new(),
        blocks: cranelift_blocks,
    };

    lowerer.bind_parameters(function, prologue)?;
    let entry = lowerer.block(BlockId(0))?;
    lowerer.builder.ins().jump(entry, &[]);

    for id in &order {
        let block = blocks
            .get(id)
            .copied()
            .ok_or_else(|| format!("bb{} vanished between planning and lowering", id.0))?;
        let cranelift_block = lowerer.block(*id)?;
        lowerer.builder.switch_to_block(cranelift_block);
        for instruction in &block.instructions {
            lowerer.instruction(instruction)?;
        }
        lowerer.terminator(&block.terminator)?;
    }

    lowerer.builder.seal_all_blocks();
    lowerer.builder.finalize(frontend_config);
    Ok(())
}

struct BodyLowerer<'a, 'f> {
    builder: FunctionBuilder<'f>,
    object: &'a mut ObjectModule,
    declared: &'a BTreeMap<ItemId, FuncId>,
    functions: &'a BTreeMap<ItemId, &'a Function>,
    values: BTreeMap<ValueId, Native>,
    blocks: BTreeMap<BlockId, Block>,
}

impl BodyLowerer<'_, '_> {
    fn block(&self, id: BlockId) -> Result<Block, String> {
        self.blocks
            .get(&id)
            .copied()
            .ok_or_else(|| format!("bb{} was never created", id.0))
    }

    fn value(&self, id: ValueId) -> Result<Native, String> {
        self.values
            .get(&id)
            .copied()
            .ok_or_else(|| format!("%{} was used before it was lowered", id.0))
    }

    fn integer(&self, id: ValueId) -> Result<Value, String> {
        match self.value(id)? {
            Native::Int(value) => Ok(value),
            _ => Err(format!("%{} is not an `i64`", id.0)),
        }
    }

    fn boolean(&self, id: ValueId) -> Result<Value, String> {
        match self.value(id)? {
            Native::Bool(value) => Ok(value),
            _ => Err(format!("%{} is not a `bool`", id.0)),
        }
    }

    /// Binds each declared parameter to its ABI position, skipping
    /// `unit` parameters, which occupy none.
    fn bind_parameters(&mut self, function: &Function, prologue: Block) -> Result<(), String> {
        self.builder.switch_to_block(prologue);
        let mut position = 0usize;
        for param in &function.params {
            let scalar = scalar_of_checked(&param.ty)?;
            let native = match abi_type(scalar) {
                None => Native::Unit,
                Some(_) => {
                    let value = self
                        .builder
                        .block_params(prologue)
                        .get(position)
                        .copied()
                        .ok_or_else(|| {
                            format!("parameter {position} is missing from the native signature")
                        })?;
                    position += 1;
                    self.wrap(scalar, value)?
                }
            };
            self.values.insert(param.value, native);
        }
        Ok(())
    }

    fn wrap(&self, scalar: Scalar, value: Value) -> Result<Native, String> {
        match scalar {
            Scalar::Int => Ok(Native::Int(value)),
            Scalar::Bool => Ok(Native::Bool(value)),
            Scalar::Unit => Err("`unit` has no runtime value to wrap".to_string()),
        }
    }

    fn int_const(&mut self, bits: i64) -> Value {
        self.builder.ins().iconst(types::I64, bits)
    }

    fn bool_const(&mut self, literal: bool) -> Value {
        self.builder.ins().iconst(types::I8, i64::from(literal))
    }

    fn instruction(&mut self, instruction: &Instruction) -> Result<(), String> {
        match instruction {
            Instruction::Value { result, ty, kind } => {
                let scalar = scalar_of_checked(ty)?;
                let native = self.value_kind(*result, scalar, kind)?;
                self.values.insert(*result, native);
                Ok(())
            }
            Instruction::Store { slot, value, .. } => {
                let target = self.value(*slot)?;
                let Native::Slot { variable, scalar } = target else {
                    return Err(format!("%{} is not a slot", slot.0));
                };
                // Matched against the *slot's own* scalar rather than
                // just "some variable, some value": `def_var` panics on
                // a type mismatch, and this backend answers a mismatch
                // with a diagnostic. Capability validation already
                // excludes one, so this only ever guards a caller who
                // reached this function another way.
                match (variable, scalar, self.value(*value)?) {
                    // A `unit` slot holds nothing, so storing into it is
                    // a complete no-op rather than a zero written
                    // somewhere.
                    (None, Scalar::Unit, Native::Unit) => Ok(()),
                    (Some(variable), Scalar::Int, Native::Int(value))
                    | (Some(variable), Scalar::Bool, Native::Bool(value)) => {
                        self.builder.def_var(variable, value);
                        Ok(())
                    }
                    _ => Err(format!("%{} cannot hold %{}", slot.0, value.0)),
                }
            }
            // Validation refuses every one of these in a reachable
            // block, so reaching one here is a defect in this backend,
            // not in the program.
            Instruction::Drop { .. }
            | Instruction::DecomposeVariant { .. }
            | Instruction::StorePlace { .. }
            | Instruction::EndObserve { .. } => {
                Err("capability validation let an unsupported instruction through".to_string())
            }
        }
    }

    fn value_kind(
        &mut self,
        result: ValueId,
        scalar: Scalar,
        kind: &ValueKind,
    ) -> Result<Native, String> {
        match kind {
            ValueKind::Alloc => {
                let variable = match abi_type(scalar) {
                    Some(ty) => Some(self.builder.declare_var(ty)),
                    None => None,
                };
                Ok(Native::Slot { variable, scalar })
            }
            ValueKind::Const(constant) => match constant {
                // Narrowed through a checked conversion, exactly as the
                // interpreter narrows the same constant. `nir::verify`
                // has already rejected one outside `i64`, so this only
                // ever guards a caller that reached code generation
                // another way.
                Const::Int(literal) => {
                    let bits = i64::try_from(*literal).map_err(|_| {
                        format!("the constant {literal} is not an i64; verification must reject it before code generation")
                    })?;
                    Ok(Native::Int(self.int_const(bits)))
                }
                Const::Bool(literal) => Ok(Native::Bool(self.bool_const(*literal))),
                Const::Unit => Ok(Native::Unit),
                Const::Float(_) | Const::Char(_) | Const::Str(_) => {
                    Err("capability validation let an unsupported constant through".to_string())
                }
            },
            ValueKind::Load(slot) => {
                let Native::Slot { variable, scalar } = self.value(*slot)? else {
                    return Err(format!("%{} is not a slot", slot.0));
                };
                match variable {
                    None => Ok(Native::Unit),
                    Some(variable) => {
                        let value = self.builder.use_var(variable);
                        self.wrap(scalar, value)
                    }
                }
            }
            ValueKind::Add(a, b) => {
                self.arithmetic(*a, *b, |builder, x, y| builder.ins().iadd(x, y))
            }
            ValueKind::Sub(a, b) => {
                self.arithmetic(*a, *b, |builder, x, y| builder.ins().isub(x, y))
            }
            ValueKind::Mul(a, b) => {
                self.arithmetic(*a, *b, |builder, x, y| builder.ins().imul(x, y))
            }
            ValueKind::And(a, b) => {
                self.arithmetic(*a, *b, |builder, x, y| builder.ins().band(x, y))
            }
            ValueKind::Or(a, b) => self.arithmetic(*a, *b, |builder, x, y| builder.ins().bor(x, y)),
            ValueKind::Xor(a, b) => {
                self.arithmetic(*a, *b, |builder, x, y| builder.ins().bxor(x, y))
            }
            ValueKind::Neg(a) => {
                let value = self.integer(*a)?;
                Ok(Native::Int(self.builder.ins().ineg(value)))
            }
            ValueKind::Not(a) => match self.value(*a)? {
                Native::Int(value) => Ok(Native::Int(self.builder.ins().bnot(value))),
                // `bxor` against 1 rather than `bnot`: a `bool` is
                // canonically 0 or 1 here, and `bnot` would leave 0xfe.
                Native::Bool(value) => Ok(Native::Bool(self.builder.ins().bxor_imm_u(value, 1))),
                _ => Err(format!("%{} cannot be inverted", a.0)),
            },
            ValueKind::Eq(a, b) => self.compare(*a, *b, IntCC::Equal, true),
            ValueKind::Ne(a, b) => self.compare(*a, *b, IntCC::NotEqual, false),
            ValueKind::Lt(a, b) => {
                self.ordered(*a, *b, IntCC::SignedLessThan, IntCC::UnsignedLessThan)
            }
            ValueKind::Le(a, b) => self.ordered(
                *a,
                *b,
                IntCC::SignedLessThanOrEqual,
                IntCC::UnsignedLessThanOrEqual,
            ),
            ValueKind::Gt(a, b) => {
                self.ordered(*a, *b, IntCC::SignedGreaterThan, IntCC::UnsignedGreaterThan)
            }
            ValueKind::Ge(a, b) => self.ordered(
                *a,
                *b,
                IntCC::SignedGreaterThanOrEqual,
                IntCC::UnsignedGreaterThanOrEqual,
            ),
            ValueKind::Call(callee, _, args, _) => self.call(result, *callee, args),
            ValueKind::Div(_, _)
            | ValueKind::Rem(_, _)
            | ValueKind::Shl(_, _)
            | ValueKind::Shr(_, _)
            | ValueKind::RecordCreate(_, _, _)
            | ValueKind::RecordField { .. }
            | ValueKind::VariantCreate { .. }
            | ValueKind::VariantPayload { .. }
            | ValueKind::ProtocolCall { .. }
            | ValueKind::Move { .. }
            | ValueKind::DeferCapture { .. }
            | ValueKind::PlaceRead { .. }
            | ValueKind::ObservePlace { .. } => {
                Err("capability validation let an unsupported instruction through".to_string())
            }
        }
    }

    fn arithmetic(
        &mut self,
        a: ValueId,
        b: ValueId,
        build: impl Fn(&mut FunctionBuilder<'_>, Value, Value) -> Value,
    ) -> Result<Native, String> {
        let left = self.integer(a)?;
        let right = self.integer(b)?;
        Ok(Native::Int(build(&mut self.builder, left, right)))
    }

    /// Equality, which `unit` also answers -- it has one inhabitant, so
    /// two of them are equal by construction and the answer is a
    /// constant rather than a comparison of invented values.
    fn compare(
        &mut self,
        a: ValueId,
        b: ValueId,
        condition: IntCC,
        unit_answer: bool,
    ) -> Result<Native, String> {
        match (self.value(a)?, self.value(b)?) {
            (Native::Unit, Native::Unit) => Ok(Native::Bool(self.bool_const(unit_answer))),
            (Native::Int(left), Native::Int(right)) | (Native::Bool(left), Native::Bool(right)) => {
                Ok(Native::Bool(
                    self.builder.ins().icmp(condition, left, right),
                ))
            }
            _ => Err(format!("%{} and %{} are not comparable", a.0, b.0)),
        }
    }

    /// An ordered comparison. Integers compare signed; `bool`s compare
    /// unsigned over their canonical `0`/`1`, which is exactly the
    /// interpreter's `false < true`.
    fn ordered(
        &mut self,
        a: ValueId,
        b: ValueId,
        signed: IntCC,
        unsigned: IntCC,
    ) -> Result<Native, String> {
        match (self.value(a)?, self.value(b)?) {
            (Native::Int(left), Native::Int(right)) => {
                Ok(Native::Bool(self.builder.ins().icmp(signed, left, right)))
            }
            (Native::Bool(left), Native::Bool(right)) => {
                Ok(Native::Bool(self.builder.ins().icmp(unsigned, left, right)))
            }
            _ => Err(format!("%{} and %{} are not ordered", a.0, b.0)),
        }
    }

    fn call(
        &mut self,
        result: ValueId,
        callee: ItemId,
        args: &[ValueId],
    ) -> Result<Native, String> {
        let target = self.functions.get(&callee).copied().ok_or_else(|| {
            format!(
                "%{} calls function id {}, which is absent",
                result.0, callee.0
            )
        })?;
        let func_id = self
            .declared
            .get(&callee)
            .copied()
            .ok_or_else(|| format!("function id {} was never declared", callee.0))?;
        let func_ref = self.object.declare_func_in_func(func_id, self.builder.func);

        let mut native_args: Vec<Value> = Vec::with_capacity(args.len());
        for arg in args {
            match self.value(*arg)? {
                // A `unit` argument occupies no ABI position, so it is
                // not passed at all.
                Native::Unit => {}
                Native::Int(value) | Native::Bool(value) => native_args.push(value),
                Native::Slot { .. } => {
                    return Err(format!("%{} is a slot, not an argument", arg.0));
                }
            }
        }

        let call = self.builder.ins().call(func_ref, &native_args);
        let returned = scalar_of_checked(&target.return_type)?;
        match abi_type(returned) {
            None => Ok(Native::Unit),
            Some(_) => {
                let value = self
                    .builder
                    .inst_results(call)
                    .first()
                    .copied()
                    .ok_or_else(|| format!("function id {} returned nothing", callee.0))?;
                self.wrap(returned, value)
            }
        }
    }

    fn terminator(&mut self, terminator: &Terminator) -> Result<(), String> {
        match terminator {
            Terminator::Return(None) => {
                self.builder.ins().return_(&[]);
                Ok(())
            }
            Terminator::Return(Some(value)) => {
                match self.value(*value)? {
                    // A `unit` result is returned by returning nothing,
                    // matching the signature this function was declared
                    // with.
                    Native::Unit => self.builder.ins().return_(&[]),
                    Native::Int(value) | Native::Bool(value) => {
                        self.builder.ins().return_(&[value])
                    }
                    Native::Slot { .. } => return Err(format!("%{} is a slot", value.0)),
                };
                Ok(())
            }
            Terminator::Branch(target) => {
                let block = self.block(*target)?;
                self.builder.ins().jump(block, &[]);
                Ok(())
            }
            Terminator::CondBranch {
                condition,
                then_block,
                else_block,
            } => {
                let condition = self.boolean(*condition)?;
                let then_block = self.block(*then_block)?;
                let else_block = self.block(*else_block)?;
                self.builder
                    .ins()
                    .brif(condition, then_block, &[], else_block, &[]);
                Ok(())
            }
            Terminator::Switch { .. } | Terminator::Invoke { .. } | Terminator::Raise { .. } => {
                Err("capability validation let an unsupported terminator through".to_string())
            }
        }
    }
}

/// Emits the exported `main` the C runtime calls.
///
/// The conversion it performs is the documented one, and the only place
/// it is performed:
///
/// * `main() -> unit` exits with status `0`;
/// * `main() -> i64` hands back the low 32 bits of the returned value
///   as the C `int` result, which the kernel then reports to a waiting
///   parent as its low 8 bits -- so the observable exit status is the
///   Napitia value taken modulo 256 (`rfcs/0015`).
fn define_entry_wrapper(
    object: &mut ObjectModule,
    context: &mut Context,
    frontend: &mut FunctionBuilderContext,
    frontend_config: isa::TargetFrontendConfig,
    declared: &BTreeMap<ItemId, FuncId>,
    plan: &NativePlan,
) -> Result<(), String> {
    let entry = declared
        .get(&plan.entry())
        .copied()
        .ok_or_else(|| "the entry function was never declared".to_string())?;

    let mut signature = object.make_signature();
    signature.returns.push(AbiParam::new(types::I32));
    context.func.signature = signature.clone();
    let wrapper = object
        .declare_function(ENTRY_SYMBOL, Linkage::Export, &signature)
        .map_err(|error| format!("could not declare `{ENTRY_SYMBOL}`: {error}"))?;

    {
        let mut builder = FunctionBuilder::new(&mut context.func, frontend);
        let block = builder.create_block();
        builder.switch_to_block(block);
        let func_ref = object.declare_func_in_func(entry, builder.func);
        let call = builder.ins().call(func_ref, &[]);
        let status = match plan.entry_result() {
            Scalar::Unit => builder.ins().iconst(types::I32, 0),
            Scalar::Int => {
                let result = builder
                    .inst_results(call)
                    .first()
                    .copied()
                    .ok_or_else(|| "`main` returned nothing".to_string())?;
                builder.ins().ireduce(types::I32, result)
            }
            Scalar::Bool => {
                return Err("`main` may only return `i64` or `unit`".to_string());
            }
        };
        builder.ins().return_(&[status]);
        builder.seal_all_blocks();
        builder.finalize(frontend_config);
    }

    object
        .define_function(wrapper, context)
        .map_err(|error| format!("Cranelift rejected the entry wrapper: {error}"))?;
    object.clear_context(context);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::{self, IrOutput};
    use crate::hir::ItemRegistry;
    use crate::native::TARGET_TRIPLE;
    use crate::native::capability;
    use crate::source::SourceMap;

    struct Built {
        object: Vec<u8>,
    }

    /// Compiles `text` through the whole native path up to (but not
    /// including) the linker, exactly as `napitia build` does.
    fn build(text: &str) -> Built {
        let mut map = SourceMap::new();
        let source = map.add_file("native.npt", text);
        let mut interner = Interner::new();
        let (nir, registry) = match driver::ir(&map, source, &mut interner) {
            IrOutput::Ready { nir, registry } => (nir, registry),
            IrOutput::Diagnostics(diagnostics) => {
                let codes: Vec<&str> = diagnostics.iter().map(|d| d.code).collect();
                panic!("this fixture must compile and verify cleanly, got {codes:?}")
            }
        };
        let plan =
            match capability::validate(&nir, source, &interner, &registry, TARGET_TRIPLE, &[]) {
                Ok(plan) => plan,
                Err(diagnostics) => {
                    let codes: Vec<&str> = diagnostics.iter().map(|d| d.code).collect();
                    panic!("this fixture must be inside the native subset, got {codes:?}")
                }
            };
        match emit_object(&nir, &interner, &plan, TARGET_TRIPLE) {
            Ok(object) => Built { object },
            Err(reason) => panic!("code generation failed: {reason}"),
        }
    }

    /// The same program compiled twice, through two independent
    /// compilations, with no shared state between them.
    fn build_twice(text: &str) -> (Vec<u8>, Vec<u8>) {
        (build(text).object, build(text).object)
    }

    fn is_elf(object: &[u8]) -> bool {
        object.starts_with(&[0x7f, b'E', b'L', b'F'])
    }

    const SCALAR_PROGRAM: &str = "
        func add(a: i64, b: i64) -> i64 { return a + b; }
        func twice(x: i64) -> i64 { return add(x, x); }
        func main() -> i64 {
            mutable total = 0;
            mutable index = 0;
            while index < 4 {
                total = total + twice(index);
                index = index + 1;
            }
            if total > 3 { return total; }
            return 0;
        }
    ";

    #[test]
    fn a_scalar_program_compiles_to_an_elf_object() {
        let built = build(SCALAR_PROGRAM);
        assert!(is_elf(&built.object), "the object must be an ELF file");
    }

    #[test]
    fn a_unit_returning_main_compiles() {
        let built =
            build("func nothing() -> unit { return; } func main() -> unit { nothing(); return; }");
        assert!(is_elf(&built.object));
    }

    #[test]
    fn every_accepted_operator_compiles() {
        let built = build(
            "
            func main() -> i64 {
                value a = 6;
                value b = 7;
                value ordered = (a < b) == !(a > b);
                value different = (a <= b) != (a >= b);
                value bits = (a & b) | (a ^ b);
                value inverted = ~bits;
                value negated = -b;
                if ordered {
                    if different { return 1; }
                    return (a + b) * (b - a) + inverted - negated;
                }
                return 0;
            }
            ",
        );
        assert!(is_elf(&built.object));
    }

    #[test]
    fn a_bool_parameter_and_result_compile() {
        let built = build(
            "func flip(x: bool) -> bool { return !x; } \
             func main() -> i64 { if flip(false) { return 1; } return 0; }",
        );
        assert!(is_elf(&built.object));
    }

    // -- determinism -------------------------------------------------------

    #[test]
    fn compiling_the_same_program_twice_produces_identical_object_bytes() {
        let (first, second) = build_twice(SCALAR_PROGRAM);
        assert_eq!(first, second, "object generation must be deterministic");
    }

    /// Storage order is not semantics: reversing how the module stores
    /// its functions, and how each function stores its blocks, must not
    /// move a single byte of the object.
    #[test]
    fn reversed_storage_order_produces_identical_object_bytes() {
        let mut map = SourceMap::new();
        let source = map.add_file("native.npt", SCALAR_PROGRAM);
        let mut interner = Interner::new();
        let IrOutput::Ready {
            nir: forward,
            registry,
        } = driver::ir(&map, source, &mut interner)
        else {
            panic!("the fixture must compile")
        };

        let mut reversed = forward.clone();
        reversed.functions.reverse();
        for function in &mut reversed.functions {
            function.blocks.reverse();
        }

        let object_of = |module: &Module, registry: &ItemRegistry| {
            let plan =
                capability::validate(module, source, &interner, registry, TARGET_TRIPLE, &[])
                    .expect("the fixture is inside the native subset");
            emit_object(module, &interner, &plan, TARGET_TRIPLE).expect("code generation succeeds")
        };

        assert_eq!(
            object_of(&forward, &registry),
            object_of(&reversed, &registry)
        );
    }

    // -- symbols -----------------------------------------------------------

    #[test]
    fn symbol_names_are_derived_from_item_identity_not_from_position() {
        assert_eq!(symbol_name(ItemId(0), "main"), "napitia_0_main");
        assert_eq!(symbol_name(ItemId(41), "add"), "napitia_41_add");
    }

    #[test]
    fn a_name_that_is_not_a_bare_identifier_still_yields_one_symbol_per_item() {
        let first = symbol_name(ItemId(1), "odd.name");
        let second = symbol_name(ItemId(2), "odd.name");
        assert_eq!(first, "napitia_1_odd_name");
        assert_ne!(first, second, "the id keeps sanitized names apart");
    }

    #[test]
    fn the_exported_entry_symbol_is_the_only_documented_one() {
        let built = build(SCALAR_PROGRAM);
        let bytes = built.object;
        let contains = |needle: &str| {
            bytes
                .windows(needle.len())
                .any(|window| window == needle.as_bytes())
        };
        assert!(contains(ENTRY_SYMBOL));
        assert!(contains("napitia_"), "internal symbols stay mangled");
    }

    // -- the backend refuses rather than panics ----------------------------

    #[test]
    fn an_unknown_target_is_reported_rather_than_panicking() {
        let mut map = SourceMap::new();
        let source = map.add_file("native.npt", "func main() -> i64 { return 1; }");
        let mut interner = Interner::new();
        let IrOutput::Ready { nir, registry } = driver::ir(&map, source, &mut interner) else {
            panic!("the fixture must compile")
        };
        let plan = capability::validate(&nir, source, &interner, &registry, TARGET_TRIPLE, &[])
            .expect("the fixture is inside the native subset");
        let failure = emit_object(&nir, &interner, &plan, "not-a-real-triple")
            .expect_err("an unknown triple has no backend");
        assert!(failure.contains("not-a-real-triple"), "{failure}");
    }
}
