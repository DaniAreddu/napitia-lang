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
use cranelift_codegen::ir::{AbiParam, Block, InstBuilder, Signature, TrapCode, Value, types};
use cranelift_codegen::isa;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, FuncId, Linkage, Module as _};
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::hir::ItemId;
use crate::nir::{
    BasicBlock, BlockId, Const, Function, Instruction, Module, Terminator, ValueId, ValueKind,
};
use crate::symbol::Interner;
use crate::types::{ArithFailure, IntOp};

use super::capability::NativePlan;
use super::{ENTRY_SYMBOL, Scalar, scalar_of};

/// The object's own module name. Constant, because it is written into
/// the emitted file and a build must not depend on where it ran.
const OBJECT_NAME: &str = "napitia";

/// The trap that terminates a block control cannot leave any other way,
/// because the call just before it does not return. See
/// [`BodyLowerer::guard`] for why a trap is the terminator here and
/// never the failure itself.
///
/// A `const`, so an invalid code would be a compile error in this
/// compiler rather than anything a Napitia program could reach.
const UNREACHABLE_AFTER_EXIT: TrapCode = TrapCode::unwrap_user(1);

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

    let mut context = object.make_context();
    let mut frontend = FunctionBuilderContext::new();
    // Emitted before anything that branches to it, so a checked
    // operation always has a failure path to name.
    let runtime = define_runtime(&mut object, &mut context, &mut frontend, frontend_config)?;

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
            &runtime,
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

/// The internal runtime this backend emits beside the program: the
/// deterministic failure path a checked operation branches to
/// (`rfcs/0015`).
///
/// It is genuinely internal. Every symbol in it is `Linkage::Local`, no
/// Napitia code can name one, and it exists only because a native
/// executable has nowhere else to report a failure to. There is no
/// runtime library to link against and no interpreter behind it.
struct RuntimeFailures {
    /// One handler per operation that can overflow, so the message is a
    /// constant rather than something selected at run time -- no
    /// branching, no table lookup, and one relocation per operation.
    handlers: BTreeMap<IntOp, FuncId>,
}

impl RuntimeFailures {
    fn handler(&self, op: IntOp) -> Result<FuncId, String> {
        self.handlers.get(&op).copied().ok_or_else(|| {
            format!(
                "no runtime failure handler was emitted for `{}`",
                op.as_str()
            )
        })
    }
}

/// The operations this backend checks. `div`, `rem`, `shl` and `shr`
/// are not here because the capability validator refuses them before
/// code generation (they are interpreter-only in this milestone), and
/// every other accepted operator -- the comparisons, the bitwise
/// operations, `not` -- cannot leave the domain at all.
const CHECKED: [IntOp; 4] = [IntOp::Add, IntOp::Sub, IntOp::Mul, IntOp::Neg];

/// The status a Napitia runtime failure exits with.
///
/// One number, chosen once (`rfcs/0015`). It cannot be a status no
/// successful program produces, because a built executable's status is
/// the low 8 bits of whatever `main` returned and every byte is
/// reachable that way. The discriminator is standard error: a
/// successful run writes nothing there, and a failure writes exactly
/// one line.
const RUNTIME_FAILURE_STATUS: i64 = 70;

/// The file descriptor a failure reports on.
const STDERR: i64 = 2;

/// The exact bytes a native runtime failure writes.
///
/// The tail is [`ArithFailure`]'s own rendering -- the same text
/// `napitia run` prints for the same failure -- prefixed so a reader
/// can tell the executable itself is speaking rather than the compiler.
fn failure_message(op: IntOp) -> String {
    let failure = ArithFailure::Overflow(op);
    format!("napitia: error[{}]: {failure}\n", failure.code())
}

/// Emits one failure handler per checked operation.
///
/// Each is `fn() -> ()` and never returns: it writes its own fixed
/// message to standard error and calls `exit`. Emitting one per
/// operation rather than one that selects a message keeps the generated
/// code branchless and the message a plain relocation.
fn define_runtime(
    object: &mut ObjectModule,
    context: &mut Context,
    frontend: &mut FunctionBuilderContext,
    frontend_config: isa::TargetFrontendConfig,
) -> Result<RuntimeFailures, String> {
    let pointer = object.target_config().pointer_type();

    // `write` and `exit` are the two libc entry points this runtime
    // needs. They are imported, not defined: the executable is linked
    // against the system C runtime already, because that is what
    // provides the `main` the entry wrapper exports.
    let mut write_signature = object.make_signature();
    write_signature.params.push(AbiParam::new(types::I32));
    write_signature.params.push(AbiParam::new(pointer));
    write_signature.params.push(AbiParam::new(pointer));
    write_signature.returns.push(AbiParam::new(pointer));
    let write = object
        .declare_function("write", Linkage::Import, &write_signature)
        .map_err(|error| format!("could not declare `write`: {error}"))?;

    let mut exit_signature = object.make_signature();
    exit_signature.params.push(AbiParam::new(types::I32));
    let exit = object
        .declare_function("exit", Linkage::Import, &exit_signature)
        .map_err(|error| format!("could not declare `exit`: {error}"))?;

    let mut handlers = BTreeMap::new();
    for op in CHECKED {
        let message = failure_message(op);
        let bytes = message.as_bytes();

        let data_symbol = format!("napitia_failure_text_{}", op.as_str());
        let data_id = object
            .declare_data(&data_symbol, Linkage::Local, false, false)
            .map_err(|error| format!("could not declare `{data_symbol}`: {error}"))?;
        let mut description = DataDescription::new();
        description.define(bytes.to_vec().into_boxed_slice());
        object
            .define_data(data_id, &description)
            .map_err(|error| format!("could not define `{data_symbol}`: {error}"))?;

        let symbol = format!("napitia_fail_{}", op.as_str());
        let signature = object.make_signature();
        context.func.signature = signature.clone();
        let func_id = object
            .declare_function(&symbol, Linkage::Local, &signature)
            .map_err(|error| format!("could not declare `{symbol}`: {error}"))?;

        {
            let mut builder = FunctionBuilder::new(&mut context.func, frontend);
            let block = builder.create_block();
            builder.switch_to_block(block);

            let text = object.declare_data_in_func(data_id, builder.func);
            let address = builder.ins().symbol_value(pointer, text);
            let descriptor = builder.ins().iconst(types::I32, STDERR);
            let length = builder.ins().iconst(pointer, bytes.len() as i64);
            let write_ref = object.declare_func_in_func(write, builder.func);
            // The result is deliberately ignored. A failure that cannot
            // even be written has nothing better to try, and retrying
            // would make the exit status depend on whether standard
            // error happened to be open.
            builder
                .ins()
                .call(write_ref, &[descriptor, address, length]);

            let status = builder.ins().iconst(types::I32, RUNTIME_FAILURE_STATUS);
            let exit_ref = object.declare_func_in_func(exit, builder.func);
            builder.ins().call(exit_ref, &[status]);
            // `exit` does not return, but Cranelift does not know that
            // and a block needs a terminator. Returning is the honest
            // one here: this function's own signature says it returns
            // nothing, and no value is fabricated.
            builder.ins().return_(&[]);

            builder.seal_all_blocks();
            builder.finalize(frontend_config);
        }

        object
            .define_function(func_id, context)
            .map_err(|error| format!("Cranelift rejected `{symbol}`: {error}"))?;
        object.clear_context(context);
        handlers.insert(op, func_id);
    }

    Ok(RuntimeFailures { handlers })
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
    runtime: &RuntimeFailures,
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
        runtime,
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
    runtime: &'a RuntimeFailures,
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
            ValueKind::Add(a, b) => self.checked_binary(IntOp::Add, *a, *b),
            ValueKind::Sub(a, b) => self.checked_binary(IntOp::Sub, *a, *b),
            ValueKind::Mul(a, b) => self.checked_binary(IntOp::Mul, *a, *b),
            ValueKind::And(a, b) => {
                self.arithmetic(*a, *b, |builder, x, y| builder.ins().band(x, y))
            }
            ValueKind::Or(a, b) => self.arithmetic(*a, *b, |builder, x, y| builder.ins().bor(x, y)),
            ValueKind::Xor(a, b) => {
                self.arithmetic(*a, *b, |builder, x, y| builder.ins().bxor(x, y))
            }
            ValueKind::Neg(a) => {
                let value = self.integer(*a)?;
                let result = self.builder.ins().ineg(value);
                // The minimum is the one value whose negation is not an
                // `i64`, and `ineg` of it quietly produces the minimum
                // again.
                let overflowed = self.builder.ins().icmp_imm_s(IntCC::Equal, value, i64::MIN);
                self.guard(IntOp::Neg, overflowed)?;
                Ok(Native::Int(result))
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

    /// One checked integer operation: the arithmetic, an explicit
    /// signed-overflow test, and a branch to the failure path
    /// (`rfcs/0015`).
    ///
    /// The tests are the ordinary two's-complement ones, and they state
    /// in machine terms exactly what [`crate::types::numeric`] states in
    /// Rust. That is the one rule in this compiler written down twice,
    /// unavoidably: a backend emits code rather than running it. The
    /// differential tests between `napitia run` and a built executable
    /// are what keep the two statements honest.
    fn checked_binary(&mut self, op: IntOp, a: ValueId, b: ValueId) -> Result<Native, String> {
        let left = self.integer(a)?;
        let right = self.integer(b)?;
        let (result, overflowed) = match op {
            IntOp::Add => {
                let result = self.builder.ins().iadd(left, right);
                // Two operands of the same sign producing a result of
                // the other sign is the only way an addition leaves the
                // domain.
                let from_left = self.builder.ins().bxor(left, result);
                let from_right = self.builder.ins().bxor(right, result);
                let both = self.builder.ins().band(from_left, from_right);
                (
                    result,
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::SignedLessThan, both, 0i64),
                )
            }
            IntOp::Sub => {
                let result = self.builder.ins().isub(left, right);
                // Operands of differing signs producing a result whose
                // sign differs from the one it was subtracted from.
                let operands = self.builder.ins().bxor(left, right);
                let from_left = self.builder.ins().bxor(left, result);
                let both = self.builder.ins().band(operands, from_left);
                (
                    result,
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::SignedLessThan, both, 0i64),
                )
            }
            IntOp::Mul => {
                let result = self.builder.ins().imul(left, right);
                // The exact 128-bit product fits in 64 bits precisely
                // when its high half is the sign extension of its low
                // half.
                let high = self.builder.ins().smulhi(left, right);
                let sign = self.builder.ins().sshr_imm_s(result, 63i64);
                (result, self.builder.ins().icmp(IntCC::NotEqual, high, sign))
            }
            IntOp::Neg | IntOp::Div | IntOp::Rem | IntOp::Shl | IntOp::Shr => {
                return Err(format!(
                    "`{}` is not a checked binary operation in this backend",
                    op.as_str()
                ));
            }
        };
        self.guard(op, overflowed)?;
        Ok(Native::Int(result))
    }

    /// Branches to `op`'s failure handler when `overflowed` holds, and
    /// continues in a fresh block when it does not.
    ///
    /// The failure block ends in a trap, and that trap is unreachable by
    /// construction: the handler writes the diagnostic and calls `exit`,
    /// so control never comes back from it. The trap is a block
    /// terminator, not the failure mechanism. Nothing about what this
    /// program means depends on what a trap does, and no hardware
    /// condition is being presented as a language rule -- the failure
    /// has already been fully delivered, in words, before it.
    fn guard(&mut self, op: IntOp, overflowed: Value) -> Result<(), String> {
        let failed = self.builder.create_block();
        let continued = self.builder.create_block();
        self.builder
            .ins()
            .brif(overflowed, failed, &[], continued, &[]);

        self.builder.switch_to_block(failed);
        let handler = self.runtime.handler(op)?;
        let handler_ref = self.object.declare_func_in_func(handler, self.builder.func);
        self.builder.ins().call(handler_ref, &[]);
        self.builder.ins().trap(UNREACHABLE_AFTER_EXIT);

        self.builder.switch_to_block(continued);
        Ok(())
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

    // -- the internal runtime ----------------------------------------------

    /// Object generation is host-independent, so the failure path can be
    /// inspected anywhere -- including on a host that could never link
    /// or run the result.
    fn object_contains(object: &[u8], needle: &str) -> bool {
        object
            .windows(needle.len())
            .any(|window| window == needle.as_bytes())
    }

    #[test]
    fn every_checked_operation_gets_its_own_handler_and_its_own_message() {
        let built = build(SCALAR_PROGRAM);
        for op in CHECKED {
            assert!(
                object_contains(&built.object, &format!("napitia_fail_{}", op.as_str())),
                "`{}` must have a failure handler in the object",
                op.as_str()
            );
            let message = failure_message(op);
            assert!(
                object_contains(&built.object, message.trim_end()),
                "`{}`'s message must be in the object as bytes: {message:?}",
                op.as_str()
            );
        }
    }

    /// The words an executable reports are the words `napitia run`
    /// reports. Read from the same table, never copied.
    #[test]
    fn a_failure_message_is_the_shared_rendering_with_this_backends_prefix() {
        for op in CHECKED {
            let failure = ArithFailure::Overflow(op);
            assert_eq!(
                failure_message(op),
                format!("napitia: error[{}]: {failure}\n", failure.code())
            );
            assert!(failure_message(op).ends_with('\n'), "one complete line");
        }
        assert_eq!(
            failure_message(IntOp::Add),
            "napitia: error[X0002]: integer overflow in `add`\n"
        );
    }

    /// The four operators the capability validator refuses have no
    /// handler, because no code can branch to one.
    #[test]
    fn the_operators_outside_the_subset_have_no_failure_handler() {
        let built = build(SCALAR_PROGRAM);
        for op in [IntOp::Div, IntOp::Rem, IntOp::Shl, IntOp::Shr] {
            assert!(
                !object_contains(&built.object, &format!("napitia_fail_{}", op.as_str())),
                "`{}` is refused before code generation, so it needs no handler",
                op.as_str()
            );
        }
    }

    #[test]
    fn the_runtime_imports_exactly_the_two_libc_entry_points_it_uses() {
        let built = build(SCALAR_PROGRAM);
        assert!(object_contains(&built.object, "write"));
        assert!(object_contains(&built.object, "exit"));
    }

    /// The exit status is part of the documented contract, not an
    /// implementation detail to be changed quietly.
    #[test]
    fn the_runtime_failure_status_is_the_one_the_rfc_documents() {
        assert_eq!(RUNTIME_FAILURE_STATUS, 70);
        assert_eq!(STDERR, 2);
    }

    /// The Cranelift IR one function lowers to, as text.
    ///
    /// Emitted bytes prove the handlers *exist*; they cannot show that
    /// anything branches to one, because every handler is emitted
    /// whether or not the program uses it. The IR shows the branch
    /// itself, and can be read on a host that could never run the
    /// result.
    fn lowered_ir(text: &str, function_name: &str) -> (String, RuntimeFailures) {
        let mut map = SourceMap::new();
        let source = map.add_file("native.npt", text);
        let mut interner = Interner::new();
        let IrOutput::Ready { nir, registry } = driver::ir(&map, source, &mut interner) else {
            panic!("the fixture must compile")
        };
        let plan = capability::validate(&nir, source, &interner, &registry, TARGET_TRIPLE, &[])
            .expect("the fixture is inside the native subset");

        let mut flags = settings::builder();
        set_flag(&mut flags, "opt_level", "none").expect("a known flag");
        set_flag(&mut flags, "is_pic", "true").expect("a known flag");
        let isa =
            isa::lookup(target_lexicon::Triple::from_str(TARGET_TRIPLE).expect("a real triple"))
                .expect("a backend for the one target")
                .finish(settings::Flags::new(flags))
                .expect("a configurable backend");
        let frontend_config = isa.frontend_config();
        let builder =
            ObjectBuilder::new(isa, OBJECT_NAME, cranelift_module::default_libcall_names())
                .expect("an object builder");
        let mut object = ObjectModule::new(builder);

        let functions = index_functions(&nir, &plan);
        let mut context = object.make_context();
        let mut frontend = FunctionBuilderContext::new();
        let runtime = define_runtime(&mut object, &mut context, &mut frontend, frontend_config)
            .expect("the runtime is emitted");

        let mut declared: BTreeMap<ItemId, FuncId> = BTreeMap::new();
        for id in plan.functions() {
            let function = lookup(&functions, *id).expect("a planned function");
            let signature = native_signature(&mut object, function).expect("a native signature");
            let symbol = symbol_name(*id, interner.resolve(function.name));
            declared.insert(
                *id,
                object
                    .declare_function(&symbol, Linkage::Local, &signature)
                    .expect("a declarable function"),
            );
        }

        for id in plan.functions() {
            let function = lookup(&functions, *id).expect("a planned function");
            if interner.resolve(function.name) != function_name {
                continue;
            }
            let reachable = plan.reachable_blocks(*id).expect("a block plan");
            context.func.signature =
                native_signature(&mut object, function).expect("a native signature");
            define_body(
                &mut object,
                &mut context,
                &mut frontend,
                frontend_config,
                &declared,
                &functions,
                &runtime,
                function,
                reachable,
            )
            .expect("the body lowers");
            return (context.func.display().to_string(), runtime);
        }
        panic!("`{function_name}` is not in the plan")
    }

    /// How Cranelift's own text names a declared function: the module's
    /// namespace and the declaration's index. The handler's symbol name
    /// does not appear in the IR, so this is what a reference to it
    /// looks like.
    fn reference_to(runtime: &RuntimeFailures, op: IntOp) -> String {
        format!(
            "u0:{}",
            runtime
                .handler(op)
                .expect("a handler for a checked op")
                .as_u32()
        )
    }

    #[test]
    fn a_checked_operation_branches_to_its_own_failure_handler() {
        for (operator, op) in [
            ("a + b", IntOp::Add),
            ("a - b", IntOp::Sub),
            ("a * b", IntOp::Mul),
        ] {
            let (ir, runtime) = lowered_ir(
                &format!(
                    "func work(a: i64, b: i64) -> i64 {{ return {operator}; }} \
                     func main() -> i64 {{ return work(1, 2); }}"
                ),
                "work",
            );
            assert!(
                ir.contains("brif"),
                "`{operator}` must branch on its own overflow test:\n{ir}"
            );
            assert!(
                ir.contains(&reference_to(&runtime, op)),
                "`{operator}` must reach `{}`'s handler and no other:\n{ir}",
                op.as_str()
            );
            for other in CHECKED.iter().filter(|other| **other != op) {
                assert!(
                    !ir.contains(&reference_to(&runtime, *other)),
                    "`{operator}` must not reach `{}`'s handler:\n{ir}",
                    other.as_str()
                );
            }
            assert!(
                ir.contains("trap"),
                "the failure block is terminated after the handler call:\n{ir}"
            );
        }
    }

    #[test]
    fn negation_branches_to_the_negation_handler_on_the_minimum_alone() {
        let (ir, runtime) = lowered_ir(
            "func work(a: i64) -> i64 { return -a; } \
             func main() -> i64 { return work(1); }",
            "work",
        );
        assert!(ir.contains("brif"), "{ir}");
        assert!(ir.contains(&reference_to(&runtime, IntOp::Neg)), "{ir}");
        assert!(
            ir.contains("-9223372036854775808"),
            "the test compares against the one value whose negation is not an i64:\n{ir}"
        );
    }

    /// An operator with no exceptional case gets no test, no branch and
    /// no trap.
    #[test]
    fn an_operator_that_cannot_leave_the_domain_gets_no_failure_branch() {
        for (operator, returns, entry) in [
            ("a & b", "i64", "return work(1, 2);"),
            ("a | b", "i64", "return work(1, 2);"),
            ("a ^ b", "i64", "return work(1, 2);"),
            ("~a", "i64", "return work(1, 2);"),
            ("a < b", "bool", "if work(1, 2) { return 1; } return 0;"),
            ("a == b", "bool", "if work(1, 2) { return 1; } return 0;"),
        ] {
            let (ir, runtime) = lowered_ir(
                &format!(
                    "func work(a: i64, b: i64) -> {returns} {{ return {operator}; }} \
                     func main() -> i64 {{ {entry} }}"
                ),
                "work",
            );
            assert!(
                !ir.contains("trap"),
                "`{operator}` cannot leave the domain, so it needs no failure path:\n{ir}"
            );
            for op in CHECKED {
                assert!(
                    !ir.contains(&reference_to(&runtime, op)),
                    "`{operator}` must reach no handler at all:\n{ir}"
                );
            }
        }
    }

    /// Every value in the generated IR is 64 bits wide, not 128.
    #[test]
    fn an_i64_is_lowered_as_a_64_bit_value() {
        let (ir, _) = lowered_ir(
            "func work(a: i64, b: i64) -> i64 { return a + b; } \
             func main() -> i64 { return work(1, 2); }",
            "work",
        );
        assert!(ir.contains("i64"), "{ir}");
        assert!(
            !ir.contains("i128"),
            "nothing is held in a 128-bit value any more:\n{ir}"
        );
        assert!(
            !ir.contains("isplit") && !ir.contains("iconcat"),
            "and nothing is assembled out of two halves any more:\n{ir}"
        );
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
