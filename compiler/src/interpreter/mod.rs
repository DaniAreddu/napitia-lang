//! A small interpreter for the NIR subset this milestone lowers to
//! (`spec/0006`), used to validate language semantics before any native
//! backend exists.
//!
//! Every runtime value is represented uniformly as an `i128`/`f64` pair
//! of kinds regardless of its declared width (`i8` and `i64` both
//! execute as `Value::Int`); this milestone does not model
//! width-specific overflow or truncation behavior. Integer arithmetic
//! wraps on overflow (`wrapping_add` etc.) rather than panicking, since
//! Rust's debug-mode overflow checks would otherwise crash the
//! interpreter on ordinary, valid Napitia programs.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use crate::hir::ItemId;
use crate::nir::{Const, Function, Module, Terminator, ValueId, ValueKind};
use crate::symbol::Interner;
use crate::types::Evidence;

/// A resource record's own identity within one [`Interpreter`]'s own
/// runtime resource table (`rfcs/0011`, Blocker 8): the table index it
/// lives at, stable for that resource's entire runtime lifetime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ResourceId(u32);

/// A capability to observe or consume one resource record, as of a
/// specific point in its own ownership history (`rfcs/0011`, Blocker
/// 8) -- `Value` itself only ever carries this, never the resource's
/// own payload directly, so an ordinary Rust `Clone` of a `Value`
/// duplicates only this cheap `(id, generation)` pair, never the
/// underlying resource's own identity or data. Every ownership
/// transfer (a `take` parameter's own argument, a returned resource)
/// bumps the table's own current generation for `id`, which makes
/// every handle still referencing the *previous* generation stale --
/// exactly the "invalidates the previous handle" contract this
/// milestone's resource model promises. Observing a resource (an
/// ordinary, non-`take` parameter; a field read) never transfers, so
/// it never bumps the generation: many simultaneously-valid observing
/// handles for the same still-current generation are expected and
/// fine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResourceHandle {
    id: ResourceId,
    generation: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ResourceStatus {
    Alive,
    Dropped,
}

#[derive(Debug, Clone)]
struct ResourceRecord {
    item: ItemId,
    generation: u64,
    status: ResourceStatus,
    /// This resource's own fields, in declaration order -- may
    /// themselves contain a `Value::Resource` handle for a nested
    /// resource-typed field, which is never duplicated by this: it is
    /// still just a handle into this same table, identifying its own
    /// separate record.
    fields: Vec<Value>,
}

/// The runtime resource table one [`Interpreter`] execution owns
/// (`rfcs/0011`, Blocker 8): every resource ever constructed during
/// this run, indexed by [`ResourceId`] (a plain, monotonically-growing
/// `Vec` index -- never a `HashMap`, and never a Rust pointer address,
/// so nothing about this table's own behavior depends on iteration
/// order or allocator behavior). Never shrinks (a dropped record's own
/// slot is kept, marked `Dropped`, so a stale handle referencing it
/// later still resolves to *something* to check the generation/status
/// of, rather than silently going out of bounds).
#[derive(Default)]
struct ResourceTable {
    records: Vec<ResourceRecord>,
}

impl ResourceTable {
    fn construct(&mut self, item: ItemId, fields: Vec<Value>) -> ResourceHandle {
        let id = ResourceId(self.records.len() as u32);
        self.records.push(ResourceRecord {
            item,
            generation: 0,
            status: ResourceStatus::Alive,
            fields,
        });
        ResourceHandle { id, generation: 0 }
    }

    fn record(&self, handle: ResourceHandle) -> Result<&ResourceRecord, InterpreterError> {
        let record = self
            .records
            .get(handle.id.0 as usize)
            .ok_or_else(|| invalid("resource handle does not refer to any known resource"))?;
        if record.generation != handle.generation {
            return Err(invalid(
                "stale resource handle: this resource's own ownership was already transferred \
                 elsewhere",
            ));
        }
        Ok(record)
    }

    /// Observes `handle`'s own current record without transferring
    /// ownership (Blocker 8: "observing does not transfer") -- still
    /// rejects a stale handle or an already-dropped resource, since
    /// neither may ever be legitimately read.
    fn observe(&self, handle: ResourceHandle) -> Result<&ResourceRecord, InterpreterError> {
        let record = self.record(handle)?;
        if record.status == ResourceStatus::Dropped {
            return Err(invalid("use of a resource after it was already dropped"));
        }
        Ok(record)
    }

    /// Transfers ownership of `handle`'s own resource to a new owner
    /// (Blocker 8: a `take` argument at registration/call time, or a
    /// returned resource) -- bumps the table's own current generation
    /// for this resource, invalidating `handle` (and every other
    /// handle still referencing the generation it was minted from),
    /// and returns the fresh handle identifying the current owner.
    fn transfer(&mut self, handle: ResourceHandle) -> Result<ResourceHandle, InterpreterError> {
        let id = handle.id;
        let record = self.record(handle)?;
        if record.status == ResourceStatus::Dropped {
            return Err(invalid(
                "cannot transfer ownership of a resource that was already dropped",
            ));
        }
        let record = &mut self.records[id.0 as usize];
        record.generation += 1;
        Ok(ResourceHandle {
            id,
            generation: record.generation,
        })
    }

    /// Destroys `handle`'s own resource exactly once (Blocker 8): a
    /// stale handle, an already-dropped resource, or an unknown handle
    /// are each their own distinct rejected case, never silently
    /// treated as success.
    fn drop_resource(&mut self, handle: ResourceHandle) -> Result<(), InterpreterError> {
        let id = handle.id;
        let record = self.record(handle)?;
        if record.status == ResourceStatus::Dropped {
            return Err(invalid("double drop of a resource"));
        }
        self.records[id.0 as usize].status = ResourceStatus::Dropped;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i128),
    Float(f64),
    Bool(bool),
    Char(char),
    Str(String),
    Unit,
    /// A record value: fields in declaration order, matching
    /// `nir::RecordLayout`.
    Record {
        item: ItemId,
        fields: Vec<Value>,
    },
    /// A variant value: `case` is the declaration index of its active
    /// case, and `payload` holds that case's payload values in
    /// declaration order (empty for a unit case).
    Variant {
        item: ItemId,
        case: usize,
        payload: Vec<Value>,
    },
    /// A `resource`-typed value (`rfcs/0011`, Blocker 8) -- unlike
    /// `Record`, never carries its own payload directly: only a handle
    /// into the current `Interpreter`'s own `ResourceTable`, so an
    /// ordinary Rust `Clone` (every value read from `values` already
    /// clones) duplicates only the cheap handle, never the resource's
    /// own runtime identity or data.
    Resource(ResourceHandle),
}

/// A condition the interpreter detects and reports instead of crashing:
/// division/remainder by zero, or an internal-invariant violation (a
/// value read before it was computed, an operator applied to
/// incompatible value kinds, an unknown function). The latter should
/// never happen for NIR produced by `nir::lower`, but the interpreter
/// still returns a structured error rather than panicking or invoking
/// undefined behavior, per the project's no-panic-on-malformed-input
/// rule.
#[derive(Debug, Clone, PartialEq)]
pub enum InterpreterError {
    DivisionByZero,
    InvalidOperation(String),
}

/// A function frame's own two possible ways to end (`rfcs/0010`) -- never
/// a Rust panic/unwind. `Raised` always carries a `Value::Variant`: the
/// exact value a `Terminator::Raise` produced (directly, or forwarded
/// unchanged from an `Invoke`'s own failure edge), with its own dynamic
/// item/case identity intact.
enum Outcome {
    Returned(Value),
    Raised(Value),
}

pub struct Interpreter<'a> {
    module: &'a Module,
    /// Every resource constructed anywhere during this `Interpreter`'s
    /// own execution (`rfcs/0011`, Blocker 8) -- shared (via interior
    /// mutability) across every nested call frame `call_function`
    /// recurses into, since ownership transfer crosses function-call
    /// boundaries: a resource this frame constructs may be handed to a
    /// callee, or one this frame's own callee returns may become this
    /// frame's own, and both sides must observe the exact same record.
    resources: RefCell<ResourceTable>,
    /// Test-only record of every function call entered and every
    /// resource actually destroyed, in the exact order this execution
    /// performed them -- the one place a test can observe that deferred
    /// calls and resource drops actually interleave in real, deterministic
    /// LIFO order at runtime, rather than merely inferring it from a
    /// program's own final return value.
    #[cfg(test)]
    event_log: RefCell<Vec<String>>,
}

impl<'a> Interpreter<'a> {
    pub fn new(module: &'a Module) -> Self {
        Interpreter {
            module,
            resources: RefCell::new(ResourceTable::default()),
            #[cfg(test)]
            event_log: RefCell::new(Vec::new()),
        }
    }

    /// `true` iff `item` names a declared `resource` (`rfcs/0011`) --
    /// mirrors `nir::lower`'s/`resourceck`'s own identical check
    /// against `nir::RecordLayout::affine`.
    fn is_resource(&self, item: ItemId) -> bool {
        self.module
            .records
            .iter()
            .any(|(id, layout)| *id == item && layout.affine)
    }

    /// Transfers ownership of `value` if it is a resource (Blocker 8);
    /// passes any other value through unchanged. Shared by both
    /// directions ownership crosses a call boundary: a `take`
    /// argument's own transfer *into* a call, and a returned value's
    /// own transfer back *out* of one.
    fn transfer_if_resource(&self, value: Value) -> Result<Value, InterpreterError> {
        match value {
            Value::Resource(handle) => Ok(Value::Resource(
                self.resources.borrow_mut().transfer(handle)?,
            )),
            other => Ok(other),
        }
    }

    /// The lowest-numbered `ValueId` among `values` still holding a live,
    /// still-current resource handle this exiting frame is itself
    /// responsible for -- one it constructed, or received through a
    /// `take` parameter, and never dropped or transferred away
    /// (`rfcs/0011`, Blocker 8). `observing_params` excludes every
    /// ordinary (non-`take`) parameter's own value: this frame never
    /// owned it in the first place (`an ordinary parameter observes
    /// without consuming`), so it never running a destructive action on
    /// it is correct, not a leak. A dropped resource's own entry is
    /// removed from `values` outright (see `Instruction::Drop`'s own
    /// handling above), and a transferred one's entry still holds its
    /// own now-stale handle (bumping the table's own generation never
    /// rewrites `values` itself) -- so either one is already excluded
    /// here without needing its own special case, purely because
    /// [`ResourceTable::record`] rejects a stale handle.
    /// `resourceck`/`nir::verify` already statically guarantee this can
    /// never actually be `Some` for NIR that passed both; this is this
    /// frame's own independent runtime backstop, not a substitute for
    /// either.
    fn leaked_resource(
        &self,
        values: &HashMap<ValueId, Value>,
        observing_params: &HashSet<ValueId>,
    ) -> Option<ValueId> {
        let resources = self.resources.borrow();
        let mut leaked: Vec<ValueId> = values
            .iter()
            .filter(|(id, _)| !observing_params.contains(id))
            .filter_map(|(id, value)| match value {
                Value::Resource(handle) => resources
                    .record(*handle)
                    .ok()
                    .filter(|record| record.status == ResourceStatus::Alive)
                    .map(|_| *id),
                _ => None,
            })
            .collect();
        leaked.sort();
        leaked.into_iter().next()
    }

    /// Calls the function named `name` with no arguments — the shape of
    /// `napitia run`'s entry point (`func main() -> ...`).
    pub fn run(&self, name: &str, interner: &Interner) -> Result<Value, InterpreterError> {
        self.call(name, interner, Vec::new())
    }

    /// This execution's own call/drop event log, in the exact order they
    /// actually happened (test-only: see [`Self::event_log`]'s own doc
    /// comment).
    #[cfg(test)]
    fn event_log(&self) -> Vec<String> {
        self.event_log.borrow().clone()
    }

    pub fn call(
        &self,
        name: &str,
        interner: &Interner,
        args: Vec<Value>,
    ) -> Result<Value, InterpreterError> {
        let function = self
            .module
            .functions
            .iter()
            .find(|f| interner.resolve(f.name) == name)
            .ok_or_else(|| {
                InterpreterError::InvalidOperation(format!("unknown function `{name}`"))
            })?;
        into_result(self.call_function(function, args, Vec::new())?)
    }

    /// Calls the function identified by `item` with no arguments -- a
    /// multi-module project's entry point, resolved by the caller to a
    /// specific `ItemId` in the configured entry module, never by a
    /// name lookup over the whole (merged) module: more than one
    /// module could otherwise declare an unrelated function also named
    /// `main`, and a name-based lookup could silently run the wrong
    /// one.
    pub fn run_item(&self, item: ItemId) -> Result<Value, InterpreterError> {
        self.call_item(item, Vec::new())
    }

    pub fn call_item(&self, item: ItemId, args: Vec<Value>) -> Result<Value, InterpreterError> {
        let function = self
            .module
            .functions
            .iter()
            .find(|f| f.id == item)
            .ok_or_else(|| {
                InterpreterError::InvalidOperation(format!("unknown function {item:?}"))
            })?;
        into_result(self.call_function(function, args, Vec::new())?)
    }

    /// `evidence` is this call's own resolved capability evidence
    /// (`rfcs/0009`), one entry per `function.requirements`, in that
    /// same order -- always fully concrete (`Evidence::Extension`) by
    /// the time a frame actually runs: whichever call constructed this
    /// vector already resolved any `Evidence::Forwarded` against *its
    /// own* calling frame first (see `resolve_evidence`), so a running
    /// frame's own evidence never itself needs further resolution, only
    /// a lookup.
    fn call_function(
        &self,
        function: &Function,
        args: Vec<Value>,
        evidence: Vec<Evidence>,
    ) -> Result<Outcome, InterpreterError> {
        // `Vec::zip` silently truncates to the shorter side: too few
        // arguments would leave the missing parameters unbound (an
        // arbitrary "value not found" error later, from whichever
        // instruction first reads one -- not a clear diagnosis of the
        // actual problem), and too many would just drop the extra ones
        // with no error at all. The verifier does not check call sites
        // against argument *values* (only NIR-to-NIR signatures), so
        // this is the one place a real arity mismatch at the API
        // boundary is still checked before it can do either.
        if function.params.len() != args.len() {
            return Err(InterpreterError::InvalidOperation(format!(
                "function expects {} argument(s), found {}",
                function.params.len(),
                args.len()
            )));
        }
        // Mirrors the argument-count check just above: the verifier
        // checks NIR-to-NIR evidence shape (`Call`'s own evidence list
        // length against its callee's declared requirements), but never
        // a value-level call across this API boundary (`Interpreter::
        // call`/`call_item`, called directly by the CLI/tests, never
        // through a `Call` instruction at all). A requirement-bearing
        // function invoked with the wrong number of evidence entries
        // fails here, immediately and by its own diagnosis, rather than
        // deferred until whichever `protocol.call` first tries to index
        // past the end of an evidence vector too short for it.
        if function.requirements.len() != evidence.len() {
            return Err(InterpreterError::InvalidOperation(format!(
                "function declares {} capability requirement(s) but was given {} evidence entries",
                function.requirements.len(),
                evidence.len()
            )));
        }
        let observing_params: HashSet<ValueId> = function
            .params
            .iter()
            .filter(|p| !p.take)
            .map(|p| p.value)
            .collect();
        let mut values: HashMap<ValueId, Value> = HashMap::new();
        for (param, arg) in function.params.iter().zip(args) {
            // A `take` parameter transfers ownership into this call
            // (`rfcs/0011`, Blocker 8): the caller's own handle (if
            // `arg` is a resource at all -- an ordinary value passed to
            // a meaningless `take` on non-resource data, already
            // rejected at check time, is left untouched here) is
            // invalidated, and this frame receives the current owner's
            // own fresh handle. An ordinary (observing) parameter never
            // transfers: `arg` is bound exactly as given.
            let arg = if param.take {
                self.transfer_if_resource(arg)?
            } else {
                arg
            };
            values.insert(param.value, arg);
        }

        // `BlockId(0)` is the entry block by definition (the verifier
        // requires exactly one to exist -- `nir::verify`), not whichever
        // block happens to be first in the vector.
        let mut block_id = crate::nir::BlockId(0);
        if !function.blocks.iter().any(|b| b.id == block_id) {
            return Err(InterpreterError::InvalidOperation(
                "function has no entry block (bb0)".to_string(),
            ));
        }

        loop {
            let block = function
                .blocks
                .iter()
                .find(|b| b.id == block_id)
                .ok_or_else(|| {
                    InterpreterError::InvalidOperation("branch to unknown block".to_string())
                })?;

            for instruction in &block.instructions {
                match instruction {
                    crate::nir::Instruction::Value { result, kind, .. } => {
                        let value = self.eval(kind, &values, &evidence)?;
                        values.insert(*result, value);
                    }
                    crate::nir::Instruction::Store { slot, value } => {
                        let v = get(&values, value)?;
                        values.insert(*slot, v);
                    }
                    crate::nir::Instruction::Drop { value } => {
                        // Destroys the resource value exactly once
                        // (`rfcs/0011`, Blocker 8): the resource table
                        // itself -- not this frame's own value map --
                        // is the single source of truth for whether
                        // this specific resource record was already
                        // dropped, so a double-drop reached through a
                        // *different* `Value::Resource` handle aliasing
                        // the same underlying record (not just the same
                        // `ValueId`) is independently caught here too,
                        // never silently treated as a fresh drop.
                        match get(&values, value)? {
                            Value::Resource(handle) => {
                                self.resources.borrow_mut().drop_resource(handle)?;
                                #[cfg(test)]
                                self.event_log
                                    .borrow_mut()
                                    .push(format!("drop:{}", handle.id.0));
                            }
                            other => {
                                return Err(invalid(format!(
                                    "drop of a non-resource value ({})",
                                    kind_name(&other)
                                )));
                            }
                        }
                        values.remove(value);
                    }
                }
            }

            match &block.terminator {
                Terminator::Return(Some(id)) => {
                    // A returned resource transfers ownership back to
                    // the caller (`rfcs/0011`, Blocker 8) -- the same
                    // transfer a `take` argument gets, just on the way
                    // out instead of in. Transferred first, so its own
                    // now-stale entry in `values` is already excluded by
                    // the leak check that follows.
                    let returned = self.transfer_if_resource(get(&values, id)?)?;
                    if let Some(leaked) = self.leaked_resource(&values, &observing_params) {
                        return Err(invalid(format!(
                            "function returned while still owning an undestroyed resource (%{})",
                            leaked.0
                        )));
                    }
                    return Ok(Outcome::Returned(returned));
                }
                Terminator::Return(None) => {
                    if let Some(leaked) = self.leaked_resource(&values, &observing_params) {
                        return Err(invalid(format!(
                            "function returned while still owning an undestroyed resource (%{})",
                            leaked.0
                        )));
                    }
                    return Ok(Outcome::Returned(Value::Unit));
                }
                Terminator::Branch(target) => block_id = *target,
                Terminator::CondBranch {
                    condition,
                    then_block,
                    else_block,
                } => {
                    block_id = match get(&values, condition)? {
                        Value::Bool(true) => *then_block,
                        Value::Bool(false) => *else_block,
                        _ => {
                            return Err(InterpreterError::InvalidOperation(
                                "branch condition was not a bool".to_string(),
                            ));
                        }
                    };
                }
                Terminator::Switch {
                    scrutinee,
                    variant,
                    cases,
                } => {
                    let Value::Variant { item, case, .. } = get(&values, scrutinee)? else {
                        return Err(invalid("switch scrutinee was not a variant value"));
                    };
                    if item != *variant {
                        return Err(invalid(
                            "switch scrutinee's variant identity does not match the switch's declared variant",
                        ));
                    }
                    block_id = *cases.get(case).ok_or_else(|| {
                        invalid("switch scrutinee's case has no corresponding target")
                    })?;
                }
                Terminator::Invoke {
                    callee,
                    type_args: _,
                    args,
                    evidence: call_evidence,
                    ok_slot,
                    ok_target,
                    err_targets,
                } => {
                    let arg_values = args
                        .iter()
                        .map(|id| get(&values, id))
                        .collect::<Result<Vec<_>, _>>()?;
                    let callee_fn = self
                        .module
                        .functions
                        .iter()
                        .find(|f| f.id == *callee)
                        .ok_or_else(|| {
                            invalid("invoke targets a function not present in this module")
                        })?;
                    let resolved_evidence = call_evidence
                        .iter()
                        .map(|e| resolve_evidence(&evidence, e))
                        .collect::<Result<Vec<_>, _>>()?;
                    match self.call_function(callee_fn, arg_values, resolved_evidence)? {
                        Outcome::Returned(value) => {
                            values.insert(*ok_slot, value);
                            block_id = *ok_target;
                        }
                        Outcome::Raised(raised) => {
                            let Value::Variant { item, .. } = &raised else {
                                return Err(invalid("a raised value must be a variant value"));
                            };
                            let target = err_targets
                                .iter()
                                .find(|t| t.variant == *item)
                                .ok_or_else(|| {
                                    invalid("invoke has no failure target for the raised variant")
                                })?;
                            values.insert(target.slot, raised);
                            block_id = target.target;
                        }
                    }
                }
                Terminator::Raise { value } => {
                    let raised = get(&values, value)?;
                    if let Some(leaked) = self.leaked_resource(&values, &observing_params) {
                        return Err(invalid(format!(
                            "function raised while still owning an undestroyed resource (%{})",
                            leaked.0
                        )));
                    }
                    return Ok(Outcome::Raised(raised));
                }
            }
        }
    }

    fn eval(
        &self,
        kind: &ValueKind,
        values: &HashMap<ValueId, Value>,
        current_evidence: &[Evidence],
    ) -> Result<Value, InterpreterError> {
        match kind {
            ValueKind::Alloc => Ok(Value::Unit),
            ValueKind::Const(c) => Ok(const_value(c)),
            ValueKind::Load(id) => get(values, id),
            ValueKind::Add(a, b) => arith(
                get(values, a)?,
                get(values, b)?,
                i128::wrapping_add,
                |x, y| x + y,
            ),
            ValueKind::Sub(a, b) => arith(
                get(values, a)?,
                get(values, b)?,
                i128::wrapping_sub,
                |x, y| x - y,
            ),
            ValueKind::Mul(a, b) => arith(
                get(values, a)?,
                get(values, b)?,
                i128::wrapping_mul,
                |x, y| x * y,
            ),
            ValueKind::Div(a, b) => div(get(values, a)?, get(values, b)?, false),
            ValueKind::Rem(a, b) => div(get(values, a)?, get(values, b)?, true),
            ValueKind::Neg(a) => match get(values, a)? {
                Value::Int(x) => Ok(Value::Int(x.wrapping_neg())),
                Value::Float(x) => Ok(Value::Float(-x)),
                other => Err(invalid(format!("cannot negate {}", kind_name(&other)))),
            },
            ValueKind::Not(a) => match get(values, a)? {
                Value::Bool(x) => Ok(Value::Bool(!x)),
                Value::Int(x) => Ok(Value::Int(!x)),
                other => Err(invalid(format!(
                    "cannot apply `not` to {}",
                    kind_name(&other)
                ))),
            },
            ValueKind::And(a, b) => bitop(get(values, a)?, get(values, b)?, |x, y| x & y),
            ValueKind::Or(a, b) => bitop(get(values, a)?, get(values, b)?, |x, y| x | y),
            ValueKind::Xor(a, b) => bitop(get(values, a)?, get(values, b)?, |x, y| x ^ y),
            ValueKind::Shl(a, b) => shift(get(values, a)?, get(values, b)?, i128::checked_shl),
            ValueKind::Shr(a, b) => shift(get(values, a)?, get(values, b)?, i128::checked_shr),
            ValueKind::Eq(a, b) => Ok(Value::Bool(eq(&get(values, a)?, &get(values, b)?)?)),
            ValueKind::Ne(a, b) => Ok(Value::Bool(!eq(&get(values, a)?, &get(values, b)?)?)),
            ValueKind::Lt(a, b) => Ok(Value::Bool(
                ord(&get(values, a)?, &get(values, b)?)? == Ordering::Less,
            )),
            ValueKind::Le(a, b) => Ok(Value::Bool(
                ord(&get(values, a)?, &get(values, b)?)? != Ordering::Greater,
            )),
            ValueKind::Gt(a, b) => Ok(Value::Bool(
                ord(&get(values, a)?, &get(values, b)?)? == Ordering::Greater,
            )),
            ValueKind::Ge(a, b) => Ok(Value::Bool(
                ord(&get(values, a)?, &get(values, b)?)? != Ordering::Less,
            )),
            // Generic type arguments are compile-time-only bookkeeping:
            // one parametric NIR function body is shared by every call
            // regardless of them (`rfcs/0008`), and a runtime `Value`
            // already carries everything execution needs (`ItemId` plus
            // its positional fields/payload) -- so the interpreter reads
            // straight past `type_args` here without needing to look at
            // it at all, the same "generics erase at runtime" approach
            // ordinary type-erased generics use.
            ValueKind::Call(item, _type_args, args, call_evidence) => {
                let arg_values = args
                    .iter()
                    .map(|id| get(values, id))
                    .collect::<Result<Vec<_>, _>>()?;
                let callee = self
                    .module
                    .functions
                    .iter()
                    .find(|f| f.id == *item)
                    .ok_or_else(|| invalid("call to a function not present in this module"))?;
                let resolved_evidence = call_evidence
                    .iter()
                    .map(|e| resolve_evidence(current_evidence, e))
                    .collect::<Result<Vec<_>, _>>()?;
                #[cfg(test)]
                self.event_log.borrow_mut().push(format!("call:{}", item.0));
                // An ordinary `Call` never targets a fallible function
                // (`rfcs/0010`) -- that always lowers to `Invoke` instead
                // (the verifier's job to guarantee). A `Raised` outcome
                // here means the callee's own `raises` metadata and its
                // actual body disagree; guarded defensively rather than
                // silently treated as the raised value itself.
                match self.call_function(callee, arg_values, resolved_evidence)? {
                    Outcome::Returned(value) => Ok(value),
                    Outcome::Raised(_) => Err(invalid(
                        "an ordinary call's callee raised a failure; only Invoke may call a fallible function",
                    )),
                }
            }
            // Dispatches through this specific call's own resolved
            // evidence (`rfcs/0009`): a concrete extension is looked up
            // by its `ItemId` and its own method table consulted by
            // canonical index, never by re-resolving a name -- this is
            // the one place a protocol call actually executes.
            ValueKind::ProtocolCall {
                protocol: _,
                arguments: _,
                method,
                evidence,
                args,
            } => {
                let arg_values = args
                    .iter()
                    .map(|id| get(values, id))
                    .collect::<Result<Vec<_>, _>>()?;
                let resolved = resolve_evidence(current_evidence, evidence)?;
                let Evidence::Extension { extend, nested } = resolved else {
                    return Err(invalid(
                        "protocol call evidence did not resolve to a concrete extension",
                    ));
                };
                let extend_layout = self
                    .module
                    .extends
                    .iter()
                    .find(|(id, _)| *id == extend)
                    .map(|(_, layout)| layout)
                    .ok_or_else(|| {
                        invalid("protocol call evidence references an unknown extend")
                    })?;
                let method_item = extend_layout.methods.get(*method).ok_or_else(|| {
                    invalid("protocol call method index out of range for its extend")
                })?;
                let callee = self
                    .module
                    .functions
                    .iter()
                    .find(|f| f.id == *method_item)
                    .ok_or_else(|| {
                        invalid(
                            "protocol call's implementing function is not present in this module",
                        )
                    })?;
                match self.call_function(callee, arg_values, nested)? {
                    Outcome::Returned(value) => Ok(value),
                    Outcome::Raised(_) => Err(invalid(
                        "a protocol call's implementing method raised a failure; protocol methods that raise are not yet supported",
                    )),
                }
            }
            ValueKind::RecordCreate(item, _type_args, field_ids) => {
                let fields = field_ids
                    .iter()
                    .map(|id| get(values, id))
                    .collect::<Result<Vec<_>, _>>()?;
                // A `resource` gets its own unique runtime identity
                // (Blocker 8) rather than being represented inline the
                // same way an ordinary, freely-copyable record is --
                // every read of a `Value::Resource` handle (`get`
                // already clones every value it returns) duplicates
                // only the cheap handle, never this record's own data.
                if self.is_resource(*item) {
                    Ok(Value::Resource(
                        self.resources.borrow_mut().construct(*item, fields),
                    ))
                } else {
                    Ok(Value::Record {
                        item: *item,
                        fields,
                    })
                }
            }
            ValueKind::RecordField {
                base,
                record,
                field,
            } => match get(values, base)? {
                Value::Record { item, fields } if item == *record => fields
                    .get(*field)
                    .cloned()
                    .ok_or_else(|| invalid("record field index out of range")),
                Value::Resource(handle) => {
                    let table = self.resources.borrow();
                    let rec = table.observe(handle)?;
                    if rec.item != *record {
                        return Err(invalid(
                            "expected a resource value of the expected type, found a different resource",
                        ));
                    }
                    rec.fields
                        .get(*field)
                        .cloned()
                        .ok_or_else(|| invalid("resource field index out of range"))
                }
                other => Err(invalid(format!(
                    "expected a record value of the expected type, found {}",
                    kind_name(&other)
                ))),
            },
            ValueKind::VariantCreate {
                variant,
                case,
                type_args: _,
                payload,
            } => {
                let payload = payload
                    .iter()
                    .map(|id| get(values, id))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Value::Variant {
                    item: *variant,
                    case: *case,
                    payload,
                })
            }
            ValueKind::VariantPayload {
                base,
                variant,
                case,
                index,
            } => match get(values, base)? {
                Value::Variant {
                    item,
                    case: active_case,
                    payload,
                } if item == *variant && active_case == *case => payload
                    .get(*index)
                    .cloned()
                    .ok_or_else(|| invalid("variant payload index out of range")),
                other => Err(invalid(format!(
                    "expected an active variant case matching this payload projection, found {}",
                    kind_name(&other)
                ))),
            },
        }
    }
}

fn get(values: &HashMap<ValueId, Value>, id: &ValueId) -> Result<Value, InterpreterError> {
    values
        .get(id)
        .cloned()
        .ok_or_else(|| invalid(format!("%{} was read before it was computed", id.0)))
}

fn invalid(message: impl Into<String>) -> InterpreterError {
    InterpreterError::InvalidOperation(message.into())
}

/// Converts a top-level call's own [`Outcome`] to this module's public
/// `Result<Value, InterpreterError>` API. A well-typed `main` (or any
/// other function reached directly through `Interpreter::call`/
/// `call_item`, never through an `Invoke`) can never legally raise
/// (`rfcs/0010`'s entry-point restriction, enforced at typeck) -- so a
/// `Raised` outcome reaching this boundary means it was never caught by
/// any `Invoke` along the way, which is only reachable through
/// malformed/hand-built NIR; guarded defensively rather than surfaced as
/// if it were an ordinary return value.
fn into_result(outcome: Outcome) -> Result<Value, InterpreterError> {
    match outcome {
        Outcome::Returned(value) => Ok(value),
        Outcome::Raised(_) => Err(invalid(
            "an unhandled failure reached the program's entry point",
        )),
    }
}

/// Resolves one static [`Evidence`] entry (from a `Call`/`ProtocolCall`
/// instruction) against the *currently executing* frame's own already-
/// resolved evidence (`rfcs/0009`): `Evidence::Extension` is
/// self-contained and passes through unchanged; `Evidence::Forwarded(k)`
/// means "use whatever this frame's own `evidence[k]` already is" --
/// exactly the frame-relative copy that lets a still-symbolic generic
/// body forward its own requirement without the interpreter ever
/// re-running any type/capability resolution. An out-of-range forwarded
/// index is malformed NIR the verifier should already have rejected;
/// the interpreter still reports it as a structured error rather than
/// panicking.
fn resolve_evidence(
    current_evidence: &[Evidence],
    entry: &Evidence,
) -> Result<Evidence, InterpreterError> {
    match entry {
        Evidence::Extension { extend, nested } => Ok(Evidence::Extension {
            extend: *extend,
            nested: nested.clone(),
        }),
        Evidence::Forwarded(index) => current_evidence
            .get(*index)
            .cloned()
            .ok_or_else(|| invalid("forwarded capability evidence index out of range")),
    }
}

fn kind_name(value: &Value) -> &'static str {
    match value {
        Value::Int(_) => "an integer",
        Value::Float(_) => "a float",
        Value::Bool(_) => "a bool",
        Value::Char(_) => "a char",
        Value::Str(_) => "a string",
        Value::Unit => "unit",
        Value::Record { .. } => "a record",
        Value::Variant { .. } => "a variant",
        Value::Resource(_) => "a resource",
    }
}

fn const_value(c: &Const) -> Value {
    match c {
        Const::Int(v) => Value::Int(*v as i128),
        Const::Float(v) => Value::Float(*v),
        Const::Bool(v) => Value::Bool(*v),
        Const::Char(v) => Value::Char(*v),
        Const::Str(v) => Value::Str(v.clone()),
        Const::Unit => Value::Unit,
    }
}

fn arith(
    a: Value,
    b: Value,
    int_op: impl Fn(i128, i128) -> i128,
    float_op: impl Fn(f64, f64) -> f64,
) -> Result<Value, InterpreterError> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(int_op(x, y))),
        (Value::Float(x), Value::Float(y)) => Ok(Value::Float(float_op(x, y))),
        (a, b) => Err(invalid(format!(
            "arithmetic between {} and {}",
            kind_name(&a),
            kind_name(&b)
        ))),
    }
}

fn div(a: Value, b: Value, remainder: bool) -> Result<Value, InterpreterError> {
    match (a, b) {
        (Value::Int(_), Value::Int(0)) => Err(InterpreterError::DivisionByZero),
        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(if remainder {
            x.wrapping_rem(y)
        } else {
            x.wrapping_div(y)
        })),
        (Value::Float(x), Value::Float(y)) => {
            Ok(Value::Float(if remainder { x % y } else { x / y }))
        }
        (a, b) => Err(invalid(format!(
            "division between {} and {}",
            kind_name(&a),
            kind_name(&b)
        ))),
    }
}

fn bitop(a: Value, b: Value, op: impl Fn(i128, i128) -> i128) -> Result<Value, InterpreterError> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(op(x, y))),
        (a, b) => Err(invalid(format!(
            "bitwise operator between {} and {}",
            kind_name(&a),
            kind_name(&b)
        ))),
    }
}

fn shift(
    a: Value,
    b: Value,
    op: impl Fn(i128, u32) -> Option<i128>,
) -> Result<Value, InterpreterError> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => {
            let amount = u32::try_from(y).map_err(|_| invalid("shift amount out of range"))?;
            op(x, amount)
                .map(Value::Int)
                .ok_or_else(|| invalid("shift amount out of range"))
        }
        (a, b) => Err(invalid(format!(
            "shift between {} and {}",
            kind_name(&a),
            kind_name(&b)
        ))),
    }
}

fn eq(a: &Value, b: &Value) -> Result<bool, InterpreterError> {
    Ok(match (a, b) {
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Float(x), Value::Float(y)) => x == y,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Char(x), Value::Char(y)) => x == y,
        (Value::Str(x), Value::Str(y)) => x == y,
        (Value::Unit, Value::Unit) => true,
        (a, b) => {
            return Err(invalid(format!(
                "compared {} with {}",
                kind_name(a),
                kind_name(b)
            )));
        }
    })
}

fn ord(a: &Value, b: &Value) -> Result<Ordering, InterpreterError> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Ok(x.cmp(y)),
        (Value::Float(x), Value::Float(y)) => x
            .partial_cmp(y)
            .ok_or_else(|| invalid("comparison involving NaN")),
        (Value::Char(x), Value::Char(y)) => Ok(x.cmp(y)),
        (Value::Str(x), Value::Str(y)) => Ok(x.cmp(y)),
        (Value::Bool(x), Value::Bool(y)) => Ok(x.cmp(y)),
        (a, b) => Err(invalid(format!(
            "ordered comparison of {} with {}",
            kind_name(a),
            kind_name(b)
        ))),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::hir::lower_module as lower_hir;
    use crate::lexer::tokenize;
    use crate::nir::lower_module as lower_nir;
    use crate::parser::Parser;
    use crate::source::SourceMap;
    use crate::typeck::check_module;

    fn run(text: &str) -> Result<Value, InterpreterError> {
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
        let resourceck_result = crate::resourceck::check_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &interner,
        );
        assert!(
            resourceck_result.diagnostics.is_empty(),
            "unexpected resource errors: {:?}",
            resourceck_result.diagnostics
        );
        let nir = lower_nir(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &resourceck_result.cleanup_edges,
            &interner,
            id,
        )
        .expect("expected lowering to succeed");
        Interpreter::new(&nir).run("main", &interner)
    }

    /// Like [`run`], but also returns the exact call/drop event order
    /// this specific execution performed -- proving actual runtime
    /// cleanup order (deferred calls, resource drops) rather than only
    /// each test's own final return value.
    fn run_with_log(text: &str) -> (Result<Value, InterpreterError>, Vec<String>) {
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
        let resourceck_result = crate::resourceck::check_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &interner,
        );
        assert!(
            resourceck_result.diagnostics.is_empty(),
            "unexpected resource errors: {:?}",
            resourceck_result.diagnostics
        );
        let nir = lower_nir(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &resourceck_result.cleanup_edges,
            &interner,
            id,
        )
        .expect("expected lowering to succeed");
        let interpreter = Interpreter::new(&nir);
        let outcome = interpreter.run("main", &interner);
        // Resolves every `call:<ItemId>` entry to the callee's own
        // source name, so an assertion against this log reads (and stays
        // correct) independent of whichever raw numeric ids this
        // particular compilation happened to assign.
        let log = interpreter
            .event_log()
            .into_iter()
            .map(|event| match event.strip_prefix("call:") {
                Some(id) => {
                    let id: u32 = id.parse().expect("call event carries a numeric ItemId");
                    let name = nir
                        .functions
                        .iter()
                        .find(|f| f.id.0 == id)
                        .map(|f| interner.resolve(f.name))
                        .expect("call event names a function present in this module");
                    format!("call:{name}")
                }
                None => event,
            })
            .collect();
        (outcome, log)
    }

    #[test]
    fn executes_arithmetic() {
        assert_eq!(
            run("func main() -> i64 { return 40 + 2 }"),
            Ok(Value::Int(42))
        );
    }

    #[test]
    fn executes_function_calls() {
        let text = "func add(left: i64, right: i64) -> i64 { return left + right } \
                    func main() -> i64 { return add(40, 2) }";
        assert_eq!(run(text), Ok(Value::Int(42)));
    }

    #[test]
    fn executes_recursive_calls() {
        let text = "func fact(n: i64) -> i64 { if n == 0 { return 1 } return n * fact(n - 1) } \
                    func main() -> i64 { return fact(5) }";
        assert_eq!(run(text), Ok(Value::Int(120)));
    }

    #[test]
    fn executes_if_else() {
        let text = "func main() -> i64 { \
                        value answer = 42; \
                        if answer == 42 { return answer } else { return 0 } \
                    }";
        assert_eq!(run(text), Ok(Value::Int(42)));
    }

    #[test]
    fn executes_while_loop() {
        let text = "func main() -> i64 { \
                        mutable total = 0; \
                        mutable i = 0; \
                        while i < 5 { total = total + i; i = i + 1; } \
                        return total \
                    }";
        assert_eq!(run(text), Ok(Value::Int(10)));
    }

    #[test]
    fn executes_loop_with_break() {
        let text = "func main() -> i64 { \
                        mutable i = 0; \
                        loop { \
                            if i == 3 { break; } \
                            i = i + 1; \
                        } \
                        return i \
                    }";
        assert_eq!(run(text), Ok(Value::Int(3)));
    }

    #[test]
    fn executes_continue() {
        let text = "func main() -> i64 { \
                        mutable i = 0; \
                        mutable total = 0; \
                        while i < 5 { \
                            i = i + 1; \
                            if i == 3 { continue; } \
                            total = total + i; \
                        } \
                        return total \
                    }";
        // i runs 1..=5, skipping the total += step only when i == 3:
        // 1 + 2 + 4 + 5 = 12.
        assert_eq!(run(text), Ok(Value::Int(12)));
    }

    #[test]
    fn detects_division_by_zero() {
        let text = "func main() -> i64 { value z = 0; return 1 / z }";
        assert_eq!(run(text), Err(InterpreterError::DivisionByZero));
    }

    #[test]
    fn detects_remainder_by_zero() {
        let text = "func main() -> i64 { value z = 0; return 1 % z }";
        assert_eq!(run(text), Err(InterpreterError::DivisionByZero));
    }

    #[test]
    fn float_division_by_zero_is_infinity_not_an_error() {
        let text = "func main() -> f64 { value z = 0.0; return 1.0 / z }";
        assert_eq!(run(text), Ok(Value::Float(f64::INFINITY)));
    }

    #[test]
    fn short_circuit_and_skips_the_right_operand() {
        // If && were not short-circuiting (or divided eagerly), this
        // would panic/error on division by zero instead of returning
        // false.
        let text = "func main() -> bool { \
                        value z = 0; \
                        return false && (1 / z == 1) \
                    }";
        assert_eq!(run(text), Ok(Value::Bool(false)));
    }

    #[test]
    fn short_circuit_or_skips_the_right_operand() {
        let text = "func main() -> bool { \
                        value z = 0; \
                        return true || (1 / z == 1) \
                    }";
        assert_eq!(run(text), Ok(Value::Bool(true)));
    }

    #[test]
    fn executes_bitwise_and_shift_operators() {
        assert_eq!(
            run("func main() -> i64 { return 6 & 3 }"),
            Ok(Value::Int(2))
        );
        assert_eq!(
            run("func main() -> i64 { return 6 | 1 }"),
            Ok(Value::Int(7))
        );
        assert_eq!(
            run("func main() -> i64 { return 5 ^ 1 }"),
            Ok(Value::Int(4))
        );
        assert_eq!(
            run("func main() -> i64 { return 1 << 4 }"),
            Ok(Value::Int(16))
        );
        assert_eq!(
            run("func main() -> i64 { return 16 >> 2 }"),
            Ok(Value::Int(4))
        );
    }

    #[test]
    fn executes_comparisons() {
        assert_eq!(
            run("func main() -> bool { return 1 < 2 }"),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run("func main() -> bool { return 2 <= 2 }"),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run("func main() -> bool { return 3 > 2 }"),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run("func main() -> bool { return 2 >= 3 }"),
            Ok(Value::Bool(false))
        );
    }

    #[test]
    fn executes_unary_negation_and_not() {
        assert_eq!(run("func main() -> i64 { return -5 }"), Ok(Value::Int(-5)));
        assert_eq!(
            run("func main() -> bool { return !false }"),
            Ok(Value::Bool(true))
        );
    }

    #[test]
    fn executes_compound_assignment() {
        let text = "func main() -> i64 { mutable x = 10; x += 5; return x }";
        assert_eq!(run(text), Ok(Value::Int(15)));
    }

    #[test]
    fn integer_overflow_wraps_instead_of_panicking() {
        let text = format!(
            "func main() -> i64 {{ value m = {}; return m + 1 }}",
            i64::MAX
        );
        // Must not panic; wrapping semantics are a documented
        // simplification of this milestone's interpreter.
        assert!(run(&text).is_ok());
    }

    #[test]
    fn diverging_initializer_short_circuits_the_rest_of_the_block() {
        // The initializer of `x` diverges before the binding ever
        // completes, so `x` never exists; the rest of the block (`x =
        // 99; return x`) is unreachable and must never run -- if NIR
        // lowering had appended instructions after the diverging
        // `return 1`'s terminator (the bug this guards against), this
        // would either panic or return 99 instead of 1.
        let text = "func main() -> i64 { mutable x = return 1; x = 99; return x }";
        assert_eq!(run(text), Ok(Value::Int(1)));
    }

    #[test]
    fn diverging_while_condition_runs_and_returns_unit() {
        // The condition always returns before the loop can ever run;
        // the whole statement -- and the function -- must simply
        // complete with `unit`, not panic or hang.
        let text = "func main() { while { return; } {} }";
        assert_eq!(run(text), Ok(Value::Unit));
    }

    #[test]
    fn if_without_else_evaluates_the_branch_but_returns_unit() {
        let text = "func main() { if true { 1 } }";
        assert_eq!(run(text), Ok(Value::Unit));
    }

    #[test]
    fn if_else_join_returns_the_non_diverging_value_when_then_diverges() {
        let text = "func choose(flag: bool) -> i64 { if flag { return 1 } else { 2 } } \
                    func main() -> i64 { return choose(false) }";
        assert_eq!(run(text), Ok(Value::Int(2)));
    }

    #[test]
    fn if_else_join_returns_the_non_diverging_value_when_else_diverges() {
        let text = "func choose(flag: bool) -> i64 { if flag { 2 } else { return 1 } } \
                    func main() -> i64 { return choose(true) }";
        assert_eq!(run(text), Ok(Value::Int(2)));
    }

    #[test]
    fn unary_not_on_a_diverging_operand_returns_the_divergent_value() {
        let text = "func main() -> i64 { !{ return 7 } }";
        assert_eq!(run(text), Ok(Value::Int(7)));
    }

    #[test]
    fn comparison_with_a_diverging_right_operand_returns_the_divergent_value() {
        let text = "func main() -> i64 { 1 == { return 7 } }";
        assert_eq!(run(text), Ok(Value::Int(7)));
    }

    #[test]
    fn assignment_with_a_diverging_right_hand_side_returns_the_divergent_value() {
        let text = "func main() -> i64 { mutable x = 0; x = { return 7 }; }";
        assert_eq!(run(text), Ok(Value::Int(7)));
    }

    #[test]
    fn calling_an_unknown_function_is_an_error_not_a_panic() {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", "func main() -> i64 { return 0 }");
        let mut interner = Interner::new();
        let (tokens, _) = tokenize(map.get(id).content(), id, &mut interner);
        let (module, _) = Parser::new(tokens, id, &mut interner).parse_module();
        let (hir, _) = lower_hir(&module, id, &interner);
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        let nir = lower_nir(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &interner,
            id,
        )
        .expect("expected lowering to succeed");
        let outcome = Interpreter::new(&nir).run("does_not_exist", &interner);
        assert!(matches!(
            outcome,
            Err(InterpreterError::InvalidOperation(_))
        ));
    }

    #[test]
    fn run_item_executes_the_function_with_that_id_not_by_name() {
        // Two functions named `main` would be a duplicate-definition
        // diagnostic within one real module, but a multi-module
        // project's *merged* NIR can legitimately contain two
        // functions that both happen to be named `main` (one per
        // module) -- run_item must run the specific one the caller
        // already resolved to, never search by name.
        let mut map = SourceMap::new();
        let id = map.add_file(
            "t.npt",
            "func main() -> i64 { return 1 } func other_main() -> i64 { return 2 }",
        );
        let mut interner = Interner::new();
        let (tokens, _) = tokenize(map.get(id).content(), id, &mut interner);
        let (module, _) = Parser::new(tokens, id, &mut interner).parse_module();
        let (hir, _) = lower_hir(&module, id, &interner);
        let result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        let nir = lower_nir(
            &hir,
            &result.local_types,
            &result.expr_types,
            &result.pattern_case,
            &result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &BTreeMap::new(),
            &interner,
            id,
        )
        .expect("expected lowering to succeed");
        let other_main_id = nir
            .functions
            .iter()
            .find(|f| interner.resolve(f.name) == "other_main")
            .expect("other_main should have lowered")
            .id;
        let outcome = Interpreter::new(&nir).run_item(other_main_id);
        assert_eq!(outcome, Ok(Value::Int(2)));
    }

    #[test]
    fn calling_with_too_few_arguments_is_an_error_not_a_silent_partial_bind() {
        // `Vec::zip` would otherwise silently truncate to the shorter
        // side, leaving the missing parameter unbound instead of
        // reporting the actual problem.
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Function, Param, Terminator};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let name = interner.intern("f");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![Function {
                id: ItemId(0),
                name,
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: vec![
                    Param {
                        value: ValueId(0),
                        ty: Ty::I64,
                        take: false,
                    },
                    Param {
                        value: ValueId(1),
                        ty: Ty::I64,
                        take: false,
                    },
                ],
                return_type: Ty::I64,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Return(Some(ValueId(0))),
                }],
            }],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let outcome = Interpreter::new(&module).call("f", &interner, vec![Value::Int(1)]);
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected an arity-mismatch error, got {outcome:?}"
        );
    }

    #[test]
    fn calling_with_too_many_arguments_is_an_error_not_a_silent_drop() {
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Function, Param, Terminator};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let name = interner.intern("f");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![Function {
                id: ItemId(0),
                name,
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: vec![Param {
                    value: ValueId(0),
                    ty: Ty::I64,
                    take: false,
                }],
                return_type: Ty::I64,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Return(Some(ValueId(0))),
                }],
            }],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let outcome =
            Interpreter::new(&module).call("f", &interner, vec![Value::Int(1), Value::Int(2)]);
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected an arity-mismatch error, got {outcome:?}"
        );
    }

    /// Fix 5: `Interpreter::call`/`call_item` are a direct value-level
    /// entry point into a function -- unlike a `Call` instruction, never
    /// mediated by the verifier's own evidence-shape check. A
    /// requirement-bearing function invoked this way with no evidence at
    /// all must fail immediately, with its own diagnosis, rather than
    /// deferred until whatever `protocol.call` inside its body first
    /// tries to index past the end of an empty evidence vector.
    #[test]
    fn calling_a_requirement_bearing_function_with_no_evidence_is_an_immediate_error() {
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Function, Param, Terminator};
        use crate::types::{CapabilityRequirement, Ty};

        let mut interner = Interner::new();
        let name = interner.intern("f");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![Function {
                id: ItemId(0),
                name,
                type_params: Vec::new(),
                requirements: vec![CapabilityRequirement::new(ItemId(1), vec![Ty::I64])],
                params: vec![Param {
                    value: ValueId(0),
                    ty: Ty::I64,
                    take: false,
                }],
                return_type: Ty::I64,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Return(Some(ValueId(0))),
                }],
            }],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let outcome = Interpreter::new(&module).call("f", &interner, vec![Value::Int(1)]);
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected an evidence-count error, got {outcome:?}"
        );
    }

    #[test]
    fn a_function_missing_its_entry_block_is_an_error_not_a_panic() {
        // `function.blocks.first()` would previously accept whichever
        // block happened to be first in the vector, regardless of its
        // id; entry status must come from being `bb0` specifically.
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Function, Terminator};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let name = interner.intern("f");
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![Function {
                id: ItemId(0),
                name,
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: Vec::new(),
                return_type: Ty::Unit,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::Return(None),
                }],
            }],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let outcome = Interpreter::new(&module).call("f", &interner, Vec::new());
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected a missing-entry-block error, got {outcome:?}"
        );
    }

    #[test]
    fn record_values_cross_function_boundaries() {
        let text = "record User { id: i64, enabled: bool } \
                     func identity(u: User) -> User { return u } \
                     func main() -> i64 { \
                         value u = User { id: 42, enabled: true }; \
                         return identity(u).id \
                     }";
        assert_eq!(run(text), Ok(Value::Int(42)));
    }

    #[test]
    fn field_access_reads_the_correct_field_regardless_of_construction_order() {
        let text = "record Point { x: i64, y: i64 } \
                     func main() -> i64 { \
                         value p = Point { y: 2, x: 40 }; \
                         return p.x + p.y \
                     }";
        assert_eq!(run(text), Ok(Value::Int(42)));
    }

    #[test]
    fn variant_values_cross_function_boundaries() {
        let text = "variant LookupResult { Found(i64), Missing } \
                     func identity(r: LookupResult) -> LookupResult { return r } \
                     func main() -> i64 { \
                         value r = identity(LookupResult.Found(42)); \
                         return match r { Found(v) => v, Missing => 0 } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(42)));
    }

    #[test]
    fn nested_aggregates_execute_correctly() {
        let text = "record User { id: i64 } \
                     variant LookupResult { Found(User), Missing } \
                     func main() -> i64 { \
                         value user = User { id: 42 }; \
                         value result = LookupResult.Found(user); \
                         return match result { \
                             Found(u) => u.id, \
                             Missing => 0, \
                         } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(42)));
    }

    #[test]
    fn match_executes_only_the_matching_variant_arm() {
        let text = "variant Shape { Circle(i64), Square(i64) } \
                     func main() -> i64 { \
                         value s = Shape.Square(7); \
                         return match s { Circle(v) => v * 100, Square(v) => v * 10 } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(70)));
    }

    #[test]
    fn match_wildcard_fallback_is_used_when_no_case_matches() {
        let text = "variant Shape { Circle(i64), Square(i64), Triangle } \
                     func main() -> i64 { \
                         value s = Shape.Triangle; \
                         return match s { Circle(v) => v, Square(v) => v, _ => 99 } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(99)));
    }

    #[test]
    fn match_returns_a_value_used_by_the_caller() {
        let text = "func main() -> i64 { return 1 + match true { true => 41, false => 0 } }";
        assert_eq!(run(text), Ok(Value::Int(42)));
    }

    #[test]
    fn match_with_one_diverging_arm_still_returns_the_other_arms_value() {
        let text = "variant Shape { Circle(i64), Empty } \
                     func f(s: Shape) -> i64 { \
                         return match s { \
                             Circle(v) => v, \
                             Empty => return 42, \
                         } \
                     } \
                     func main() -> i64 { return f(Shape.Circle(7)) }";
        assert_eq!(run(text), Ok(Value::Int(7)));
    }

    #[test]
    fn fully_diverging_match_never_produces_a_fabricated_value() {
        let text = "variant Shape { Circle, Empty } \
                     func f(s: Shape) -> i64 { \
                         match s { \
                             Circle => return 1, \
                             Empty => return 2, \
                         } \
                     } \
                     func main() -> i64 { return f(Shape.Empty) }";
        assert_eq!(run(text), Ok(Value::Int(2)));
    }

    #[test]
    fn nested_variant_pattern_extracts_the_correct_payload() {
        let text = "variant Inner { X, Y } \
                     variant Outer { A(Inner), B } \
                     func main() -> i64 { \
                         value o = Outer.A(Inner.Y); \
                         return match o { \
                             A(X) => 1, \
                             A(Y) => 2, \
                             B => 3, \
                         } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(2)));
    }

    #[test]
    fn malformed_switch_on_a_non_variant_value_is_an_error_not_a_panic() {
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Instruction};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let name = interner.intern("f");
        let variant = ItemId(1);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![Function {
                id: ItemId(0),
                name,
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: Vec::new(),
                return_type: Ty::I64,
                raises: Vec::new(),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![Instruction::Value {
                            result: ValueId(0),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(1)),
                        }],
                        terminator: Terminator::Switch {
                            scrutinee: ValueId(0),
                            variant,
                            cases: vec![BlockId(1), BlockId(1)],
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: Terminator::Return(Some(ValueId(0))),
                    },
                ],
            }],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let outcome = Interpreter::new(&module).call("f", &interner, Vec::new());
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected a structured error, not a panic, got {outcome:?}"
        );
    }

    #[test]
    fn malformed_record_field_projection_on_the_wrong_record_is_an_error_not_a_panic() {
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Instruction};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let name = interner.intern("f");
        let record_a = ItemId(1);
        let record_b = ItemId(2);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![Function {
                id: ItemId(0),
                name,
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: Vec::new(),
                return_type: Ty::I64,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(1)),
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::Named(record_a, name),
                            kind: ValueKind::RecordCreate(record_a, Vec::new(), vec![ValueId(0)]),
                        },
                        Instruction::Value {
                            result: ValueId(2),
                            ty: Ty::I64,
                            kind: ValueKind::RecordField {
                                base: ValueId(1),
                                record: record_b,
                                field: 0,
                            },
                        },
                    ],
                    terminator: Terminator::Return(Some(ValueId(2))),
                }],
            }],
            records: Vec::new(),
            variants: Vec::new(),
        };
        let outcome = Interpreter::new(&module).call("f", &interner, Vec::new());
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected a structured error, not a panic, got {outcome:?}"
        );
    }

    // -- Deterministic cleanup order (`rfcs/0011`) -----------------------

    #[test]
    fn multiple_defers_run_in_reverse_registration_order_interleaved_with_drops() {
        // `rfcs/0011`'s own LIFO rule ("Multiple `defer`s in one scope
        // run in LIFO order... the same reverse-declaration-order
        // discipline implicit resource destruction itself follows, so
        // the two interleave in exactly the declaration-reversed order")
        // is only exercised end-to-end when a `defer` sits *between* two
        // resource declarations, not after both: the declaration order
        // here is `a`, `defer(a)`, `b`, `defer(b)`, so its exact reverse
        // is `defer(b)`, `b`'s own implicit drop, `defer(a)`, `a`'s own
        // implicit drop.
        let text = "resource File { descriptor: i64 } \
                     func inspect(file: File) -> i64 { return file.descriptor } \
                     func main() -> i64 { \
                         value a = File { descriptor: 1 }; \
                         defer inspect(a); \
                         value b = File { descriptor: 2 }; \
                         defer inspect(b); \
                         return 0; \
                     }";
        let (outcome, log) = run_with_log(text);
        assert_eq!(outcome, Ok(Value::Int(0)));
        assert_eq!(
            log,
            vec!["call:inspect", "drop:1", "call:inspect", "drop:0"],
            "expected declaration-reversed interleaving of defers and drops, \
             not defers and drops running as two separate groups"
        );
    }

    #[test]
    fn a_consuming_defer_runs_exactly_once_at_scope_exit() {
        // `consume`'s own `take file` parameter is never explicitly
        // dropped in its body, so it is implicitly dropped exactly once
        // inside `consume`'s own frame (matching
        // `an_unmoved_resource_local_is_implicitly_dropped_at_function_exit`
        // in `nir::lower`'s tests) -- the caller's frame performs no
        // destruction of its own for `file`, since the `defer` already
        // moved it out at registration time.
        let text = "resource File { descriptor: i64 } \
                     func consume(take file: File) -> i64 { return file.descriptor } \
                     func main() -> i64 { \
                         value file = File { descriptor: 7 }; \
                         defer consume(file); \
                         return 0; \
                     }";
        let (outcome, log) = run_with_log(text);
        assert_eq!(outcome, Ok(Value::Int(0)));
        assert_eq!(
            log,
            vec!["call:consume", "drop:0"],
            "consume's own take parameter must be dropped exactly once, inside \
             consume itself, with no separate drop in the caller's own frame"
        );
    }

    // -- Runtime resource identity (`rfcs/0011`, Blocker 8) -------------
    //
    // `resourceck`/`nir::verify` already reject every one of these
    // shapes before a real program's NIR reaches the interpreter at
    // all -- these two exist to prove the interpreter's own
    // `ResourceTable` independently refuses them too, reached here only
    // through hand-built NIR that bypasses the checker on purpose. Each
    // hand-builds a second local (`ValueId(1)`, via `Load`) that
    // aliases the exact same resource record as `ValueId(0)`: an
    // ordinary Rust `Clone` of a `Value::Resource` duplicates only the
    // cheap handle, never the resource's own identity, so the table
    // must still recognize both locals as the same underlying record.

    #[test]
    fn a_resource_dropped_through_two_aliased_handles_is_an_error_not_a_panic() {
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Instruction, RecordLayout};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![Function {
                id: ItemId(0),
                name,
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: Vec::new(),
                return_type: Ty::Unit,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: resource_ty.clone(),
                            kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: resource_ty,
                            kind: ValueKind::Load(ValueId(0)),
                        },
                        Instruction::Drop { value: ValueId(0) },
                        Instruction::Drop { value: ValueId(1) },
                    ],
                    terminator: Terminator::Return(None),
                }],
            }],
            records: vec![(
                resource,
                RecordLayout {
                    name: resource_name,
                    type_params: Vec::new(),
                    fields: Vec::new(),
                    affine: true,
                },
            )],
            variants: Vec::new(),
        };
        let outcome = Interpreter::new(&module).call("f", &interner, Vec::new());
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected a structured double-drop error, not a panic, got {outcome:?}"
        );
    }

    #[test]
    fn a_stale_resource_handle_left_behind_by_a_take_call_is_an_error_not_a_panic() {
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Instruction, Param, RecordLayout};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let sink_name = interner.intern("sink");
        let resource_name = interner.intern("File");
        let resource = ItemId(2);
        let f = ItemId(0);
        let sink = ItemId(1);
        let resource_ty = Ty::Named(resource, resource_name);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![
                Function {
                    id: f,
                    name: f_name,
                    type_params: Vec::new(),
                    requirements: Vec::new(),
                    params: Vec::new(),
                    return_type: Ty::Unit,
                    raises: Vec::new(),
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        instructions: vec![
                            Instruction::Value {
                                result: ValueId(0),
                                ty: resource_ty.clone(),
                                kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                            },
                            // Aliases `ValueId(0)`'s own handle *before*
                            // the call below transfers it away -- this
                            // local's own copy is left stale the moment
                            // the transfer happens, same as `ValueId(0)`
                            // itself, even though nothing here re-reads
                            // `ValueId(0)` again to prove it.
                            Instruction::Value {
                                result: ValueId(1),
                                ty: resource_ty.clone(),
                                kind: ValueKind::Load(ValueId(0)),
                            },
                            Instruction::Value {
                                result: ValueId(2),
                                ty: Ty::Unit,
                                kind: ValueKind::Call(
                                    sink,
                                    Vec::new(),
                                    vec![ValueId(0)],
                                    Vec::new(),
                                ),
                            },
                            Instruction::Drop { value: ValueId(1) },
                        ],
                        terminator: Terminator::Return(None),
                    }],
                },
                Function {
                    id: sink,
                    name: sink_name,
                    type_params: Vec::new(),
                    requirements: Vec::new(),
                    params: vec![Param {
                        value: ValueId(0),
                        ty: resource_ty.clone(),
                        take: true,
                    }],
                    return_type: Ty::Unit,
                    raises: Vec::new(),
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Return(None),
                    }],
                },
            ],
            records: vec![(
                resource,
                RecordLayout {
                    name: resource_name,
                    type_params: Vec::new(),
                    fields: Vec::new(),
                    affine: true,
                },
            )],
            variants: Vec::new(),
        };
        let outcome = Interpreter::new(&module).call("f", &interner, Vec::new());
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected a structured stale-handle error, not a panic, got {outcome:?}"
        );
    }

    #[test]
    fn a_frame_that_returns_while_still_owning_a_resource_is_an_error_not_a_panic() {
        // This function constructs a resource and returns without ever
        // dropping or transferring it away -- `resourceck`/`nir::verify`
        // both already statically forbid a well-typed source program
        // from reaching this shape at all, so this hand-built module
        // exercises the interpreter's own independent frame-exit
        // backstop directly, never relying on either static guarantee.
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Instruction, RecordLayout};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let f = ItemId(0);
        let resource_ty = Ty::Named(resource, resource_name);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![Function {
                id: f,
                name: f_name,
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: Vec::new(),
                return_type: Ty::Unit,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(0),
                        ty: resource_ty.clone(),
                        kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                    }],
                    terminator: Terminator::Return(None),
                }],
            }],
            records: vec![(
                resource,
                RecordLayout {
                    name: resource_name,
                    type_params: Vec::new(),
                    fields: Vec::new(),
                    affine: true,
                },
            )],
            variants: Vec::new(),
        };
        let outcome = Interpreter::new(&module).call("f", &interner, Vec::new());
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "expected a structured frame-exit leak error, not a panic, got {outcome:?}"
        );
    }

    #[test]
    fn an_ordinary_parameters_own_observation_is_never_a_frame_exit_leak() {
        // `file` is an ordinary (non-`take`) parameter: this frame never
        // owns it, so returning without dropping or transferring it is
        // entirely correct -- proving `leaked_resource`'s own exclusion
        // of observing parameters actually holds, not just that a
        // constructed-and-abandoned resource is caught.
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Param, RecordLayout};
        use crate::types::Ty;

        let mut interner = Interner::new();
        let f_name = interner.intern("f");
        let resource_name = interner.intern("File");
        let resource = ItemId(1);
        let f = ItemId(0);
        let resource_ty = Ty::Named(resource, resource_name);
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            functions: vec![Function {
                id: f,
                name: f_name,
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: vec![Param {
                    value: ValueId(0),
                    ty: resource_ty.clone(),
                    take: false,
                }],
                return_type: Ty::Unit,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Return(None),
                }],
            }],
            records: vec![(
                resource,
                RecordLayout {
                    name: resource_name,
                    type_params: Vec::new(),
                    fields: Vec::new(),
                    affine: true,
                },
            )],
            variants: Vec::new(),
        };
        let interpreter = Interpreter::new(&module);
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(resource, Vec::new());
        let outcome = interpreter.call_function(
            &module.functions[0],
            vec![Value::Resource(handle)],
            Vec::new(),
        );
        assert!(
            matches!(outcome, Ok(Outcome::Returned(Value::Unit))),
            "an ordinary parameter's own observation must never be a frame-exit leak"
        );
    }

    // -- Generic execution (`rfcs/0008`) --------------------------------

    #[test]
    fn a_generic_identity_function_runs_end_to_end() {
        assert_eq!(
            run(
                "func identity[T](x: T) -> T { return x } func main() -> i64 { return identity[i64](42) }"
            ),
            Ok(Value::Int(42))
        );
    }

    #[test]
    fn a_generic_record_construction_and_field_access_runs_end_to_end() {
        assert_eq!(
            run("record Box[T] { payload: T } \
                 func main() -> i64 { value b = Box[i64] { payload: 42 }; return b.payload }"),
            Ok(Value::Int(42))
        );
    }

    #[test]
    fn a_generic_variant_construction_and_exhaustive_match_runs_end_to_end() {
        assert_eq!(
            run("variant Maybe[T] { Some(T), None } \
                 func main() -> i64 { \
                     return match Maybe[i64].Some(42) { \
                         Some(n) => n, \
                         None => 0, \
                     } \
                 }"),
            Ok(Value::Int(42))
        );
    }

    #[test]
    fn a_bare_generic_unit_case_runs_end_to_end() {
        assert_eq!(
            run("variant Maybe[T] { Some(T), None } \
                 func main() -> i64 { \
                     return match Maybe[i64].None { \
                         Some(n) => n, \
                         None => 7, \
                     } \
                 }"),
            Ok(Value::Int(7))
        );
    }

    #[test]
    fn a_generic_record_nested_inside_another_generic_record_runs_end_to_end() {
        assert_eq!(
            run("record Box[T] { payload: T } \
                 variant Maybe[T] { Some(T), None } \
                 func main() -> i64 { \
                     value b = Box[Maybe[i64]] { payload: Maybe[i64].Some(42) }; \
                     return match b.payload { \
                         Some(n) => n, \
                         None => 0, \
                     } \
                 }"),
            Ok(Value::Int(42))
        );
    }

    #[test]
    fn distinct_generic_instantiations_do_not_confuse_each_others_runtime_values() {
        // `Box[i64]` and `Box[bool]` share one lowered `Box` layout at
        // runtime (generics erase at runtime, `rfcs/0008`) -- this must
        // never let a `bool`'s runtime representation be misread as an
        // `i64` or vice versa.
        assert_eq!(
            run("record Box[T] { payload: T } \
                 func unwrap_bool(b: Box[bool]) -> bool { return b.payload } \
                 func main() -> i64 { \
                     value flag = Box[bool] { payload: true }; \
                     value number = Box[i64] { payload: 42 }; \
                     return if unwrap_bool(flag) { number.payload } else { 0 } \
                 }"),
            Ok(Value::Int(42))
        );
    }

    // -- Typed outcomes: raise/?/handle (`rfcs/0010`) -------------------

    #[test]
    fn a_handled_raise_runs_the_matching_failure_arm() {
        let text = "variant FileError { Missing, PermissionDenied } \
                     func read(ok: bool) -> i64 raises FileError { \
                         if ok { return 42 } \
                         raise FileError.Missing; \
                     } \
                     func main() -> i64 { \
                         return handle read(false) { \
                             success v => v, \
                             failure FileError.Missing => -1, \
                             failure FileError.PermissionDenied => -2, \
                         } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(-1)));
    }

    #[test]
    fn a_handled_success_runs_the_success_arm() {
        let text = "variant FileError { Missing } \
                     func read(ok: bool) -> i64 raises FileError { \
                         if ok { return 42 } \
                         raise FileError.Missing; \
                     } \
                     func main() -> i64 { \
                         return handle read(true) { \
                             success v => v, \
                             failure _ => -1, \
                         } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(42)));
    }

    #[test]
    fn postfix_try_forwards_a_raised_value_to_the_caller_unchanged() {
        let text = "variant FileError { Missing } \
                     func read(ok: bool) -> i64 raises FileError { \
                         if ok { return 42 } \
                         raise FileError.Missing; \
                     } \
                     func forward(ok: bool) -> i64 raises FileError { \
                         return read(ok)?; \
                     } \
                     func main() -> i64 { \
                         return handle forward(false) { \
                             success v => v, \
                             failure FileError.Missing => -7, \
                         } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(-7)));
    }

    #[test]
    fn postfix_try_forwards_a_success_value_to_the_caller_unchanged() {
        let text = "variant FileError { Missing } \
                     func read(ok: bool) -> i64 raises FileError { \
                         if ok { return 42 } \
                         raise FileError.Missing; \
                     } \
                     func forward(ok: bool) -> i64 raises FileError { \
                         return read(ok)?; \
                     } \
                     func main() -> i64 { \
                         return handle forward(true) { \
                             success v => v, \
                             failure FileError.Missing => -7, \
                         } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(42)));
    }

    #[test]
    fn handle_dispatches_the_right_case_among_multiple_raised_variants() {
        let text = "variant FileError { Missing, PermissionDenied } \
                     variant NetworkError { Timeout } \
                     func read(mode: i64) -> i64 raises FileError, NetworkError { \
                         if mode == 0 { return 42 } \
                         if mode == 1 { raise FileError.Missing; } \
                         if mode == 2 { raise FileError.PermissionDenied; } \
                         raise NetworkError.Timeout; \
                     } \
                     func run_with(mode: i64) -> i64 { \
                         return handle read(mode) { \
                             success v => v, \
                             failure FileError.Missing => -1, \
                             failure FileError.PermissionDenied => -2, \
                             failure NetworkError.Timeout => -3, \
                         } \
                     } \
                     func main() -> i64 { \
                         return run_with(0) * 1000 + run_with(1) * 100 + run_with(2) * 10 + run_with(3) \
                     }";
        assert_eq!(run(text), Ok(Value::Int(42000 - 100 - 20 - 3)));
    }

    #[test]
    fn handle_wildcard_covers_a_case_carrying_a_payload() {
        let text = "variant FileError { Missing(i64), PermissionDenied } \
                     func read(ok: bool) -> i64 raises FileError { \
                         if ok { return 42 } \
                         raise FileError.Missing(9); \
                     } \
                     func main() -> i64 { \
                         return handle read(false) { \
                             success v => v, \
                             failure _ => -1, \
                         } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(-1)));
    }

    #[test]
    fn handle_binds_a_raised_cases_payload() {
        let text = "variant FileError { Missing(i64) } \
                     func read(ok: bool) -> i64 raises FileError { \
                         if ok { return 42 } \
                         raise FileError.Missing(9); \
                     } \
                     func main() -> i64 { \
                         return handle read(false) { \
                             success v => v, \
                             failure FileError.Missing(code) => code, \
                         } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(9)));
    }

    #[test]
    fn a_raise_inside_a_handled_arms_own_body_is_not_implicitly_caught() {
        // A nested fallible call's own raise inside a `handle` arm's body
        // needs its own `?`/`handle` -- the enclosing `handle` only ever
        // dispatches on its own direct operand, never on anything a
        // sibling arm's body happens to also raise.
        let text = "variant FileError { Missing } \
                     func read(ok: bool) -> i64 raises FileError { \
                         if ok { return 42 } \
                         raise FileError.Missing; \
                     } \
                     func outer() -> i64 raises FileError { \
                         return handle read(true) { \
                             success v => read(false)?, \
                             failure FileError.Missing => -1, \
                         } \
                     } \
                     func main() -> i64 { \
                         return handle outer() { \
                             success v => v, \
                             failure FileError.Missing => -9, \
                         } \
                     }";
        assert_eq!(run(text), Ok(Value::Int(-9)));
    }

    // -- Fix 3: diverging operands under `?`/`handle` (`rfcs/0010`) -----

    #[test]
    fn postfix_try_with_a_diverging_argument_returns_through_the_argument_exactly_once() {
        // `read` is never actually invoked -- the argument's own `return`
        // ends `main` first, exactly once, before the fallible call (and
        // therefore the postfix `?` after it) is ever reached.
        let text = "variant FileError { Missing } \
                     func read(path: str) -> str raises FileError { \
                         if path == \"\" { raise FileError.Missing; } \
                         return \"ok\"; \
                     } \
                     func main() -> i64 { \
                         return read({ return 7 })?; \
                     }";
        assert_eq!(run(text), Ok(Value::Int(7)));
    }

    #[test]
    fn handle_with_a_diverging_argument_returns_through_the_argument_exactly_once() {
        let text = "variant FileError { Missing } \
                     func read(path: str) -> str raises FileError { \
                         if path == \"\" { raise FileError.Missing; } \
                         return \"ok\"; \
                     } \
                     func main() -> i64 { \
                         return handle read({ return 7 }) { \
                             success v => 1, \
                             failure FileError.Missing => 2, \
                         }; \
                     }";
        assert_eq!(run(text), Ok(Value::Int(7)));
    }
}
