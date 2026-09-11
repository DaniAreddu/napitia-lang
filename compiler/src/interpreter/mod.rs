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
use crate::nir::{Const, Function, Module, OwnershipMode, Terminator, ValueId, ValueKind};
use crate::place::{Place, Projection};
use crate::symbol::Interner;
use crate::types::{Evidence, Ty};

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
/// Whether a [`ResourceHandle`] currently grants owning or merely
/// observing access to its own resource (`rfcs/0011`) -- carried on the
/// handle itself, independently of `nir::verify`'s own static role
/// tracking, so the interpreter never has to trust that a module it is
/// running actually passed verification: an owning operation (`take`,
/// `Move`/`DeferCapture`, `store.transfer`, `Drop`, `return`) attempted
/// through an `Observer` handle is rejected here too, as a structured
/// error, not merely a diagnosed-away compile-time concern.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RuntimeOwnershipRole {
    Owner,
    Observer,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResourceHandle {
    id: ResourceId,
    generation: u64,
    role: RuntimeOwnershipRole,
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
        ResourceHandle {
            id,
            generation: 0,
            role: RuntimeOwnershipRole::Owner,
        }
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
    /// neither may ever be legitimately read. Deliberately independent
    /// of `handle`'s own `role`: both an owner and an observer may
    /// always read (`rfcs/0011`) -- only *consuming* operations
    /// (`transfer`/`drop_resource`, below) are role-gated.
    fn observe(&self, handle: ResourceHandle) -> Result<&ResourceRecord, InterpreterError> {
        let record = self.record(handle)?;
        if record.status == ResourceStatus::Dropped {
            return Err(invalid("use of a resource after it was already dropped"));
        }
        Ok(record)
    }

    /// Downgrades `handle` to a merely-observing reference to the same
    /// current record (`rfcs/0011`): every ordinary (non-`take`)
    /// parameter binding, and every `store.observe`'d value, produces
    /// one of these rather than reusing the original handle as-is --
    /// otherwise an owner passed into an observing context would still
    /// carry owning access there, letting a merely-observing reference
    /// illegally `Drop`/transfer the very resource it was only supposed
    /// to observe. Still rejects a stale handle or an already-dropped
    /// resource, exactly like [`Self::observe`].
    fn to_observer(&self, handle: ResourceHandle) -> Result<ResourceHandle, InterpreterError> {
        self.observe(handle)?;
        Ok(ResourceHandle {
            id: handle.id,
            generation: handle.generation,
            role: RuntimeOwnershipRole::Observer,
        })
    }

    /// Transfers ownership of `handle`'s own resource to a new owner
    /// (Blocker 8: a `take` argument at registration/call time, or a
    /// returned resource) -- bumps the table's own current generation
    /// for this resource, invalidating `handle` (and every other
    /// handle still referencing the generation it was minted from),
    /// and returns the fresh handle identifying the current owner.
    /// Rejects `handle` outright if it is only an `Observer`: an
    /// observation must never be silently promoted into an owner, no
    /// matter what `nir::verify` already statically guarantees about
    /// the module this frame happens to be executing.
    fn transfer(&mut self, handle: ResourceHandle) -> Result<ResourceHandle, InterpreterError> {
        if handle.role != RuntimeOwnershipRole::Owner {
            return Err(invalid(
                "cannot transfer ownership through a merely-observing resource handle",
            ));
        }
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
            role: RuntimeOwnershipRole::Owner,
        })
    }

    /// Destroys `handle`'s own resource exactly once (Blocker 8): a
    /// stale handle, an already-dropped resource, or an unknown handle
    /// are each their own distinct rejected case, never silently
    /// treated as success. Rejects `handle` outright if it is only an
    /// `Observer`, for the same reason [`Self::transfer`] does.
    fn drop_resource(&mut self, handle: ResourceHandle) -> Result<(), InterpreterError> {
        if handle.role != RuntimeOwnershipRole::Owner {
            return Err(invalid(
                "cannot drop a resource through a merely-observing resource handle",
            ));
        }
        let id = handle.id;
        let record = self.record(handle)?;
        if record.status == ResourceStatus::Dropped {
            return Err(invalid("double drop of a resource"));
        }
        self.records[id.0 as usize].status = ResourceStatus::Dropped;
        Ok(())
    }

    /// Reads `handle`'s own field at `index` without disturbing it
    /// (`rfcs/0012`) -- legal through both an `Owner` and an `Observer`
    /// handle, exactly like reading the resource's own top-level
    /// identity already is ([`Self::observe`]).
    fn observe_field(
        &self,
        handle: ResourceHandle,
        index: usize,
    ) -> Result<Value, InterpreterError> {
        let record = self.observe(handle)?;
        record
            .fields
            .get(index)
            .cloned()
            .ok_or_else(|| invalid("a place projects a field index out of range for this resource"))
    }

    /// Removes `handle`'s own field at `index`, leaving a
    /// [`Value::Moved`] tombstone behind, and returns the removed value
    /// (`rfcs/0012`) -- only ever legal through an `Owner` handle:
    /// transferring a field out through a merely-observing handle would
    /// let an observer silently grant itself ownership of something it
    /// was only ever supposed to read.
    fn take_field(
        &mut self,
        handle: ResourceHandle,
        index: usize,
    ) -> Result<Value, InterpreterError> {
        if handle.role != RuntimeOwnershipRole::Owner {
            return Err(invalid(
                "cannot transfer a field through a merely-observing resource handle",
            ));
        }
        let record = self.observe(handle)?;
        let _ = record;
        let slot = self.records[handle.id.0 as usize]
            .fields
            .get_mut(index)
            .ok_or_else(|| {
                invalid("a place projects a field index out of range for this resource")
            })?;
        Ok(std::mem::replace(slot, Value::Moved))
    }

    /// Overwrites `handle`'s own field at `index` with `value`
    /// (`rfcs/0012`, structural reinitialization) -- only ever legal
    /// through an `Owner` handle, for the same reason
    /// [`Self::take_field`] is. Defensively rejects overwriting a field
    /// that is not currently a tombstone (`Moved`/`Dropped`): `nir::
    /// verify` already statically guarantees `StorePlace` only ever
    /// targets a provably-empty place, but this stage never trusts that
    /// blindly either.
    fn set_field(
        &mut self,
        handle: ResourceHandle,
        index: usize,
        value: Value,
    ) -> Result<(), InterpreterError> {
        if handle.role != RuntimeOwnershipRole::Owner {
            return Err(invalid(
                "cannot reinitialize a field through a merely-observing resource handle",
            ));
        }
        let record = self.observe(handle)?;
        let _ = record;
        let slot = self.records[handle.id.0 as usize]
            .fields
            .get_mut(index)
            .ok_or_else(|| {
                invalid("a place projects a field index out of range for this resource")
            })?;
        if !matches!(slot, Value::Moved | Value::Dropped) {
            return Err(invalid(
                "cannot overwrite a resource field that still owns a live value",
            ));
        }
        *slot = value;
        Ok(())
    }

    /// Writes `container` back into `handle`'s own field at `index`
    /// after a place traversal passed *through* it (`rfcs/0012`) --
    /// deliberately **not** [`Self::set_field`]: that one is the
    /// user-facing structural reinitialization primitive `StorePlace`
    /// lowers to, and correctly refuses to overwrite a field that still
    /// owns a live value. This one is the internal, transactional
    /// counterpart: the field genuinely *is* still live here (the
    /// traversal only ever reached deeper *through* it), and what is
    /// being written back is that very same container with at most one
    /// of its own descendants tombstoned. Conflating the two is exactly
    /// what made a mixed `resource` -> `record` chain report a bogus
    /// live-overwrite error.
    ///
    /// Still `Owner`-gated, exactly like [`Self::take_field`]/
    /// [`Self::set_field`]: a merely-observing handle must never be able
    /// to write through an intermediate container either, or a
    /// `record` -> `resource` -> `field` transfer reached through an
    /// observer would silently grant itself ownership. Only ever called
    /// *after* the recursion it accompanies already succeeded, so a
    /// failure deeper in the chain leaves this field exactly as it was
    /// rather than half-mutated.
    fn restore_field(
        &mut self,
        handle: ResourceHandle,
        index: usize,
        container: Value,
    ) -> Result<(), InterpreterError> {
        if handle.role != RuntimeOwnershipRole::Owner {
            return Err(invalid(
                "cannot write through a merely-observing resource handle",
            ));
        }
        self.observe(handle)?;
        let slot = self.records[handle.id.0 as usize]
            .fields
            .get_mut(index)
            .ok_or_else(|| {
                invalid("a place projects a field index out of range for this resource")
            })?;
        *slot = container;
        Ok(())
    }
}

/// One recursive place-traversal step's own complete result
/// (`rfcs/0012`): the value actually read or removed at the place's own
/// final projection, *and* the container this step was handed, in
/// exactly the state it must now be written back into whatever slot it
/// came from.
///
/// `container` is always present, and always meaningful -- never an
/// `Option` doing double duty for both "the caller must write this
/// back" and "this container's own ownership disappeared." For a
/// `resource` intermediate the mutation already happened directly in
/// the resource table, and `container` is that same
/// [`Value::Resource`] handle, unchanged, so the caller reinserting it
/// into its own parent slot keeps the handle exactly where it belongs
/// instead of tombstoning a live resource out of its owner.
struct AccessResult {
    extracted: Value,
    container: Value,
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
        /// This value's own *concrete* type arguments, in the
        /// declaration's own parameter order (`rfcs/0008`) -- empty for
        /// a non-generic record.
        ///
        /// Carried on the value itself, not re-derived, because
        /// `item` alone cannot answer what this aggregate owns: `Box`'s
        /// own declared field type is the symbolic `Ty::Param(T)`, and
        /// asking whether *that* is affine answers "no" for every
        /// instantiation, `Box[File]` included. Never inferred from the
        /// payload values either -- a moved-out field is a tombstone
        /// with no type left to read, so a value that has already given
        /// up a field could no longer say what it is.
        type_args: Vec<Ty>,
        fields: Vec<Value>,
    },
    /// A variant value: `case` is the declaration index of its active
    /// case, and `payload` holds that case's payload values in
    /// declaration order (empty for a unit case).
    Variant {
        item: ItemId,
        /// See [`Value::Record::type_args`] -- identical role, and
        /// identically load-bearing: a `Maybe[File]` whose payload is
        /// declared `Ty::Param(T)` owns a resource, and a `Maybe[i64]`
        /// does not.
        type_args: Vec<Ty>,
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
    /// A structural tombstone (`rfcs/0012`, Alpha 0.1.8) left behind in
    /// exactly the field slot a `PlaceRead { mode: Transfer }` just took
    /// ownership out of, inside a plain `Record`/`Variant` value (a
    /// `resource`'s own fields are tombstoned directly in its
    /// `ResourceTable` record instead -- see [`ResourceRecord::fields`]
    /// -- since they are never held inline the way an ordinary
    /// aggregate's are). Reading a `Moved` field is a structured runtime
    /// error, never a silent `Unit`/default value -- `nir::verify`
    /// already statically guarantees this can never happen for verified
    /// NIR; this is this stage's own independent backstop, not a
    /// substitute for it.
    Moved,
    /// Like [`Value::Moved`], but left by the recursive structural
    /// destruction a `Drop` of an enclosing aggregate applies to each of
    /// its own still-live affine fields (`rfcs/0012`) -- distinguished
    /// from `Moved` only for a clearer error message on a later
    /// (already-impossible, for verified NIR) use.
    Dropped,
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

    /// `true` iff `ty` is transitively affine (`rfcs/0012`) -- mirrors
    /// `nir::lower`'s/`resourceck`'s identical query, independently
    /// recomputed from this module's own `records`/`variants` layouts
    /// (never a generic-instantiation-aware substitution here: this is
    /// only ever consulted while destroying an *already-constructed*
    /// runtime `Variant` value's own active-case payload, whose payload
    /// types come from that one concrete case's own declared shape).
    /// Guarded against a genuinely cyclic declaration the same way every
    /// other stage's identical query is: a cycle back-edge contributes
    /// `false` to that one occurrence alone, never cached (this is not
    /// called densely enough to need memoizing).
    fn is_affine(&self, ty: &Ty) -> bool {
        self.is_affine_visiting(ty, &mut HashSet::new(), 0)
    }

    fn is_affine_visiting(&self, ty: &Ty, visiting: &mut HashSet<ItemId>, depth: usize) -> bool {
        // For a `Ty::Applied` this is the *only* termination guard:
        // `visiting` is keyed by bare `ItemId` and so cannot tell a
        // genuine cycle apart from a legitimately nested instantiation
        // of the same declaration -- `Box[Box[Box[File]]]` reaches
        // `Box` three times with different arguments and must answer
        // from the innermost one.
        if depth >= crate::limits::MAX_GENERIC_DEPTH {
            return false;
        }
        let item = match ty {
            Ty::Named(item, _) => *item,
            // A generic instantiation's own affinity depends on what it
            // was instantiated *with* (`Box[File]` is affine, `Box[i64]`
            // is not), so its own arguments are substituted into the
            // declaration's field types before recursing -- never
            // silently answered `false`, which would leave a
            // `Box[File]` looking freely copyable at runtime.
            Ty::Applied(item, args) => {
                if self.is_resource(*item) {
                    return true;
                }
                // Missing or arity-disagreeing generic metadata fails
                // *closed*, to affine: an unsubstituted `Ty::Param`
                // would answer `false` below and let a genuinely affine
                // instantiation be treated as a freely-copyable value
                // this stage never destroys -- the one direction that
                // leaks rather than over-demands.
                let Some(subst) = self.type_substitution(*item, args) else {
                    return true;
                };
                return self.item_field_types(*item).iter().any(|fty| {
                    self.is_affine_visiting(
                        &crate::types::substitute(fty, &subst),
                        visiting,
                        depth + 1,
                    )
                });
            }
            _ => return false,
        };
        if self.is_resource(item) {
            return true;
        }
        if !visiting.insert(item) {
            return false;
        }
        let result = self
            .item_field_types(item)
            .iter()
            .any(|fty| self.is_affine_visiting(fty, visiting, depth + 1));
        visiting.remove(&item);
        result
    }

    /// `item`'s own declared type parameters paired with `args`, for
    /// substituting a generic aggregate's own declared field types down
    /// to this one instantiation's concrete shape (`rfcs/0008`).
    /// `None` -- never a partial or empty map -- when `item` has no
    /// recorded layout at all, or when its declared arity disagrees with
    /// `args`: an unmapped `Ty::Param` would stay symbolic and answer
    /// "not affine", which is the one direction that leaks.
    fn type_substitution(
        &self,
        item: ItemId,
        args: &[Ty],
    ) -> Option<std::collections::HashMap<crate::hir::TypeParamId, Ty>> {
        let params: Vec<crate::hir::TypeParamId> = self
            .module
            .records
            .iter()
            .find(|(id, _)| *id == item)
            .map(|(_, r)| r.type_params.iter().map(|(id, _)| *id).collect())
            .or_else(|| {
                self.module
                    .variants
                    .iter()
                    .find(|(id, _)| *id == item)
                    .map(|(_, v)| v.type_params.iter().map(|(id, _)| *id).collect())
            })?;
        if params.len() != args.len() {
            return None;
        }
        Some(params.into_iter().zip(args.iter().cloned()).collect())
    }

    /// `true` iff this *runtime* value is transitively affine -- what
    /// makes it a legal structural `Drop` target (`rfcs/0012`).
    /// Answered from the value's own dynamic item identity, never from
    /// a static type this stage would otherwise have to be handed.
    fn is_affine_value(&self, value: &Value) -> Result<bool, InterpreterError> {
        let (item, type_args) = match value {
            Value::Resource(_) => return Ok(true),
            Value::Record {
                item, type_args, ..
            }
            | Value::Variant {
                item, type_args, ..
            } => (*item, type_args),
            _ => return Ok(false),
        };
        if self.is_resource(item) {
            return Ok(true);
        }
        // Answered from this value's own *concrete* instantiation, not
        // from its declaration: `Box`'s declared field is `Ty::Param(T)`
        // and is affine for no instantiation at all, while `Box[File]`
        // plainly owns a resource.
        let subst = self.checked_substitution(item, type_args)?;
        let mut visiting = HashSet::new();
        Ok(self.item_field_types(item).iter().any(|fty| {
            self.is_affine_visiting(&crate::types::substitute(fty, &subst), &mut visiting, 0)
        }))
    }

    /// Reads or removes the value at `place`'s own final projection step
    /// (`rfcs/0012`), recursing through zero or more `Value::Record`
    /// ancestors it passes through on the way there and rebuilding each
    /// one, then writing the rebuilt root back into `values[place.root]`
    /// -- a plain record's own fields are held directly, by value, with
    /// no separate addressable identity of their own -- but mutating a
    /// `resource`'s own field storage in place, directly through the
    /// resource table, the moment the walk passes through one, since a
    /// resource's own fields are never held inline (`rfcs/0011`, Blocker
    /// 8). `mode: Observe` never mutates anything at all (only ever
    /// clones); `mode: Transfer` leaves a [`Value::Moved`] tombstone
    /// behind at the exact field it removed.
    fn access_place(
        &self,
        values: &mut HashMap<ValueId, Value>,
        load_origin: &HashMap<ValueId, ValueId>,
        place: &Place<ValueId>,
        mode: OwnershipMode,
    ) -> Result<Value, InterpreterError> {
        let root_id = canonical_root(load_origin, place.root);
        let place = &Place {
            root: root_id,
            projections: place.projections.clone(),
        };
        let root = get(values, &place.root)?;
        match mode {
            // Observing never writes anything back -- not the root, not
            // any intermediate inline record, and not any intermediate
            // resource's own field storage (`rfcs/0012`). Reading
            // `outer.inner.file` must leave `outer` byte-for-byte as it
            // was, however many `record`/`resource` layers alternate on
            // the way there.
            OwnershipMode::Observe => self.observe_projections(&root, &place.projections),
            OwnershipMode::Transfer => {
                let result = self.take_projections(root, &place.projections)?;
                values.insert(place.root, result.container);
                Ok(result.extracted)
            }
        }
    }

    /// Writes `value` into `place`'s own final projection step
    /// (`rfcs/0012`, structural reinitialization) -- the write-only
    /// counterpart of [`Self::access_place`]'s `Transfer` mode, sharing
    /// its identical container-navigation logic.
    /// Reinitializes `place` with the value `source` names, as a genuine
    /// **ownership transfer** (`rfcs/0011`, `rfcs/0012`) -- what
    /// `Instruction::StorePlace` actually means, as opposed to merely
    /// copying a value into a field and leaving the original looking
    /// like a current owner too.
    ///
    /// Runs in three strictly ordered phases so the whole operation is
    /// transactional:
    ///
    /// 1. **Validate**, mutating nothing: the destination chain must be
    ///    reachable and its final field provably empty, and every
    ///    resource reachable through `source` must be a live, current,
    ///    owning handle. A failure here leaves the source valid, the
    ///    destination untouched, and no generation bumped.
    /// 2. **Transfer**: every resource identity nested in `source` is
    ///    transferred, which bumps its generation and makes every handle
    ///    minted from the previous one stale. Phase 1 already proved
    ///    each one transferable, so this cannot fail partway and leave
    ///    some children transferred and others not.
    /// 3. **Commit**: the transferred value is written into the place,
    ///    and `source`'s own entry is tombstoned so a later read is a
    ///    structured error rather than a stale handle that happens to
    ///    look plausible. Both the exact id and the storage it
    ///    canonicalizes to are tombstoned -- a `Load` result and the
    ///    slot it read share one identity, exactly as `nir::verify`
    ///    treats them.
    ///
    /// Self-aliasing is rejected up front: a store whose source is the
    /// very storage its destination is rooted in would have to place an
    /// aggregate inside itself.
    fn store_place_transfer(
        &self,
        values: &mut HashMap<ValueId, Value>,
        load_origin: &HashMap<ValueId, ValueId>,
        place: &Place<ValueId>,
        source: ValueId,
    ) -> Result<(), InterpreterError> {
        let root_id = canonical_root(load_origin, place.root);
        let source_id = canonical_root(load_origin, source);
        if source_id == root_id {
            return Err(invalid(
                "a structural store's own source and destination name the same storage",
            ));
        }
        let root = get(values, &root_id)?;
        let incoming = get(values, &source)?;

        // Phase 1 -- validation only; nothing below this point mutates.
        self.validate_store_target(&root, &place.projections)?;
        self.validate_transferable(&incoming)?;

        // Phase 2 -- the only phase that bumps a generation.
        let owned = self.transfer_if_resource(incoming)?;

        // Phase 3 -- commit.
        let updated_root = self.store_projections(root, &place.projections, owned)?;
        values.insert(root_id, updated_root);
        values.insert(source, Value::Moved);
        values.insert(source_id, Value::Moved);
        Ok(())
    }

    /// Proves `projections` reaches a field that may legally be
    /// reinitialized, without mutating anything (`rfcs/0012`) -- the
    /// read-only half of [`Self::store_place_transfer`]'s own phase 1.
    /// Every intermediate must be a live container, and the final field
    /// must already be a `Moved`/`Dropped` tombstone: reinitializing
    /// over a live value would silently leak it.
    fn validate_store_target(
        &self,
        container: &Value,
        projections: &[Projection],
    ) -> Result<(), InterpreterError> {
        let Some((first, rest)) = projections.split_first() else {
            return Err(invalid("a structural store names no field to reinitialize"));
        };
        let index = Self::projection_index(first)?;
        match container {
            Value::Resource(handle) => {
                if handle.role != RuntimeOwnershipRole::Owner {
                    return Err(invalid(
                        "cannot reinitialize a field through a merely-observing resource handle",
                    ));
                }
                let inner = self.resources.borrow().observe_field(*handle, index)?;
                if rest.is_empty() {
                    if !matches!(inner, Value::Moved | Value::Dropped) {
                        return Err(invalid(
                            "cannot overwrite a resource field that still owns a live value",
                        ));
                    }
                    Ok(())
                } else {
                    self.validate_store_target(&inner, rest)
                }
            }
            Value::Record { fields, .. } => {
                let slot = fields.get(index).ok_or_else(|| {
                    invalid("a place projects a field index out of range for this record")
                })?;
                if rest.is_empty() {
                    if !matches!(slot, Value::Moved | Value::Dropped) {
                        return Err(invalid(
                            "cannot overwrite a record field that still owns a live value",
                        ));
                    }
                    Ok(())
                } else {
                    self.validate_store_target(slot, rest)
                }
            }
            Value::Moved => Err(invalid(
                "a place reinitializes through a field that was already moved",
            )),
            Value::Dropped => Err(invalid(
                "a place reinitializes through a field that was already dropped",
            )),
            other => Err(invalid(format!(
                "a place projects through a non-aggregate value ({})",
                kind_name(other)
            ))),
        }
    }

    /// Proves every resource identity reachable through `value` can be
    /// transferred, without transferring any of them (`rfcs/0011`) --
    /// the other read-only half of phase 1. Checking the whole tree up
    /// front is what makes a nested aggregate's transfer all-or-nothing:
    /// bumping the first child's generation and then discovering the
    /// second is stale would leave the value half-transferred with no
    /// way back.
    fn validate_transferable(&self, value: &Value) -> Result<(), InterpreterError> {
        match value {
            Value::Resource(handle) => {
                if handle.role != RuntimeOwnershipRole::Owner {
                    return Err(invalid(
                        "cannot transfer ownership through a merely-observing resource handle",
                    ));
                }
                let table = self.resources.borrow();
                let record = table.record(*handle)?;
                if record.status == ResourceStatus::Dropped {
                    return Err(invalid(
                        "cannot transfer ownership of a resource that was already dropped",
                    ));
                }
                Ok(())
            }
            Value::Record { fields, .. } => fields
                .iter()
                .try_for_each(|field| self.validate_transferable(field)),
            Value::Variant { payload, .. } => payload
                .iter()
                .try_for_each(|field| self.validate_transferable(field)),
            Value::Moved => Err(invalid("transfer of a value that was already moved")),
            Value::Dropped => Err(invalid("transfer of a value that was already destroyed")),
            _ => Ok(()),
        }
    }

    /// Reads the value at `projections`' own final step out of
    /// `container` without mutating anything at all, at any depth
    /// (`rfcs/0012`): no ancestor is tombstoned, no inline record is
    /// rebuilt, and no resource's own field storage is written -- an
    /// observation is a pure read, whatever mixture of inline `Record`
    /// and resource-table-backed `Resource` containers it passes
    /// through on the way. Cloning an intermediate is always safe here:
    /// a `Value::Resource` carries only a cheap `(id, generation, role)`
    /// handle, never the resource's own identity or data, and observing
    /// never bumps a generation.
    fn observe_projections(
        &self,
        container: &Value,
        projections: &[Projection],
    ) -> Result<Value, InterpreterError> {
        let Some((first, rest)) = projections.split_first() else {
            return Ok(container.clone());
        };
        let index = Self::projection_index(first)?;
        match container {
            Value::Resource(handle) => {
                let inner = self.resources.borrow().observe_field(*handle, index)?;
                self.observe_projections(&inner, rest)
            }
            Value::Record { fields, .. } => {
                let slot = fields.get(index).ok_or_else(|| {
                    invalid("a place projects a field index out of range for this record")
                })?;
                self.observe_projections(slot, rest)
            }
            Value::Moved => Err(invalid("use of a field after it was already moved")),
            Value::Dropped => Err(invalid("use of a field after it was already dropped")),
            other => Err(invalid(format!(
                "a place projects through a non-aggregate value ({})",
                kind_name(other)
            ))),
        }
    }

    /// Removes the value at `projections`' own final step out of
    /// `container`, tombstoning **only** that one final field and
    /// returning the container itself for its own caller to reinsert
    /// (`rfcs/0012`).
    ///
    /// Every intermediate is preserved, whichever kind it is: an inline
    /// `Record` is handed back rebuilt (with its own descendant's
    /// updated state in place), and a `Resource` is handed back as the
    /// very same handle, with the update already applied directly to
    /// its own field storage through [`ResourceTable::restore_field`]
    /// -- never through the user-facing `set_field`, which would
    /// (correctly, for its own purpose) reject the still-live
    /// intermediate as an overwrite.
    ///
    /// Transactional: the recursion runs to completion on a *clone* of
    /// the intermediate before anything is written back, so a failure
    /// deeper in the chain leaves every container on the path exactly
    /// as it was rather than half-mutated.
    fn take_projections(
        &self,
        container: Value,
        projections: &[Projection],
    ) -> Result<AccessResult, InterpreterError> {
        let Some((first, rest)) = projections.split_first() else {
            // A zero-projection place is the whole root value itself:
            // there is no container above it to tombstone a field in,
            // and `nir::verify` tracks a bare root through its own
            // whole-value ownership lattice rather than this one.
            return Ok(AccessResult {
                extracted: container.clone(),
                container,
            });
        };
        let index = Self::projection_index(first)?;
        match container {
            Value::Resource(handle) => {
                if rest.is_empty() {
                    let extracted = self.resources.borrow_mut().take_field(handle, index)?;
                    if matches!(extracted, Value::Moved | Value::Dropped) {
                        // Put the tombstone back exactly as it was:
                        // this took nothing, and must not look like it
                        // did.
                        self.resources
                            .borrow_mut()
                            .restore_field(handle, index, extracted)?;
                        return Err(invalid(
                            "transfer of a resource field that was already moved or dropped",
                        ));
                    }
                    Ok(AccessResult {
                        extracted,
                        container: Value::Resource(handle),
                    })
                } else {
                    let inner = self.resources.borrow().observe_field(handle, index)?;
                    let inner = self.take_projections(inner, rest)?;
                    self.resources
                        .borrow_mut()
                        .restore_field(handle, index, inner.container)?;
                    Ok(AccessResult {
                        extracted: inner.extracted,
                        container: Value::Resource(handle),
                    })
                }
            }
            Value::Record {
                item,
                type_args,
                mut fields,
            } => {
                if fields.len() <= index {
                    return Err(invalid(
                        "a place projects a field index out of range for this record",
                    ));
                }
                if rest.is_empty() {
                    if matches!(fields[index], Value::Moved | Value::Dropped) {
                        return Err(invalid(
                            "transfer of a record field that was already moved or dropped",
                        ));
                    }
                    let extracted = std::mem::replace(&mut fields[index], Value::Moved);
                    Ok(AccessResult {
                        extracted,
                        container: Value::Record {
                            item,
                            type_args,
                            fields,
                        },
                    })
                } else {
                    let inner = self.take_projections(fields[index].clone(), rest)?;
                    fields[index] = inner.container;
                    Ok(AccessResult {
                        extracted: inner.extracted,
                        container: Value::Record {
                            item,
                            type_args,
                            fields,
                        },
                    })
                }
            }
            Value::Moved => Err(invalid("use of a field after it was already moved")),
            Value::Dropped => Err(invalid("use of a field after it was already dropped")),
            other => Err(invalid(format!(
                "a place projects through a non-aggregate value ({})",
                kind_name(&other)
            ))),
        }
    }

    /// One projection step's own field index, rejecting the
    /// `VariantField` shape this milestone's runtime never produces
    /// (a variant payload is only ever reached through a
    /// `ValueKind::VariantPayload` extraction on its own case-refined
    /// edge, never through a `Place`).
    fn projection_index(projection: &Projection) -> Result<usize, InterpreterError> {
        match projection {
            Projection::Field { field, .. } => Ok(field.0 as usize),
            Projection::VariantField { .. } => Err(invalid(
                "a place projects through a variant field, which this milestone's runtime never \
                 produces",
            )),
        }
    }

    /// The write-only counterpart of [`Self::access_projections`]:
    /// navigates the same way, but only ever replaces the final field's
    /// own tombstone with `value` (`rfcs/0012`), rather than reading or
    /// removing anything.
    fn store_projections(
        &self,
        container: Value,
        projections: &[Projection],
        value: Value,
    ) -> Result<Value, InterpreterError> {
        let Some((first, rest)) = projections.split_first() else {
            return Ok(value);
        };
        let index = Self::projection_index(first)?;
        match container {
            Value::Resource(handle) => {
                if rest.is_empty() {
                    // The one genuine reinitialization in this whole
                    // walk: the *final* step, which really must find a
                    // provably-empty slot (`rfcs/0012`).
                    self.resources
                        .borrow_mut()
                        .set_field(handle, index, value)?;
                } else {
                    // An *intermediate* resource field is still live by
                    // construction -- this walk only reached deeper
                    // through it -- so it goes back through the
                    // internal `restore_field`, never `set_field`,
                    // which would reject it as a live overwrite.
                    let inner = self.resources.borrow().observe_field(handle, index)?;
                    let updated_inner = self.store_projections(inner, rest, value)?;
                    self.resources
                        .borrow_mut()
                        .restore_field(handle, index, updated_inner)?;
                }
                Ok(Value::Resource(handle))
            }
            Value::Record {
                item,
                type_args,
                mut fields,
            } => {
                if fields.len() <= index {
                    return Err(invalid(
                        "a place projects a field index out of range for this record",
                    ));
                }
                if rest.is_empty() {
                    if !matches!(fields[index], Value::Moved | Value::Dropped) {
                        return Err(invalid(
                            "cannot overwrite a record field that still owns a live value",
                        ));
                    }
                    fields[index] = value;
                } else {
                    // Recurse on a clone and only write back once it
                    // succeeded, exactly like `take_projections`: a
                    // failure deeper in the chain must never leave this
                    // record holding a `Moved` tombstone where a live
                    // intermediate used to be.
                    fields[index] = self.store_projections(fields[index].clone(), rest, value)?;
                }
                Ok(Value::Record {
                    item,
                    type_args,
                    fields,
                })
            }
            Value::Moved => Err(invalid(
                "a place reinitializes through a field that was already moved",
            )),
            Value::Dropped => Err(invalid(
                "a place reinitializes through a field that was already dropped",
            )),
            other => Err(invalid(format!(
                "a place projects through a non-aggregate value ({})",
                kind_name(&other)
            ))),
        }
    }

    /// Recursively destroys `value` (`rfcs/0012`): a `resource` handle
    /// goes through the ordinary resource table drop; a plain, still-
    /// affine `Variant`'s own *active* case is walked to destroy every
    /// one of its own live affine payload fields, exactly the "only the
    /// active case is destroyed" rule `rfcs/0012` specifies -- the one
    /// case `resourceck`'s own compile-time cleanup planning cannot
    /// expand into individual per-field `Drop` actions itself, since
    /// which case is live is not known until runtime (see
    /// `resourceck::flow::FlowChecker::structural_drop_targets`'s own
    /// doc comment on `variant_items`). A plain, non-affine value (or
    /// one already `Moved`/`Dropped`) is left untouched -- the caller is
    /// responsible for only ever calling this on something it already
    /// knows is still live.
    fn drop_value(&self, value: Value) -> Result<(), InterpreterError> {
        match value {
            Value::Resource(handle) => {
                // A declared `resource`'s own remaining live children
                // are destroyed first, in reverse declaration order,
                // and its own outer identity last (`rfcs/0012`). Every
                // child this frame's own NIR already destroyed
                // individually (the ordinary case: `resourceck`'s own
                // cleanup planning expands a resource place into its
                // affine fields before the place itself) is a `Moved`/
                // `Dropped` tombstone by now and is skipped here, so
                // the two never double-destroy the same child. This
                // recursion is what keeps a resource reached *without*
                // that expansion -- a resource nested in a variant
                // payload, whose live case is only known at runtime --
                // from leaking its own children.
                let (item, arity) = {
                    let table = self.resources.borrow();
                    let record = table.observe(handle)?;
                    (record.item, record.fields.len())
                };
                // A declared `resource` is never generic in this
                // milestone's grammar, so its own declared field types
                // are already concrete -- but they are still resolved
                // through the same checked path, so an unknown item or
                // a malformed layout is an error rather than an empty
                // list that would silently skip every field.
                let field_types = self.record_field_types(item, &[])?;
                for index in (0..arity).rev() {
                    let Some(ty) = field_types.get(index) else {
                        continue;
                    };
                    if !self.is_affine(ty) {
                        continue;
                    }
                    let field = self.resources.borrow().observe_field(handle, index)?;
                    if matches!(field, Value::Moved | Value::Dropped) {
                        continue;
                    }
                    // Tombstoned *before* the recursive destruction, not
                    // after: a failure partway through destroying this
                    // child must never leave it reachable for a second
                    // destruction attempt through the same parent.
                    self.resources
                        .borrow_mut()
                        .restore_field(handle, index, Value::Dropped)?;
                    self.drop_value(field)?;
                }
                self.resources.borrow_mut().drop_resource(handle)?;
                #[cfg(test)]
                self.event_log
                    .borrow_mut()
                    .push(format!("drop:{}", handle.id.0));
                Ok(())
            }
            Value::Record {
                item,
                type_args,
                mut fields,
            } => {
                // An ordinary `record` that merely *contains* affine
                // fields has no separate runtime identity of its own to
                // destroy -- only its own live affine fields, in
                // reverse declaration order. Silently ignoring this
                // shape is exactly what let a variant carrying an
                // affine record leak that record's own resources.
                //
                // The field types come from this value's *own*
                // instantiation: a `Box[File]` destroyed through its
                // declaration's symbolic `Ty::Param(T)` would find
                // nothing affine and leak the `File` it holds.
                let field_types = self.record_field_types(item, &type_args)?;
                // A value whose own field count disagrees with its
                // declaration is malformed metadata, not a value with
                // some untyped extras: skipping the surplus would skip
                // exactly the fields nothing can say the affinity of.
                if field_types.len() != fields.len() {
                    return Err(invalid(
                        "a runtime record value's own field count disagrees with its declaration",
                    ));
                }
                for index in (0..fields.len()).rev() {
                    let Some(ty) = field_types.get(index) else {
                        continue;
                    };
                    if !self.is_affine(ty) {
                        continue;
                    }
                    if matches!(fields[index], Value::Moved | Value::Dropped) {
                        continue;
                    }
                    let field = std::mem::replace(&mut fields[index], Value::Dropped);
                    self.drop_value(field)?;
                }
                Ok(())
            }
            Value::Variant {
                item,
                type_args,
                case,
                mut payload,
            } => {
                // Only the active case, and only its own live payload
                // fields, in reverse declaration order (`rfcs/0012`) --
                // substituted with this value's own type arguments, so
                // a `Maybe[File]` destroys the `File` its declaration
                // only ever calls `T`.
                let payload_types = self.case_payload_types(item, &type_args, case)?;
                // See the record arm: a payload count disagreeing with
                // the active case's own declaration is malformed
                // metadata, never a value with untyped extras.
                if payload_types.len() != payload.len() {
                    return Err(invalid(
                        "a runtime variant value's own payload count disagrees with its active \
                         case's declaration",
                    ));
                }
                for index in (0..payload.len()).rev() {
                    let Some(ty) = payload_types.get(index) else {
                        continue;
                    };
                    if !self.is_affine(ty) {
                        continue;
                    }
                    if matches!(payload[index], Value::Moved | Value::Dropped) {
                        continue;
                    }
                    let field = std::mem::replace(&mut payload[index], Value::Dropped);
                    self.drop_value(field)?;
                }
                Ok(())
            }
            Value::Moved => Err(invalid("drop of a field that was already moved")),
            Value::Dropped => Err(invalid("double drop: this value was already destroyed")),
            other => Err(invalid(format!(
                "drop of a non-affine value ({})",
                kind_name(&other)
            ))),
        }
    }

    /// Every field type of the declared record/`resource` `item`, or
    /// every payload type of the variant `item` flattened across its own
    /// cases, in declaration order -- empty for an unknown item. Read
    /// straight off this module's own layouts rather than re-derived.
    fn item_field_types(&self, item: ItemId) -> Vec<Ty> {
        if let Some((_, record)) = self.module.records.iter().find(|(id, _)| *id == item) {
            return record.fields.iter().map(|(_, t)| t.clone()).collect();
        }
        if let Some((_, variant)) = self.module.variants.iter().find(|(id, _)| *id == item) {
            return variant
                .cases
                .iter()
                .flat_map(|c| c.payload.clone())
                .collect();
        }
        Vec::new()
    }

    /// `item`'s own declared field types with `type_args` substituted
    /// in, in declaration order (`rfcs/0008`, `rfcs/0012`) -- what a
    /// runtime value's own fields *actually* are at this instantiation,
    /// as opposed to the symbolic `Ty::Param` its declaration was
    /// written with.
    ///
    /// Errors -- never an empty or partial list -- when `item` has no
    /// recorded layout or when its declared arity disagrees with
    /// `type_args`: destroying an aggregate from a substitution nobody
    /// could build would skip exactly the fields whose types went
    /// missing.
    fn record_field_types(
        &self,
        item: ItemId,
        type_args: &[Ty],
    ) -> Result<Vec<Ty>, InterpreterError> {
        let Some((_, record)) = self.module.records.iter().find(|(id, _)| *id == item) else {
            return Err(invalid(
                "a runtime aggregate names a record this module never declared",
            ));
        };
        let subst = self.checked_substitution(item, type_args)?;
        Ok(record
            .fields
            .iter()
            .map(|(_, t)| crate::types::substitute(t, &subst))
            .collect())
    }

    /// `item`'s own declared payload types for `case`, with `type_args`
    /// substituted in (`rfcs/0008`, `rfcs/0012`) -- only the *active*
    /// case, never the flattened cross-case list: a case that was never
    /// constructed owns nothing.
    fn case_payload_types(
        &self,
        item: ItemId,
        type_args: &[Ty],
        case: usize,
    ) -> Result<Vec<Ty>, InterpreterError> {
        let Some((_, variant)) = self.module.variants.iter().find(|(id, _)| *id == item) else {
            return Err(invalid(
                "a runtime aggregate names a variant this module never declared",
            ));
        };
        let Some(layout) = variant.cases.get(case) else {
            return Err(invalid(
                "a runtime variant value names a case out of range for its own declaration",
            ));
        };
        let subst = self.checked_substitution(item, type_args)?;
        Ok(layout
            .payload
            .iter()
            .map(|t| crate::types::substitute(t, &subst))
            .collect())
    }

    /// [`Self::type_substitution`] as a hard requirement: a structured,
    /// deterministic error rather than an `Option` the caller might be
    /// tempted to paper over with a default.
    fn checked_substitution(
        &self,
        item: ItemId,
        type_args: &[Ty],
    ) -> Result<std::collections::HashMap<crate::hir::TypeParamId, Ty>, InterpreterError> {
        self.type_substitution(item, type_args).ok_or_else(|| {
            invalid(
                "a runtime aggregate carries type arguments that disagree with its own \
                 declaration's parameter list",
            )
        })
    }

    /// Transfers ownership of `value` if it is a resource (Blocker 8),
    /// recursing into a plain `Record`/`Variant`'s own fields/payload to
    /// transfer any resource nested inside *those* too (`rfcs/0012`) --
    /// without this, constructing a new aggregate from an existing
    /// resource value would leave the *source* `ValueId`'s own cached
    /// copy holding a handle whose generation was never bumped, so it
    /// would still look like a live, undestroyed obligation of this
    /// frame's own to `leaked_resource`, even once the resource is only
    /// really reachable through the new aggregate now. A no-op for a
    /// non-affine leaf. Shared by every place ownership genuinely
    /// crosses a boundary: a `take` argument's own transfer *into* a
    /// call, a returned value's own transfer back *out* of one, and a
    /// `record.create`/`variant.create`'s own field/payload arguments
    /// (`resourceck`/`nir::verify` already require every one of those to
    /// be an unconditional transfer, mirrored here).
    fn transfer_if_resource(&self, value: Value) -> Result<Value, InterpreterError> {
        match value {
            Value::Resource(handle) => Ok(Value::Resource(
                self.resources.borrow_mut().transfer(handle)?,
            )),
            // A transfer rebuilds the aggregate around freshly-generated
            // handles, so it must carry this value's own type arguments
            // across unchanged: an ownership transfer is not the place
            // a `Box[File]` quietly becomes a `Box[T]`.
            Value::Record {
                item,
                type_args,
                fields,
            } => Ok(Value::Record {
                item,
                type_args,
                fields: fields
                    .into_iter()
                    .map(|f| self.transfer_if_resource(f))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            Value::Variant {
                item,
                type_args,
                case,
                payload,
            } => Ok(Value::Variant {
                item,
                type_args,
                case,
                payload: payload
                    .into_iter()
                    .map(|f| self.transfer_if_resource(f))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            other => Ok(other),
        }
    }

    /// Downgrades `value` to a merely-observing handle if it is a
    /// resource at all (`rfcs/0011`) -- every ordinary (non-`take`)
    /// parameter binding, and every `store.observe`, goes through this
    /// rather than binding the caller's own handle as-is.
    fn to_observer_if_resource(&self, value: Value) -> Result<Value, InterpreterError> {
        match value {
            Value::Resource(handle) => Ok(Value::Resource(
                self.resources.borrow().to_observer(handle)?,
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
                // A merely-observing handle never counts as owned here
                // regardless of `observing_params` -- which only ever
                // lists this frame's own *parameters* -- since a value
                // downgraded mid-function (`store.observe`) is exactly
                // as much a non-owner as an ordinary parameter is.
                Value::Resource(handle) if handle.role == RuntimeOwnershipRole::Owner => resources
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
        // Every `Load`'s own result paired with the slot it reads --
        // see `canonical_root`. Built once per frame from the whole
        // function, exactly like `nir::verify` builds its own.
        let load_origin: HashMap<ValueId, ValueId> = function
            .blocks
            .iter()
            .flat_map(|b| b.instructions.iter())
            .filter_map(|i| match i {
                crate::nir::Instruction::Value {
                    result,
                    kind: ValueKind::Load(slot),
                    ..
                } => Some((*result, *slot)),
                _ => None,
            })
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
                self.to_observer_if_resource(arg)?
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
                        let value = if let ValueKind::PlaceRead { place, mode } = kind {
                            self.access_place(&mut values, &load_origin, place, *mode)?
                        } else {
                            self.eval(kind, &values, &evidence)?
                        };
                        values.insert(*result, value);
                    }
                    crate::nir::Instruction::Store { slot, value, mode } => {
                        let v = get(&values, value)?;
                        let v = match mode {
                            // A transferring store immediately
                            // invalidates `value`'s own prior identity
                            // (`rfcs/0011`): any later read through that
                            // same `ValueId` now fails the resource
                            // table's own generation check, exactly
                            // like a `take` argument's or a `return`'s
                            // own transfer already does.
                            crate::nir::OwnershipMode::Transfer => self.transfer_if_resource(v)?,
                            // An observing store never transfers -- and
                            // must never let the slot's own later reads
                            // inherit owning access either, even when
                            // `value` itself is presently an owner: the
                            // slot is always a merely-observing window
                            // (`rfcs/0011`).
                            crate::nir::OwnershipMode::Observe => {
                                self.to_observer_if_resource(v)?
                            }
                        };
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
                        // Every *transitively affine* value is a legal
                        // structural drop target (`rfcs/0012`), not
                        // just a declared `resource` or a variant: an
                        // ordinary `record` carrying an affine field
                        // owns real resources too, and silently
                        // accepting it as a no-op leaked them.
                        match get(&values, value)? {
                            v @ Value::Resource(_) => self.drop_value(v)?,
                            v @ (Value::Record { .. } | Value::Variant { .. })
                                if self.is_affine_value(&v)? =>
                            {
                                self.drop_value(v)?
                            }
                            other => {
                                return Err(invalid(format!(
                                    "drop of a non-affine value ({})",
                                    kind_name(&other)
                                )));
                            }
                        }
                        values.remove(value);
                    }
                    crate::nir::Instruction::StorePlace { place, value } => {
                        // A structural reinitialization *transfers*
                        // ownership into the place (`rfcs/0012`): the
                        // source is consumed here, not copied, so it
                        // must not go on looking like a current owner.
                        self.store_place_transfer(&mut values, &load_origin, place, *value)?;
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
            // Both explicitly transfer ownership (`rfcs/0011`): the
            // source's own handle is immediately stale (any later read
            // of its own `ValueId` fails the resource table's own
            // generation check), and this instruction's own result is
            // the fresh, current owner. `transfer_if_resource` passes a
            // non-resource value through unchanged, matching
            // `nir::verify`'s own requirement that `Move`/`DeferCapture`
            // only ever appear on a resource-typed value in the first
            // place -- defended here too, rather than trusted blindly.
            ValueKind::Move { source } => self.transfer_if_resource(get(values, source)?),
            ValueKind::DeferCapture { source } => self.transfer_if_resource(get(values, source)?),
            // Always intercepted by `call_function`'s own instruction
            // loop before `eval` is ever reached (`rfcs/0012`): unlike
            // every other `ValueKind`, a place read may need to *mutate*
            // `values` itself (writing back a rebuilt container after a
            // `Transfer`), which this method's own `&HashMap` (not
            // `&mut`) signature cannot do.
            ValueKind::PlaceRead { .. } => Err(invalid(
                "ValueKind::PlaceRead must be evaluated by call_function directly, never through eval",
            )),
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
            ValueKind::RecordCreate(item, type_args, field_ids) => {
                let fields = field_ids
                    .iter()
                    .map(|id| get(values, id).and_then(|v| self.transfer_if_resource(v)))
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
                        type_args: type_args.clone(),
                        fields,
                    })
                }
            }
            ValueKind::RecordField {
                base,
                record,
                field,
            } => match get(values, base)? {
                Value::Record { item, fields, .. } if item == *record => fields
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
                type_args,
                payload,
            } => {
                let payload = payload
                    .iter()
                    .map(|id| get(values, id).and_then(|v| self.transfer_if_resource(v)))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Value::Variant {
                    item: *variant,
                    type_args: type_args.clone(),
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
                    ..
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

/// The storage location a place's own root actually names: a `Load`'s
/// own result shares its identity with the slot it loaded from
/// (`rfcs/0012`), exactly as `nir::verify::verify_structural_places`
/// already canonicalizes it. A `mutable` binding reloads its whole
/// current value as a *fresh* `ValueId` every time a place projects
/// into it, so tombstoning a field in the load's own cached copy --
/// rather than in the slot every later load reads back from -- would
/// lose the mutation entirely, and a later reinitialization would find
/// the field still live.
///
/// Follows a chain of loads to its fixed point, bounded by the number
/// of entries so a hand-built cyclic `load` chain terminates instead of
/// spinning.
fn canonical_root(load_origin: &HashMap<ValueId, ValueId>, root: ValueId) -> ValueId {
    let mut current = root;
    for _ in 0..=load_origin.len() {
        match load_origin.get(&current) {
            Some(next) if *next != current => current = *next,
            _ => return current,
        }
    }
    current
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
        Value::Moved => "a moved field",
        Value::Dropped => "a dropped field",
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
            &crate::resourceck::AffineContext {
                aggregate_field_types: &result.aggregate_field_types,
                declared_resources: &result.declared_resources,
                item_type_params: &result.item_type_params,
                field_projections: &result.field_projections,
            },
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
            &resourceck_result.consume_sites,
            &resourceck_result.defer_plans,
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
    pub(super) fn run_with_log(text: &str) -> (Result<Value, InterpreterError>, Vec<String>) {
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
            &crate::resourceck::AffineContext {
                aggregate_field_types: &result.aggregate_field_types,
                declared_resources: &result.declared_resources,
                item_type_params: &result.item_type_params,
                field_projections: &result.field_projections,
            },
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
            &resourceck_result.consume_sites,
            &resourceck_result.defer_plans,
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
        let resourceck_result = crate::resourceck::check_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &interner,
            &crate::resourceck::AffineContext {
                aggregate_field_types: &result.aggregate_field_types,
                declared_resources: &result.declared_resources,
                item_type_params: &result.item_type_params,
                field_projections: &result.field_projections,
            },
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
            &resourceck_result.consume_sites,
            &resourceck_result.defer_plans,
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
        let resourceck_result = crate::resourceck::check_module(
            &hir,
            &result.local_types,
            &result.expr_types,
            &interner,
            &crate::resourceck::AffineContext {
                aggregate_field_types: &result.aggregate_field_types,
                declared_resources: &result.declared_resources,
                item_type_params: &result.item_type_params,
                field_projections: &result.field_projections,
            },
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
            &resourceck_result.consume_sites,
            &resourceck_result.defer_plans,
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
    fn a_stale_resource_handle_left_behind_by_a_defer_capture_is_an_error_not_a_panic() {
        // `nir::lower` emits `ValueKind::DeferCapture` to transfer a
        // `take`-flagged `defer` argument's ownership away *at the
        // `defer` statement's own lexical registration point*
        // (`rfcs/0011`) -- this hand-built module reads the original
        // `%0` again immediately afterward, bypassing `nir::verify`'s
        // own static `RESOURCE_USE_AFTER_CONSUME` rejection entirely,
        // to prove the interpreter's own independent runtime backstop
        // (the resource table's generation check) catches a stale use
        // between registration and replay on its own, exactly like it
        // already does for an ordinary `take` call argument.
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
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: resource_ty.clone(),
                            kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: resource_ty.clone(),
                            kind: ValueKind::DeferCapture { source: ValueId(0) },
                        },
                        // Malformed: `%0` was already captured above --
                        // this aliases its own now-stale handle, same
                        // shape as the analogous take-call regression.
                        Instruction::Value {
                            result: ValueId(2),
                            ty: resource_ty,
                            kind: ValueKind::Load(ValueId(0)),
                        },
                        Instruction::Drop { value: ValueId(2) },
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
            "expected a structured stale-handle error, not a panic, got {outcome:?}"
        );
    }

    #[test]
    fn dropping_an_observing_store_loaded_alias_is_an_error_not_a_panic() {
        // `nir::verify`'s own RESOURCE_OBSERVER_CONSUMED already
        // statically rejects this exact shape -- this hand-built module
        // bypasses verification entirely to prove the *runtime* itself
        // independently distinguishes an owner from an observer: `%2`
        // is loaded from a `store.observe`'d slot, so its own handle is
        // downgraded to a mere observer, and dropping it must fail as a
        // structured error rather than actually destroying `%0`'s own
        // resource out from under it.
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
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(0),
                            ty: resource_ty.clone(),
                            kind: ValueKind::RecordCreate(resource, Vec::new(), Vec::new()),
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: resource_ty.clone(),
                            kind: ValueKind::Alloc,
                        },
                        Instruction::Store {
                            slot: ValueId(1),
                            value: ValueId(0),
                            mode: crate::nir::OwnershipMode::Observe,
                        },
                        Instruction::Value {
                            result: ValueId(2),
                            ty: resource_ty,
                            kind: ValueKind::Load(ValueId(1)),
                        },
                        Instruction::Drop { value: ValueId(2) },
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
            "expected a structured observer-drop error, not a panic, got {outcome:?}"
        );
    }

    #[test]
    fn transferring_an_ordinary_parameters_own_handle_is_an_error_not_a_panic() {
        // `f`'s own `file` parameter is an ordinary (non-`take`)
        // parameter -- bound as a mere observer at the call boundary --
        // yet this hand-built body still attempts to `Move` it (an
        // unconditional transfer). `nir::verify`'s own
        // RESOURCE_OBSERVER_CONSUMED already statically rejects this;
        // bypassing verification entirely proves the runtime's own
        // parameter-binding role downgrade independently blocks it too.
        use crate::hir::ItemId;
        use crate::nir::{BasicBlock, BlockId, Instruction, Param, RecordLayout};
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
                    instructions: vec![
                        Instruction::Value {
                            result: ValueId(1),
                            ty: resource_ty,
                            kind: ValueKind::Move { source: ValueId(0) },
                        },
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
        let interpreter = Interpreter::new(&module);
        let arg = interpreter
            .resources
            .borrow_mut()
            .construct(resource, Vec::new());
        let outcome =
            interpreter.call_function(&module.functions[0], vec![Value::Resource(arg)], Vec::new());
        match outcome {
            Err(InterpreterError::InvalidOperation(_)) => {}
            Err(other) => panic!("expected a structured observer-move error, got {other:?}"),
            Ok(_) => panic!("expected a structured observer-move error, but the call succeeded"),
        }
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

/// Missing-metadata fail-closed behavior at runtime (`rfcs/0008`,
/// `rfcs/0012`), and the structural drop/traversal properties this
/// stage answers entirely on its own -- from a module's own layouts,
/// never trusted from an earlier stage's verdict.
#[cfg(test)]
mod structural_runtime {
    use super::*;
    use crate::nir::RecordLayout;
    use crate::symbol::Symbol;

    const BOXY: ItemId = ItemId(80);
    const FILE: ItemId = ItemId(81);

    fn module_with(type_params: Vec<(crate::hir::TypeParamId, Symbol)>) -> Module {
        let param = crate::hir::TypeParamId(0);
        let name = Symbol(0);
        Module {
            functions: Vec::new(),
            records: vec![
                (
                    FILE,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::I64)],
                        affine: true,
                    },
                ),
                (
                    BOXY,
                    RecordLayout {
                        name,
                        type_params,
                        fields: vec![(name, Ty::Param(param, name))],
                        affine: false,
                    },
                ),
            ],
            variants: Vec::new(),
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    fn nested_module() -> Module {
        let name = Symbol(0);
        Module {
            functions: Vec::new(),
            records: vec![
                (
                    FILE,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::I64)],
                        affine: true,
                    },
                ),
                (
                    BOXY,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Named(FILE, name))],
                        affine: false,
                    },
                ),
            ],
            variants: Vec::new(),
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    #[test]
    fn a_well_formed_generic_instantiation_is_affine_only_for_an_affine_argument() {
        let name = Symbol(0);
        let module = module_with(vec![(crate::hir::TypeParamId(0), name)]);
        let interpreter = Interpreter::new(&module);
        assert!(
            interpreter.is_affine(&Ty::Applied(BOXY, vec![Ty::Named(FILE, name)])),
            "`Box[File]` must be affine at runtime"
        );
        assert!(
            !interpreter.is_affine(&Ty::Applied(BOXY, vec![Ty::I64])),
            "`Box[i64]` must not be affine at runtime"
        );
    }

    #[test]
    fn a_missing_type_parameter_list_fails_closed_to_affine() {
        let module = module_with(Vec::new());
        let interpreter = Interpreter::new(&module);
        assert!(
            interpreter.is_affine(&Ty::Applied(BOXY, vec![Ty::I64])),
            "missing generic metadata must never be answered as an empty substitution"
        );
    }

    #[test]
    fn an_unknown_generic_item_fails_closed_to_affine() {
        let module = module_with(vec![(crate::hir::TypeParamId(0), Symbol(0))]);
        let interpreter = Interpreter::new(&module);
        assert!(
            interpreter.is_affine(&Ty::Applied(ItemId(9999), vec![Ty::I64])),
            "an item with no recorded layout must never be answered as non-affine"
        );
    }

    #[test]
    fn an_affine_record_is_a_legal_structural_drop_target() {
        let module = nested_module();
        let interpreter = Interpreter::new(&module);
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let record = Value::Record {
            item: BOXY,
            type_args: Vec::new(),
            fields: vec![Value::Resource(handle)],
        };
        assert!(
            interpreter
                .is_affine_value(&record)
                .expect("the fixture's own layout is well formed"),
            "a record containing a resource must be a legal drop target"
        );
        interpreter
            .drop_value(record)
            .expect("dropping an affine record must destroy its own resource field");
        assert!(
            interpreter.resources.borrow().observe(handle).is_err(),
            "the nested resource must actually have been destroyed"
        );
    }

    #[test]
    fn dropping_an_already_destroyed_value_is_a_structured_error_not_a_panic() {
        let module = module_with(Vec::new());
        let interpreter = Interpreter::new(&module);
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        interpreter
            .drop_value(Value::Resource(handle))
            .expect("the first drop must succeed");
        let second = interpreter.drop_value(Value::Resource(handle));
        assert!(
            matches!(second, Err(InterpreterError::InvalidOperation(_))),
            "a second drop must be a structured error, got {second:?}"
        );
    }

    #[test]
    fn dropping_a_tombstone_is_a_structured_error_not_a_silent_success() {
        let module = module_with(Vec::new());
        let interpreter = Interpreter::new(&module);
        assert!(
            matches!(
                interpreter.drop_value(Value::Moved),
                Err(InterpreterError::InvalidOperation(_))
            ),
            "dropping a moved tombstone must be reported, not silently accepted"
        );
        assert!(
            matches!(
                interpreter.drop_value(Value::Dropped),
                Err(InterpreterError::InvalidOperation(_))
            ),
            "dropping an already-destroyed tombstone must be reported"
        );
    }

    #[test]
    fn a_place_projecting_through_a_variant_field_is_a_structured_error() {
        let module = module_with(Vec::new());
        let interpreter = Interpreter::new(&module);
        let projection = crate::place::Projection::VariantField {
            variant: BOXY,
            case: crate::place::CaseId(0),
            field: crate::place::FieldId(0),
        };
        let result = interpreter.observe_projections(&Value::Unit, &[projection]);
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "a variant-field projection must be rejected, got {result:?}"
        );
    }

    #[test]
    fn observing_through_a_mixed_chain_mutates_nothing_at_any_depth() {
        let module = nested_module();
        let interpreter = Interpreter::new(&module);
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(5)]);
        let outer = Value::Record {
            item: BOXY,
            type_args: Vec::new(),
            fields: vec![Value::Resource(handle)],
        };
        let path = [
            crate::place::Projection::Field {
                owner: BOXY,
                field: crate::place::FieldId(0),
            },
            crate::place::Projection::Field {
                owner: FILE,
                field: crate::place::FieldId(0),
            },
        ];
        let read = interpreter
            .observe_projections(&outer, &path)
            .expect("observing through record -> resource must succeed");
        assert_eq!(read, Value::Int(5));
        // Nothing above the leaf may have been disturbed: the inline
        // record still holds its own handle, and the resource's own
        // field storage is untouched.
        let Value::Record { ref fields, .. } = outer else {
            unreachable!("constructed as a record immediately above")
        };
        assert!(matches!(fields[0], Value::Resource(_)));
        assert_eq!(
            interpreter
                .resources
                .borrow()
                .observe_field(handle, 0)
                .expect("the resource must still hold its own field"),
            Value::Int(5)
        );
    }

    #[test]
    fn a_failed_traversal_leaves_every_container_on_the_path_untouched() {
        let module = nested_module();
        let interpreter = Interpreter::new(&module);
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let outer = Value::Record {
            item: BOXY,
            type_args: Vec::new(),
            fields: vec![Value::Resource(handle)],
        };
        // Projects one level too deep: the inner resource has no field
        // index 9, so the walk fails -- and must leave the outer
        // record's own live intermediate exactly where it was rather
        // than tombstoned by a half-applied mutation.
        let deep = [
            crate::place::Projection::Field {
                owner: BOXY,
                field: crate::place::FieldId(0),
            },
            crate::place::Projection::Field {
                owner: FILE,
                field: crate::place::FieldId(9),
            },
        ];
        assert!(interpreter.take_projections(outer.clone(), &deep).is_err());
        assert!(
            interpreter.resources.borrow().observe(handle).is_ok(),
            "a failed traversal must not destroy or invalidate an intermediate"
        );
        let Value::Record { ref fields, .. } = outer else {
            unreachable!("constructed as a record immediately above")
        };
        assert!(
            matches!(fields[0], Value::Resource(_)),
            "the intermediate container must still hold its own live value"
        );
    }

    #[test]
    fn transferring_through_a_mixed_chain_empties_only_the_final_field() {
        let module = nested_module();
        let interpreter = Interpreter::new(&module);
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(3)]);
        let outer = Value::Record {
            item: BOXY,
            type_args: Vec::new(),
            fields: vec![Value::Resource(handle)],
        };
        let path = [
            crate::place::Projection::Field {
                owner: BOXY,
                field: crate::place::FieldId(0),
            },
            crate::place::Projection::Field {
                owner: FILE,
                field: crate::place::FieldId(0),
            },
        ];
        let result = interpreter
            .take_projections(outer, &path)
            .expect("transferring through record -> resource must succeed");
        assert_eq!(result.extracted, Value::Int(3));
        // The intermediate resource handle is still exactly where it
        // belongs in the rebuilt container -- never tombstoned along
        // with the leaf that actually moved.
        let Value::Record { fields, .. } = result.container else {
            unreachable!("the container is the same record it went in as")
        };
        assert!(matches!(fields[0], Value::Resource(_)));
        assert_eq!(
            interpreter
                .resources
                .borrow()
                .observe_field(handle, 0)
                .expect("the resource itself must still be alive"),
            Value::Moved,
            "only the final selected field may be tombstoned"
        );
    }
}

/// Observable destruction order (`rfcs/0012`). Every resource is
/// constructed with a distinct table id in source order, and the event
/// log records each destruction as `drop:<id>` at the moment it
/// actually happens -- so these assertions pin the *exact* sequence,
/// not merely that everything was eventually destroyed.
#[cfg(test)]
mod destruction_order {
    use super::tests::run_with_log;

    /// Only `drop:` events, in the order they actually happened.
    fn drops(text: &str) -> Vec<String> {
        let (result, log) = run_with_log(text);
        assert!(result.is_ok(), "program failed at runtime: {result:?}");
        log.into_iter()
            .filter(|event| event.starts_with("drop:"))
            .collect()
    }

    #[test]
    fn a_records_own_affine_fields_are_destroyed_in_reverse_declaration_order() {
        // `first` is table id 0 and `second` is id 1; reverse
        // declaration order destroys 1 before 0.
        let order = drops(
            "resource File { descriptor: i64 } \
             record Pair { first: File, second: File } \
             func main() -> i64 { \
                 value pair = Pair { \
                     first: File { descriptor: 1 }, \
                     second: File { descriptor: 2 }, \
                 }; \
                 return 0 \
             }",
        );
        assert_eq!(order, vec!["drop:1", "drop:0"]);
    }

    #[test]
    fn a_resources_own_children_are_destroyed_before_its_outer_identity() {
        // `input` is id 0, `output` is id 1, and `Session` itself is id
        // 2: reverse field order first, then the outer identity last.
        let order = drops(
            "resource File { descriptor: i64 } \
             resource Session { input: File, output: File } \
             func main() -> i64 { \
                 value session = Session { \
                     input: File { descriptor: 1 }, \
                     output: File { descriptor: 2 }, \
                 }; \
                 return 0 \
             }",
        );
        assert_eq!(order, vec!["drop:1", "drop:0", "drop:2"]);
    }

    #[test]
    fn a_variants_active_case_payload_is_destroyed_in_reverse_declaration_order() {
        let order = drops(
            "resource File { descriptor: i64 } \
             variant Pair { Both(File, File), Neither } \
             func main() -> i64 { \
                 value pair = Pair.Both( \
                     File { descriptor: 1 }, \
                     File { descriptor: 2 }, \
                 ); \
                 return 0 \
             }",
        );
        assert_eq!(order, vec!["drop:1", "drop:0"]);
    }

    #[test]
    fn only_the_active_variant_case_is_destroyed() {
        // The `Neither` case owns nothing at all: the `File` built for
        // the *other* construction is destroyed on its own, and nothing
        // fabricates a payload destruction for the inactive case.
        let order = drops(
            "resource File { descriptor: i64 } \
             variant Held { Carrying(File), Neither } \
             func main() -> i64 { \
                 value empty = Held.Neither; \
                 value full = Held.Carrying(File { descriptor: 1 }); \
                 return 0 \
             }",
        );
        assert_eq!(order, vec!["drop:0"]);
    }

    #[test]
    fn a_record_nested_inside_a_variant_has_its_own_resources_destroyed() {
        let order = drops(
            "resource File { descriptor: i64 } \
             record Envelope { file: File } \
             variant Held { Carrying(Envelope), Neither } \
             func main() -> i64 { \
                 value held = Held.Carrying(Envelope { file: File { descriptor: 1 } }); \
                 return 0 \
             }",
        );
        assert_eq!(order, vec!["drop:0"]);
    }

    #[test]
    fn a_variant_nested_inside_a_resource_has_its_active_case_destroyed() {
        // `File` is id 0 and `Holder` (a declared resource) is id 1:
        // the variant field's own live payload first, the resource's
        // own outer identity last.
        let order = drops(
            "resource File { descriptor: i64 } \
             variant Held { Carrying(File), Neither } \
             resource Holder { held: Held } \
             func main() -> i64 { \
                 value holder = Holder { held: Held.Carrying(File { descriptor: 1 }) }; \
                 return 0 \
             }",
        );
        assert_eq!(order, vec!["drop:0", "drop:1"]);
    }

    #[test]
    fn a_partially_moved_parent_destroys_only_what_is_left() {
        // `input` (id 0) is moved out and destroyed explicitly first;
        // the structural drop of `session` then destroys `output` (id
        // 1) and the session's own outer identity (id 2), and never
        // touches `input` again.
        let order = drops(
            "resource File { descriptor: i64 } \
             resource Session { input: File, output: File } \
             func main() -> i64 { \
                 value session = Session { \
                     input: File { descriptor: 1 }, \
                     output: File { descriptor: 2 }, \
                 }; \
                 value input = session.input; \
                 drop input; \
                 return 0 \
             }",
        );
        assert_eq!(order, vec!["drop:0", "drop:1", "drop:2"]);
    }

    #[test]
    fn an_already_destroyed_child_is_never_destroyed_a_second_time() {
        let order = drops(
            "resource File { descriptor: i64 } \
             resource Session { input: File, output: File } \
             func main() -> i64 { \
                 value session = Session { \
                     input: File { descriptor: 1 }, \
                     output: File { descriptor: 2 }, \
                 }; \
                 drop session.input; \
                 drop session; \
                 return 0 \
             }",
        );
        assert_eq!(order, vec!["drop:0", "drop:1", "drop:2"]);
    }

    #[test]
    fn an_ignored_wildcard_payload_is_destroyed_exactly_once_before_the_arm_body() {
        // `sentinel` (id 1) is constructed after the ignored payload
        // (id 0) and destroyed by the arm body, so the ignored
        // payload's own destruction must appear *first*: it happens
        // before the body runs at all.
        let order = drops(
            "resource File { descriptor: i64 } \
             variant Held { Carrying(File), Neither } \
             func sink(take file: File) -> i64 { \
                 value descriptor = file.descriptor; \
                 drop file; \
                 return descriptor \
             } \
             func discard(take held: Held) -> i64 { \
                 return match held { \
                     Carrying(_) => sink(File { descriptor: 9 }), \
                     Neither => 0, \
                 } \
             } \
             func main() -> i64 { \
                 return discard(Held.Carrying(File { descriptor: 1 })) \
             }",
        );
        assert_eq!(order, vec!["drop:0", "drop:1"]);
    }

    #[test]
    fn two_payload_positions_are_destroyed_in_reverse_declaration_order() {
        let order = drops(
            "resource File { descriptor: i64 } \
             variant Pair { Both(File, File), Neither } \
             func discard(take pair: Pair) -> i64 { \
                 return match pair { \
                     Both(_, _) => 1, \
                     Neither => 0, \
                 } \
             } \
             func main() -> i64 { \
                 return discard(Pair.Both( \
                     File { descriptor: 1 }, \
                     File { descriptor: 2 }, \
                 )) \
             }",
        );
        assert_eq!(
            order,
            vec!["drop:1", "drop:0"],
            "an ignored payload must be destroyed in reverse declaration order"
        );
    }

    #[test]
    fn the_destruction_order_is_identical_across_repeated_runs() {
        let text = "resource File { descriptor: i64 } \
             resource Session { input: File, output: File } \
             record Pair { left: Session, right: File } \
             func main() -> i64 { \
                 value pair = Pair { \
                     left: Session { \
                         input: File { descriptor: 1 }, \
                         output: File { descriptor: 2 }, \
                     }, \
                     right: File { descriptor: 3 }, \
                 }; \
                 return 0 \
             }";
        let first = drops(text);
        let second = drops(text);
        assert_eq!(
            first, second,
            "the same program destroyed its resources in a different order twice"
        );
        // `input`=0, `output`=1, `Session`=2, `right`=3. Reverse
        // declaration order visits `right` first, then `left`, whose
        // own children precede its outer identity.
        assert_eq!(first, vec!["drop:3", "drop:1", "drop:0", "drop:2"]);
    }
}

/// Whole-aggregate destruction of a *generic* instantiation
/// (`rfcs/0008`, `rfcs/0012`). Every one of these drops the aggregate
/// itself rather than moving its fields out first, which is the only
/// shape that actually reaches the runtime's own structural drop for a
/// generic value -- and the shape under which a discarded type argument
/// leaks silently, because nothing else observes the loss.
///
/// The event log is the proof: each destruction appears as `drop:<table
/// id>` at the moment it happens, so these pin the exact sequence
/// rather than merely asserting the program finished.
#[cfg(test)]
mod generic_destruction {
    use super::tests::run_with_log;
    use super::*;
    use crate::symbol::Symbol;

    const DECLS: &str = "resource File { descriptor: i64 } \
                         record Box[T] { item: T } \
                         variant Maybe[T] { Some(T), None } ";

    fn drops(text: &str) -> Vec<String> {
        let (result, log) = run_with_log(text);
        assert!(result.is_ok(), "program failed at runtime: {result:?}");
        log.into_iter()
            .filter(|event| event.starts_with("drop:"))
            .collect()
    }

    #[test]
    fn dropping_a_generic_record_destroys_its_substituted_field() {
        let order = drops(&format!(
            "{DECLS} func main() -> i64 {{ \
               value boxed = Box[File] {{ item: File {{ descriptor: 1 }} }}; \
               drop boxed; \
               return 0 \
             }}"
        ));
        assert_eq!(
            order,
            vec!["drop:0"],
            "`Box[File]`'s own `File` must be destroyed exactly once"
        );
    }

    #[test]
    fn dropping_a_nested_generic_record_destroys_through_both_levels() {
        let order = drops(&format!(
            "{DECLS} func main() -> i64 {{ \
               value nested = Box[Box[File]] {{ item: Box[File] {{ item: File {{ descriptor: 2 }} }} }}; \
               drop nested; \
               return 0 \
             }}"
        ));
        assert_eq!(
            order,
            vec!["drop:0"],
            "`Box[Box[File]]` must destroy the `File` two substitutions down"
        );
    }

    #[test]
    fn dropping_a_generic_variant_destroys_only_its_active_case() {
        let order = drops(&format!(
            "{DECLS} func main() -> i64 {{ \
               value present = Maybe[File].Some(File {{ descriptor: 3 }}); \
               drop present; \
               value absent = Maybe[File].None; \
               drop absent; \
               return 0 \
             }}"
        ));
        assert_eq!(
            order,
            vec!["drop:0"],
            "the `Some` payload is destroyed once and `None` owns nothing"
        );
    }

    #[test]
    fn a_non_affine_instantiation_destroys_nothing_at_runtime() {
        let order = drops(&format!(
            "{DECLS} func main() -> i64 {{ \
               value plain = Box[i64] {{ item: 7 }}; \
               value file = File {{ descriptor: 1 }}; \
               drop file; \
               return plain.item \
             }}"
        ));
        assert_eq!(
            order,
            vec!["drop:0"],
            "`Box[i64]` owns nothing, so only the standalone `File` is destroyed"
        );
    }

    #[test]
    fn a_generic_record_inside_a_variant_payload_is_destroyed() {
        let order = drops(&format!(
            "{DECLS} variant Holder {{ Carry(Box[File]), Nothing }} \
             func main() -> i64 {{ \
               value held = Holder.Carry(Box[File] {{ item: File {{ descriptor: 4 }} }}); \
               drop held; \
               return 0 \
             }}"
        ));
        assert_eq!(
            order,
            vec!["drop:0"],
            "a variant payload's own generic record must not leak its resource"
        );
    }

    #[test]
    fn a_generic_variant_inside_an_ordinary_record_is_destroyed() {
        let order = drops(&format!(
            "{DECLS} record Wrap {{ m: Maybe[File] }} \
             func main() -> i64 {{ \
               value w = Wrap {{ m: Maybe[File].Some(File {{ descriptor: 5 }}) }}; \
               drop w; \
               return 0 \
             }}"
        ));
        assert_eq!(
            order,
            vec!["drop:0"],
            "an ordinary record's own generic variant field must not leak its resource"
        );
    }

    #[test]
    fn a_generic_aggregate_keeps_its_type_arguments_across_a_call_boundary() {
        let order = drops(&format!(
            "{DECLS} func relay(take boxed: Box[File]) -> Box[File] {{ return boxed }} \
             func main() -> i64 {{ \
               value first = Box[File] {{ item: File {{ descriptor: 6 }} }}; \
               value second = relay(first); \
               drop second; \
               return 0 \
             }}"
        ));
        assert_eq!(
            order,
            vec!["drop:0"],
            "type arguments must survive a transfer into and back out of a call"
        );
    }

    #[test]
    fn a_partially_moved_generic_aggregate_destroys_only_what_is_left() {
        // Two affine fields: the first is moved out and destroyed
        // explicitly (table id 0), then the aggregate itself is dropped
        // and destroys only the second (id 1).
        let order = drops(
            "resource File { descriptor: i64 } \
             record Pair[T] { left: T, right: T } \
             func sink(take file: File) -> i64 { \
                 value descriptor = file.descriptor; \
                 drop file; \
                 return descriptor \
             } \
             func main() -> i64 { \
                 value pair = Pair[File] { \
                     left: File { descriptor: 1 }, \
                     right: File { descriptor: 2 }, \
                 }; \
                 value left = pair.left; \
                 value taken = sink(left); \
                 drop pair; \
                 return taken \
             }",
        );
        assert_eq!(
            order,
            vec!["drop:0", "drop:1"],
            "a partially moved generic aggregate destroys only its remaining field"
        );
    }

    #[test]
    fn a_generic_aggregates_fields_are_destroyed_in_reverse_declaration_order() {
        let order = drops(
            "resource File { descriptor: i64 } \
             record Pair[T] { left: T, right: T } \
             func main() -> i64 { \
                 value pair = Pair[File] { \
                     left: File { descriptor: 1 }, \
                     right: File { descriptor: 2 }, \
                 }; \
                 drop pair; \
                 return 0 \
             }",
        );
        assert_eq!(
            order,
            vec!["drop:1", "drop:0"],
            "reverse declaration order, exactly as for a concrete aggregate"
        );
    }

    #[test]
    fn the_generic_destruction_order_is_identical_across_repeated_runs() {
        let text = "resource File { descriptor: i64 } \
                    record Pair[T] { left: T, right: T } \
                    func main() -> i64 { \
                        value pair = Pair[Box[File]] { \
                            left: Box[File] { item: File { descriptor: 1 } }, \
                            right: Box[File] { item: File { descriptor: 2 } }, \
                        }; \
                        drop pair; \
                        return 0 \
                    } \
                    record Box[T] { item: T }";
        let first = drops(text);
        let second = drops(text);
        assert_eq!(
            first, second,
            "the same program destroyed in a different order"
        );
        assert_eq!(first, vec!["drop:1", "drop:0"]);
    }

    // -- malformed runtime metadata ------------------------------------

    fn generic_module() -> Module {
        let name = Symbol(0);
        let param = crate::hir::TypeParamId(0);
        Module {
            functions: Vec::new(),
            records: vec![
                (
                    ItemId(90),
                    crate::nir::RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::I64)],
                        affine: true,
                    },
                ),
                (
                    ItemId(91),
                    crate::nir::RecordLayout {
                        name,
                        type_params: vec![(param, name)],
                        fields: vec![(name, Ty::Param(param, name))],
                        affine: false,
                    },
                ),
            ],
            variants: Vec::new(),
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    #[test]
    fn a_runtime_arity_disagreement_is_a_structured_error_not_a_silent_skip() {
        let module = generic_module();
        let interpreter = Interpreter::new(&module);
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(ItemId(90), vec![Value::Int(1)]);
        // `Box` declares one type parameter; this value carries two.
        let malformed = Value::Record {
            item: ItemId(91),
            type_args: vec![Ty::I64, Ty::I64],
            fields: vec![Value::Resource(handle)],
        };
        assert!(
            matches!(
                interpreter.is_affine_value(&malformed),
                Err(InterpreterError::InvalidOperation(_))
            ),
            "an arity disagreement must be reported, never answered from a partial substitution"
        );
        assert!(
            matches!(
                interpreter.drop_value(malformed),
                Err(InterpreterError::InvalidOperation(_))
            ),
            "destroying from a substitution nobody could build must be refused"
        );
        assert!(
            interpreter.resources.borrow().observe(handle).is_ok(),
            "a refused destruction must not have destroyed anything"
        );
    }

    #[test]
    fn an_unknown_runtime_item_is_a_structured_error() {
        let module = generic_module();
        let interpreter = Interpreter::new(&module);
        let unknown = Value::Record {
            item: ItemId(9999),
            type_args: Vec::new(),
            fields: Vec::new(),
        };
        assert!(matches!(
            interpreter.is_affine_value(&unknown),
            Err(InterpreterError::InvalidOperation(_))
        ));
        assert!(matches!(
            interpreter.drop_value(unknown),
            Err(InterpreterError::InvalidOperation(_))
        ));
    }

    #[test]
    fn a_well_formed_generic_value_answers_from_its_own_arguments() {
        let module = generic_module();
        let interpreter = Interpreter::new(&module);
        let name = Symbol(0);
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(ItemId(90), vec![Value::Int(1)]);
        let affine = Value::Record {
            item: ItemId(91),
            type_args: vec![Ty::Named(ItemId(90), name)],
            fields: vec![Value::Resource(handle)],
        };
        assert_eq!(interpreter.is_affine_value(&affine), Ok(true));
        let plain = Value::Record {
            item: ItemId(91),
            type_args: vec![Ty::I64],
            fields: vec![Value::Int(1)],
        };
        assert_eq!(interpreter.is_affine_value(&plain), Ok(false));
    }

    // -- malformed runtime *shape*, as opposed to malformed type args --

    #[test]
    fn a_record_value_with_more_fields_than_its_declaration_is_refused() {
        let module = generic_module();
        let interpreter = Interpreter::new(&module);
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(ItemId(90), vec![Value::Int(1)]);
        // `Box` declares exactly one field; this value carries two, so
        // the second has no declared type to answer affinity from.
        // Skipping it would skip exactly the field nothing can classify.
        let malformed = Value::Record {
            item: ItemId(91),
            type_args: vec![Ty::I64],
            fields: vec![Value::Int(1), Value::Resource(handle)],
        };
        assert!(
            matches!(
                interpreter.drop_value(malformed),
                Err(InterpreterError::InvalidOperation(_))
            ),
            "a field count disagreeing with the declaration must be refused"
        );
        assert!(
            interpreter.resources.borrow().observe(handle).is_ok(),
            "a refused destruction must not have destroyed anything"
        );
    }

    #[test]
    fn a_variant_value_with_the_wrong_payload_count_is_refused() {
        let name = Symbol(0);
        let module = Module {
            functions: Vec::new(),
            records: vec![(
                ItemId(90),
                crate::nir::RecordLayout {
                    name,
                    type_params: Vec::new(),
                    fields: vec![(name, Ty::I64)],
                    affine: true,
                },
            )],
            variants: vec![(
                ItemId(95),
                crate::nir::VariantLayout {
                    name,
                    type_params: Vec::new(),
                    cases: vec![crate::nir::CaseLayout {
                        name,
                        payload: vec![Ty::Named(ItemId(90), name)],
                    }],
                },
            )],
            protocols: Vec::new(),
            extends: Vec::new(),
        };
        let interpreter = Interpreter::new(&module);
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(ItemId(90), vec![Value::Int(1)]);
        let malformed = Value::Variant {
            item: ItemId(95),
            type_args: Vec::new(),
            case: 0,
            payload: vec![Value::Resource(handle), Value::Int(2)],
        };
        assert!(
            matches!(
                interpreter.drop_value(malformed),
                Err(InterpreterError::InvalidOperation(_))
            ),
            "a payload count disagreeing with the active case must be refused"
        );
        assert!(interpreter.resources.borrow().observe(handle).is_ok());
    }

    #[test]
    fn a_variant_value_naming_an_out_of_range_case_is_refused() {
        let module = generic_module();
        let interpreter = Interpreter::new(&module);
        let malformed = Value::Variant {
            item: ItemId(91),
            type_args: vec![Ty::I64],
            case: 7,
            payload: Vec::new(),
        };
        assert!(matches!(
            interpreter.drop_value(malformed),
            Err(InterpreterError::InvalidOperation(_))
        ));
    }
}

/// `StorePlace` as a genuine ownership transfer (`rfcs/0011`,
/// `rfcs/0012`), driven through the interpreter's own primitives rather
/// than through lowered source, so each phase can be observed
/// separately: the destination must be provably empty *before* anything
/// is transferred, the transfer must be all-or-nothing, and the source
/// must stop being a current owner the moment it succeeds.
#[cfg(test)]
mod store_place_transfer {
    use super::*;
    use crate::nir::RecordLayout;
    use crate::place::{FieldId, Projection};
    use crate::symbol::Symbol;

    const FILE: ItemId = ItemId(60);
    const HOLDER: ItemId = ItemId(61);
    const BOXY: ItemId = ItemId(62);

    /// `File` (a declared `resource`), `Holder` (an ordinary record with
    /// one `File` field), and `Box[T]` (generic, one field).
    fn module() -> Module {
        let name = Symbol(0);
        let param = crate::hir::TypeParamId(0);
        Module {
            functions: Vec::new(),
            records: vec![
                (
                    FILE,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::I64)],
                        affine: true,
                    },
                ),
                (
                    HOLDER,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Named(FILE, name))],
                        affine: false,
                    },
                ),
                (
                    BOXY,
                    RecordLayout {
                        name,
                        type_params: vec![(param, name)],
                        fields: vec![(name, Ty::Param(param, name))],
                        affine: false,
                    },
                ),
            ],
            variants: Vec::new(),
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    fn field(owner: ItemId, index: u32) -> Vec<Projection> {
        vec![Projection::Field {
            owner,
            field: FieldId(index),
        }]
    }

    fn place(root: u32, projections: Vec<Projection>) -> Place<ValueId> {
        Place {
            root: ValueId(root),
            projections,
        }
    }

    /// A `Holder` whose own field is already a tombstone (as it would be
    /// after the field was moved out), plus a fresh `File` to store back
    /// into it.
    fn emptied_holder(
        interpreter: &Interpreter<'_>,
        holder_id: u32,
        source_id: u32,
    ) -> (HashMap<ValueId, Value>, ResourceHandle) {
        let replacement = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(2)]);
        let mut values = HashMap::new();
        values.insert(
            ValueId(holder_id),
            Value::Record {
                item: HOLDER,
                type_args: Vec::new(),
                fields: vec![Value::Moved],
            },
        );
        values.insert(ValueId(source_id), Value::Resource(replacement));
        (values, replacement)
    }

    #[test]
    fn a_successful_store_transfers_ownership_into_the_place() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (mut values, replacement) = emptied_holder(&interpreter, 0, 1);

        interpreter
            .store_place_transfer(
                &mut values,
                &HashMap::new(),
                &place(0, field(HOLDER, 0)),
                ValueId(1),
            )
            .expect("storing into a provably empty field must succeed");

        let Some(Value::Record { fields, .. }) = values.get(&ValueId(0)) else {
            unreachable!("the destination is still a record")
        };
        let Value::Resource(stored) = fields[0] else {
            unreachable!("the field now holds the transferred resource")
        };
        assert_eq!(stored.id, replacement.id, "the same resource identity");
        assert!(
            stored.generation > replacement.generation,
            "a transfer must bump the generation, so the caller's own handle goes stale"
        );
        assert!(
            interpreter.resources.borrow().observe(stored).is_ok(),
            "the new owner's handle is current"
        );
    }

    #[test]
    fn the_old_source_is_no_longer_a_current_owner_after_a_store() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (mut values, replacement) = emptied_holder(&interpreter, 0, 1);

        interpreter
            .store_place_transfer(
                &mut values,
                &HashMap::new(),
                &place(0, field(HOLDER, 0)),
                ValueId(1),
            )
            .expect("the store must succeed");

        assert_eq!(
            values.get(&ValueId(1)),
            Some(&Value::Moved),
            "the source is tombstoned, not left holding a plausible-looking handle"
        );
        assert!(
            interpreter.resources.borrow().observe(replacement).is_err(),
            "the handle the source held must be stale"
        );
        assert!(
            interpreter
                .drop_value(Value::Resource(replacement))
                .is_err(),
            "a double drop attempted through the stale source must be refused"
        );
    }

    #[test]
    fn a_store_into_a_live_field_leaves_the_source_untouched() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let replacement = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(2)]);
        let mut values = HashMap::new();
        // The destination field is *not* empty: the store must be
        // refused before anything is transferred.
        values.insert(
            ValueId(0),
            Value::Record {
                item: HOLDER,
                type_args: Vec::new(),
                fields: vec![Value::Resource(live)],
            },
        );
        values.insert(ValueId(1), Value::Resource(replacement));
        let before = values.clone();

        let result = interpreter.store_place_transfer(
            &mut values,
            &HashMap::new(),
            &place(0, field(HOLDER, 0)),
            ValueId(1),
        );
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "overwriting a live field must be a structured error, got {result:?}"
        );
        assert_eq!(values, before, "a refused store must mutate nothing");
        assert!(
            interpreter.resources.borrow().observe(replacement).is_ok(),
            "the source must still be a current owner: no generation may have been bumped"
        );
        assert!(
            interpreter.resources.borrow().observe(live).is_ok(),
            "the destination's own live value must be untouched"
        );
    }

    #[test]
    fn a_store_of_an_already_dropped_source_leaves_the_destination_empty() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (mut values, replacement) = emptied_holder(&interpreter, 0, 1);
        interpreter
            .drop_value(Value::Resource(replacement))
            .expect("destroying the source first");
        let before = values.clone();

        let result = interpreter.store_place_transfer(
            &mut values,
            &HashMap::new(),
            &place(0, field(HOLDER, 0)),
            ValueId(1),
        );
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "storing a destroyed value must be refused, got {result:?}"
        );
        assert_eq!(
            values, before,
            "the destination field must still be the tombstone it was"
        );
    }

    #[test]
    fn a_store_whose_source_and_destination_are_the_same_storage_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let mut values = HashMap::new();
        values.insert(
            ValueId(0),
            Value::Record {
                item: HOLDER,
                type_args: Vec::new(),
                fields: vec![Value::Moved],
            },
        );
        let before = values.clone();

        let result = interpreter.store_place_transfer(
            &mut values,
            &HashMap::new(),
            &place(0, field(HOLDER, 0)),
            ValueId(0),
        );
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "an aggregate may not be stored into its own field, got {result:?}"
        );
        assert_eq!(values, before, "a refused self-store must mutate nothing");
    }

    /// A `Load` result and the slot it read share one storage identity,
    /// so aliasing them is the same self-store.
    #[test]
    fn a_store_aliasing_its_destination_through_a_load_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let mut values = HashMap::new();
        values.insert(
            ValueId(0),
            Value::Record {
                item: HOLDER,
                type_args: Vec::new(),
                fields: vec![Value::Moved],
            },
        );
        values.insert(ValueId(1), Value::Unit);
        // `%1` is a `Load` of slot `%0`.
        let load_origin = HashMap::from([(ValueId(1), ValueId(0))]);

        let result = interpreter.store_place_transfer(
            &mut values,
            &load_origin,
            &place(0, field(HOLDER, 0)),
            ValueId(1),
        );
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "a load of the destination's own slot is still the destination, got {result:?}"
        );
    }

    #[test]
    fn a_nested_affine_record_is_transferred_whole() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let inner = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(3)]);
        let mut values = HashMap::new();
        // Destination: a `Box[Holder]` whose field is empty.
        values.insert(
            ValueId(0),
            Value::Record {
                item: BOXY,
                type_args: vec![Ty::Named(HOLDER, Symbol(0))],
                fields: vec![Value::Moved],
            },
        );
        // Source: a whole `Holder` carrying a live resource.
        values.insert(
            ValueId(1),
            Value::Record {
                item: HOLDER,
                type_args: Vec::new(),
                fields: vec![Value::Resource(inner)],
            },
        );

        interpreter
            .store_place_transfer(
                &mut values,
                &HashMap::new(),
                &place(0, field(BOXY, 0)),
                ValueId(1),
            )
            .expect("storing a whole affine record must succeed");

        assert!(
            interpreter.resources.borrow().observe(inner).is_err(),
            "the nested resource's own identity must have been transferred too"
        );
        assert_eq!(values.get(&ValueId(1)), Some(&Value::Moved));
        // The transferred value is destroyed exactly once through its
        // new owner, and its type arguments survived the store.
        let stored = values.remove(&ValueId(0)).expect("the destination");
        assert!(
            interpreter
                .is_affine_value(&stored)
                .expect("well-formed metadata"),
            "`Box[Holder]` owns a resource through its stored field"
        );
        interpreter
            .drop_value(stored)
            .expect("destroying the new owner must succeed exactly once");
    }

    #[test]
    fn a_store_into_a_generic_aggregate_preserves_its_type_arguments() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let replacement = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(4)]);
        let mut values = HashMap::new();
        values.insert(
            ValueId(0),
            Value::Record {
                item: BOXY,
                type_args: vec![Ty::Named(FILE, Symbol(0))],
                fields: vec![Value::Moved],
            },
        );
        values.insert(ValueId(1), Value::Resource(replacement));

        interpreter
            .store_place_transfer(
                &mut values,
                &HashMap::new(),
                &place(0, field(BOXY, 0)),
                ValueId(1),
            )
            .expect("the store must succeed");

        let Some(Value::Record { type_args, .. }) = values.get(&ValueId(0)) else {
            unreachable!("the destination is still a record")
        };
        assert_eq!(
            type_args,
            &vec![Ty::Named(FILE, Symbol(0))],
            "a store must not quietly turn a `Box[File]` into a `Box[T]`"
        );
    }

    #[test]
    fn a_store_through_a_missing_field_index_is_a_structured_error() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (mut values, replacement) = emptied_holder(&interpreter, 0, 1);
        let before = values.clone();

        let result = interpreter.store_place_transfer(
            &mut values,
            &HashMap::new(),
            &place(0, field(HOLDER, 9)),
            ValueId(1),
        );
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "an out-of-range field must be reported, got {result:?}"
        );
        assert_eq!(values, before);
        assert!(
            interpreter.resources.borrow().observe(replacement).is_ok(),
            "a refused store must not have bumped the source's generation"
        );
    }

    #[test]
    fn a_refused_store_reports_the_identical_error_every_time() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (mut values, _) = emptied_holder(&interpreter, 0, 1);
        let first = interpreter.store_place_transfer(
            &mut values,
            &HashMap::new(),
            &place(0, field(HOLDER, 9)),
            ValueId(1),
        );
        let second = interpreter.store_place_transfer(
            &mut values,
            &HashMap::new(),
            &place(0, field(HOLDER, 9)),
            ValueId(1),
        );
        assert_eq!(first, second, "the same refusal must be deterministic");
    }
}
