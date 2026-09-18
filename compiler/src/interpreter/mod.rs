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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    /// The observation lease this handle was minted under (`rfcs/0013`),
    /// or `None` for a handle that belongs to no explicit observation
    /// scope at all (an owner, or an ordinary parameter's own
    /// call-scoped observation).
    ///
    /// Carried on the handle rather than looked up from the resource,
    /// because the same resource can legitimately be reached both
    /// through an observation and directly by its owner at the same
    /// time: what has ended is the *view*, not the resource. A read
    /// through a handle whose lease has ended is a structured error;
    /// the owner's own untagged handle keeps working.
    lease: Option<RuntimeObservationId>,
}

/// One runtime observation lease's own identity within one
/// [`Interpreter`]'s own lease table (`rfcs/0013`): a plain,
/// monotonically-growing index, never a pointer address and never a
/// `HashMap` key iterated for output, so nothing about a lease's
/// identity or ordering depends on allocator or hashing behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct RuntimeObservationId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LeaseStatus {
    Active,
    Ended,
}

/// One lexically scoped observation, as a real runtime object
/// (`rfcs/0013`).
///
/// The interpreter enforces observations itself and does not assume the
/// module it is running passed `nir::verify`: an ended lease really
/// stops working, a still-active lease really blocks every ownership
/// operation on what it holds, and ending a lease a derived one is
/// still nested inside is refused here too rather than left to the
/// verifier's LIFO guarantee.
#[derive(Debug, Clone)]
struct RuntimeObservation {
    id: RuntimeObservationId,
    status: LeaseStatus,
    /// Every resource identity reachable through the observed place at
    /// the moment the lease was taken, in deterministic discovery
    /// order (outermost first, then each field in declaration order).
    observed: Vec<ResourceId>,
    /// The lease this one was opened inside, if any -- what makes
    /// "ending a parent while a child is still active" answerable here
    /// rather than only statically.
    parent: Option<RuntimeObservationId>,
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
    /// Every observation lease taken during this run, indexed by
    /// [`RuntimeObservationId`] (`rfcs/0013`). Never shrinks: an ended
    /// lease keeps its slot so a handle still tagged with it resolves
    /// to something to *reject*, rather than silently going out of
    /// bounds or -- worse -- colliding with a later lease's id.
    leases: Vec<RuntimeObservation>,
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
            lease: None,
        }
    }

    /// Opens a lease over `observed` (`rfcs/0013`), nested inside
    /// `parent` when one is already active in the same frame.
    fn begin_lease(
        &mut self,
        observed: Vec<ResourceId>,
        parent: Option<RuntimeObservationId>,
    ) -> RuntimeObservationId {
        let id = RuntimeObservationId(self.leases.len() as u32);
        self.leases.push(RuntimeObservation {
            id,
            status: LeaseStatus::Active,
            observed,
            parent,
        });
        id
    }

    fn lease(&self, id: RuntimeObservationId) -> Result<&RuntimeObservation, InterpreterError> {
        self.leases
            .get(id.0 as usize)
            .ok_or_else(|| invalid("an observation handle does not refer to any known observation"))
    }

    /// Ends `id` exactly once (`rfcs/0013`).
    ///
    /// Refused when it was never opened, when it already ended, or
    /// when a lease derived from it is still active -- the last one
    /// being the runtime's own independent statement of the nesting
    /// rule, so the interpreter does not depend on having been handed
    /// verified NIR.
    fn end_lease(&mut self, id: RuntimeObservationId) -> Result<(), InterpreterError> {
        let lease = self.lease(id)?;
        if lease.status == LeaseStatus::Ended {
            return Err(invalid(
                "an observation was ended more than once at run time",
            ));
        }
        if self
            .leases
            .iter()
            .any(|other| other.parent == Some(id) && other.status == LeaseStatus::Active)
        {
            return Err(invalid(
                "cannot end an observation while an observation opened inside it is still active",
            ));
        }
        self.leases[id.0 as usize].status = LeaseStatus::Ended;
        Ok(())
    }

    /// The lowest-numbered still-active lease holding `resource`, if any
    /// (`rfcs/0013`) -- a `Vec` scan in index order, so the answer never
    /// depends on iteration order of anything hashed.
    fn active_lease_holding(&self, resource: ResourceId) -> Option<RuntimeObservationId> {
        self.leases
            .iter()
            .find(|lease| lease.status == LeaseStatus::Active && lease.observed.contains(&resource))
            .map(|lease| lease.id)
    }

    fn record(&self, handle: ResourceHandle) -> Result<&ResourceRecord, InterpreterError> {
        // A handle minted under an observation stops working the moment
        // that observation ends (`rfcs/0013`) -- checked here, at the
        // one place every read and every ownership operation resolves a
        // handle, so no later caller can forget it. The owner's own
        // untagged handle for the same resource is unaffected: what
        // ended is the view, not the resource.
        if let Some(lease) = handle.lease
            && self.lease(lease)?.status == LeaseStatus::Ended
        {
            return Err(invalid(
                "use of an observation after its own `observe` block already ended",
            ));
        }
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
            // Preserved, not cleared: downgrading an already-leased
            // handle keeps it bound to the same observation
            // (`rfcs/0013`).
            lease: handle.lease,
        })
    }

    /// Like [`Self::to_observer`], but binding the result to `lease`
    /// (`rfcs/0013`) -- what every handle an `observe.place` view
    /// carries is minted through, so ending that lease really does stop
    /// all of them working at once.
    fn to_leased_observer(
        &self,
        handle: ResourceHandle,
        lease: RuntimeObservationId,
    ) -> Result<ResourceHandle, InterpreterError> {
        self.observe(handle)?;
        Ok(ResourceHandle {
            id: handle.id,
            generation: handle.generation,
            role: RuntimeOwnershipRole::Observer,
            lease: Some(lease),
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
    ///
    /// Test-only, and deliberately so. Every ownership transfer the
    /// interpreter really performs now goes through
    /// [`Interpreter::plan_transfer`] and [`Interpreter::commit_transfer`],
    /// which validate the *whole* operation before moving any of it;
    /// this one-resource-at-a-time version is exactly the shape that
    /// left an operation half-applied when a later field turned out to
    /// be invalid. Keeping it out of the non-test build means a future
    /// caller cannot reintroduce that shape without the compiler saying
    /// so. Tests still use it to mint a deliberately stale handle.
    #[cfg(test)]
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
            lease: None,
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
        let field = record.fields.get(index).cloned().ok_or_else(|| {
            invalid("a place projects a field index out of range for this resource")
        })?;
        // Reading *through* an observer may never hand back an owning
        // handle: the field's stored handle is the owner's, and
        // returning it as-is would let an observation promote itself by
        // one projection.
        //
        // Transitively, and at every depth. Downgrading only a handle
        // stored *directly* in the field left a field holding a plain
        // `Box[Session]` record handed back untouched, owning handles
        // and all -- so one projection through a generic aggregate
        // laundered an observation back into ownership.
        match handle.role {
            // Reading through a *leased* observer binds what comes back
            // to that same lease (`rfcs/0013`): the stored field's own
            // handle belongs to the owner and carries no lease at all,
            // so handing it back untouched would let one projection
            // outlive the observation it was reached through.
            RuntimeOwnershipRole::Observer => self.observing_view(field, handle.lease, 0),
            RuntimeOwnershipRole::Owner => Ok(field),
        }
    }

    /// Rebuilds `value` as an observing view of itself: every resource
    /// handle it carries inline, at any depth, becomes an `Observer`
    /// (`rfcs/0011`).
    ///
    /// The table-level counterpart of
    /// [`Interpreter::to_observing_view`], needed here because a
    /// resource's own fields are read out of this table rather than
    /// held inline by the value that owns them. Nothing is mutated: the
    /// stored field keeps its owning handles, and only the copy handed
    /// back is downgraded.
    fn observing_view(
        &self,
        value: Value,
        lease: Option<RuntimeObservationId>,
        depth: usize,
    ) -> Result<Value, InterpreterError> {
        if depth >= crate::limits::MAX_GENERIC_DEPTH {
            return Err(invalid(
                "a runtime value is nested more deeply than this milestone supports",
            ));
        }
        match value {
            Value::Resource(inner) => Ok(Value::Resource(match lease {
                Some(lease) => self.to_leased_observer(inner, lease)?,
                None => self.to_observer(inner)?,
            })),
            Value::Record {
                item,
                type_args,
                fields,
            } => Ok(Value::Record {
                item,
                type_args,
                fields: fields
                    .into_iter()
                    .map(|field| self.observing_view(field, lease, depth + 1))
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
                    .map(|slot| self.observing_view(slot, lease, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            other => Ok(other),
        }
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

/// What a projection chain is about to be walked *for*
/// (`rfcs/0012`). The navigation is identical either way; only the
/// final step's own conditions differ, and both are refused outright
/// once the walk has crossed an observer.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PathIntent {
    /// The final field's value is about to be moved out of it, so it
    /// must currently hold one.
    Take,
    /// The final field is about to be reinitialized, so it must
    /// currently be a tombstone.
    Store,
}

/// A complete, not-yet-applied plan for one structural store
/// (`rfcs/0012`), collected before anything is mutated.
///
/// The two sets answer different questions and must not be confused.
///
/// `reachable` is the *whole* ownership graph the source carries,
/// including everything a resource holds in its own `ResourceRecord`
/// rather than inline in the value. Stopping at a resource's outer
/// handle -- as this once did -- hides exactly the cases that matter: a
/// child duplicated between a resource and its own container, an
/// identity the destination is reached through, and an ownership cycle
/// no destruction order could ever satisfy.
///
/// `transitions` is only the identities whose ownership *handle* really
/// crosses this boundary, with the generation each one moves to. A
/// child that stays nested inside a moved parent never crosses: its
/// owner is the same resource it always was, so its generation must not
/// change and handles to it stay current.
#[derive(Default)]
struct StorePlan {
    reachable: HashSet<ResourceId>,
    transitions: Vec<(ResourceId, u64)>,
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
    /// `ResourceTable` record instead -- see `ResourceRecord::fields`
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
    /// How many Napitia call frames are currently entered
    /// (`crate::limits::MAX_CALL_DEPTH`). One Napitia frame is one
    /// native `call_function` frame, so without this an ordinary
    /// recursive function exhausts the native stack and aborts the
    /// process instead of producing an error anything can report.
    call_depth: std::cell::Cell<usize>,
}

impl<'a> Interpreter<'a> {
    pub fn new(module: &'a Module) -> Self {
        Interpreter {
            module,
            resources: RefCell::new(ResourceTable::default()),
            #[cfg(test)]
            event_log: RefCell::new(Vec::new()),
            call_depth: std::cell::Cell::new(0),
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
    /// `args` (see [`crate::types::checked_substitution`], which owns
    /// that second rule for every stage): an unmapped `Ty::Param` would
    /// stay symbolic and answer "not affine", which is the one direction
    /// that leaks. Resolving the parameter list against this module's
    /// own layouts is the half that stays here.
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
        crate::types::checked_substitution(&params, args)
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
    /// `%v = observe.place @obsN <place>` (`rfcs/0013`).
    ///
    /// Strictly read-only in its first half: the place is walked
    /// through `observe_projections`, which mutates nothing at any
    /// depth, and every resource it reaches is collected in
    /// deterministic discovery order. Only then is a lease opened, and
    /// the view rebuilt around handles bound to it.
    ///
    /// A failure anywhere before the lease is opened therefore leaves
    /// the lease table, the resource table and the frame's values
    /// exactly as they were.
    fn begin_observe(
        &self,
        values: &mut HashMap<ValueId, Value>,
        load_origin: &HashMap<ValueId, ValueId>,
        active_leases: &mut Vec<(crate::hir::ObservationId, RuntimeObservationId)>,
        observation: crate::hir::ObservationId,
        place: &Place<ValueId>,
    ) -> Result<Value, InterpreterError> {
        if active_leases.iter().any(|(id, _)| *id == observation) {
            return Err(invalid(
                "an observation began again while it was still active",
            ));
        }
        let root_id = canonical_root(load_origin, place.root);
        let root = get(values, &root_id)?;
        let seen = self.observe_projections(&root, &place.projections)?;
        let mut identities = HashSet::new();
        let mut observed = Vec::new();
        self.collect_reachable_resources(&seen, &mut identities, &mut observed, 0)?;
        let parent = active_leases.last().map(|(_, lease)| *lease);
        let lease = self.resources.borrow_mut().begin_lease(observed, parent);
        active_leases.push((observation, lease));
        self.to_leased_view(seen, lease, 0)
    }

    /// `end.observe @obsN` (`rfcs/0013`).
    fn end_observe(
        &self,
        active_leases: &mut Vec<(crate::hir::ObservationId, RuntimeObservationId)>,
        observation: crate::hir::ObservationId,
    ) -> Result<(), InterpreterError> {
        match active_leases.last() {
            Some((id, lease)) if *id == observation => {
                let lease = *lease;
                self.resources.borrow_mut().end_lease(lease)?;
                active_leases.pop();
                Ok(())
            }
            Some(_) => Err(invalid(
                "an observation ended while an observation opened inside it is still active",
            )),
            None => Err(invalid(
                "an observation ended that this frame never began",
            )),
        }
    }

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
            //
            // The value handed back is an observing *view* of what the
            // walk found, at every depth. `observe_field` downgrades
            // only when the handle it reads through is already an
            // observer -- correct for that helper, which also serves
            // the traversal half of a genuine transfer, where an
            // intermediate must stay owning for the final `take_field`
            // to be legal at all. The opcode is where the answer is
            // known: `Observe` means "read without disturbing this
            // place's own current owner", and a read that is repeatable
            // by definition cannot hand back an owner, or two repeats
            // would be two owners of one resource.
            OwnershipMode::Observe => {
                let seen = self.observe_projections(&root, &place.projections)?;
                self.to_observer_if_resource(seen)
            }
            OwnershipMode::Transfer => {
                // Preflight, mutating nothing: what this move would
                // take out must not be held by an active observation
                // (`rfcs/0013`). Asked against a read-only view of the
                // exact same place, so a refusal leaves the container,
                // every generation and every field precisely as they
                // were.
                let seen = self.observe_projections(&root, &place.projections)?;
                self.reject_leased_value(&seen, "moved out of its place")?;
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

        // Phase A -- validation and planning. Nothing below this point
        // mutates anything, and the plan is complete before it does:
        // every identity the source carries, the generation each one
        // moves to, and the fully rebuilt value to install.
        //
        // The shape comes first: the planner reasons about declared
        // types, so a value that disagrees with its own declaration --
        // a resource standing where a primitive is declared, an
        // instantiation that is not the one its position names -- must
        // be refused before any of that reasoning is trusted.
        self.validate_owned_graph(&incoming)?;
        let mut plan = StorePlan::default();
        let rebuilt = self.plan_transfer(&incoming, &mut plan, 0)?;
        self.validate_store_target(&root, &place.projections)?;
        // The two ownership graphs must be disjoint, and both halves of
        // that matter.
        //
        // An identity the destination is *traversed through* would be
        // invalidated by the very transfer whose install has to reach
        // through it -- and, since the source would then own it,
        // becomes a cycle no destruction order can satisfy.
        //
        // An identity the destination merely *owns* somewhere else,
        // off the traversal path, is equally fatal: installing the
        // source would give one identity two owners inside one value.
        // Neither is visible from the outer handles alone, which is why
        // `plan.reachable` and this walk both go all the way down.
        let mut destination = Vec::new();
        self.destination_identities(&root, &place.projections, &mut destination)?;
        let mut destination_owned = HashSet::new();
        self.collect_owned_identities(&root, &mut destination_owned, 0)?;
        destination_owned.extend(destination);
        for id in destination_owned {
            if plan.reachable.contains(&id) {
                return Err(invalid(
                    "a structural store's own source and destination share a resource identity",
                ));
            }
        }

        // Phase B -- commit. Every fallible question was already
        // answered above, and the one remaining step that *returns* a
        // `Result` runs first, deliberately: the install walks the exact
        // chain `validate_store_target` just proved reachable and empty,
        // and it touches only destination identities, which Phase A
        // proved disjoint from everything moving. Running it before the
        // generation transitions means no fallible step remains after a
        // generation has changed -- so even a failure this cannot
        // actually reach would leave every generation as it found it.
        let updated_root = self.store_projections(root, &place.projections, rebuilt)?;
        self.commit_transfer(&plan);
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

    /// Takes a variant apart into one specific case, moving each claimed
    /// payload position out of the shell that still holds it
    /// (`rfcs/0012`).
    ///
    /// Validated completely before anything is written: the shell must
    /// be a live variant value of the named declaration, currently in
    /// the named case, every claimed position must exist, none may
    /// already have moved, no position may be claimed twice, and every
    /// value receiving a payload must be one this frame actually
    /// computed. A failure therefore leaves the shell exactly as it was.
    ///
    /// The values receiving the payloads are *not* re-materialized here:
    /// the preceding `VariantPayload` reads produced them, and the read
    /// plus this transfer together are one move -- the read hands the
    /// value over, this tombstones the storage so the shell can no
    /// longer be said to own it too. Without it, a later structural
    /// destruction of the shell would destroy what the arm now owns.
    fn decompose_variant(
        &self,
        values: &mut HashMap<ValueId, Value>,
        load_origin: &HashMap<ValueId, ValueId>,
        value: ValueId,
        variant: ItemId,
        case: usize,
        taken: &[(usize, ValueId)],
    ) -> Result<(), InterpreterError> {
        let shell_id = canonical_root(load_origin, value);
        let shell = get(values, &shell_id)?;
        let Value::Variant {
            item,
            type_args,
            case: active_case,
            mut payload,
        } = shell
        else {
            return Err(invalid(
                "a variant decomposition names a value that is not a variant",
            ));
        };
        if item != variant {
            return Err(invalid(
                "a variant decomposition names a different variant than its own value holds",
            ));
        }
        if active_case != case {
            return Err(invalid(
                "a variant decomposition names a case other than the one actually live",
            ));
        }
        // Taking a variant apart transfers every payload position it
        // claims, so an observation holding any of them blocks the
        // whole decomposition (`rfcs/0013`) -- checked before the shell
        // is touched.
        for slot in &payload {
            self.reject_leased_value(slot, "decomposed out of its variant")?;
        }
        // The shell's own shape first: every claim below is checked
        // against its declared payload types, so a shell that disagrees
        // with its declaration must be refused before any of that is
        // trusted.
        self.validate_owned_graph(&Value::Variant {
            item,
            type_args: type_args.clone(),
            case: active_case,
            payload: payload.clone(),
        })?;
        // Phase 1 -- validate every claim before writing any of them, so
        // a bad claim partway through cannot leave the shell with some
        // positions moved and others not.
        let mut seen: HashSet<usize> = HashSet::new();
        for (index, owner) in taken {
            if !values.contains_key(owner) {
                return Err(invalid(
                    "a variant decomposition hands a payload to a value this frame never computed",
                ));
            }
            if !seen.insert(*index) {
                return Err(invalid(
                    "a variant decomposition claims the same payload position more than once",
                ));
            }
            let Some(slot) = payload.get(*index) else {
                return Err(invalid(
                    "a variant decomposition claims a payload position out of range for its case",
                ));
            };
            if matches!(slot, Value::Moved | Value::Dropped) {
                return Err(invalid(
                    "a variant decomposition claims a position whose ownership already moved",
                ));
            }
            // The receiving value must be the value this position
            // actually holds. A different value of the same shape would
            // leave the real payload owned by nothing while this frame
            // acquired an obligation for something it never received --
            // and the shell would be tombstoned for a transfer that
            // never happened.
            let Some(receiver) = values.get(owner) else {
                return Err(invalid(
                    "a variant decomposition hands a payload to a value this frame never computed",
                ));
            };
            if receiver != slot {
                return Err(invalid(
                    "a variant decomposition hands a payload position to a value that is not what \
                     that position holds",
                ));
            }
        }
        // Phase 2 -- commit.
        for (index, _) in taken {
            payload[*index] = Value::Moved;
        }
        values.insert(
            shell_id,
            Value::Variant {
                item,
                type_args,
                case: active_case,
                payload,
            },
        );
        Ok(())
    }

    /// Builds the complete transfer plan for `value` and returns the
    /// value rebuilt around the handles it will own *after* the commit
    /// (`rfcs/0011`, `rfcs/0012`) -- validating the whole graph without
    /// mutating any of it.
    ///
    /// Validates, in one traversal: the declaration exists and its kind
    /// matches the runtime value, generic type-argument arity resolves,
    /// the runtime field/payload count equals the declared one, the
    /// active variant case exists, every handle is a live current owner,
    /// and no resource identity appears twice anywhere in the graph.
    ///
    /// That last check is why this exists at all. Validating values
    /// recursively is not enough: a malformed graph carrying the *same*
    /// identity in two positions passes a per-value check twice, because
    /// each occurrence independently sees the one live handle. The
    /// transfer then moves the first, and the second -- now stale --
    /// fails partway through, leaving the runtime half-mutated with the
    /// new owner unreachable. Collecting identities makes the duplicate
    /// visible before anything moves.
    ///
    /// The post-transfer generation is *computed*, never applied, so
    /// the rebuilt value can be constructed in full while the resource
    /// table still holds its pre-transfer state.
    ///
    /// `plan` may already carry other roots of the same operation, and
    /// is meant to: a call with several `take` arguments, or an
    /// aggregate with several fields, plans all of them into one plan so
    /// that an identity duplicated *across* two roots is caught before
    /// either is committed. `depth` bounds inline aggregate nesting,
    /// which carries no resource identity of its own to record and so
    /// cannot be bounded by `plan.reachable` the way a resource graph
    /// is.
    fn plan_transfer(
        &self,
        value: &Value,
        plan: &mut StorePlan,
        depth: usize,
    ) -> Result<Value, InterpreterError> {
        let rebuilt = self.plan_transfer_inner(value, plan, depth)?;
        // Asked once, at the top of the whole planned operation, over
        // *every* identity the transfer would move -- including the
        // ones nested inside a moved resource, which the recursion
        // reaches only through `collect_owned_identities` and never
        // individually (`rfcs/0013`). Still strictly inside phase A:
        // nothing has been mutated yet, so a refusal here leaves every
        // generation, status, field and event exactly as it found them.
        if depth == 0 {
            self.reject_leased_identities(&plan.reachable, "transferred")?;
        }
        Ok(rebuilt)
    }

    /// Refuses an ownership operation over any identity a still-active
    /// observation is holding (`rfcs/0013`).
    ///
    /// Deterministic in its own right: the offending identity is the
    /// lowest-numbered one, and the lease named is the lowest-numbered
    /// active lease holding it, so the same refused operation reports a
    /// byte-identical error every time.
    fn reject_leased_identities(
        &self,
        identities: &HashSet<ResourceId>,
        what: &str,
    ) -> Result<(), InterpreterError> {
        let mut ordered: Vec<ResourceId> = identities.iter().copied().collect();
        ordered.sort_by_key(|id| id.0);
        let table = self.resources.borrow();
        for id in ordered {
            if let Some(lease) = table.active_lease_holding(id) {
                return Err(invalid(format!(
                    "a resource cannot be {what} while observation {} is still holding it",
                    lease.0
                )));
            }
        }
        Ok(())
    }

    /// [`Self::reject_leased_identities`] for a value rather than an
    /// already-collected identity set: collects every resource the
    /// value reaches, tolerating repeats (an ownership graph's own
    /// duplicate/cycle rejection belongs to the operation being
    /// planned, not to this question).
    fn reject_leased_value(&self, value: &Value, what: &str) -> Result<(), InterpreterError> {
        let mut seen = HashSet::new();
        let mut ordered = Vec::new();
        self.collect_reachable_resources(value, &mut seen, &mut ordered, 0)?;
        self.reject_leased_identities(&seen, what)
    }

    /// Every resource identity reachable through `value`, in
    /// deterministic discovery order: the value's own handles
    /// outermost-first, then each resource's own stored fields in
    /// declaration order (`rfcs/0013`).
    ///
    /// Unlike [`Self::collect_owned_identities`], a repeat is skipped
    /// rather than refused: this answers "what does this reach", which
    /// is a question with an answer even for a graph no ownership
    /// operation would accept. Skipping repeats is also what bounds the
    /// walk on a malformed cyclic graph, alongside the depth guard.
    fn collect_reachable_resources(
        &self,
        value: &Value,
        seen: &mut HashSet<ResourceId>,
        ordered: &mut Vec<ResourceId>,
        depth: usize,
    ) -> Result<(), InterpreterError> {
        if depth >= crate::limits::MAX_GENERIC_DEPTH {
            return Err(invalid(
                "a runtime ownership graph is nested more deeply than this milestone supports",
            ));
        }
        match value {
            Value::Resource(handle) => {
                if !seen.insert(handle.id) {
                    return Ok(());
                }
                ordered.push(handle.id);
                let fields = {
                    let table = self.resources.borrow();
                    // A stale or dropped handle has nothing to walk
                    // into; whichever operation is being planned reports
                    // that on its own terms.
                    match table.record(*handle) {
                        Ok(record) => record.fields.clone(),
                        Err(_) => return Ok(()),
                    }
                };
                for field in &fields {
                    self.collect_reachable_resources(field, seen, ordered, depth + 1)?;
                }
                Ok(())
            }
            Value::Record { fields, .. } => {
                for field in fields {
                    self.collect_reachable_resources(field, seen, ordered, depth + 1)?;
                }
                Ok(())
            }
            Value::Variant { payload, .. } => {
                for slot in payload {
                    self.collect_reachable_resources(slot, seen, ordered, depth + 1)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn plan_transfer_inner(
        &self,
        value: &Value,
        plan: &mut StorePlan,
        depth: usize,
    ) -> Result<Value, InterpreterError> {
        if depth >= crate::limits::MAX_GENERIC_DEPTH {
            return Err(invalid(
                "a runtime value is nested more deeply than this milestone supports",
            ));
        }
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
                if !plan.reachable.insert(handle.id) {
                    return Err(invalid(
                        "a structural store's own source carries the same resource identity more \
                         than once",
                    ));
                }
                let generation = record.generation + 1;
                let nested = record.fields.clone();
                drop(table);
                plan.transitions.push((handle.id, generation));
                // Everything this resource owns stays nested inside it:
                // its generation does not change, but its identity is
                // still part of the graph being moved, and must be
                // visible to the duplicate, cycle and overlap checks.
                for field in &nested {
                    self.collect_owned_identities(field, &mut plan.reachable, 1)?;
                }
                Ok(Value::Resource(ResourceHandle {
                    id: handle.id,
                    generation,
                    role: RuntimeOwnershipRole::Owner,
                    lease: None,
                }))
            }
            Value::Record {
                item,
                type_args,
                fields,
            } => {
                let declared = self.record_field_types(*item, type_args)?;
                if declared.len() != fields.len() {
                    return Err(invalid(
                        "a structural store's own source record carries a field count its \
                         declaration does not declare",
                    ));
                }
                let rebuilt = fields
                    .iter()
                    .map(|field| self.plan_transfer_inner(field, plan, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Value::Record {
                    item: *item,
                    type_args: type_args.clone(),
                    fields: rebuilt,
                })
            }
            Value::Variant {
                item,
                type_args,
                case,
                payload,
            } => {
                let declared = self.case_payload_types(*item, type_args, *case)?;
                if declared.len() != payload.len() {
                    return Err(invalid(
                        "a structural store's own source variant carries a payload count its \
                         active case does not declare",
                    ));
                }
                let rebuilt = payload
                    .iter()
                    .map(|field| self.plan_transfer_inner(field, plan, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Value::Variant {
                    item: *item,
                    type_args: type_args.clone(),
                    case: *case,
                    payload: rebuilt,
                })
            }
            Value::Moved => Err(invalid("transfer of a value that was already moved")),
            Value::Dropped => Err(invalid("transfer of a value that was already destroyed")),
            other => Ok(other.clone()),
        }
    }

    /// Every resource identity `value` owns, however deeply, including
    /// the ones held inside a resource's own `ResourceRecord` rather
    /// than inline (`rfcs/0012`).
    ///
    /// This is the half a value-only walk cannot see. A `Session` value
    /// is one handle; the `File` it owns lives in the resource table,
    /// so stopping at the handle hides a child duplicated between the
    /// session and its own container, a child the destination is
    /// reached through, and any ownership cycle.
    ///
    /// An identity reached twice is refused outright: within one graph
    /// that is either a duplicate -- one identity with two owners -- or
    /// a cycle, and it is also what makes this walk terminate.
    fn collect_owned_identities(
        &self,
        value: &Value,
        out: &mut HashSet<ResourceId>,
        depth: usize,
    ) -> Result<(), InterpreterError> {
        if depth >= crate::limits::MAX_GENERIC_DEPTH {
            return Err(invalid(
                "a runtime ownership graph is nested more deeply than this milestone supports",
            ));
        }
        match value {
            Value::Resource(handle) => {
                if !out.insert(handle.id) {
                    return Err(invalid(
                        "a runtime ownership graph reaches the same resource identity twice, \
                         either duplicated or through a cycle",
                    ));
                }
                let nested = {
                    let table = self.resources.borrow();
                    table.record(*handle)?.fields.clone()
                };
                for field in &nested {
                    self.collect_owned_identities(field, out, depth + 1)?;
                }
                Ok(())
            }
            Value::Record { fields, .. } => {
                for field in fields {
                    self.collect_owned_identities(field, out, depth + 1)?;
                }
                Ok(())
            }
            Value::Variant { payload, .. } => {
                for slot in payload {
                    self.collect_owned_identities(slot, out, depth + 1)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Every resource identity the *destination* traversal has to reach
    /// through, in deterministic order (`rfcs/0012`) -- the root itself
    /// when it is resource-backed, and every intermediate the
    /// projections pass through. Never the final field being written,
    /// which holds a tombstone by the time this runs.
    ///
    /// Compared against the source's own identities so a store can never
    /// invalidate the very handle the install has to reach through.
    fn destination_identities(
        &self,
        container: &Value,
        projections: &[Projection],
        out: &mut Vec<ResourceId>,
    ) -> Result<(), InterpreterError> {
        let Some((first, rest)) = projections.split_first() else {
            return Ok(());
        };
        let index = Self::projection_index(first)?;
        match container {
            Value::Resource(handle) => {
                out.push(handle.id);
                if rest.is_empty() {
                    return Ok(());
                }
                let inner = self.resources.borrow().observe_field(*handle, index)?;
                self.destination_identities(&inner, rest, out)
            }
            Value::Record { fields, .. } => {
                let slot = fields.get(index).ok_or_else(|| {
                    invalid("a place projects a field index out of range for this record")
                })?;
                if rest.is_empty() {
                    return Ok(());
                }
                self.destination_identities(slot, rest, out)
            }
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
        // Preflight. The whole chain is validated against a value
        // nothing has written to yet, so a rejection cannot leave a
        // half-applied mutation behind: every reason this walk could
        // fail is discovered here, before the committing walk below
        // touches anything.
        self.validate_place_path(&container, projections, PathIntent::Take, false, 0)?;
        self.commit_take_projections(container, projections)
    }

    /// The committing half of [`Self::take_projections`], run only once
    /// [`Self::validate_place_path`] has proven the whole chain.
    fn commit_take_projections(
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
                    let inner = self.commit_take_projections(inner, rest)?;
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
                    let inner = self.commit_take_projections(fields[index].clone(), rest)?;
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

    /// Validates a complete projection chain before any of it is
    /// applied (`rfcs/0011`, `rfcs/0012`) -- mutating nothing, emitting
    /// no event, and advancing no generation.
    ///
    /// This is the preflight half of the three-phase shape every
    /// ownership operation in this interpreter now follows: *validate
    /// the whole access, build the complete plan, commit only once
    /// every validation succeeded.* The walk it guards used to mutate
    /// as it went and discover an ancestor's role on the way back out,
    /// which left a nested resource tombstoned behind a returned
    /// `Err`.
    ///
    /// `observed` is the transitive observation capability, and is the
    /// heart of the invariant: once the traversal crosses a merely
    /// observing handle it stays crossed, through records, variants and
    /// generic aggregates alike, so no owner-capable operation can
    /// emerge anywhere in the subtree below it. A resource's own fields
    /// are stored as the owner minted them, so propagating this flag --
    /// rather than re-reading the stored handle's role -- is what makes
    /// observation transitive rather than one level deep.
    fn validate_place_path(
        &self,
        container: &Value,
        projections: &[Projection],
        intent: PathIntent,
        observed: bool,
        depth: usize,
    ) -> Result<(), InterpreterError> {
        if depth >= crate::limits::MAX_GENERIC_DEPTH {
            return Err(invalid(
                "a place projects more deeply than this milestone supports",
            ));
        }
        let Some((first, rest)) = projections.split_first() else {
            return Ok(());
        };
        let index = Self::projection_index(first)?;
        match container {
            Value::Resource(handle) => {
                // Reading the record validates the handle itself: an
                // unknown identity, a stale generation and an
                // already-dropped resource are each refused here,
                // before anything downstream is considered.
                let inner = {
                    let table = self.resources.borrow();
                    let record = table.observe(*handle)?;
                    record.fields.get(index).cloned().ok_or_else(|| {
                        invalid("a place projects a field index out of range for this resource")
                    })?
                };
                let observed = observed || handle.role != RuntimeOwnershipRole::Owner;
                if rest.is_empty() {
                    Self::validate_final_step(&inner, intent, observed, true)
                } else {
                    self.validate_place_path(&inner, rest, intent, observed, depth + 1)
                }
            }
            Value::Record { fields, .. } => {
                let inner = fields.get(index).ok_or_else(|| {
                    invalid("a place projects a field index out of range for this record")
                })?;
                if rest.is_empty() {
                    Self::validate_final_step(inner, intent, observed, false)
                } else {
                    self.validate_place_path(inner, rest, intent, observed, depth + 1)
                }
            }
            Value::Moved => Err(invalid("use of a field after it was already moved")),
            Value::Dropped => Err(invalid("use of a field after it was already dropped")),
            other => Err(invalid(format!(
                "a place projects through a non-aggregate value ({})",
                kind_name(other)
            ))),
        }
    }

    /// The final projection step's own conditions, which are the only
    /// ones that differ between reading a value out of a place and
    /// writing one back into it.
    fn validate_final_step(
        slot: &Value,
        intent: PathIntent,
        observed: bool,
        in_resource: bool,
    ) -> Result<(), InterpreterError> {
        let tombstone = matches!(slot, Value::Moved | Value::Dropped);
        match intent {
            PathIntent::Take => {
                if observed {
                    return Err(invalid(
                        "cannot transfer a field through a merely-observing resource handle",
                    ));
                }
                if tombstone {
                    return Err(invalid(if in_resource {
                        "transfer of a resource field that was already moved or dropped"
                    } else {
                        "transfer of a record field that was already moved or dropped"
                    }));
                }
                Ok(())
            }
            PathIntent::Store => {
                if observed {
                    return Err(invalid(
                        "cannot reinitialize a field through a merely-observing resource handle",
                    ));
                }
                if !tombstone {
                    return Err(invalid(if in_resource {
                        "cannot overwrite a resource field that still owns a live value"
                    } else {
                        "cannot overwrite a record field that still owns a live value"
                    }));
                }
                Ok(())
            }
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
        // Preflight, for the same reason [`Self::take_projections`]
        // runs one: reaching the destination used to write into the
        // last resource on the path before discovering that an ancestor
        // above it was merely observed.
        self.validate_place_path(&container, projections, PathIntent::Store, false, 0)?;
        self.commit_store_projections(container, projections, value)
    }

    /// The committing half of [`Self::store_projections`], run only
    /// once [`Self::validate_place_path`] has proven the whole chain.
    fn commit_store_projections(
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
                    let updated_inner = self.commit_store_projections(inner, rest, value)?;
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
                    fields[index] =
                        self.commit_store_projections(fields[index].clone(), rest, value)?;
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

    /// Checks that `value` really is an inhabitant of the type its
    /// position declares, all the way down (`rfcs/0008`, `rfcs/0011`,
    /// `rfcs/0012`) -- mutating nothing.
    ///
    /// Counting fields and type arguments is not enough, and neither is
    /// looking only at positions whose *declared* type is affine. A
    /// `Wrapper` whose one declared field is `i64` but whose runtime
    /// slot holds a live `Resource` passed every count-based check, and
    /// destroying it left that resource alive and unreachable, because
    /// the non-affine position was never looked at.
    ///
    /// `expected` is `None` only for the root of a graph: the root
    /// declares its own identity and has no enclosing position to
    /// disagree with. Every position below it is checked against the
    /// declaration, never against the value's own claim.
    ///
    /// `seen` carries every resource identity already reached, so one
    /// identity occurring twice -- including a resource reachable from
    /// itself -- is refused rather than destroyed twice or walked
    /// forever.
    fn validate_value_against_ty(
        &self,
        value: &Value,
        expected: Option<&Ty>,
        seen: &mut HashSet<ResourceId>,
        depth: usize,
    ) -> Result<(), InterpreterError> {
        if depth >= crate::limits::MAX_GENERIC_DEPTH {
            return Err(invalid(
                "a runtime value is nested more deeply than this milestone supports",
            ));
        }
        // A tombstone stands where ownership *was*. A position that
        // never owned anything has nothing that could have moved out of
        // it, so a tombstone there is a malformed value, not an empty
        // one.
        if matches!(value, Value::Moved | Value::Dropped) {
            return match expected {
                Some(ty) if self.is_affine(ty) => Ok(()),
                Some(_) => Err(invalid(
                    "a runtime tombstone stands in a position whose declared type owns nothing",
                )),
                None => Ok(()),
            };
        }
        let primitive_ok = |matches: bool| -> Result<(), InterpreterError> {
            if matches {
                Ok(())
            } else {
                Err(invalid(
                    "a runtime value is of a different kind than its position declares",
                ))
            }
        };
        match value {
            Value::Int(_) => primitive_ok(matches!(
                expected,
                None | Some(
                    Ty::I8
                        | Ty::I16
                        | Ty::I32
                        | Ty::I64
                        | Ty::Isize
                        | Ty::U8
                        | Ty::U16
                        | Ty::U32
                        | Ty::U64
                        | Ty::Usize
                )
            )),
            Value::Float(_) => primitive_ok(matches!(expected, None | Some(Ty::F32 | Ty::F64))),
            Value::Bool(_) => primitive_ok(matches!(expected, None | Some(Ty::Bool))),
            Value::Char(_) => primitive_ok(matches!(expected, None | Some(Ty::Char))),
            Value::Str(_) => primitive_ok(matches!(expected, None | Some(Ty::Str))),
            Value::Unit => primitive_ok(matches!(expected, None | Some(Ty::Unit))),
            Value::Record {
                item,
                type_args,
                fields,
            } => {
                if let Some((declared_item, declared_args)) = required_declaration(expected)?
                    && (declared_item != *item || declared_args != *type_args)
                {
                    return Err(invalid(
                        "a runtime record names a different declaration or instantiation than its \
                         position declares",
                    ));
                }
                // A declared `resource` never lives inline: it is
                // constructed into the resource table and stands as a
                // handle, so an inline record claiming to be one is
                // malformed.
                if self.is_resource(*item) {
                    return Err(invalid(
                        "a runtime record value claims a declaration that is a `resource`, which \
                         is only ever represented by a handle",
                    ));
                }
                let declared = self.record_field_types(*item, type_args)?;
                if declared.len() != fields.len() {
                    return Err(invalid(
                        "a runtime record value's own field count disagrees with its declaration",
                    ));
                }
                for (field, field_ty) in fields.iter().zip(declared.iter()) {
                    self.validate_value_against_ty(field, Some(field_ty), seen, depth + 1)?;
                }
                Ok(())
            }
            Value::Variant {
                item,
                type_args,
                case,
                payload,
            } => {
                if let Some((declared_item, declared_args)) = required_declaration(expected)?
                    && (declared_item != *item || declared_args != *type_args)
                {
                    return Err(invalid(
                        "a runtime variant names a different declaration or instantiation than \
                         its position declares",
                    ));
                }
                let declared = self.case_payload_types(*item, type_args, *case)?;
                if declared.len() != payload.len() {
                    return Err(invalid(
                        "a runtime variant value's own payload count disagrees with its active \
                         case's declaration",
                    ));
                }
                for (slot, slot_ty) in payload.iter().zip(declared.iter()) {
                    self.validate_value_against_ty(slot, Some(slot_ty), seen, depth + 1)?;
                }
                Ok(())
            }
            Value::Resource(handle) => {
                let (item, fields) = {
                    let table = self.resources.borrow();
                    let record = table.record(*handle)?;
                    (record.item, record.fields.clone())
                };
                if let Some((declared_item, declared_args)) = required_declaration(expected)?
                    && (declared_item != item || !declared_args.is_empty())
                {
                    return Err(invalid(
                        "a runtime resource handle names a different declaration than its \
                         position declares",
                    ));
                }
                // One identity reached twice is either a duplicate --
                // which would be destroyed or transferred twice -- or a
                // cycle, which no destruction order can satisfy.
                if !seen.insert(handle.id) {
                    return Err(invalid(
                        "a runtime value graph reaches the same resource identity twice, either \
                         duplicated or through a cycle",
                    ));
                }
                let declared = self.record_field_types(item, &[])?;
                if declared.len() != fields.len() {
                    return Err(invalid(
                        "a runtime resource's own field count disagrees with its declaration",
                    ));
                }
                for (field, field_ty) in fields.iter().zip(declared.iter()) {
                    self.validate_value_against_ty(field, Some(field_ty), seen, depth + 1)?;
                }
                Ok(())
            }
            Value::Moved | Value::Dropped => Ok(()),
        }
    }

    /// Validates a whole owned graph from its root, which declares its
    /// own identity (`rfcs/0012`). Every ownership operation runs this
    /// before it plans anything, so no operation ever trusts the shape
    /// of the Rust enum it was handed.
    fn validate_owned_graph(&self, value: &Value) -> Result<(), InterpreterError> {
        let mut seen = HashSet::new();
        self.validate_value_against_ty(value, None, &mut seen, 0)
    }

    /// Validates one call argument against its parameter's own declared
    /// type, before anything is bound (`rfcs/0008`, `rfcs/0011`).
    ///
    /// The declared type is used where it is actually *resolved*, at
    /// every depth. A generic function's parameter is declared with
    /// `Ty::Param` -- either as the whole type (`value: T`) or nested
    /// inside an instantiation (`value: Box[T]`) -- and one parametric
    /// NIR body is shared by every instantiation (`rfcs/0008`), so at
    /// this boundary there is no concrete type to check the runtime
    /// value against: a `Box[File]` really does arrive where `Box[T]`
    /// is written, and demanding they match would reject every generic
    /// call. Checking only the outermost constructor is not enough
    /// either, since `Applied`'s own arguments are compared
    /// structurally.
    ///
    /// The value's own internal consistency is checked either way:
    /// shape against its own declaration, field and payload counts,
    /// tombstones only where something could have moved out, and no
    /// resource identity reached twice.
    ///
    /// `seen` is fresh per argument, deliberately. An identity appearing
    /// in two *different* arguments is only a fault when both take
    /// ownership, and that is the shared [`StorePlan`]'s question, not
    /// this one: two observations of the same resource are perfectly
    /// legal.
    fn validate_argument(&self, value: &Value, declared: &Ty) -> Result<(), InterpreterError> {
        // First prove that the value is internally consistent. Then
        // compare its declaration with the parameter type pattern. This
        // lets a symbolic parameter act as a local wildcard without
        // erasing a concrete surrounding constructor.
        let mut seen = HashSet::new();
        self.validate_value_against_ty(value, None, &mut seen, 0)?;
        if self.argument_matches_declared(value, declared)? {
            Ok(())
        } else {
            Err(invalid(
                "a runtime argument disagrees with the concrete part of its parameter's declared type",
            ))
        }
    }

    /// Matches an argument against a possibly-partial generic type.
    /// A type parameter is a wildcard only at its own position.
    fn argument_matches_declared(
        &self,
        value: &Value,
        declared: &Ty,
    ) -> Result<bool, InterpreterError> {
        match declared {
            Ty::Param(..) => Ok(true),
            Ty::Var(_) | Ty::Never | Ty::Error => Err(invalid(
                "a runtime argument fills a parameter whose declared type was never resolved",
            )),
            Ty::Applied(expected_item, expected_args) => {
                let (actual_item, actual_args) = match value {
                    Value::Record {
                        item, type_args, ..
                    }
                    | Value::Variant {
                        item, type_args, ..
                    } => (*item, type_args.clone()),
                    Value::Resource(handle) => {
                        let table = self.resources.borrow();
                        (table.record(*handle)?.item, Vec::new())
                    }
                    _ => return Ok(false),
                };
                if actual_item != *expected_item
                    || actual_args.len() != expected_args.len()
                    || !actual_args.iter().all(fully_resolved)
                {
                    return Ok(false);
                }
                let mut bindings = HashMap::new();
                Ok(expected_args
                    .iter()
                    .zip(actual_args.iter())
                    .all(|(expected, actual)| {
                        type_pattern_matches(expected, actual, &mut bindings)
                    }))
            }
            Ty::Named(expected_item, _) => {
                let actual_item = match value {
                    Value::Record { item, .. } | Value::Variant { item, .. } => *item,
                    Value::Resource(handle) => self.resources.borrow().record(*handle)?.item,
                    _ => return Ok(false),
                };
                Ok(actual_item == *expected_item)
            }
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::Isize
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::Usize => Ok(matches!(value, Value::Int(_))),
            Ty::F32 | Ty::F64 => Ok(matches!(value, Value::Float(_))),
            Ty::Bool => Ok(matches!(value, Value::Bool(_))),
            Ty::Char => Ok(matches!(value, Value::Char(_))),
            Ty::Str => Ok(matches!(value, Value::Str(_))),
            Ty::Unit => Ok(matches!(value, Value::Unit)),
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
    /// Destroys `value` and everything it still owns (`rfcs/0012`), as a
    /// transaction: the complete destruction graph is validated and
    /// ordered *before* any resource status changes or any event is
    /// emitted, so a malformed graph changes nothing at all.
    ///
    /// The earlier implementation looked each field's declared type up
    /// with `get(index)` and skipped past a miss, which let a value
    /// carrying an extra runtime field have its outer resource destroyed
    /// while a live resource in that extra field leaked -- reported as
    /// success. Nothing is ever skipped now: a shape that disagrees with
    /// its declaration is an error.
    fn drop_value(&self, value: Value) -> Result<(), InterpreterError> {
        // Phase A0 -- the shape itself, before anything is planned. The
        // planner below looks only at positions whose *declared* type
        // is affine; this looks at every position, so a live resource
        // sitting where an `i64` is declared is refused rather than
        // walked past and left unreachable.
        self.validate_owned_graph(&value)?;
        // Phase A1 -- observations, before the destruction order is
        // even computed (`rfcs/0013`). Destroying something an
        // observation is still holding is exactly what a lease exists
        // to prevent, and refusing it here leaves every status,
        // generation and event untouched.
        self.reject_leased_value(&value, "dropped")?;
        let mut plan = Vec::new();
        let mut seen = HashSet::new();
        self.plan_drop(&value, &mut seen, &mut plan, 0)?;
        // Phase B: every question was answered above, so this cannot
        // fail partway and leave the graph half-destroyed.
        for handle in plan {
            self.resources.borrow_mut().drop_resource(handle)?;
            #[cfg(test)]
            self.event_log
                .borrow_mut()
                .push(format!("drop:{}", handle.id.0));
        }
        Ok(())
    }

    /// Validates the complete destruction graph reachable through
    /// `value` and appends every resource identity to `plan` in the
    /// exact order it must be destroyed (`rfcs/0012`) -- mutating
    /// nothing.
    ///
    /// Validates at every level: the declaration exists and its kind
    /// matches the runtime value, generic type-argument arity resolves,
    /// the runtime field count equals the declared field count, the
    /// active variant case exists with the exact declared payload count,
    /// every handle is a live current owner, and no resource identity
    /// appears twice anywhere in the graph -- which alone would make one
    /// identity destroyed twice.
    ///
    /// Order is deterministic and is the destruction order itself: a
    /// value's own live affine fields in *reverse* declaration order,
    /// each fully expanded first, and a declared `resource`'s own outer
    /// identity after all of its remaining children. Only the active
    /// case of a variant is ever visited.
    fn plan_drop(
        &self,
        value: &Value,
        seen: &mut HashSet<ResourceId>,
        plan: &mut Vec<ResourceHandle>,
        depth: usize,
    ) -> Result<(), InterpreterError> {
        if depth >= crate::limits::MAX_GENERIC_DEPTH {
            return Err(invalid(
                "a destruction graph is nested more deeply than this milestone supports",
            ));
        }
        match value {
            Value::Resource(handle) => {
                if handle.role != RuntimeOwnershipRole::Owner {
                    return Err(invalid(
                        "cannot drop a resource through a merely-observing resource handle",
                    ));
                }
                if !seen.insert(handle.id) {
                    return Err(invalid(
                        "a destruction graph reaches the same resource identity twice",
                    ));
                }
                let (item, fields) = {
                    let table = self.resources.borrow();
                    // Rejects a stale handle and an already-dropped
                    // record alike, before anything is planned.
                    let record = table.observe(*handle)?;
                    (record.item, record.fields.clone())
                };
                let declared = self.record_field_types(item, &[])?;
                if declared.len() != fields.len() {
                    return Err(invalid(
                        "a runtime resource's own field count disagrees with its declaration",
                    ));
                }
                for index in (0..fields.len()).rev() {
                    if !self.is_affine(&declared[index]) {
                        continue;
                    }
                    // A child this frame's own NIR already destroyed or
                    // moved out is not this graph's to destroy.
                    if matches!(fields[index], Value::Moved | Value::Dropped) {
                        continue;
                    }
                    self.plan_drop(&fields[index], seen, plan, depth + 1)?;
                }
                // The outer identity goes last: after every child it
                // delegates to has been accounted for.
                plan.push(*handle);
                Ok(())
            }
            Value::Record {
                item,
                type_args,
                fields,
            } => {
                let declared = self.record_field_types(*item, type_args)?;
                if declared.len() != fields.len() {
                    return Err(invalid(
                        "a runtime record value's own field count disagrees with its declaration",
                    ));
                }
                for index in (0..fields.len()).rev() {
                    if !self.is_affine(&declared[index]) {
                        continue;
                    }
                    if matches!(fields[index], Value::Moved | Value::Dropped) {
                        continue;
                    }
                    self.plan_drop(&fields[index], seen, plan, depth + 1)?;
                }
                Ok(())
            }
            Value::Variant {
                item,
                type_args,
                case,
                payload,
            } => {
                // Only the active case: a case that was never
                // constructed owns nothing.
                let declared = self.case_payload_types(*item, type_args, *case)?;
                if declared.len() != payload.len() {
                    return Err(invalid(
                        "a runtime variant value's own payload count disagrees with its active \
                         case's declaration",
                    ));
                }
                for index in (0..payload.len()).rev() {
                    if !self.is_affine(&declared[index]) {
                        continue;
                    }
                    if matches!(payload[index], Value::Moved | Value::Dropped) {
                        continue;
                    }
                    self.plan_drop(&payload[index], seen, plan, depth + 1)?;
                }
                Ok(())
            }
            Value::Moved => Err(invalid("drop of a field that was already moved")),
            Value::Dropped => Err(invalid("double drop: this value was already destroyed")),
            other => Err(invalid(format!(
                "drop of a non-affine value ({})",
                kind_name(other)
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
    ///
    /// Transactional, exactly like [`Self::store_place_transfer`] and
    /// for the identical reason: the whole graph is walked, validated
    /// and *planned* first, and no generation moves until nothing
    /// fallible is left. Recursing field by field and bumping each
    /// generation as it went -- which this used to do -- meant a second
    /// field that turned out to be an observer, stale, duplicated or
    /// cyclic returned `Err` with the *first* field already transferred:
    /// the caller's handle stale, the new owning handle discarded with
    /// the failed result, and the resource permanently unreachable and
    /// undestroyable.
    ///
    /// For an operation spanning several roots -- a call's `take`
    /// arguments, an aggregate's fields -- do not call this once per
    /// root. Share one [`StorePlan`] across [`Self::plan_transfer`] for
    /// all of them and [`Self::commit_transfer`] once at the end, so a
    /// failure anywhere leaves *every* root untouched and an identity
    /// duplicated across two roots is still caught.
    fn transfer_if_resource(&self, value: Value) -> Result<Value, InterpreterError> {
        let mut plan = StorePlan::default();
        let rebuilt = self.plan_transfer(&value, &mut plan, 0)?;
        self.commit_transfer(&plan);
        Ok(rebuilt)
    }

    /// Applies a fully-built [`StorePlan`]'s own generation transitions
    /// -- the one and only point at which a planned transfer becomes
    /// real.
    ///
    /// Infallible by construction, which is the whole discipline: every
    /// question that could fail was answered while planning, so a caller
    /// can order this last and know that no error can leave the resource
    /// table half-moved. Callers must therefore have already completed
    /// every other fallible step of the operation before calling it.
    fn commit_transfer(&self, plan: &StorePlan) {
        let mut table = self.resources.borrow_mut();
        for (id, generation) in &plan.transitions {
            // Indexing is sound: every entry originates from
            // `plan_transfer`, which produced it only after
            // `ResourceTable::record` proved the id in range, and the
            // table only ever grows.
            table
                .records
                .get_mut(id.0 as usize)
                .expect("a planned transition names a record `plan_transfer` already resolved")
                .generation = *generation;
        }
    }

    /// Downgrades `value` to a merely-observing handle if it is a
    /// resource at all (`rfcs/0011`) -- every ordinary (non-`take`)
    /// parameter binding, and every `store.observe`, goes through this
    /// rather than binding the caller's own handle as-is.
    fn to_observer_if_resource(&self, value: Value) -> Result<Value, InterpreterError> {
        self.to_observing_view(value, 0)
    }

    /// Rebuilds `value` as an observing *view* of itself: every resource
    /// handle it carries, at any depth, becomes an `Observer`
    /// (`rfcs/0011`, `rfcs/0012`).
    ///
    /// Observation is transitive. Downgrading only a bare
    /// `Value::Resource` left every handle inside a `Record` or a
    /// `Variant` owning, so a `Box[File]` bound to an ordinary parameter
    /// handed the callee full owning access to the `File` the caller
    /// still owned.
    ///
    /// Nothing is mutated: a new value is built, and the caller's own
    /// keeps its owning handles.
    /// [`Self::to_observing_view`], but binding every handle it rebuilds
    /// to `lease` (`rfcs/0013`) -- what an `observe.place` hands to its
    /// own alias, so every handle the view carries, at any depth, stops
    /// working the instant that exact observation ends.
    fn to_leased_view(
        &self,
        value: Value,
        lease: RuntimeObservationId,
        depth: usize,
    ) -> Result<Value, InterpreterError> {
        if depth >= crate::limits::MAX_GENERIC_DEPTH {
            return Err(invalid(
                "a runtime value is nested more deeply than this milestone supports",
            ));
        }
        match value {
            Value::Resource(handle) => Ok(Value::Resource(
                self.resources.borrow().to_leased_observer(handle, lease)?,
            )),
            Value::Record {
                item,
                type_args,
                fields,
            } => Ok(Value::Record {
                item,
                type_args,
                fields: fields
                    .into_iter()
                    .map(|field| self.to_leased_view(field, lease, depth + 1))
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
                    .map(|slot| self.to_leased_view(slot, lease, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            other => Ok(other),
        }
    }

    fn to_observing_view(&self, value: Value, depth: usize) -> Result<Value, InterpreterError> {
        if depth >= crate::limits::MAX_GENERIC_DEPTH {
            return Err(invalid(
                "a runtime value is nested more deeply than this milestone supports",
            ));
        }
        match value {
            Value::Resource(handle) => Ok(Value::Resource(
                self.resources.borrow().to_observer(handle)?,
            )),
            Value::Record {
                item,
                type_args,
                fields,
            } => Ok(Value::Record {
                item,
                type_args,
                fields: fields
                    .into_iter()
                    .map(|field| self.to_observing_view(field, depth + 1))
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
                    .map(|slot| self.to_observing_view(slot, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
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
    /// `exiting` names the resource identities that are *leaving* this
    /// frame with the value it is returning or raising, and which
    /// therefore are not leaks. It exists because the transfer that
    /// hands them over has deliberately not happened yet: the frame may
    /// still be rejected here, and nothing may have moved if it is. The
    /// old ordering transferred first and let the resulting stale
    /// handles fall out of this walk on their own -- correct only for
    /// the frames that were never going to be rejected.
    fn leaked_resource(
        &self,
        values: &HashMap<ValueId, Value>,
        observing_params: &HashSet<ValueId>,
        exiting: &HashSet<ResourceId>,
    ) -> Option<ValueId> {
        // Sorted first, so the *lowest* `ValueId` still owning anything
        // is the one reported no matter what order the map iterates in.
        let mut candidates: Vec<(&ValueId, &Value)> = values
            .iter()
            .filter(|(id, _)| !observing_params.contains(id))
            .collect();
        candidates.sort_by_key(|(id, _)| **id);
        for (id, value) in candidates {
            let mut seen = HashSet::new();
            if self.owns_a_live_resource(value, &mut seen, 0, exiting) {
                return Some(*id);
            }
        }
        None
    }

    /// Whether `value` still owns any live resource, however deeply
    /// (`rfcs/0011`, `rfcs/0012`).
    ///
    /// Looking only at a bare `Value::Resource` missed every nested one:
    /// a `Box[File]` built inside a branch and abandoned there carries
    /// its owner handle one level down, and the frame exited reporting
    /// nothing. Records, variants, generic instantiations and a
    /// resource's own `ResourceRecord` fields are all walked.
    ///
    /// A merely-observing handle never counts: this frame never owned
    /// what it points at. `seen` bounds the walk, so a duplicated
    /// identity is visited once and a cycle terminates; `depth` bounds
    /// it again for inline nesting, which carries no identity to record.
    ///
    /// This is a backstop for malformed NIR, not a replacement for
    /// `nir::verify`'s own static answer.
    fn owns_a_live_resource(
        &self,
        value: &Value,
        seen: &mut HashSet<ResourceId>,
        depth: usize,
        exiting: &HashSet<ResourceId>,
    ) -> bool {
        if depth >= crate::limits::MAX_GENERIC_DEPTH {
            return false;
        }
        match value {
            Value::Resource(handle) => {
                if handle.role != RuntimeOwnershipRole::Owner {
                    return false;
                }
                // Leaving with the returned or raised value, along with
                // everything nested inside it: not this frame's to
                // account for any more. `exiting` already holds the
                // whole reachable graph, not merely its outer handles,
                // so there is nothing further down to walk.
                if exiting.contains(&handle.id) {
                    return false;
                }
                if !seen.insert(handle.id) {
                    return false;
                }
                let nested = {
                    let resources = self.resources.borrow();
                    match resources.record(*handle) {
                        Ok(record) if record.status == ResourceStatus::Alive => {
                            return true;
                        }
                        // Stale or already destroyed: this handle owns
                        // nothing, but a record it still names may.
                        Ok(record) => record.fields.clone(),
                        Err(_) => return false,
                    }
                };
                nested
                    .iter()
                    .any(|field| self.owns_a_live_resource(field, seen, depth + 1, exiting))
            }
            Value::Record { fields, .. } => fields
                .iter()
                .any(|field| self.owns_a_live_resource(field, seen, depth + 1, exiting)),
            Value::Variant { payload, .. } => payload
                .iter()
                .any(|slot| self.owns_a_live_resource(slot, seen, depth + 1, exiting)),
            _ => false,
        }
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
        into_result(self.call_function(function, &[], args, Vec::new())?)
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
        into_result(self.call_function(function, &[], args, Vec::new())?)
    }

    /// `evidence` is this call's own resolved capability evidence
    /// (`rfcs/0009`), one entry per `function.requirements`, in that
    /// same order -- always fully concrete (`Evidence::Extension`) by
    /// the time a frame actually runs: whichever call constructed this
    /// vector already resolved any `Evidence::Forwarded` against *its
    /// own* calling frame first (see `resolve_evidence`), so a running
    /// frame's own evidence never itself needs further resolution, only
    /// a lookup.
    /// Resolves one instruction's own written type arguments against the
    /// running frame's instantiation and requires the result to be
    /// concrete (`rfcs/0008`).
    ///
    /// A generic body is lowered once and shared, so `outer[T]` calling
    /// `inner[T]`, or constructing a `Box[T]`, really does carry
    /// `Ty::Param(T)` on the instruction. What makes it concrete is the
    /// frame: executing `outer[i64]` carries `T -> i64`, and
    /// substituting through that is what turns the symbolic argument
    /// back into the instantiation actually being run.
    ///
    /// Every site that carries type arguments goes through this, not
    /// just calls. A construction that kept them symbolic would hand the
    /// resulting *value* a type argument naming a parameter of a frame
    /// that has already returned -- and every later question asked of
    /// that value reads it: its own declared field types resolve to
    /// `Ty::Param`, which disagrees with the concrete value actually
    /// stored there, and `is_affine` answers `false` for it, which is
    /// the direction that leaks rather than over-demands.
    ///
    /// Anything still unresolved afterwards names a type nobody can
    /// supply, and is refused rather than silently used to build a
    /// substitution that would leave parameters symbolic.
    fn resolve_type_args(
        &self,
        type_args: &[Ty],
        frame_subst: &HashMap<crate::hir::TypeParamId, Ty>,
    ) -> Result<Vec<Ty>, InterpreterError> {
        type_args
            .iter()
            .map(|ty| {
                let resolved = crate::types::substitute(ty, frame_subst);
                if fully_resolved(&resolved) {
                    Ok(resolved)
                } else {
                    Err(invalid(
                        "a type argument is still unresolved after the running frame's own \
                         instantiation is applied",
                    ))
                }
            })
            .collect()
    }

    /// `type_args` is this invocation's own instantiation, in the
    /// callee's declared parameter order (`rfcs/0008`). One substitution
    /// is built from it and used for *every* parameter, which is what
    /// makes a repeated `T` mean one type across the whole argument
    /// list: `same[T](first: Box[T], second: Box[T])` cannot be handed a
    /// `Box[i64]` and a `Box[bool]`, because both are checked against
    /// the same resolved `Box[i64]`.
    ///
    /// The public entry points (`call`, `call_item`) pass no type
    /// arguments, so a generic function is refused there rather than
    /// instantiated by guesswork. Inferring one from the argument values
    /// would have to pick a binding per argument and then reconcile
    /// them, and a boundary that reconciles by taking the first answer
    /// is exactly the inconsistency this substitution exists to
    /// prevent. Callers that need a generic function instantiate it the
    /// way NIR does: through a `Call` carrying its arguments.
    ///
    /// Every entry claims one frame of
    /// [`crate::limits::MAX_CALL_DEPTH`], because one Napitia frame is
    /// one native frame: a recursion the program never terminates would
    /// otherwise exhaust the native stack and abort the process, which
    /// is not something a `Result` can report, a CLI can exit with, or a
    /// caller can catch. Exceeding the budget is an ordinary
    /// [`InterpreterError`] instead, on the same terms as every other
    /// runtime refusal.
    ///
    /// The claim is released here rather than by a `Drop` guard: this
    /// stage deliberately never relies on Rust's own destruction order
    /// for anything it means, and the one call below has exactly one way
    /// out.
    fn call_function(
        &self,
        function: &Function,
        type_args: &[Ty],
        args: Vec<Value>,
        evidence: Vec<Evidence>,
    ) -> Result<Outcome, InterpreterError> {
        if self.call_depth.get() >= crate::limits::MAX_CALL_DEPTH {
            return Err(invalid(format!(
                "call depth exceeded {} frames: a recursion this execution never unwound",
                crate::limits::MAX_CALL_DEPTH
            )));
        }
        self.call_depth.set(self.call_depth.get() + 1);
        let outcome = self.call_function_in_frame(function, type_args, args, evidence);
        self.call_depth.set(self.call_depth.get() - 1);
        outcome
    }

    /// One frame's own body, entered only through [`Self::call_function`]
    /// so the depth budget can never be bypassed.
    fn call_function_in_frame(
        &self,
        function: &Function,
        type_args: &[Ty],
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
        // One substitution for this whole invocation, built before any
        // argument is looked at. `checked_substitution` refuses rather
        // than truncating, so a generic function handed the wrong number
        // of type arguments -- none at all included, which is how the
        // public entry points reach it -- is rejected here instead of
        // being validated against parameter types that stayed symbolic.
        let declared_params: Vec<crate::hir::TypeParamId> =
            function.type_params.iter().map(|(id, _)| *id).collect();
        let Some(frame_subst) = crate::types::checked_substitution(&declared_params, type_args)
        else {
            return Err(invalid(format!(
                "function declares {} type parameter(s) but was instantiated with {}",
                declared_params.len(),
                type_args.len()
            )));
        };
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
        // Binding the parameters is one transaction over *all* of them,
        // not a per-argument one (`rfcs/0011`, `rfcs/0012`).
        //
        // A `take` parameter transfers ownership into this call: the
        // caller's own handle (if `arg` is a resource at all -- an
        // ordinary value passed to a meaningless `take` on non-resource
        // data, already rejected at check time, is left untouched here)
        // is invalidated, and this frame receives the current owner's
        // own fresh handle. An ordinary (observing) parameter never
        // transfers: `arg` is bound as a view of exactly what it was
        // given.
        //
        // Phase A -- validate and plan every argument, mutating
        // nothing. One shared `StorePlan` across all of them, which is
        // what makes an identity passed to *two* different `take`
        // parameters visible as the duplicate it is: planning each
        // argument in isolation would see one live handle twice and
        // accept both. Building the observing views here too costs
        // nothing (they allocate a new value and mutate no state) and
        // keeps every fallible step ahead of the commit.
        let mut plan = StorePlan::default();
        let mut bindings: Vec<(ValueId, Value, bool)> = Vec::with_capacity(function.params.len());
        // Every identity any observing argument can reach, collected
        // before anything is planned. An identity that also crosses the
        // boundary as a `take` argument would leave the callee holding
        // an owner it may destroy at any point *and* a view that stays
        // readable for exactly as long, with nothing sequencing the
        // two. That is refused outright below rather than accommodated:
        // an earlier attempt to make it work by rebasing the observer
        // onto the generation the transfer installs only hid the
        // problem, since the observation is still live after the owner
        // is dropped.
        let mut observed_identities: HashSet<ResourceId> = HashSet::new();
        for (param, arg) in function.params.iter().zip(args) {
            // Every parameter is checked against its type under the one
            // shared instantiation, never against the declaration's own
            // symbolic form: that is what ties a repeated `T` together
            // across the whole argument list.
            let declared = crate::types::substitute(&param.ty, &frame_subst);
            self.validate_argument(&arg, &declared)?;
            if !param.take {
                // Per argument, then unioned. A repeat *within* one
                // argument's graph is a genuine fault and stays one;
                // the same resource observed by two different arguments
                // is not, since neither observation can end it.
                let mut reached = HashSet::new();
                self.collect_owned_identities(&arg, &mut reached, 0)?;
                observed_identities.extend(reached);
            }
            let bound = if param.take {
                self.plan_transfer(&arg, &mut plan, 0)?
            } else {
                self.to_observing_view(arg, 0)?
            };
            bindings.push((param.value, bound, !param.take));
        }
        // `plan.reachable` is every identity the `take` arguments carry,
        // at any depth and through resource records as well as inline
        // aggregates, so this one intersection covers bare resources,
        // records, variants, generic instantiations and any nesting of
        // them.
        if let Some(shared) = plan
            .reachable
            .iter()
            .find(|id| observed_identities.contains(id))
        {
            return Err(invalid(format!(
                "one resource (#{}) is passed to this call as both an observing argument and a \
                 `take` argument, so the callee could destroy it while the observation is still \
                 readable",
                shared.0
            )));
        }
        // `BlockId(0)` is the entry block by definition (the verifier
        // requires exactly one to exist -- `nir::verify`), not whichever
        // block happens to be first in the vector.
        //
        // Checked *before* the commit, and last among the checks, so
        // that the commit below has no fallible step after it. A
        // malformed callee with no `bb0` used to bump every argument's
        // generation and only then report the missing block, leaving the
        // caller holding stale handles for a call that never ran a
        // single instruction.
        let mut block_id = crate::nir::BlockId(0);
        if !function.blocks.iter().any(|b| b.id == block_id) {
            return Err(InterpreterError::InvalidOperation(
                "function has no entry block (bb0)".to_string(),
            ));
        }

        // Every boundary question is now answered, so this is the last
        // action before the frame runs and nothing after it can fail.
        self.commit_transfer(&plan);
        let mut values: HashMap<ValueId, Value> = HashMap::new();
        for (id, bound, _) in bindings {
            values.insert(id, bound);
        }
        // This frame's own currently-active observation leases
        // (`rfcs/0013`), innermost last: the NIR identity paired with
        // the runtime lease it opened. A stack, so `end.observe` can
        // insist on being handed the innermost one at run time,
        // independently of whatever the verifier already proved, and so
        // a nested observation records the right `parent`. Per frame,
        // never shared: an observation cannot span a call boundary.
        let mut active_leases: Vec<(crate::hir::ObservationId, RuntimeObservationId)> = Vec::new();

        // The one place a call is recorded, and it means exactly one
        // thing: this callee's frame was successfully entered, with
        // every boundary check already passed -- arity, capability
        // evidence, generic instantiation, argument types, handle
        // liveness, duplicate transfers and observe/take aliasing.
        //
        // It used to be written at the `ValueKind::Call` site *before*
        // any of that ran, so a call rejected at the boundary still left
        // a record of having happened. Emitting it here instead makes
        // every entry path -- `Call`, `Invoke`, a protocol method, the
        // public API -- agree without each having to remember to.
        //
        // Deliberately not a claim about the body: a runtime error
        // *after* this point leaves the event standing, because the
        // frame really was entered and whatever it did before failing
        // really did happen.
        #[cfg(test)]
        self.event_log
            .borrow_mut()
            .push(format!("call:{}", function.id.0));

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
                        let value = match kind {
                            ValueKind::PlaceRead { place, mode } => {
                                self.access_place(&mut values, &load_origin, place, *mode)?
                            }
                            // Beginning an observation (`rfcs/0013`):
                            // reads the place without disturbing it,
                            // opens a lease over every resource it
                            // reaches, and binds the resulting view --
                            // recursively, at every depth -- to that
                            // lease.
                            ValueKind::ObservePlace { observation, place } => self.begin_observe(
                                &mut values,
                                &load_origin,
                                &mut active_leases,
                                *observation,
                                place,
                            )?,
                            _ => self.eval(kind, &values, &evidence, &frame_subst)?,
                        };
                        values.insert(*result, value);
                    }
                    // Ending one (`rfcs/0013`). Refused unless it is
                    // this frame's own innermost active observation:
                    // ending out of order, ending twice, and ending one
                    // that never began here are each rejected at run
                    // time in their own right, not merely statically.
                    crate::nir::Instruction::EndObserve { observation } => {
                        self.end_observe(&mut active_leases, *observation)?;
                    }
                    // Ownership of one active case's payload position
                    // genuinely moves out of the shell here
                    // (`rfcs/0012`): the slot it came from is
                    // tombstoned, so a later structural destruction of
                    // the shell skips it instead of destroying what the
                    // arm now owns, and a second transfer of the same
                    // position is a structured error rather than a
                    // silent duplicate owner.
                    crate::nir::Instruction::DecomposeVariant {
                        value,
                        variant,
                        case,
                        taken,
                    } => {
                        self.decompose_variant(
                            &mut values,
                            &load_origin,
                            *value,
                            *variant,
                            *case,
                            taken,
                        )?;
                    }
                    crate::nir::Instruction::Store { slot, value, mode } => {
                        // The runtime's own equivalent of the verifier's
                        // `STORE_OVER_OWNED_SLOT` (V0100). Writing the
                        // slot discards whatever it held, so if that is
                        // still a live owner the write would make the
                        // resource permanently unreachable and
                        // undestroyable. Checked *before* the incoming
                        // value is transferred, so a refused store bumps
                        // no generation at all.
                        //
                        // A backstop for malformed NIR, not a substitute
                        // for the static answer: verified NIR can never
                        // reach it.
                        //
                        // What the destination is allowed to hold
                        // depends on which identities this store
                        // *retires*, and only a transferring store
                        // retires any. Deciding that by comparing the
                        // source's canonical root against the slot's --
                        // as this once did, for both modes alike -- was
                        // unsound twice over: a matching root does not
                        // make a historical `Load` the slot's current
                        // value, and an observing store retires nothing
                        // no matter where its source came from.
                        let incoming = get(&values, value)?;
                        let (installed, retired) = match mode {
                            // A transferring store immediately
                            // invalidates `value`'s own prior identity
                            // (`rfcs/0011`): any later read through that
                            // same `ValueId` now fails the resource
                            // table's own generation check, exactly
                            // like a `take` argument's or a `return`'s
                            // own transfer already does.
                            //
                            // Planned rather than applied, so the
                            // overwrite check below can ask the one
                            // question that matters -- does the
                            // destination still own anything this
                            // transfer is *not* taking with it -- while
                            // the table is still untouched.
                            crate::nir::OwnershipMode::Transfer => {
                                self.validate_owned_graph(&incoming)?;
                                let mut plan = StorePlan::default();
                                let rebuilt = self.plan_transfer(&incoming, &mut plan, 0)?;
                                (Some(rebuilt), plan)
                            }
                            // An observing store never transfers -- and
                            // must never let the slot's own later reads
                            // inherit owning access either, even when
                            // `value` itself is presently an owner: the
                            // slot is always a merely-observing window
                            // (`rfcs/0011`). It retires nothing, so an
                            // owner in the destination is discarded
                            // outright, its own loaded value included.
                            crate::nir::OwnershipMode::Observe => (None, StorePlan::default()),
                        };
                        if let Some(existing) = values.get(slot) {
                            let mut seen = HashSet::new();
                            if self.owns_a_live_resource(existing, &mut seen, 0, &retired.reachable)
                            {
                                return Err(invalid(format!(
                                    "a store would overwrite a slot (%{}) that still owns an \
                                     undestroyed resource",
                                    slot.0
                                )));
                            }
                        }
                        // Every fallible step is behind us, so the
                        // commit and the install can no longer leave the
                        // table half-moved.
                        let v = match installed {
                            Some(rebuilt) => {
                                self.commit_transfer(&retired);
                                rebuilt
                            }
                            None => self.to_observer_if_resource(incoming)?,
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
                    // out instead of in.
                    //
                    // Planned but *not* applied first, because the leak
                    // backstop below can still reject this frame. This
                    // used to transfer outright and rely on the
                    // resulting stale entry in `values` to hide the
                    // returned value from the leak check -- so a frame
                    // that turned out to be leaking something else
                    // returned `Err` having already bumped the returned
                    // resource's generation, leaving the caller's own
                    // handles stale for a call that never completed.
                    // Instead the identities that really cross the
                    // boundary are named explicitly, and the commit
                    // happens only once nothing fallible is left.
                    // The result is a typed destination like any other:
                    // a value that disagrees with the signature it is
                    // leaving through is refused before it moves, so a
                    // hand-built body cannot hand its caller a
                    // `Session` where the signature promises a `File`.
                    // Checked against the *instantiated* return type, so
                    // a generic function's own `T` is compared where it
                    // is actually resolved.
                    let value = get(&values, id)?;
                    let declared = crate::types::substitute(&function.return_type, &frame_subst);
                    self.validate_argument(&value, &declared)?;
                    let mut plan = StorePlan::default();
                    let returned = self.plan_transfer(&value, &mut plan, 0)?;
                    if let Some(leaked) =
                        self.leaked_resource(&values, &observing_params, &plan.reachable)
                    {
                        return Err(invalid(format!(
                            "function returned while still owning an undestroyed resource (%{})",
                            leaked.0
                        )));
                    }
                    self.commit_transfer(&plan);
                    return Ok(Outcome::Returned(returned));
                }
                Terminator::Return(None) => {
                    if let Some(leaked) =
                        self.leaked_resource(&values, &observing_params, &HashSet::new())
                    {
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
                    type_args,
                    args,
                    evidence: call_evidence,
                    ok_slot,
                    ok_target,
                    err_targets,
                } => {
                    // Resolved through this frame's own instantiation, on
                    // exactly the terms `ValueKind::Call` uses: an
                    // `Invoke` inside a generic body carries its type
                    // arguments symbolically too.
                    let invoke_type_args = self.resolve_type_args(type_args, &frame_subst)?;
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

                    // Check all possible output slots before executing
                    // the callee. Previous occupants consumed by take
                    // arguments are excluded because the call retires
                    // exactly those identities.
                    if callee_fn.params.len() == arg_values.len()
                        && callee_fn.requirements.len() == resolved_evidence.len()
                    {
                        let callee_params: Vec<crate::hir::TypeParamId> =
                            callee_fn.type_params.iter().map(|(id, _)| *id).collect();
                        // Under the callee's own instantiation, as in
                        // `call_function`: this preflight must not judge
                        // an argument against a parameter type that is
                        // still symbolic.
                        let callee_subst =
                            crate::types::checked_substitution(&callee_params, &invoke_type_args);
                        let mut incoming = StorePlan::default();
                        for (param, arg) in callee_fn.params.iter().zip(arg_values.iter()) {
                            if let Some(subst) = &callee_subst {
                                let declared = crate::types::substitute(&param.ty, subst);
                                self.validate_argument(arg, &declared)?;
                            }
                            if param.take {
                                self.plan_transfer(arg, &mut incoming, 0)?;
                            }
                        }
                        for slot in std::iter::once(*ok_slot)
                            .chain(err_targets.iter().map(|target| target.slot))
                        {
                            if let Some(existing) = values.get(&slot) {
                                let mut seen = HashSet::new();
                                if self.owns_a_live_resource(
                                    existing,
                                    &mut seen,
                                    0,
                                    &incoming.reachable,
                                ) {
                                    return Err(invalid(format!(
                                        "an invoke would overwrite a slot (%{}) that still owns an undestroyed resource",
                                        slot.0
                                    )));
                                }
                            }
                        }
                    }
                    match self.call_function(
                        callee_fn,
                        &invoke_type_args,
                        arg_values,
                        resolved_evidence,
                    )? {
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
                    // A raised value leaves this frame exactly as a
                    // returned one does (`rfcs/0010`), so it transfers
                    // on the same terms and in the same order: plan,
                    // let the leak backstop judge the frame it is
                    // actually leaving, and only then commit.
                    let mut plan = StorePlan::default();
                    let raised = self.plan_transfer(&get(&values, value)?, &mut plan, 0)?;
                    if let Some(leaked) =
                        self.leaked_resource(&values, &observing_params, &plan.reachable)
                    {
                        return Err(invalid(format!(
                            "function raised while still owning an undestroyed resource (%{})",
                            leaked.0
                        )));
                    }
                    self.commit_transfer(&plan);
                    return Ok(Outcome::Raised(raised));
                }
            }
        }
    }

    /// `frame_subst` is the instantiation the *currently executing*
    /// function was called with (`rfcs/0008`): one parametric body is
    /// shared by every instantiation, so a nested call inside a generic
    /// body carries its type arguments symbolically -- `outer[T]`
    /// calling `inner[T]` lowers to `call @inner[T]`, and only the
    /// frame knows what `T` is right now. Resolving a call site's own
    /// type arguments through this is what turns that back into a
    /// concrete instantiation.
    fn eval(
        &self,
        kind: &ValueKind,
        values: &HashMap<ValueId, Value>,
        current_evidence: &[Evidence],
        frame_subst: &HashMap<crate::hir::TypeParamId, Ty>,
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
            // Same reason (`rfcs/0013`): beginning an observation needs
            // the frame's own lease stack, which this method cannot
            // reach.
            ValueKind::ObservePlace { .. } => Err(invalid(
                "ValueKind::ObservePlace must be evaluated by call_function directly, never through eval",
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
            ValueKind::Call(item, type_args, args, call_evidence) => {
                // Resolved through the frame's own instantiation, so a
                // nested generic call inside a generic body reaches its
                // callee concretely rather than symbolically.
                let call_type_args = self.resolve_type_args(type_args, frame_subst)?;
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
                // An ordinary `Call` never targets a fallible function
                // (`rfcs/0010`) -- that always lowers to `Invoke` instead
                // (the verifier's job to guarantee). A `Raised` outcome
                // here means the callee's own `raises` metadata and its
                // actual body disagree; guarded defensively rather than
                // silently treated as the raised value itself.
                match self.call_function(callee, &call_type_args, arg_values, resolved_evidence)? {
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
                arguments,
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
                // The implementing method is generic in the *extend's*
                // own parameters, not the protocol's, so its
                // instantiation has to be recovered rather than copied:
                // `extend[T] Equal[Box[T]]` reached through
                // `Equal[Box[i64]]` binds `T -> i64`. Matching the
                // extend's declared protocol arguments against this call
                // site's is what recovers it, and a concrete extension
                // (`extend Equal[i64]`) simply binds nothing.
                let call_arguments = self.resolve_type_args(arguments, frame_subst)?;
                if extend_layout.protocol_arguments.len() != call_arguments.len() {
                    return Err(invalid(
                        "a protocol call's own type arguments do not match the arity its \
                         extension declares",
                    ));
                }
                let mut bindings: HashMap<crate::hir::TypeParamId, Ty> = HashMap::new();
                for (declared, actual) in extend_layout
                    .protocol_arguments
                    .iter()
                    .zip(call_arguments.iter())
                {
                    if !type_pattern_matches(declared, actual, &mut bindings) {
                        return Err(invalid(
                            "a protocol call's own type arguments do not match the extension \
                             selected for it",
                        ));
                    }
                }
                let method_type_args = extend_layout
                    .type_params
                    .iter()
                    .map(|(id, _)| {
                        bindings.get(id).cloned().ok_or_else(|| {
                            invalid(
                                "an extension's own type parameter was not determined by the \
                                 protocol arguments at this call site",
                            )
                        })
                    })
                    .collect::<Result<Vec<Ty>, _>>()?;
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
                match self.call_function(callee, &method_type_args, arg_values, nested)? {
                    Outcome::Returned(value) => Ok(value),
                    Outcome::Raised(_) => Err(invalid(
                        "a protocol call's implementing method raised a failure; protocol methods that raise are not yet supported",
                    )),
                }
            }
            ValueKind::RecordCreate(item, type_args, field_ids) => {
                // Resolved against the running frame *before* anything
                // moves: a construction inside a generic body writes its
                // own type arguments symbolically (`Box[Box[T]]`), and a
                // value carrying `Ty::Param` outlives the frame that
                // parameter belongs to. Every later question asked of
                // the value reads those arguments -- its declared field
                // types, whether it is affine, whether it agrees with
                // the position it sits in -- and a symbolic one makes
                // all three wrong at once.
                let type_args = self.resolve_type_args(type_args, frame_subst)?;
                // Every field is planned into one shared plan before any
                // of them moves (`rfcs/0012`). Transferring field by
                // field meant a construction that failed on its *last*
                // field had already moved all the earlier ones, with the
                // fresh owning handles thrown away along with the failed
                // result -- and an identity appearing in two different
                // fields looked live to each of them in turn.
                // Every value is checked against the type its *own*
                // declaration resolves to, before any of them is planned
                // (`rfcs/0008`, `rfcs/0011`). Counting them is not
                // enough: a `File` whose one declared field is
                // `descriptor: i64` used to be constructible out of a
                // live resource handle, because nothing ever compared
                // the value with the position it was filling.
                let declared = self.record_field_types(*item, &type_args)?;
                if declared.len() != field_ids.len() {
                    return Err(invalid(
                        "a runtime construction supplies a field count its declaration does not \
                         declare",
                    ));
                }
                let supplied = field_ids
                    .iter()
                    .map(|id| get(values, id))
                    .collect::<Result<Vec<_>, _>>()?;
                for (value, field_ty) in supplied.iter().zip(declared.iter()) {
                    let mut seen = HashSet::new();
                    self.validate_value_against_ty(value, Some(field_ty), &mut seen, 0)?;
                }
                // Only now does anything move. Every field is planned
                // into one shared plan before any of them moves
                // (`rfcs/0012`).
                let mut plan = StorePlan::default();
                let mut fields = Vec::with_capacity(field_ids.len());
                for value in &supplied {
                    fields.push(self.plan_transfer(value, &mut plan, 0)?);
                }
                self.commit_transfer(&plan);
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
                        type_args,
                        fields,
                    })
                }
            }
            ValueKind::RecordField {
                base,
                record,
                field,
            } => {
                let selected = match get(values, base)? {
                    Value::Record { item, fields, .. } if item == *record => fields
                        .get(*field)
                        .cloned()
                        .ok_or_else(|| invalid("record field index out of range"))?,
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
                            .ok_or_else(|| invalid("resource field index out of range"))?
                    }
                    other => {
                        return Err(invalid(format!(
                            "expected a record value of the expected type, found {}",
                            kind_name(&other)
                        )));
                    }
                };
                // Selecting a field is a *read*, never a transfer:
                // `nir::lower` only ever emits this for a non-affine
                // field (an affine one becomes a `PlaceRead`, whose
                // mode says explicitly which it is), and
                // `nir::verify`'s own lattice already classifies it as
                // an observation source. Handing back what the storage
                // holds made the runtime the one stage that disagreed:
                // a resource's own field storage keeps the owning
                // handle, so reading it out of a `Session` bound to an
                // ordinary parameter produced an *owner* for the
                // nested `File` the caller still owned -- an
                // observation laundered into ownership by one
                // projection. Downgraded through the same recursive
                // view every other observation boundary uses, so a
                // resource nested at any depth, inline or through a
                // generic aggregate or a variant payload, is covered by
                // one answer rather than a second partial one.
                self.to_observer_if_resource(selected)
            }
            ValueKind::VariantCreate {
                variant,
                case,
                type_args,
                payload,
            } => {
                // Resolved against the running frame first, for the same
                // reason `RecordCreate` resolves its own.
                let type_args = self.resolve_type_args(type_args, frame_subst)?;
                // One plan across the whole payload, for the identical
                // reason `RecordCreate` uses one across the whole field
                // list.
                // The active case's own declared payload, substituted,
                // and checked before anything moves -- for the same
                // reason `RecordCreate` checks its fields. Resolving it
                // is also what rejects a case index this variant never
                // declared.
                let declared = self.case_payload_types(*variant, &type_args, *case)?;
                if declared.len() != payload.len() {
                    return Err(invalid(
                        "a runtime construction supplies a payload count its active case does not \
                         declare",
                    ));
                }
                let supplied = payload
                    .iter()
                    .map(|id| get(values, id))
                    .collect::<Result<Vec<_>, _>>()?;
                for (value, slot_ty) in supplied.iter().zip(declared.iter()) {
                    let mut seen = HashSet::new();
                    self.validate_value_against_ty(value, Some(slot_ty), &mut seen, 0)?;
                }
                let mut plan = StorePlan::default();
                let mut values_out = Vec::with_capacity(payload.len());
                for value in &supplied {
                    values_out.push(self.plan_transfer(value, &mut plan, 0)?);
                }
                self.commit_transfer(&plan);
                Ok(Value::Variant {
                    item: *variant,
                    type_args,
                    case: *case,
                    payload: values_out,
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
            &resourceck_result.observations,
            &resourceck_result.observation_exits,
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
            &resourceck_result.observations,
            &resourceck_result.observation_exits,
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
            &resourceck_result.observations,
            &resourceck_result.observation_exits,
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
            &resourceck_result.observations,
            &resourceck_result.observation_exits,
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
            // `call:main` leads every log now: a call event means "this
            // frame was entered after its boundary preflight passed", and
            // the entry frame qualifies exactly as a nested one does.
            vec![
                "call:main",
                "call:inspect",
                "drop:1",
                "call:inspect",
                "drop:0"
            ],
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
            vec!["call:main", "call:consume", "drop:0"],
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
        let outcome = interpreter.call_function(
            &module.functions[0],
            &[],
            vec![Value::Resource(arg)],
            Vec::new(),
        );
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
            &[],
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
    const PAIR: ItemId = ItemId(63);
    const HOLDERS: ItemId = ItemId(64);
    const MIXED: ItemId = ItemId(65);
    const SESSION: ItemId = ItemId(66);
    const MAYBE: ItemId = ItemId(67);
    const NEST: ItemId = ItemId(68);
    const LINKED: ItemId = ItemId(69);

    /// `File` (a declared `resource`), `Holder` (an ordinary record with
    /// one `File` field), `Box[T]` (generic, one field), `Pair` (two
    /// `File` fields), `Holders` (two `Holder` fields), `Mixed` (a
    /// `File` and a `Maybe[File]`), `Session` (a `resource` with one
    /// `File` field, used as a destination spine) and the generic
    /// variant `Maybe[T]`.
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
                (
                    PAIR,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Named(FILE, name)), (name, Ty::Named(FILE, name))],
                        affine: false,
                    },
                ),
                (
                    HOLDERS,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![
                            (name, Ty::Named(HOLDER, name)),
                            (name, Ty::Named(HOLDER, name)),
                        ],
                        affine: false,
                    },
                ),
                (
                    MIXED,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![
                            (name, Ty::Named(FILE, name)),
                            (name, Ty::Applied(MAYBE, vec![Ty::Named(FILE, name)])),
                        ],
                        affine: false,
                    },
                ),
                (
                    SESSION,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Named(FILE, name))],
                        affine: true,
                    },
                ),
                (
                    NEST,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Named(SESSION, name))],
                        affine: true,
                    },
                ),
                (
                    LINKED,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![
                            (name, Ty::Named(SESSION, name)),
                            (name, Ty::Named(FILE, name)),
                        ],
                        affine: false,
                    },
                ),
            ],
            variants: vec![(
                MAYBE,
                crate::nir::VariantLayout {
                    name,
                    type_params: vec![(param, name)],
                    cases: vec![
                        crate::nir::CaseLayout {
                            name,
                            payload: vec![Ty::Param(param, name)],
                        },
                        crate::nir::CaseLayout {
                            name,
                            payload: Vec::new(),
                        },
                    ],
                },
            )],
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

    /// A malformed source graph carrying the *same* resource identity
    /// twice validated twice -- each check looked at the one live
    /// handle independently -- and only failed partway through the
    /// transfer, after the first occurrence had already been moved.
    #[test]
    fn a_duplicate_identity_in_the_source_is_refused_without_mutation() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let shared = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let mut values = HashMap::new();
        values.insert(
            ValueId(0),
            Value::Record {
                item: BOXY,
                type_args: vec![Ty::Named(HOLDER, Symbol(0))],
                fields: vec![Value::Moved],
            },
        );
        // The same resource identity in both of `Pair`'s own fields.
        values.insert(
            ValueId(1),
            Value::Record {
                item: PAIR,
                type_args: Vec::new(),
                fields: vec![Value::Resource(shared), Value::Resource(shared)],
            },
        );
        let before = values.clone();
        let result = interpreter.store_place_transfer(
            &mut values,
            &HashMap::new(),
            &place(0, field(BOXY, 0)),
            ValueId(1),
        );
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "a duplicated resource identity must be refused, got {result:?}"
        );
        assert_eq!(values, before, "a refused store must mutate nothing");
        assert!(
            interpreter.resources.borrow().observe(shared).is_ok(),
            "no generation may have been bumped"
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

    // -- transactional rejection: nothing may change on any failure ----

    /// Every refused store must leave the frame value map, the resource
    /// table, every generation and every Alive/Moved/Dropped status
    /// exactly as it found them. Asserted by comparing the whole
    /// observable state before and after.
    fn assert_refused_without_mutation(
        interpreter: &Interpreter<'_>,
        values: &mut HashMap<ValueId, Value>,
        place: &Place<ValueId>,
        source: ValueId,
        watched: &[ResourceHandle],
        what: &str,
    ) {
        let before_values = values.clone();
        let before_table: Vec<(ItemId, u64, bool, Vec<Value>)> = interpreter
            .resources
            .borrow()
            .records
            .iter()
            .map(|r| {
                (
                    r.item,
                    r.generation,
                    r.status == ResourceStatus::Alive,
                    r.fields.clone(),
                )
            })
            .collect();

        let result = interpreter.store_place_transfer(values, &HashMap::new(), place, source);
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "{what}: expected a structured error, got {result:?}"
        );
        assert_eq!(
            *values, before_values,
            "{what}: the frame value map changed"
        );
        let after_table: Vec<(ItemId, u64, bool, Vec<Value>)> = interpreter
            .resources
            .borrow()
            .records
            .iter()
            .map(|r| {
                (
                    r.item,
                    r.generation,
                    r.status == ResourceStatus::Alive,
                    r.fields.clone(),
                )
            })
            .collect();
        assert_eq!(
            before_table, after_table,
            "{what}: the resource table changed"
        );
        for handle in watched {
            assert!(
                interpreter.resources.borrow().observe(*handle).is_ok(),
                "{what}: a watched handle went stale"
            );
        }

        // The identical error, with the state still unchanged, on a
        // second attempt.
        let again = interpreter.store_place_transfer(values, &HashMap::new(), place, source);
        assert_eq!(result, again, "{what}: the refusal is not deterministic");
        assert_eq!(*values, before_values, "{what}: the retry mutated state");
    }

    /// An empty `Box` destination plus whatever source the caller wants
    /// to try storing into it.
    fn destination_and(source: Value) -> (HashMap<ValueId, Value>, Place<ValueId>) {
        destination_typed(Ty::Named(HOLDER, Symbol(0)), source)
    }

    /// The same empty `Box` destination, instantiated for whatever the
    /// source actually is -- so a *successful* store leaves a value
    /// whose every position really does hold what it declares.
    fn destination_typed(held: Ty, source: Value) -> (HashMap<ValueId, Value>, Place<ValueId>) {
        let mut values = HashMap::new();
        values.insert(
            ValueId(0),
            Value::Record {
                item: BOXY,
                type_args: vec![held],
                fields: vec![Value::Moved],
            },
        );
        values.insert(ValueId(1), source);
        (values, place(0, field(BOXY, 0)))
    }

    #[test]
    fn a_duplicate_handle_nested_inside_records_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let shared = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        // The same identity reached through two separate `Holder`
        // records nested in one `Box`.
        let holder = |handle| Value::Record {
            item: HOLDER,
            type_args: Vec::new(),
            fields: vec![Value::Resource(handle)],
        };
        let (mut values, destination) = destination_and(Value::Record {
            item: HOLDERS,
            type_args: Vec::new(),
            fields: vec![holder(shared), holder(shared)],
        });
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[shared],
            "duplicate identity nested in records",
        );
    }

    #[test]
    fn a_duplicate_handle_across_record_and_variant_nesting_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let shared = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let (mut values, destination) = destination_typed(
            Ty::Named(MIXED, Symbol(0)),
            Value::Record {
                item: MIXED,
                type_args: Vec::new(),
                fields: vec![
                    Value::Resource(shared),
                    Value::Variant {
                        item: MAYBE,
                        type_args: vec![Ty::Named(FILE, Symbol(0))],
                        case: 0,
                        payload: vec![Value::Resource(shared)],
                    },
                ],
            },
        );
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[shared],
            "duplicate identity across record and variant",
        );
    }

    #[test]
    fn a_source_sharing_an_identity_with_the_destination_path_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        // The destination is reached *through* this resource, and the
        // source carries the same identity: transferring it would
        // invalidate the handle the install has to walk through.
        let spine = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Moved]);
        let mut values = HashMap::new();
        values.insert(ValueId(0), Value::Resource(spine));
        values.insert(ValueId(2), Value::Resource(spine));
        let destination = place(0, field(SESSION, 0));
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(2),
            &[spine],
            "source and destination path share an identity",
        );
    }

    #[test]
    fn a_stale_child_after_a_valid_sibling_is_refused_without_moving_the_sibling() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let good = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let stale = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(2)]);
        // Make the second child's handle stale by transferring it away.
        let _ = interpreter
            .resources
            .borrow_mut()
            .transfer(stale)
            .expect("transferring to create a stale handle");
        let (mut values, destination) = destination_and(Value::Record {
            item: PAIR,
            type_args: Vec::new(),
            fields: vec![Value::Resource(good), Value::Resource(stale)],
        });
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[good],
            "stale child after a valid sibling",
        );
    }

    #[test]
    fn a_source_whose_field_count_disagrees_with_its_declaration_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        // `Holder` declares one field; this value carries three.
        let (mut values, destination) = destination_and(Value::Record {
            item: HOLDER,
            type_args: Vec::new(),
            fields: vec![Value::Resource(live), Value::Int(1), Value::Int(2)],
        });
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[live],
            "field count disagreeing with the declaration",
        );
    }

    #[test]
    fn a_source_with_mismatched_generic_type_arguments_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        // `Box` declares one type parameter; this value carries two.
        let (mut values, destination) = destination_and(Value::Record {
            item: BOXY,
            type_args: vec![Ty::I64, Ty::I64],
            fields: vec![Value::Resource(live)],
        });
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[live],
            "mismatched generic type arguments",
        );
    }

    #[test]
    fn a_source_variant_with_the_wrong_payload_count_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let (mut values, destination) = destination_and(Value::Variant {
            item: MAYBE,
            type_args: vec![Ty::Named(FILE, Symbol(0))],
            case: 0,
            payload: vec![Value::Resource(live), Value::Int(2)],
        });
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[live],
            "variant payload count disagreeing with its active case",
        );
    }

    #[test]
    fn a_destination_traversed_through_a_stale_resource_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let spine = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Moved]);
        let _ = interpreter
            .resources
            .borrow_mut()
            .transfer(spine)
            .expect("transferring to make the spine handle stale");
        let replacement = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let mut values = HashMap::new();
        values.insert(ValueId(0), Value::Resource(spine));
        values.insert(ValueId(1), Value::Resource(replacement));
        let destination = place(0, field(SESSION, 0));
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[replacement],
            "destination traversed through a stale resource",
        );
    }

    #[test]
    fn a_successful_nested_generic_store_transfers_every_resource_once() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let first = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let second = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(2)]);
        let (mut values, destination) = destination_typed(
            Ty::Named(MIXED, Symbol(0)),
            Value::Record {
                item: MIXED,
                type_args: Vec::new(),
                fields: vec![
                    Value::Resource(first),
                    Value::Variant {
                        item: MAYBE,
                        type_args: vec![Ty::Named(FILE, Symbol(0))],
                        case: 0,
                        payload: vec![Value::Resource(second)],
                    },
                ],
            },
        );

        interpreter
            .store_place_transfer(&mut values, &HashMap::new(), &destination, ValueId(1))
            .expect("a well-formed nested store must succeed");

        // Every identity moved exactly once: the caller's own handles
        // are stale, and the installed graph's are current.
        for stale in [first, second] {
            assert!(
                interpreter.resources.borrow().observe(stale).is_err(),
                "each transferred identity must have moved exactly once"
            );
        }
        assert_eq!(values.get(&ValueId(1)), Some(&Value::Moved));
        let stored = values.remove(&ValueId(0)).expect("the destination");
        assert!(
            interpreter
                .is_affine_value(&stored)
                .expect("well-formed metadata"),
            "the destination owns the transferred graph"
        );
        interpreter
            .drop_value(stored)
            .expect("destroying the new owner must succeed exactly once");
    }

    // -- the complete owned graph, not just the outer handles ----------
    //
    // A resource's own children live in the resource table, not in the
    // value, so planning a transfer by walking only the value stops at
    // the outer handle. Duplicates, ownership cycles and
    // source/destination overlap all hide below that line
    // (`rfcs/0012`).

    /// Replaces `owner`'s single field with `child`, directly in the
    /// resource table -- what the runtime itself does when a resource
    /// is constructed around another.
    fn own(interpreter: &Interpreter<'_>, owner: ResourceHandle, child: Value) {
        interpreter.resources.borrow_mut().records[owner.id.0 as usize].fields = vec![child];
    }

    /// A `Session` whose one `File` field is empty.
    fn session(interpreter: &Interpreter<'_>) -> ResourceHandle {
        interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Moved])
    }

    /// A `Nest` owning `inner`.
    fn nest(interpreter: &Interpreter<'_>, inner: ResourceHandle) -> ResourceHandle {
        interpreter
            .resources
            .borrow_mut()
            .construct(NEST, vec![Value::Resource(inner)])
    }

    fn a_file(interpreter: &Interpreter<'_>, descriptor: i128) -> ResourceHandle {
        interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(descriptor)])
    }

    #[test]
    fn a_duplicate_reached_through_a_resource_and_directly_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let shared = a_file(&interpreter, 1);
        let owner = session(&interpreter);
        own(&interpreter, owner, Value::Resource(shared));
        // `Linked` carries the `Session` that owns `shared`, and
        // `shared` itself. One identity, two owners -- invisible to
        // anything that stops at the `Session`'s outer handle.
        let (mut values, destination) = destination_typed(
            Ty::Named(LINKED, Symbol(0)),
            Value::Record {
                item: LINKED,
                type_args: Vec::new(),
                fields: vec![Value::Resource(owner), Value::Resource(shared)],
            },
        );
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[shared, owner],
            "one identity owned both directly and through a resource",
        );
    }

    #[test]
    fn a_duplicate_nested_several_levels_down_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let shared = a_file(&interpreter, 1);
        let inner = session(&interpreter);
        own(&interpreter, inner, Value::Resource(shared));
        let outer = nest(&interpreter, inner);
        // `outer -> inner -> shared`, with `shared` alongside it again.
        let (mut values, destination) = destination_typed(
            Ty::Named(LINKED, Symbol(0)),
            Value::Record {
                item: LINKED,
                type_args: Vec::new(),
                fields: vec![Value::Resource(inner), Value::Resource(shared)],
            },
        );
        values.insert(ValueId(4), Value::Resource(outer));
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[shared, inner, outer],
            "the same identity twice, two levels apart",
        );
    }

    #[test]
    fn a_source_descendant_that_is_the_destination_spine_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        // The destination is written *through* `spine`, and the source
        // owns `spine` below its own outer handle. Transferring it
        // would invalidate the very handle the install walks through,
        // and leave `spine` owning the thing it lives inside.
        let spine = session(&interpreter);
        let carrier = nest(&interpreter, spine);
        let mut values = HashMap::new();
        values.insert(ValueId(0), Value::Resource(spine));
        values.insert(ValueId(2), Value::Resource(carrier));
        let destination = place(0, field(SESSION, 0));
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(2),
            &[spine, carrier],
            "a source descendant that is the destination's own spine",
        );
    }

    #[test]
    fn a_destination_descendant_that_is_in_the_source_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let shared = a_file(&interpreter, 1);
        // The destination container already owns `shared` in a sibling
        // of the slot being written, and the source carries it too.
        // Neither is on the traversal path, so only a full walk of the
        // destination's own graph can see it.
        let mut values = HashMap::new();
        values.insert(
            ValueId(0),
            Value::Record {
                item: HOLDERS,
                type_args: Vec::new(),
                fields: vec![
                    Value::Record {
                        item: HOLDER,
                        type_args: Vec::new(),
                        fields: vec![Value::Moved],
                    },
                    Value::Record {
                        item: HOLDER,
                        type_args: Vec::new(),
                        fields: vec![Value::Resource(shared)],
                    },
                ],
            },
        );
        values.insert(ValueId(1), Value::Resource(shared));
        let destination = Place {
            root: ValueId(0),
            projections: vec![
                Projection::Field {
                    owner: HOLDERS,
                    field: FieldId(0),
                },
                Projection::Field {
                    owner: HOLDER,
                    field: FieldId(0),
                },
            ],
        };
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[shared],
            "a destination descendant that is also in the source",
        );
    }

    #[test]
    fn a_direct_ownership_cycle_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let spine = session(&interpreter);
        // `spine` would end up owning itself.
        let mut values = HashMap::new();
        values.insert(ValueId(0), Value::Resource(spine));
        values.insert(ValueId(2), Value::Resource(spine));
        let destination = place(0, field(SESSION, 0));
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(2),
            &[spine],
            "a resource stored into itself",
        );
    }

    #[test]
    fn an_indirect_ownership_cycle_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let spine = session(&interpreter);
        let middle = nest(&interpreter, spine);
        // Writing `middle` into `spine`'s own empty field closes the
        // loop `spine -> middle -> spine`, two links long.
        let mut values = HashMap::new();
        values.insert(ValueId(0), Value::Resource(spine));
        values.insert(ValueId(2), Value::Resource(middle));
        let destination = place(0, field(SESSION, 0));
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(2),
            &[spine, middle],
            "an ownership cycle two links long",
        );
    }

    #[test]
    fn a_stale_child_inside_a_resource_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let stale = a_file(&interpreter, 1);
        let carrier = session(&interpreter);
        own(&interpreter, carrier, Value::Resource(stale));
        // The nested handle goes stale without the carrier knowing.
        let _ = interpreter
            .resources
            .borrow_mut()
            .transfer(stale)
            .expect("transferring to create a stale nested handle");
        let (mut values, destination) =
            destination_typed(Ty::Named(SESSION, Symbol(0)), Value::Resource(carrier));
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[],
            "a stale handle nested inside the resource being transferred",
        );
    }

    #[test]
    fn a_malformed_value_nested_inside_a_resource_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let carrier = session(&interpreter);
        // `Session` declares one `File` field; this one holds an `i64`.
        own(&interpreter, carrier, Value::Int(7));
        let (mut values, destination) =
            destination_typed(Ty::Named(SESSION, Symbol(0)), Value::Resource(carrier));
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &destination,
            ValueId(1),
            &[],
            "a nested value disagreeing with the resource's own declaration",
        );
    }

    #[test]
    fn a_nested_child_keeps_its_own_generation_when_its_parent_moves() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let child = a_file(&interpreter, 1);
        let carrier = session(&interpreter);
        own(&interpreter, carrier, Value::Resource(child));
        let before = interpreter.resources.borrow().records[child.id.0 as usize].generation;
        let (mut values, destination) =
            destination_typed(Ty::Named(SESSION, Symbol(0)), Value::Resource(carrier));

        interpreter
            .store_place_transfer(&mut values, &HashMap::new(), &destination, ValueId(1))
            .expect("a well-formed nested transfer must succeed");

        assert_eq!(
            interpreter.resources.borrow().records[child.id.0 as usize].generation,
            before,
            "ownership of the child never crossed the boundary, so its handle stays current"
        );
        assert!(
            interpreter.resources.borrow().observe(child).is_ok(),
            "the child is still reachable through its unchanged handle"
        );
        assert!(
            interpreter.resources.borrow().observe(carrier).is_err(),
            "the carrier's own handle moved, so the caller's copy is stale"
        );
        let stored = values.remove(&ValueId(0)).expect("the destination");
        interpreter
            .drop_value(stored)
            .expect("destroying the new owner must succeed exactly once");
    }
}

/// Variant ownership is per *path* (`rfcs/0012`): one branch may destroy
/// the whole value while a disjoint branch takes it apart and owns the
/// payload instead. The event log is the proof that each resource is
/// destroyed exactly once on whichever path actually ran -- a leak and a
/// double drop both show up here, and neither shows up in a return
/// value.
#[cfg(test)]
mod branch_local_variants {
    use super::tests::run_with_log;

    const DECLS: &str = "resource File { descriptor: i64 } \
                         variant Maybe[T] { Some(T), None } \
                         func sink(take file: File) -> i64 { \
                             value descriptor = file.descriptor; \
                             drop file; \
                             return descriptor \
                         } ";

    fn drops(text: &str) -> Vec<String> {
        let (result, log) = run_with_log(text);
        assert!(result.is_ok(), "program failed at runtime: {result:?}");
        log.into_iter()
            .filter(|event| event.starts_with("drop:"))
            .collect()
    }

    const DISPOSE: &str = "func dispose(cond: bool, take maybe: Maybe[File]) -> i64 { \
                               if cond { \
                                   drop maybe; \
                                   return 1; \
                               } \
                               return match maybe { \
                                   Some(file) => { drop file; 2 }, \
                                   None => 0, \
                               } \
                           } ";

    #[test]
    fn the_whole_value_branch_destroys_its_payload_exactly_once() {
        let order = drops(&format!(
            "{DECLS}{DISPOSE} func main() -> i64 {{ \
               return dispose(true, Maybe[File].Some(File {{ descriptor: 1 }})) \
             }}"
        ));
        assert_eq!(
            order,
            vec!["drop:0"],
            "dropping the shell destroys the payload it still owns, once"
        );
    }

    #[test]
    fn the_matching_branch_destroys_its_payload_exactly_once() {
        let order = drops(&format!(
            "{DECLS}{DISPOSE} func main() -> i64 {{ \
               return dispose(false, Maybe[File].Some(File {{ descriptor: 1 }})) \
             }}"
        ));
        assert_eq!(
            order,
            vec!["drop:0"],
            "the arm owns the payload and destroys it, once -- the shell no longer owns it"
        );
    }

    #[test]
    fn the_inactive_case_destroys_nothing() {
        let order = drops(&format!(
            "{DECLS}{DISPOSE} func main() -> i64 {{ \
               return dispose(false, Maybe[File].None) \
             }}"
        ));
        assert_eq!(order, Vec::<String>::new(), "`None` owns nothing at all");
    }

    /// The same program with the branches written the other way round
    /// must behave identically: nothing about this may depend on which
    /// branch happens to come first.
    #[test]
    fn reversing_the_branch_order_changes_nothing() {
        let reversed = "func dispose(cond: bool, take maybe: Maybe[File]) -> i64 { \
                            if cond { \
                                return match maybe { \
                                    Some(file) => { drop file; 2 }, \
                                    None => 0, \
                                }; \
                            } \
                            drop maybe; \
                            return 1 \
                        } ";
        let matched = drops(&format!(
            "{DECLS}{reversed} func main() -> i64 {{ \
               return dispose(true, Maybe[File].Some(File {{ descriptor: 1 }})) \
             }}"
        ));
        let dropped = drops(&format!(
            "{DECLS}{reversed} func main() -> i64 {{ \
               return dispose(false, Maybe[File].Some(File {{ descriptor: 1 }})) \
             }}"
        ));
        assert_eq!(matched, vec!["drop:0"]);
        assert_eq!(dropped, vec!["drop:0"]);
    }

    #[test]
    fn an_arm_returning_its_payload_transfers_it_instead_of_destroying_it() {
        // The returned payload is destroyed by its new owner, after the
        // fallback the other arm would have returned: exactly one
        // destruction each, in caller order.
        let order = drops(&format!(
            "{DECLS} func unwrap(take maybe: Maybe[File], take fallback: File) -> File {{ \
               return match maybe {{ \
                 Some(file) => {{ drop fallback; file }}, \
                 None => fallback, \
               }} \
             }} \
             func main() -> i64 {{ \
               value taken = unwrap( \
                 Maybe[File].Some(File {{ descriptor: 1 }}), \
                 File {{ descriptor: 2 }}, \
               ); \
               return sink(taken) \
             }}"
        ));
        assert_eq!(
            order,
            vec!["drop:1", "drop:0"],
            "the unused fallback is destroyed inside the arm, the returned payload by its caller"
        );
    }

    #[test]
    fn a_wildcard_arm_destroys_the_payload_it_ignores() {
        let order = drops(&format!(
            "{DECLS} func discard(take maybe: Maybe[File]) -> i64 {{ \
               return match maybe {{ Some(_) => 7, None => 0 }} \
             }} \
             func main() -> i64 {{ \
               return discard(Maybe[File].Some(File {{ descriptor: 1 }})) \
             }}"
        ));
        assert_eq!(order, vec!["drop:0"]);
    }

    #[test]
    fn a_nested_generic_variant_is_taken_apart_at_each_level() {
        let decls = "resource File { descriptor: i64 } \
                     variant Maybe[T] { Some(T), None } \
                     variant Outer { Wrap(Maybe[File]), Empty } \
                     func nested(take outer: Outer) -> i64 { \
                         return match outer { \
                             Wrap(Some(file)) => { drop file; 1 }, \
                             Wrap(None) => 2, \
                             Empty => 3, \
                         } \
                     } ";
        assert_eq!(
            drops(&format!(
                "{decls} func main() -> i64 {{ \
                   return nested(Outer.Wrap(Maybe[File].Some(File {{ descriptor: 1 }}))) \
                 }}"
            )),
            vec!["drop:0"],
            "the innermost payload is destroyed exactly once"
        );
        assert_eq!(
            drops(&format!(
                "{decls} func main() -> i64 {{ \
                   return nested(Outer.Wrap(Maybe[File].None)) \
                 }}"
            )),
            Vec::<String>::new(),
            "an inactive inner case owns nothing"
        );
        assert_eq!(
            drops(&format!(
                "{decls} func main() -> i64 {{ return nested(Outer.Empty) }}"
            )),
            Vec::<String>::new(),
            "an inactive outer case owns nothing"
        );
    }

    #[test]
    fn a_diverging_arm_still_destroys_what_it_owns() {
        let order = drops(&format!(
            "variant Fail {{ Bad }} {DECLS} \
             func diverging(take maybe: Maybe[File]) -> i64 raises Fail {{ \
               return match maybe {{ \
                 Some(file) => {{ drop file; raise Fail.Bad; }}, \
                 None => 5, \
               }} \
             }} \
             func main() -> i64 {{ \
               return handle diverging(Maybe[File].Some(File {{ descriptor: 1 }})) {{ \
                 success v => v, \
                 failure Fail.Bad => 100, \
               }} \
             }}"
        ));
        assert_eq!(order, vec!["drop:0"]);
    }

    #[test]
    fn a_match_whose_arms_all_diverge_accounts_for_each_path() {
        let decls = format!(
            "{DECLS} func all_diverging(take maybe: Maybe[File]) -> i64 {{ \
               match maybe {{ \
                 Some(file) => {{ return sink(file); }}, \
                 None => {{ return 0; }}, \
               }} \
             }} "
        );
        assert_eq!(
            drops(&format!(
                "{decls} func main() -> i64 {{ \
                   return all_diverging(Maybe[File].Some(File {{ descriptor: 1 }})) \
                 }}"
            )),
            vec!["drop:0"]
        );
        assert_eq!(
            drops(&format!(
                "{decls} func main() -> i64 {{ return all_diverging(Maybe[File].None) }}"
            )),
            Vec::<String>::new()
        );
    }

    /// Two payload positions, one bound and one ignored: both are
    /// claimed by the same decomposition, and destroyed in reverse
    /// payload declaration order.
    #[test]
    fn two_payload_positions_are_each_claimed_exactly_once() {
        let order = drops(
            "resource File { descriptor: i64 } \
             variant Pair { Both(File, File), Neither } \
             func sink(take file: File) -> i64 { \
                 value descriptor = file.descriptor; \
                 drop file; \
                 return descriptor \
             } \
             func first(take pair: Pair) -> i64 { \
                 return match pair { \
                     Both(left, _) => sink(left), \
                     Neither => 0, \
                 } \
             } \
             func main() -> i64 { \
                 return first(Pair.Both( \
                     File { descriptor: 1 }, \
                     File { descriptor: 2 }, \
                 )) \
             }",
        );
        assert_eq!(
            order,
            vec!["drop:1", "drop:0"],
            "the ignored position is destroyed first, then the bound one by its consumer"
        );
    }

    #[test]
    fn the_destruction_order_is_identical_across_repeated_runs() {
        let text = format!(
            "{DECLS}{DISPOSE} func main() -> i64 {{ \
               value a = dispose(true, Maybe[File].Some(File {{ descriptor: 1 }})); \
               value b = dispose(false, Maybe[File].Some(File {{ descriptor: 2 }})); \
               return a + b \
             }}"
        );
        let first = drops(&text);
        let second = drops(&text);
        assert_eq!(
            first, second,
            "the same program destroyed in a different order"
        );
        assert_eq!(first, vec!["drop:0", "drop:1"]);
    }
}

/// Destruction is a transaction (`rfcs/0012`): the complete graph is
/// validated and ordered before any resource status changes or any event
/// is emitted, so a malformed graph changes nothing at all.
///
/// An earlier implementation looked each field's declared type up with
/// `get(index)` and skipped past a miss, which let a value carrying an
/// extra runtime field have its outer resource destroyed while a live
/// resource in that extra field leaked -- reported as success.
#[cfg(test)]
mod drop_transaction {
    use super::*;
    use crate::nir::{CaseLayout, RecordLayout, VariantLayout};
    use crate::symbol::Symbol;

    const FILE: ItemId = ItemId(70);
    const SESSION: ItemId = ItemId(71);
    const ENVELOPE: ItemId = ItemId(72);
    const BOXY: ItemId = ItemId(73);
    const MAYBE: ItemId = ItemId(74);
    const PAIR: ItemId = ItemId(75);

    /// `File` (a `resource` with one `i64`), `Session` (a `resource`
    /// with one `File`), `Envelope` (a record with one `File`), `Box[T]`
    /// (generic) and `Maybe[T]` (a generic variant).
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
                    SESSION,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Named(FILE, name))],
                        affine: true,
                    },
                ),
                (
                    ENVELOPE,
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
                (
                    PAIR,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Named(FILE, name)), (name, Ty::Named(FILE, name))],
                        affine: false,
                    },
                ),
            ],
            variants: vec![(
                MAYBE,
                VariantLayout {
                    name,
                    type_params: vec![(param, name)],
                    cases: vec![
                        CaseLayout {
                            name,
                            payload: vec![Ty::Param(param, name)],
                        },
                        CaseLayout {
                            name,
                            payload: Vec::new(),
                        },
                    ],
                },
            )],
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    fn file(interpreter: &Interpreter<'_>, descriptor: i128) -> ResourceHandle {
        interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(descriptor)])
    }

    /// One resource record, reduced to everything a failed
    /// destruction must leave untouched.
    type RecordState = (ItemId, u64, bool, Vec<Value>);

    /// Snapshot of everything a failed destruction must leave
    /// untouched: the whole resource table, and the event log.
    fn snapshot(interpreter: &Interpreter<'_>) -> (Vec<RecordState>, Vec<String>) {
        let table: Vec<RecordState> = interpreter
            .resources
            .borrow()
            .records
            .iter()
            .map(|r| {
                (
                    r.item,
                    r.generation,
                    r.status == ResourceStatus::Alive,
                    r.fields.clone(),
                )
            })
            .collect();
        (table, interpreter.event_log())
    }

    fn assert_refused_without_mutation(interpreter: &Interpreter<'_>, value: Value, what: &str) {
        let before = snapshot(interpreter);
        let result = interpreter.drop_value(value);
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "{what}: expected a structured error, got {result:?}"
        );
        assert_eq!(
            before,
            snapshot(interpreter),
            "{what}: a refused destruction changed the resource table or the event log"
        );
    }

    #[test]
    fn a_resource_with_an_extra_runtime_field_is_refused_and_leaks_nothing() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let leaked = file(&interpreter, 1);
        // `Session` declares one field; this record carries two, and the
        // extra one holds a live resource. Skipping it would destroy the
        // session while leaking the file.
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Int(0), Value::Resource(leaked)]);
        assert_refused_without_mutation(
            &interpreter,
            Value::Resource(handle),
            "resource with an extra runtime field",
        );
        assert!(
            interpreter.resources.borrow().observe(leaked).is_ok(),
            "the resource in the extra field must still be alive and reachable"
        );
    }

    #[test]
    fn a_resource_with_a_missing_runtime_field_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let handle = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, Vec::new());
        assert_refused_without_mutation(
            &interpreter,
            Value::Resource(handle),
            "resource with a missing runtime field",
        );
    }

    #[test]
    fn a_record_with_a_missing_generic_type_argument_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = file(&interpreter, 1);
        assert_refused_without_mutation(
            &interpreter,
            Value::Record {
                item: BOXY,
                type_args: Vec::new(),
                fields: vec![Value::Resource(live)],
            },
            "missing generic type argument",
        );
        assert!(interpreter.resources.borrow().observe(live).is_ok());
    }

    #[test]
    fn a_record_with_an_extra_generic_type_argument_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = file(&interpreter, 1);
        assert_refused_without_mutation(
            &interpreter,
            Value::Record {
                item: BOXY,
                type_args: vec![Ty::I64, Ty::I64],
                fields: vec![Value::Resource(live)],
            },
            "extra generic type argument",
        );
        assert!(interpreter.resources.borrow().observe(live).is_ok());
    }

    #[test]
    fn a_nested_malformed_record_is_refused_before_its_valid_sibling_is_destroyed() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let good = file(&interpreter, 1);
        let inner = file(&interpreter, 2);
        // The outer record is well formed; its *second* field is an
        // `Envelope` carrying one field too many. Validation has to
        // reach it before the first field is destroyed.
        assert_refused_without_mutation(
            &interpreter,
            Value::Record {
                item: ENVELOPE,
                type_args: Vec::new(),
                fields: vec![Value::Record {
                    item: ENVELOPE,
                    type_args: Vec::new(),
                    fields: vec![Value::Resource(inner), Value::Resource(good)],
                }],
            },
            "nested malformed record",
        );
        for handle in [good, inner] {
            assert!(interpreter.resources.borrow().observe(handle).is_ok());
        }
    }

    #[test]
    fn a_nested_malformed_variant_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = file(&interpreter, 1);
        assert_refused_without_mutation(
            &interpreter,
            Value::Record {
                item: ENVELOPE,
                type_args: Vec::new(),
                fields: vec![Value::Variant {
                    item: MAYBE,
                    type_args: vec![Ty::Named(FILE, Symbol(0))],
                    case: 0,
                    payload: vec![Value::Resource(live), Value::Int(9)],
                }],
            },
            "nested malformed variant",
        );
        assert!(interpreter.resources.borrow().observe(live).is_ok());
    }

    #[test]
    fn a_variant_naming_an_invalid_active_case_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        assert_refused_without_mutation(
            &interpreter,
            Value::Variant {
                item: MAYBE,
                type_args: vec![Ty::Named(FILE, Symbol(0))],
                case: 7,
                payload: Vec::new(),
            },
            "invalid active case",
        );
    }

    #[test]
    fn a_duplicate_resource_handle_in_two_fields_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let shared = file(&interpreter, 1);
        // One identity reached through two positions would be
        // destroyed twice.
        assert_refused_without_mutation(
            &interpreter,
            Value::Record {
                item: PAIR,
                type_args: Vec::new(),
                fields: vec![Value::Resource(shared), Value::Resource(shared)],
            },
            "duplicate identity in two fields",
        );
        assert!(interpreter.resources.borrow().observe(shared).is_ok());
    }

    #[test]
    fn a_stale_child_after_a_valid_sibling_is_refused_without_destroying_the_sibling() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let good = file(&interpreter, 1);
        let stale = file(&interpreter, 2);
        let _ = interpreter
            .resources
            .borrow_mut()
            .transfer(stale)
            .expect("transferring to create a stale handle");
        // Reverse declaration order reaches the second field first, but
        // either way nothing is destroyed until the whole graph
        // validates.
        assert_refused_without_mutation(
            &interpreter,
            Value::Record {
                item: PAIR,
                type_args: Vec::new(),
                fields: vec![Value::Resource(good), Value::Resource(stale)],
            },
            "stale child after a valid sibling",
        );
        assert!(
            interpreter.resources.borrow().observe(good).is_ok(),
            "the valid sibling must not have been destroyed"
        );
    }

    #[test]
    fn an_already_dropped_nested_child_is_skipped_not_destroyed_twice() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = file(&interpreter, 1);
        let session = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Dropped]);
        interpreter
            .drop_value(Value::Resource(session))
            .expect("a tombstoned child is skipped, not destroyed again");
        assert!(interpreter.resources.borrow().observe(session).is_err());
        assert!(
            interpreter.resources.borrow().observe(live).is_ok(),
            "an unrelated resource is untouched"
        );
    }

    #[test]
    fn a_deeply_nested_generic_graph_is_destroyed_in_exact_order() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let first = file(&interpreter, 1);
        let second = file(&interpreter, 2);
        let session = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Resource(second)]);
        // `Box[Maybe[Session]]` holding a `Some(Session)`: reverse
        // declaration order, each resource's own children before its
        // outer identity. Every position holds exactly what its own
        // declaration says it holds.
        let graph = Value::Record {
            item: BOXY,
            type_args: vec![Ty::Applied(MAYBE, vec![Ty::Named(SESSION, Symbol(0))])],
            fields: vec![Value::Variant {
                item: MAYBE,
                type_args: vec![Ty::Named(SESSION, Symbol(0))],
                case: 0,
                payload: vec![Value::Resource(session)],
            }],
        };
        interpreter
            .drop_value(graph)
            .expect("a well-formed nested generic graph must be destroyed");
        assert_eq!(
            interpreter.event_log(),
            vec![
                format!("drop:{}", second.id.0),
                format!("drop:{}", session.id.0)
            ],
            "the session's own child is destroyed before its outer identity"
        );
        assert!(
            interpreter.resources.borrow().observe(first).is_ok(),
            "an unrelated resource is untouched"
        );
    }

    #[test]
    fn a_refused_destruction_reports_the_identical_error_every_time() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = file(&interpreter, 1);
        let malformed = || Value::Record {
            item: BOXY,
            type_args: Vec::new(),
            fields: vec![Value::Resource(live)],
        };
        let first = interpreter.drop_value(malformed());
        let second = interpreter.drop_value(malformed());
        assert_eq!(first, second, "the refusal must be deterministic");
        assert!(interpreter.resources.borrow().observe(live).is_ok());
    }
}

/// A decomposition transfers the storage one payload position actually
/// holds (`rfcs/0012`). Every claim is checked against that storage
/// before the shell is tombstoned, so a malformed decomposition changes
/// nothing at all.
#[cfg(test)]
mod decomposition_claims {
    use super::*;
    use crate::nir::{CaseLayout, RecordLayout, VariantLayout};
    use crate::symbol::Symbol;

    const FILE: ItemId = ItemId(90);
    const MAYBE: ItemId = ItemId(91);

    fn module() -> Module {
        let name = Symbol(0);
        let param = crate::hir::TypeParamId(0);
        Module {
            functions: Vec::new(),
            records: vec![(
                FILE,
                RecordLayout {
                    name,
                    type_params: Vec::new(),
                    fields: vec![(name, Ty::I64)],
                    affine: true,
                },
            )],
            variants: vec![(
                MAYBE,
                VariantLayout {
                    name,
                    type_params: vec![(param, name)],
                    cases: vec![
                        CaseLayout {
                            name,
                            payload: vec![Ty::Param(param, name)],
                        },
                        CaseLayout {
                            name,
                            payload: Vec::new(),
                        },
                    ],
                },
            )],
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    /// `%0` holds `Some(file)`; `%1` holds that same payload value, and
    /// `%2` holds an unrelated, separately constructed `File`.
    fn frame(
        interpreter: &Interpreter<'_>,
    ) -> (HashMap<ValueId, Value>, ResourceHandle, ResourceHandle) {
        let real = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let unrelated = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(2)]);
        let mut values = HashMap::new();
        values.insert(
            ValueId(0),
            Value::Variant {
                item: MAYBE,
                type_args: vec![Ty::Named(FILE, Symbol(0))],
                case: 0,
                payload: vec![Value::Resource(real)],
            },
        );
        values.insert(ValueId(1), Value::Resource(real));
        values.insert(ValueId(2), Value::Resource(unrelated));
        (values, real, unrelated)
    }

    fn assert_refused_without_mutation(
        interpreter: &Interpreter<'_>,
        values: &mut HashMap<ValueId, Value>,
        taken: &[(usize, ValueId)],
        case: usize,
        what: &str,
    ) {
        let before = values.clone();
        let result =
            interpreter.decompose_variant(values, &HashMap::new(), ValueId(0), MAYBE, case, taken);
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "{what}: expected a structured error, got {result:?}"
        );
        assert_eq!(
            *values, before,
            "{what}: a refused decomposition changed the frame"
        );
        let again =
            interpreter.decompose_variant(values, &HashMap::new(), ValueId(0), MAYBE, case, taken);
        assert_eq!(result, again, "{what}: the refusal is not deterministic");
        assert_eq!(*values, before, "{what}: the retry mutated the frame");
    }

    #[test]
    fn a_claim_naming_an_unrelated_value_is_refused_and_the_shell_is_untouched() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (mut values, real, unrelated) = frame(&interpreter);
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &[(0, ValueId(2))],
            0,
            "claim naming an unrelated value of the same shape",
        );
        for handle in [real, unrelated] {
            assert!(
                interpreter.resources.borrow().observe(handle).is_ok(),
                "no resource may have been touched"
            );
        }
    }

    #[test]
    fn a_claim_naming_a_value_this_frame_never_computed_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (mut values, _, _) = frame(&interpreter);
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &[(0, ValueId(9))],
            0,
            "claim naming an uncomputed value",
        );
    }

    #[test]
    fn a_claim_of_a_position_out_of_range_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (mut values, _, _) = frame(&interpreter);
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &[(3, ValueId(1))],
            0,
            "claim of a position out of range",
        );
    }

    #[test]
    fn a_decomposition_naming_the_inactive_case_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (mut values, _, _) = frame(&interpreter);
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &[],
            1,
            "decomposition of a case that is not live",
        );
    }

    #[test]
    fn one_bad_claim_after_a_good_one_leaves_the_shell_entirely_untouched() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (mut values, real, _) = frame(&interpreter);
        // Position 0 is claimed correctly; position 3 does not exist.
        // Validating claim by claim and writing as it goes would have
        // tombstoned position 0 before discovering the second.
        assert_refused_without_mutation(
            &interpreter,
            &mut values,
            &[(0, ValueId(1)), (3, ValueId(1))],
            0,
            "a valid claim followed by an invalid one",
        );
        assert!(
            interpreter.resources.borrow().observe(real).is_ok(),
            "the real payload is still exactly where it was"
        );
    }

    #[test]
    fn the_matching_claim_moves_exactly_that_position_out_of_the_shell() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (mut values, real, _) = frame(&interpreter);
        interpreter
            .decompose_variant(
                &mut values,
                &HashMap::new(),
                ValueId(0),
                MAYBE,
                0,
                &[(0, ValueId(1))],
            )
            .expect("claiming the value the position actually holds must succeed");
        assert_eq!(
            values.get(&ValueId(0)),
            Some(&Value::Variant {
                item: MAYBE,
                type_args: vec![Ty::Named(FILE, Symbol(0))],
                case: 0,
                payload: vec![Value::Moved],
            }),
            "the shell keeps its case and loses exactly the claimed position"
        );
        assert!(
            interpreter.resources.borrow().observe(real).is_ok(),
            "the payload itself is untouched -- only who owns it changed"
        );
    }
}

/// Matches a partially symbolic type pattern against a concrete
/// runtime type. Repeated parameters must resolve consistently.
fn type_pattern_matches(
    expected: &Ty,
    actual: &Ty,
    bindings: &mut HashMap<crate::hir::TypeParamId, Ty>,
) -> bool {
    match expected {
        Ty::Param(id, _) => match bindings.get(id) {
            Some(bound) => bound == actual,
            None => {
                bindings.insert(*id, actual.clone());
                true
            }
        },
        Ty::Applied(expected_item, expected_args) => {
            let Ty::Applied(actual_item, actual_args) = actual else {
                return false;
            };
            expected_item == actual_item
                && expected_args.len() == actual_args.len()
                && expected_args
                    .iter()
                    .zip(actual_args.iter())
                    .all(|(expected, actual)| type_pattern_matches(expected, actual, bindings))
        }
        Ty::Var(_) | Ty::Never | Ty::Error => false,
        _ => expected == actual,
    }
}

/// Whether a runtime type argument is concrete all the way down.
fn fully_resolved(ty: &Ty) -> bool {
    match ty {
        Ty::Param(..) | Ty::Var(_) | Ty::Never | Ty::Error => false,
        Ty::Applied(_, arguments) => arguments.iter().all(fully_resolved),
        _ => true,
    }
}

/// The declaration a position requires of a record, variant or resource
/// standing in it. None is reserved for a root that declares itself.
fn required_declaration(
    expected: Option<&Ty>,
) -> Result<Option<(ItemId, Vec<Ty>)>, InterpreterError> {
    match expected {
        None => Ok(None),
        Some(Ty::Named(item, _)) => Ok(Some((*item, Vec::new()))),
        Some(Ty::Applied(item, args)) => Ok(Some((*item, args.clone()))),
        Some(Ty::Param(..) | Ty::Var(_) | Ty::Never) => Err(invalid(
            "a runtime value fills a position whose declared type was never resolved",
        )),
        Some(_) => Err(invalid(
            "a runtime aggregate or resource stands in a position whose declared type owns nothing",
        )),
    }
}

/// Every runtime value is checked against the type its declaration says
/// it has, before any ownership operation touches it (`rfcs/0011`,
/// `rfcs/0012`).
///
/// Counting fields and type arguments is not enough. A `Wrapper` whose
/// one declared field is `i64` but whose runtime slot holds a live
/// `Resource` passed every count-based check, and was destroyed with the
/// resource inside it left alive and unreachable, because a field whose
/// *declared* type is not affine was never looked at.
#[cfg(test)]
mod value_shape {
    use super::*;
    use crate::nir::{CaseLayout, RecordLayout, VariantLayout};
    use crate::symbol::Symbol;

    const FILE: ItemId = ItemId(120);
    const WRAPPER: ItemId = ItemId(121);
    const HOLDER: ItemId = ItemId(122);
    const BOXY: ItemId = ItemId(123);
    const MAYBE: ItemId = ItemId(124);
    const OTHER: ItemId = ItemId(125);

    /// `File` (a resource with one `i64`), `Wrapper` (a resource with
    /// one `i64`), `Holder` (a record with one `File`), `Box[T]`,
    /// `Maybe[T]` and `Other` (a second record with one `i64`).
    fn module() -> Module {
        let name = Symbol(0);
        let param = crate::hir::TypeParamId(0);
        let resource_with_int = |affine| RecordLayout {
            name,
            type_params: Vec::new(),
            fields: vec![(name, Ty::I64)],
            affine,
        };
        Module {
            functions: Vec::new(),
            records: vec![
                (FILE, resource_with_int(true)),
                (WRAPPER, resource_with_int(true)),
                (OTHER, resource_with_int(false)),
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
            variants: vec![(
                MAYBE,
                VariantLayout {
                    name,
                    type_params: vec![(param, name)],
                    cases: vec![
                        CaseLayout {
                            name,
                            payload: vec![Ty::Param(param, name)],
                        },
                        CaseLayout {
                            name,
                            payload: Vec::new(),
                        },
                    ],
                },
            )],
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    fn file(interpreter: &Interpreter<'_>, descriptor: i128) -> ResourceHandle {
        interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(descriptor)])
    }

    type RecordState = (ItemId, u64, bool, Vec<Value>);

    fn snapshot(interpreter: &Interpreter<'_>) -> (Vec<RecordState>, Vec<String>) {
        let table: Vec<RecordState> = interpreter
            .resources
            .borrow()
            .records
            .iter()
            .map(|r| {
                (
                    r.item,
                    r.generation,
                    r.status == ResourceStatus::Alive,
                    r.fields.clone(),
                )
            })
            .collect();
        (table, interpreter.event_log())
    }

    fn assert_refused_without_mutation(interpreter: &Interpreter<'_>, value: Value, what: &str) {
        let before = snapshot(interpreter);
        let result = interpreter.drop_value(value.clone());
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "{what}: expected a structured error, got {result:?}"
        );
        assert_eq!(
            before,
            snapshot(interpreter),
            "{what}: a refused destruction changed the resource table or the event log"
        );
        let again = interpreter.drop_value(value);
        assert_eq!(result, again, "{what}: the refusal is not deterministic");
        assert_eq!(
            before,
            snapshot(interpreter),
            "{what}: the retry mutated state"
        );
    }

    #[test]
    fn a_resource_hidden_in_a_non_affine_field_is_refused_and_stays_alive() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let hidden = file(&interpreter, 1);
        // `Wrapper` declares one `i64` field. This one holds a live
        // resource, which a count-based check walks straight past.
        let wrapper = interpreter
            .resources
            .borrow_mut()
            .construct(WRAPPER, vec![Value::Resource(hidden)]);
        assert_refused_without_mutation(
            &interpreter,
            Value::Resource(wrapper),
            "a resource hidden in an `i64` field",
        );
        assert!(
            interpreter.resources.borrow().observe(hidden).is_ok(),
            "the hidden resource must still be alive and reachable"
        );
    }

    #[test]
    fn an_integer_in_a_resource_typed_field_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        assert_refused_without_mutation(
            &interpreter,
            Value::Record {
                item: HOLDER,
                type_args: Vec::new(),
                fields: vec![Value::Int(7)],
            },
            "an integer where a `File` is declared",
        );
    }

    #[test]
    fn a_record_naming_the_wrong_declaration_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = file(&interpreter, 1);
        // `Holder`'s field is declared `File`; this value claims to be
        // an `Other`, which is a different declaration entirely.
        assert_refused_without_mutation(
            &interpreter,
            Value::Record {
                item: HOLDER,
                type_args: Vec::new(),
                fields: vec![Value::Record {
                    item: OTHER,
                    type_args: Vec::new(),
                    fields: vec![Value::Resource(live)],
                }],
            },
            "a record naming a different declaration than its position declares",
        );
        assert!(interpreter.resources.borrow().observe(live).is_ok());
    }

    #[test]
    fn a_variant_naming_the_wrong_declaration_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = file(&interpreter, 1);
        assert_refused_without_mutation(
            &interpreter,
            Value::Record {
                item: BOXY,
                type_args: vec![Ty::Applied(MAYBE, vec![Ty::Named(FILE, Symbol(0))])],
                fields: vec![Value::Variant {
                    item: HOLDER,
                    type_args: Vec::new(),
                    case: 0,
                    payload: vec![Value::Resource(live)],
                }],
            },
            "a variant naming a declaration the position does not declare",
        );
        assert!(interpreter.resources.borrow().observe(live).is_ok());
    }

    #[test]
    fn a_resource_handle_of_the_wrong_declaration_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        // A `Wrapper` handle standing where a `File` is declared.
        let wrapper = interpreter
            .resources
            .borrow_mut()
            .construct(WRAPPER, vec![Value::Int(0)]);
        assert_refused_without_mutation(
            &interpreter,
            Value::Record {
                item: HOLDER,
                type_args: Vec::new(),
                fields: vec![Value::Resource(wrapper)],
            },
            "a resource handle of a different declaration",
        );
        assert!(interpreter.resources.borrow().observe(wrapper).is_ok());
    }

    #[test]
    fn a_value_of_the_right_length_but_the_wrong_kind_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = file(&interpreter, 1);
        // One field, as declared -- but a `Variant` where a `Record` is.
        assert_refused_without_mutation(
            &interpreter,
            Value::Variant {
                item: HOLDER,
                type_args: Vec::new(),
                case: 0,
                payload: vec![Value::Resource(live)],
            },
            "a variant value for a record declaration",
        );
        assert!(interpreter.resources.borrow().observe(live).is_ok());
    }

    #[test]
    fn a_tombstone_in_a_non_affine_field_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        // Nothing can have moved out of an `i64`: there is no ownership
        // there to move.
        let wrapper = interpreter
            .resources
            .borrow_mut()
            .construct(WRAPPER, vec![Value::Moved]);
        assert_refused_without_mutation(
            &interpreter,
            Value::Resource(wrapper),
            "a tombstone where a non-affine field is declared",
        );
    }

    #[test]
    fn a_tombstone_in_an_affine_field_is_accepted() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let untouched = file(&interpreter, 1);
        // The `File` really was moved out of this `Holder` already.
        interpreter
            .drop_value(Value::Record {
                item: HOLDER,
                type_args: Vec::new(),
                fields: vec![Value::Moved],
            })
            .expect("a partially moved aggregate destroys what is left");
        assert!(interpreter.resources.borrow().observe(untouched).is_ok());
    }

    #[test]
    fn a_nested_generic_instantiation_is_validated_all_the_way_down() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = file(&interpreter, 1);
        // `Box[Maybe[File]]` whose `Maybe` claims to hold an `i64`.
        assert_refused_without_mutation(
            &interpreter,
            Value::Record {
                item: BOXY,
                type_args: vec![Ty::Applied(MAYBE, vec![Ty::Named(FILE, Symbol(0))])],
                fields: vec![Value::Variant {
                    item: MAYBE,
                    type_args: vec![Ty::I64],
                    case: 0,
                    payload: vec![Value::Resource(live)],
                }],
            },
            "a nested instantiation disagreeing with the position it fills",
        );
        assert!(interpreter.resources.borrow().observe(live).is_ok());
    }

    #[test]
    fn a_well_formed_nested_generic_graph_is_accepted() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let live = file(&interpreter, 1);
        interpreter
            .drop_value(Value::Record {
                item: BOXY,
                type_args: vec![Ty::Applied(MAYBE, vec![Ty::Named(FILE, Symbol(0))])],
                fields: vec![Value::Variant {
                    item: MAYBE,
                    type_args: vec![Ty::Named(FILE, Symbol(0))],
                    case: 0,
                    payload: vec![Value::Resource(live)],
                }],
            })
            .expect("a well-formed nested generic graph must be destroyed");
        assert_eq!(
            interpreter.event_log(),
            vec![format!("drop:{}", live.id.0)],
            "exactly the one resource it owns"
        );
    }

    #[test]
    fn a_resource_owning_itself_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let outer = interpreter
            .resources
            .borrow_mut()
            .construct(HOLDER, vec![Value::Int(0)]);
        // Point the resource's own field back at itself. Destroying it
        // would have to destroy it first.
        interpreter.resources.borrow_mut().records[outer.id.0 as usize].fields =
            vec![Value::Resource(outer)];
        let before = snapshot(&interpreter);
        let result = interpreter.drop_value(Value::Resource(outer));
        assert!(
            matches!(result, Err(InterpreterError::InvalidOperation(_))),
            "an ownership cycle must be refused, got {result:?}"
        );
        assert_eq!(
            before,
            snapshot(&interpreter),
            "a refused destruction changed state"
        );
    }
}

/// An ordinary (non-`take`) parameter observes, and so does everything
/// reachable through it (`rfcs/0011`, `rfcs/0012`).
///
/// The runtime's own backstop for that: binding an observing parameter
/// produces an observing *view* of the whole value, however deeply the
/// owner handles are buried, and reading through an observer never hands
/// back an owning handle. `nir::verify` already rejects the NIR that
/// would need this; this is the independent second answer, not a
/// substitute.
#[cfg(test)]
mod transitive_observation {
    use super::*;
    use crate::nir::{CaseLayout, RecordLayout, VariantLayout};
    use crate::symbol::Symbol;

    const FILE: ItemId = ItemId(140);
    const SESSION: ItemId = ItemId(141);
    const BOXY: ItemId = ItemId(142);
    const MAYBE: ItemId = ItemId(143);

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
                    SESSION,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Named(FILE, name))],
                        affine: true,
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
            variants: vec![(
                MAYBE,
                VariantLayout {
                    name,
                    type_params: vec![(param, name)],
                    cases: vec![
                        CaseLayout {
                            name,
                            payload: vec![Ty::Param(param, name)],
                        },
                        CaseLayout {
                            name,
                            payload: Vec::new(),
                        },
                    ],
                },
            )],
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    fn file(interpreter: &Interpreter<'_>, descriptor: i128) -> ResourceHandle {
        interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(descriptor)])
    }

    /// Every resource handle `value` carries inline, in order.
    fn handles(value: &Value, out: &mut Vec<ResourceHandle>) {
        match value {
            Value::Resource(handle) => out.push(*handle),
            Value::Record { fields, .. } => {
                for field in fields {
                    handles(field, out);
                }
            }
            Value::Variant { payload, .. } => {
                for slot in payload {
                    handles(slot, out);
                }
            }
            _ => {}
        }
    }

    fn assert_all_observers(value: &Value, what: &str) {
        let mut found = Vec::new();
        handles(value, &mut found);
        assert!(!found.is_empty(), "{what}: the fixture carries no handles");
        for handle in found {
            assert_eq!(
                handle.role,
                RuntimeOwnershipRole::Observer,
                "{what}: an owning handle survived into an observing view"
            );
        }
    }

    #[test]
    fn a_record_of_resources_becomes_an_observing_view_throughout() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owned = file(&interpreter, 1);
        let value = Value::Record {
            item: BOXY,
            type_args: vec![Ty::Named(FILE, Symbol(0))],
            fields: vec![Value::Resource(owned)],
        };
        let view = interpreter
            .to_observer_if_resource(value.clone())
            .expect("observing a well-formed value must succeed");
        assert_all_observers(&view, "a `Box[File]` bound to an observing parameter");
        let mut original = Vec::new();
        handles(&value, &mut original);
        assert_eq!(
            original,
            vec![owned],
            "the caller's own value is untouched: it still holds its owning handle"
        );
        assert!(
            interpreter.resources.borrow().observe(owned).is_ok(),
            "nothing about the resource itself changed"
        );
    }

    #[test]
    fn a_variant_payload_becomes_an_observing_view() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owned = file(&interpreter, 1);
        let view = interpreter
            .to_observer_if_resource(Value::Variant {
                item: MAYBE,
                type_args: vec![Ty::Named(FILE, Symbol(0))],
                case: 0,
                payload: vec![Value::Resource(owned)],
            })
            .expect("observing a well-formed value must succeed");
        assert_all_observers(&view, "a `Maybe[File]` bound to an observing parameter");
    }

    #[test]
    fn a_deeply_nested_value_becomes_an_observing_view_at_every_level() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owned = file(&interpreter, 1);
        let view = interpreter
            .to_observer_if_resource(Value::Record {
                item: BOXY,
                type_args: vec![Ty::Applied(MAYBE, vec![Ty::Named(FILE, Symbol(0))])],
                fields: vec![Value::Variant {
                    item: MAYBE,
                    type_args: vec![Ty::Named(FILE, Symbol(0))],
                    case: 0,
                    payload: vec![Value::Resource(owned)],
                }],
            })
            .expect("observing a well-formed value must succeed");
        assert_all_observers(&view, "a `Box[Maybe[File]]`");
    }

    #[test]
    fn reading_a_field_through_an_observer_yields_an_observer() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let inner = file(&interpreter, 1);
        let session = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Resource(inner)]);
        let observer = interpreter
            .resources
            .borrow()
            .to_observer(session)
            .expect("downgrading an owner must succeed");
        let field = interpreter
            .resources
            .borrow()
            .observe_field(observer, 0)
            .expect("reading a field of an observed resource must succeed");
        let Value::Resource(handle) = field else {
            panic!("the field holds a resource, got {field:?}");
        };
        assert_eq!(
            handle.role,
            RuntimeOwnershipRole::Observer,
            "reading through an observer must never hand back an owning handle"
        );
    }

    #[test]
    fn reading_a_field_through_an_owner_still_yields_the_owner() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let inner = file(&interpreter, 1);
        let session = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Resource(inner)]);
        let field = interpreter
            .resources
            .borrow()
            .observe_field(session, 0)
            .expect("reading a field of an owned resource must succeed");
        assert_eq!(
            field,
            Value::Resource(inner),
            "an owner reading its own field still reaches the owning handle"
        );
    }

    #[test]
    fn an_observing_view_cannot_be_transferred_or_destroyed() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owned = file(&interpreter, 1);
        let view = interpreter
            .to_observer_if_resource(Value::Record {
                item: BOXY,
                type_args: vec![Ty::Named(FILE, Symbol(0))],
                fields: vec![Value::Resource(owned)],
            })
            .expect("observing a well-formed value must succeed");
        let before = interpreter.resources.borrow().records[owned.id.0 as usize].generation;
        assert!(
            matches!(
                interpreter.drop_value(view.clone()),
                Err(InterpreterError::InvalidOperation(_))
            ),
            "destroying through an observing view must be refused"
        );
        assert_eq!(
            interpreter.resources.borrow().records[owned.id.0 as usize].generation,
            before,
            "a refused destruction changed a generation"
        );
        assert!(
            interpreter.resources.borrow().observe(owned).is_ok(),
            "the caller still owns its resource"
        );
    }
}

/// The runtime's own exit backstop against malformed NIR (`rfcs/0011`):
/// a frame that leaves any live resource still owned is an error, and a
/// resource nested inside a record, a variant or another resource is
/// just as owned as a bare handle.
///
/// `nir::verify` already rejects the NIR that would reach here; this is
/// the independent second answer, not a substitute for it.
#[cfg(test)]
mod leak_backstop {
    use super::*;
    use crate::nir::{CaseLayout, RecordLayout, VariantLayout};
    use crate::symbol::Symbol;

    const FILE: ItemId = ItemId(150);
    const SESSION: ItemId = ItemId(151);
    const BOXY: ItemId = ItemId(152);
    const MAYBE: ItemId = ItemId(153);

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
                    SESSION,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Named(FILE, name))],
                        affine: true,
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
            variants: vec![(
                MAYBE,
                VariantLayout {
                    name,
                    type_params: vec![(param, name)],
                    cases: vec![
                        CaseLayout {
                            name,
                            payload: vec![Ty::Param(param, name)],
                        },
                        CaseLayout {
                            name,
                            payload: Vec::new(),
                        },
                    ],
                },
            )],
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    fn file(interpreter: &Interpreter<'_>, descriptor: i128) -> ResourceHandle {
        interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(descriptor)])
    }

    fn boxed(value: Value, held: Ty) -> Value {
        Value::Record {
            item: BOXY,
            type_args: vec![held],
            fields: vec![value],
        }
    }

    fn frame(entries: Vec<(u32, Value)>) -> HashMap<ValueId, Value> {
        entries
            .into_iter()
            .map(|(id, value)| (ValueId(id), value))
            .collect()
    }

    #[test]
    fn a_resource_nested_in_a_record_is_reported() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owned = file(&interpreter, 1);
        let values = frame(vec![(
            7,
            boxed(Value::Resource(owned), Ty::Named(FILE, Symbol(0))),
        )]);
        assert_eq!(
            interpreter.leaked_resource(&values, &HashSet::new(), &HashSet::new()),
            Some(ValueId(7)),
            "a `Box[File]` abandoned at an exit still owns its `File`"
        );
    }

    #[test]
    fn a_resource_nested_in_a_variant_is_reported() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owned = file(&interpreter, 1);
        let values = frame(vec![(
            3,
            Value::Variant {
                item: MAYBE,
                type_args: vec![Ty::Named(FILE, Symbol(0))],
                case: 0,
                payload: vec![Value::Resource(owned)],
            },
        )]);
        assert_eq!(
            interpreter.leaked_resource(&values, &HashSet::new(), &HashSet::new()),
            Some(ValueId(3)),
            "an active case's payload is owned exactly like a bare handle"
        );
    }

    #[test]
    fn a_resource_nested_several_levels_down_is_reported() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owned = file(&interpreter, 1);
        let values = frame(vec![(
            2,
            boxed(
                Value::Variant {
                    item: MAYBE,
                    type_args: vec![Ty::Named(FILE, Symbol(0))],
                    case: 0,
                    payload: vec![Value::Resource(owned)],
                },
                Ty::Applied(MAYBE, vec![Ty::Named(FILE, Symbol(0))]),
            ),
        )]);
        assert_eq!(
            interpreter.leaked_resource(&values, &HashSet::new(), &HashSet::new()),
            Some(ValueId(2)),
            "depth changes nothing about who owns it"
        );
    }

    #[test]
    fn an_observing_view_is_never_reported() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owned = file(&interpreter, 1);
        let view = interpreter
            .to_observer_if_resource(boxed(Value::Resource(owned), Ty::Named(FILE, Symbol(0))))
            .expect("observing a well-formed value must succeed");
        let values = frame(vec![(1, view)]);
        assert_eq!(
            interpreter.leaked_resource(&values, &HashSet::new(), &HashSet::new()),
            None,
            "this frame never owned what an observing view points at"
        );
    }

    #[test]
    fn a_fully_destroyed_aggregate_is_never_reported() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owned = file(&interpreter, 1);
        let value = boxed(Value::Resource(owned), Ty::Named(FILE, Symbol(0)));
        interpreter
            .drop_value(value)
            .expect("destroying a well-formed aggregate must succeed");
        let values = frame(vec![(1, Value::Moved)]);
        assert_eq!(
            interpreter.leaked_resource(&values, &HashSet::new(), &HashSet::new()),
            None,
            "nothing is left to leak"
        );
    }

    #[test]
    fn the_lowest_owning_value_id_is_reported_whatever_the_map_order() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let first = file(&interpreter, 1);
        let second = file(&interpreter, 2);
        let values = frame(vec![
            (9, boxed(Value::Resource(first), Ty::Named(FILE, Symbol(0)))),
            (
                4,
                boxed(Value::Resource(second), Ty::Named(FILE, Symbol(0))),
            ),
            (2, Value::Int(0)),
        ]);
        assert_eq!(
            interpreter.leaked_resource(&values, &HashSet::new(), &HashSet::new()),
            Some(ValueId(4)),
            "the lowest owning id, deterministically, never whatever the map yields first"
        );
    }

    #[test]
    fn a_resource_owning_itself_terminates_and_is_reported_once() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Moved]);
        interpreter.resources.borrow_mut().records[owner.id.0 as usize].fields =
            vec![Value::Resource(owner)];
        let values = frame(vec![(5, Value::Resource(owner))]);
        assert_eq!(
            interpreter.leaked_resource(&values, &HashSet::new(), &HashSet::new()),
            Some(ValueId(5)),
            "a cycle must terminate, and it is still a leak"
        );
    }

    #[test]
    fn a_stale_handle_owning_a_live_child_is_still_reported() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let child = file(&interpreter, 1);
        let owner = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Resource(child)]);
        // The outer handle goes stale, but the record it names still
        // owns a live `File` that nothing else can reach.
        let _ = interpreter
            .resources
            .borrow_mut()
            .transfer(owner)
            .expect("transferring to make the outer handle stale");
        let values = frame(vec![(6, Value::Resource(owner))]);
        assert_eq!(
            interpreter.leaked_resource(&values, &HashSet::new(), &HashSet::new()),
            None,
            "a stale handle owns nothing: the current owner holds the record"
        );
    }
}

/// Blocker 3: every ownership transfer is one transaction, spanning the
/// whole operation rather than one field or one argument of it.
///
/// `transfer_if_resource` used to recurse and bump each resource's
/// generation as it reached it. A later field that turned out to be an
/// observer, stale, duplicated or cyclic then returned `Err` with the
/// earlier fields already moved: the caller's handles stale, the fresh
/// owning handles discarded along with the failed result, and the
/// resources permanently unreachable. The same shape appeared once per
/// place ownership crosses a boundary -- `take` parameters bound one at
/// a time, `record.create`/`variant.create` field by field, and
/// `return`/`raise` transferring *before* the leak backstop could still
/// reject the frame.
///
/// Every test here asserts the same contract: on rejection, the frame's
/// values, the resource table (identity, generation, status and fields)
/// and the event log are all exactly as they were, and repeating the
/// operation produces a byte-identical error.
#[cfg(test)]
mod transfer_transaction {
    use super::*;
    use crate::nir::{BasicBlock, BlockId, Instruction, Param, RecordLayout};
    use crate::symbol::Symbol;

    const FILE: ItemId = ItemId(80);
    const PAIR: ItemId = ItemId(81);
    const HOLDER: ItemId = ItemId(82);
    const MAYBE: ItemId = ItemId(83);
    const TWO_TAKES: ItemId = ItemId(84);
    const BOXY: ItemId = ItemId(99);

    fn file_ty() -> Ty {
        Ty::Named(FILE, Symbol(0))
    }

    /// `File` (a declared `resource` with one `i64` field), `Pair` (two
    /// `File` fields), `Holder` (one `File` field) and `Maybe[T]`.
    fn module() -> Module {
        let name = Symbol(0);
        let param = crate::hir::TypeParamId(0);
        Module {
            functions: vec![two_take_files()],
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
                    PAIR,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, file_ty()), (name, file_ty())],
                        affine: false,
                    },
                ),
                (
                    HOLDER,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, file_ty())],
                        affine: false,
                    },
                ),
                // Generic, so one declaration can be instantiated
                // inconsistently across a call's arguments -- which is
                // exactly what a shared substitution has to prevent.
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
            variants: vec![(
                MAYBE,
                crate::nir::VariantLayout {
                    name,
                    type_params: vec![(param, name)],
                    cases: vec![
                        crate::nir::CaseLayout {
                            name,
                            payload: vec![Ty::Param(param, name), Ty::Param(param, name)],
                        },
                        crate::nir::CaseLayout {
                            name,
                            payload: Vec::new(),
                        },
                    ],
                },
            )],
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    /// `f(take a: File, take b: File)`, destroying both.
    fn two_take_files() -> Function {
        Function {
            id: TWO_TAKES,
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![
                Param {
                    value: ValueId(0),
                    ty: file_ty(),
                    take: true,
                },
                Param {
                    value: ValueId(1),
                    ty: file_ty(),
                    take: true,
                },
            ],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Drop { value: ValueId(0) },
                    Instruction::Drop { value: ValueId(1) },
                ],
                terminator: Terminator::Return(None),
            }],
        }
    }

    fn new_file(interpreter: &Interpreter<'_>, descriptor: i128) -> ResourceHandle {
        interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(descriptor)])
    }

    /// Everything a rejected operation must leave exactly as it found
    /// it: every resource record's own identity, generation, status and
    /// fields, plus the execution's own event log. Rendered rather than
    /// compared field by field so a difference anywhere in the table --
    /// including one this test never thought to name -- still shows up.
    fn runtime_state(interpreter: &Interpreter<'_>) -> String {
        format!(
            "table={:?} events={:?}",
            interpreter.resources.borrow().records,
            interpreter.event_log()
        )
    }

    /// The frame's own values, in `ValueId` order so no `HashMap`
    /// iteration order can reach the comparison.
    fn frame_state(values: &HashMap<ValueId, Value>) -> String {
        let mut entries: Vec<(&ValueId, &Value)> = values.iter().collect();
        entries.sort_by_key(|(id, _)| **id);
        format!("{entries:?}")
    }

    /// Runs `attempt` twice and asserts that it is rejected both times
    /// with a byte-identical error, having changed no runtime state at
    /// all either time. This is the whole contract in one helper: a
    /// partially-applied transfer shows up as either a state difference
    /// or a *different* second error (the first attempt having already
    /// moved something the second then finds stale).
    fn rejected_without_a_trace(
        interpreter: &Interpreter<'_>,
        what: &str,
        mut attempt: impl FnMut() -> Result<(), InterpreterError>,
    ) {
        let before = runtime_state(interpreter);
        let first = attempt().expect_err(what);
        assert_eq!(
            runtime_state(interpreter),
            before,
            "{what}: the rejected operation changed runtime state"
        );
        let second = attempt().expect_err(what);
        assert_eq!(
            runtime_state(interpreter),
            before,
            "{what}: repeating the rejected operation changed runtime state"
        );
        assert_eq!(
            format!("{first:?}"),
            format!("{second:?}"),
            "{what}: the retry produced a different error, so the first attempt left a trace"
        );
    }

    fn pair_of(first: Value, second: Value) -> Value {
        Value::Record {
            item: PAIR,
            type_args: Vec::new(),
            fields: vec![first, second],
        }
    }

    // -- `call_function`: all `take` arguments planned together ---------

    #[test]
    fn a_call_whose_second_take_argument_is_an_observer_transfers_neither() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let other = new_file(&interpreter, 2);
        let observer = interpreter
            .resources
            .borrow()
            .to_observer(other)
            .expect("a fresh owner may be observed");
        let callee = two_take_files();

        rejected_without_a_trace(
            &interpreter,
            "a `take` parameter may not be given an observing handle",
            || {
                interpreter
                    .call_function(
                        &callee,
                        &[],
                        vec![Value::Resource(owner), Value::Resource(observer)],
                        Vec::new(),
                    )
                    .map(|_| ())
            },
        );
        assert!(
            interpreter.resources.borrow().observe(owner).is_ok(),
            "the first argument's own handle must still be current: the call never happened"
        );
    }

    #[test]
    fn a_call_whose_second_take_argument_is_stale_transfers_neither() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let other = new_file(&interpreter, 2);
        // Moved elsewhere, so `other` itself is now a stale handle.
        let _current = interpreter
            .resources
            .borrow_mut()
            .transfer(other)
            .expect("the first transfer succeeds");
        let callee = two_take_files();

        rejected_without_a_trace(&interpreter, "a stale handle may not be taken", || {
            interpreter
                .call_function(
                    &callee,
                    &[],
                    vec![Value::Resource(owner), Value::Resource(other)],
                    Vec::new(),
                )
                .map(|_| ())
        });
        assert!(
            interpreter.resources.borrow().observe(owner).is_ok(),
            "the first argument's own handle must still be current"
        );
    }

    #[test]
    fn one_identity_passed_to_two_take_parameters_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let callee = two_take_files();

        // Planning each argument in isolation would see one live handle
        // twice and accept both, giving the callee two owners of one
        // resource. One shared plan across every argument is what makes
        // the duplicate visible.
        rejected_without_a_trace(
            &interpreter,
            "one identity may not be taken by two parameters of the same call",
            || {
                interpreter
                    .call_function(
                        &callee,
                        &[],
                        vec![Value::Resource(owner), Value::Resource(owner)],
                        Vec::new(),
                    )
                    .map(|_| ())
            },
        );
    }

    #[test]
    fn an_observing_argument_aliasing_a_later_take_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let callee = Function {
            id: ItemId(87),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![
                Param {
                    value: ValueId(0),
                    ty: file_ty(),
                    take: false,
                },
                Param {
                    value: ValueId(1),
                    ty: file_ty(),
                    take: true,
                },
            ],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(2),
                        ty: Ty::I64,
                        kind: ValueKind::RecordField {
                            base: ValueId(0),
                            record: FILE,
                            field: 0,
                        },
                    },
                    Instruction::Drop { value: ValueId(1) },
                ],
                terminator: Terminator::Return(None),
            }],
        };

        // This call used to be *accepted*, by rebasing the observing
        // argument onto the generation the transfer was about to
        // install. That only worked because this particular callee
        // happens to read the observation before dropping the owner.
        // Nothing in the signature says it does, and swapping those two
        // instructions leaves the observation pointing at a destroyed
        // resource -- so the accommodation made the caller's safety
        // depend on the callee's statement order. The pairing is
        // refused at the boundary instead.
        let error = interpreter
            .call_function(
                &callee,
                &[],
                vec![Value::Resource(owner), Value::Resource(owner)],
                Vec::new(),
            )
            .map(|_| ())
            .expect_err("one resource may not be observed and taken by one call");
        assert!(
            format!("{error:?}").contains("both an observing argument and a `take` argument"),
            "the boundary itself must refuse the pairing, got {error:?}"
        );

        let table = interpreter.resources.borrow();
        let record = &table.records[owner.id.0 as usize];
        assert_eq!(
            record.generation, owner.generation,
            "a refused call moves no generation"
        );
        assert_eq!(record.status, ResourceStatus::Alive, "and destroys nothing");
    }

    #[test]
    fn a_call_whose_arguments_are_all_valid_transfers_each_exactly_once() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let first = new_file(&interpreter, 1);
        let second = new_file(&interpreter, 2);
        let callee = two_take_files();

        interpreter
            .call_function(
                &callee,
                &[],
                vec![Value::Resource(first), Value::Resource(second)],
                Vec::new(),
            )
            .expect("two distinct live owners are a legal pair of `take` arguments");

        let table = interpreter.resources.borrow();
        for handle in [first, second] {
            let record = &table.records[handle.id.0 as usize];
            assert_eq!(
                record.generation,
                handle.generation + 1,
                "each identity's generation moves exactly once, never twice and never not at all"
            );
            assert_eq!(
                record.status,
                ResourceStatus::Dropped,
                "the callee destroyed what it was given"
            );
        }
    }

    // -- aggregates: all fields planned together ------------------------

    #[test]
    fn an_aggregate_whose_second_field_is_an_observer_transfers_neither() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let other = new_file(&interpreter, 2);
        let observer = interpreter
            .resources
            .borrow()
            .to_observer(other)
            .expect("a fresh owner may be observed");

        rejected_without_a_trace(
            &interpreter,
            "an observing handle may not be transferred into an aggregate",
            || {
                interpreter
                    .transfer_if_resource(pair_of(
                        Value::Resource(owner),
                        Value::Resource(observer),
                    ))
                    .map(|_| ())
            },
        );
        assert!(
            interpreter.resources.borrow().observe(owner).is_ok(),
            "the first field's own handle must still be current"
        );
    }

    #[test]
    fn an_aggregate_whose_second_field_is_stale_transfers_neither() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let other = new_file(&interpreter, 2);
        let _current = interpreter
            .resources
            .borrow_mut()
            .transfer(other)
            .expect("the first transfer succeeds");

        rejected_without_a_trace(&interpreter, "a stale field may not be transferred", || {
            interpreter
                .transfer_if_resource(pair_of(Value::Resource(owner), Value::Resource(other)))
                .map(|_| ())
        });
        assert!(
            interpreter.resources.borrow().observe(owner).is_ok(),
            "the first field's own handle must still be current"
        );
    }

    #[test]
    fn one_identity_in_two_fields_of_one_aggregate_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);

        rejected_without_a_trace(
            &interpreter,
            "one identity may not occupy two fields of one aggregate",
            || {
                interpreter
                    .transfer_if_resource(pair_of(Value::Resource(owner), Value::Resource(owner)))
                    .map(|_| ())
            },
        );
    }

    #[test]
    fn an_ownership_cycle_between_two_resources_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let first = new_file(&interpreter, 1);
        let second = new_file(&interpreter, 2);
        {
            let mut table = interpreter.resources.borrow_mut();
            table.records[first.id.0 as usize].fields = vec![Value::Resource(second)];
            table.records[second.id.0 as usize].fields = vec![Value::Resource(first)];
        }

        rejected_without_a_trace(
            &interpreter,
            "a cycle no destruction order could satisfy is refused",
            || {
                interpreter
                    .transfer_if_resource(Value::Resource(first))
                    .map(|_| ())
            },
        );
    }

    #[test]
    fn a_resource_owning_itself_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let only = new_file(&interpreter, 1);
        interpreter.resources.borrow_mut().records[only.id.0 as usize].fields =
            vec![Value::Resource(only)];

        rejected_without_a_trace(&interpreter, "a self-cycle is refused", || {
            interpreter
                .transfer_if_resource(Value::Resource(only))
                .map(|_| ())
        });
    }

    #[test]
    fn a_record_create_failing_on_its_last_field_moves_none_of_the_earlier_ones() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let other = new_file(&interpreter, 2);
        let observer = interpreter
            .resources
            .borrow()
            .to_observer(other)
            .expect("a fresh owner may be observed");
        let mut values = HashMap::new();
        values.insert(ValueId(0), Value::Resource(owner));
        values.insert(ValueId(1), Value::Resource(observer));
        let kind = ValueKind::RecordCreate(PAIR, Vec::new(), vec![ValueId(0), ValueId(1)]);

        let frame_before = frame_state(&values);
        rejected_without_a_trace(
            &interpreter,
            "a construction that fails on its last field moves nothing",
            || {
                interpreter
                    .eval(&kind, &values, &[], &HashMap::new())
                    .map(|_| ())
            },
        );
        assert_eq!(
            frame_state(&values),
            frame_before,
            "the frame's own values are untouched by a refused construction"
        );
    }

    #[test]
    fn a_variant_create_failing_on_its_last_payload_moves_none_of_the_earlier_ones() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let other = new_file(&interpreter, 2);
        let observer = interpreter
            .resources
            .borrow()
            .to_observer(other)
            .expect("a fresh owner may be observed");
        let mut values = HashMap::new();
        values.insert(ValueId(0), Value::Resource(owner));
        values.insert(ValueId(1), Value::Resource(observer));
        let kind = ValueKind::VariantCreate {
            variant: MAYBE,
            case: 0,
            type_args: vec![file_ty()],
            payload: vec![ValueId(0), ValueId(1)],
        };

        let frame_before = frame_state(&values);
        rejected_without_a_trace(
            &interpreter,
            "a variant construction that fails on its last payload moves nothing",
            || {
                interpreter
                    .eval(&kind, &values, &[], &HashMap::new())
                    .map(|_| ())
            },
        );
        assert_eq!(
            frame_state(&values),
            frame_before,
            "the frame's own values are untouched by a refused construction"
        );
    }

    // -- exits: nothing moves before the leak backstop has spoken -------

    /// `f(take a: File, take b: File) -> File` that returns `a` and
    /// simply abandons `b` -- a frame the leak backstop must reject.
    fn returns_one_leaks_the_other() -> Function {
        Function {
            id: ItemId(85),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![
                Param {
                    value: ValueId(0),
                    ty: file_ty(),
                    take: true,
                },
                Param {
                    value: ValueId(1),
                    ty: file_ty(),
                    take: true,
                },
            ],
            return_type: file_ty(),
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        }
    }

    #[test]
    fn a_return_rejected_by_the_leak_backstop_moves_no_generation() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let returned = new_file(&interpreter, 1);
        let leaked = new_file(&interpreter, 2);
        let callee = returns_one_leaks_the_other();

        // The arguments are transferred *into* the frame legitimately,
        // so the generations that matter are the ones the frame holds
        // when it tries to leave.
        let inside_returned =
            interpreter.resources.borrow().records[returned.id.0 as usize].generation;
        let result = interpreter.call_function(
            &callee,
            &[],
            vec![Value::Resource(returned), Value::Resource(leaked)],
            Vec::new(),
        );
        let error = result
            .map(|_| ())
            .expect_err("a frame abandoning a live resource must be rejected");
        assert!(
            format!("{error:?}").contains("undestroyed resource"),
            "the leak backstop is what rejected it, got {error:?}"
        );
        assert_eq!(
            interpreter.resources.borrow().records[returned.id.0 as usize].generation,
            inside_returned + 1,
            "the returned value's generation moved exactly once -- when it was taken *into* the \
             frame -- and never again for the return the backstop refused"
        );
    }

    /// `f(take a: File, take b: File) -> Pair` returning an aggregate
    /// built from `a` and a *stale* handle, so the return's own transfer
    /// is what fails.
    fn returns_a_half_valid_aggregate() -> Function {
        Function {
            id: ItemId(86),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: Ty::Named(PAIR, Symbol(0)),
                take: true,
            }],
            return_type: Ty::Named(PAIR, Symbol(0)),
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Return(Some(ValueId(0))),
            }],
        }
    }

    #[test]
    fn a_returned_aggregate_with_one_invalid_child_moves_neither_child() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let good = new_file(&interpreter, 1);
        let other = new_file(&interpreter, 2);
        let observer = interpreter
            .resources
            .borrow()
            .to_observer(other)
            .expect("a fresh owner may be observed");
        let callee = returns_a_half_valid_aggregate();

        // The `take` parameter binding itself is the first transaction
        // and it must refuse the pair outright, so neither child moves.
        rejected_without_a_trace(
            &interpreter,
            "an aggregate with an observing child may not cross a boundary",
            || {
                interpreter
                    .call_function(
                        &callee,
                        &[],
                        vec![pair_of(Value::Resource(good), Value::Resource(observer))],
                        Vec::new(),
                    )
                    .map(|_| ())
            },
        );
        assert!(
            interpreter.resources.borrow().observe(good).is_ok(),
            "the valid child's own handle must still be current"
        );
    }

    /// `f(take a: Holder)` that raises `a` -- so the raise's own
    /// transfer is the operation under test.
    fn raises_its_argument() -> Function {
        Function {
            id: ItemId(87),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: Ty::Applied(MAYBE, vec![file_ty()]),
                take: true,
            }],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Raise { value: ValueId(0) },
            }],
        }
    }

    #[test]
    fn a_raise_whose_transfer_fails_moves_nothing() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let good = new_file(&interpreter, 1);
        let other = new_file(&interpreter, 2);
        let observer = interpreter
            .resources
            .borrow()
            .to_observer(other)
            .expect("a fresh owner may be observed");
        let callee = raises_its_argument();
        let raised = Value::Variant {
            item: MAYBE,
            type_args: vec![file_ty()],
            case: 0,
            payload: vec![Value::Resource(good), Value::Resource(observer)],
        };

        rejected_without_a_trace(
            &interpreter,
            "a raised value carrying an observing handle may not cross the boundary",
            || {
                interpreter
                    .call_function(&callee, &[], vec![raised.clone()], Vec::new())
                    .map(|_| ())
            },
        );
        assert!(
            interpreter.resources.borrow().observe(good).is_ok(),
            "the valid payload's own handle must still be current"
        );
    }

    // -- ordering and determinism ---------------------------------------

    #[test]
    fn a_valid_aggregate_transfer_moves_every_identity_exactly_once() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let first = new_file(&interpreter, 1);
        let second = new_file(&interpreter, 2);

        let moved = interpreter
            .transfer_if_resource(pair_of(Value::Resource(first), Value::Resource(second)))
            .expect("two distinct live owners are a legal pair of fields");

        let Value::Record { fields, .. } = &moved else {
            unreachable!("a transferred record is still a record")
        };
        let table = interpreter.resources.borrow();
        for (index, handle) in [first, second].into_iter().enumerate() {
            let Value::Resource(rebuilt) = fields[index] else {
                unreachable!("each field is still a resource handle")
            };
            assert_eq!(
                rebuilt.id, handle.id,
                "field {index} keeps its own identity across the transfer"
            );
            assert_eq!(
                rebuilt.generation,
                handle.generation + 1,
                "field {index}'s generation moves exactly once"
            );
            assert_eq!(
                table.records[handle.id.0 as usize].generation, rebuilt.generation,
                "the rebuilt handle is the one the table now considers current"
            );
        }
        assert!(
            table.observe(first).is_err() && table.observe(second).is_err(),
            "both of the caller's own handles went stale together"
        );
    }

    #[test]
    fn planning_alone_moves_no_generation_at_all() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let first = new_file(&interpreter, 1);
        let second = new_file(&interpreter, 2);
        let before = runtime_state(&interpreter);

        // The plan is complete -- every identity resolved, every new
        // generation computed, the whole value rebuilt -- and yet
        // nothing has moved. That separation is the entire mechanism:
        // it is what lets an operation abandon a fully-formed plan at
        // any point with no trace.
        let mut plan = StorePlan::default();
        let rebuilt = interpreter
            .plan_transfer(
                &pair_of(Value::Resource(first), Value::Resource(second)),
                &mut plan,
                0,
            )
            .expect("both fields are live owners");
        assert_eq!(
            plan.transitions.len(),
            2,
            "both identities are planned to move"
        );
        assert_eq!(
            runtime_state(&interpreter),
            before,
            "planning must not change a single generation, status or field"
        );
        assert!(
            interpreter.resources.borrow().observe(first).is_ok()
                && interpreter.resources.borrow().observe(second).is_ok(),
            "the caller's own handles are still current until the commit"
        );

        interpreter.commit_transfer(&plan);
        assert_ne!(
            runtime_state(&interpreter),
            before,
            "the commit is what makes the planned transfer real"
        );
        drop(rebuilt);
    }

    // -- the runtime's own defence against overwriting a live slot ------

    #[test]
    fn a_store_over_a_slot_that_still_owns_a_resource_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let first = new_file(&interpreter, 1);
        let second = new_file(&interpreter, 2);
        // Hand-built NIR the verifier would reject under V0100: two
        // transferring stores into one slot, with nothing emptying it in
        // between. The runtime is the independent backstop.
        let function = Function {
            id: ItemId(88),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![
                Param {
                    value: ValueId(1),
                    ty: file_ty(),
                    take: true,
                },
                Param {
                    value: ValueId(2),
                    ty: file_ty(),
                    take: true,
                },
            ],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: file_ty(),
                        kind: ValueKind::Alloc,
                    },
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(1),
                        mode: OwnershipMode::Transfer,
                    },
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(2),
                        mode: OwnershipMode::Transfer,
                    },
                ],
                terminator: Terminator::Return(None),
            }],
        };

        let error = interpreter
            .call_function(
                &function,
                &[],
                vec![Value::Resource(first), Value::Resource(second)],
                Vec::new(),
            )
            .map(|_| ())
            .expect_err("the second store would lose the first resource");
        assert!(
            format!("{error:?}").contains("still owns an undestroyed resource"),
            "the store itself must refuse, rather than silently discarding an owner, got \
             {error:?}"
        );
        // The second store is refused *before* it transfers, so the
        // value it was going to install never moved.
        assert_eq!(
            interpreter.resources.borrow().records[second.id.0 as usize].generation,
            second.generation + 1,
            "the second resource moved only for the `take` binding, never for the refused store"
        );
    }

    #[test]
    fn an_invoke_cannot_overwrite_a_slot_that_still_owns_a_resource() {
        const RETURNS_FILE: ItemId = ItemId(85);
        let callee = Function {
            id: RETURNS_FILE,
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: file_ty(),
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: Ty::I64,
                        kind: ValueKind::Const(Const::Int(7)),
                    },
                    Instruction::Value {
                        result: ValueId(1),
                        ty: file_ty(),
                        kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(0)]),
                    },
                ],
                terminator: Terminator::Return(Some(ValueId(1))),
            }],
        };
        let mut module = module();
        module.functions.push(callee);
        let interpreter = Interpreter::new(&module);
        let existing = new_file(&interpreter, 1);
        let caller = Function {
            id: ItemId(86),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: file_ty(),
                take: true,
            }],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Invoke {
                        callee: RETURNS_FILE,
                        type_args: Vec::new(),
                        args: Vec::new(),
                        evidence: Vec::new(),
                        ok_slot: ValueId(0),
                        ok_target: BlockId(1),
                        err_targets: Vec::new(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![Instruction::Drop { value: ValueId(0) }],
                    terminator: Terminator::Return(None),
                },
            ],
        };

        let error = match interpreter.call_function(
            &caller,
            &[],
            vec![Value::Resource(existing)],
            Vec::new(),
        ) {
            Err(error) => error,
            Ok(_) => panic!("invoke must not discard the previous owner"),
        };
        assert!(
            format!("{error:?}").contains("an invoke would overwrite a slot"),
            "the invoke must refuse before running its callee, got {error:?}"
        );
        let table = interpreter.resources.borrow();
        assert_eq!(
            table.records.len(),
            1,
            "the rejected invoke must not execute its resource-producing callee"
        );
        assert_eq!(
            table.records[existing.id.0 as usize].status,
            ResourceStatus::Alive
        );
    }

    /// The runtime counterpart of the verifier's own exemption: a store
    /// whose source is a `Load` of the very slot being written --
    /// `session = session` -- discards nothing, because what it installs
    /// is what was already there.
    ///
    /// The overwrite backstop must not refuse it. `check` and `ir` both
    /// accept this program, so a false positive here is a stage
    /// disagreement that reaches the user as a runtime failure on a
    /// program every earlier stage passed.
    #[test]
    fn a_store_of_a_slots_own_contents_is_not_refused_as_an_overwrite() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        // `%0` is the slot; `%2` is a `Load` of it, stored straight
        // back. `%1` is the incoming owner that fills the slot first.
        let function = Function {
            id: ItemId(89),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(1),
                ty: file_ty(),
                take: true,
            }],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: file_ty(),
                        kind: ValueKind::Alloc,
                    },
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(1),
                        mode: OwnershipMode::Transfer,
                    },
                    Instruction::Value {
                        result: ValueId(2),
                        ty: file_ty(),
                        kind: ValueKind::Load(ValueId(0)),
                    },
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(2),
                        mode: OwnershipMode::Transfer,
                    },
                    Instruction::Value {
                        result: ValueId(3),
                        ty: file_ty(),
                        kind: ValueKind::Load(ValueId(0)),
                    },
                    Instruction::Drop { value: ValueId(3) },
                ],
                terminator: Terminator::Return(None),
            }],
        };

        interpreter
            .call_function(&function, &[], vec![Value::Resource(owner)], Vec::new())
            .expect("storing a slot's own contents back into it discards nothing");
        assert_eq!(
            interpreter
                .event_log()
                .iter()
                .filter(|event| event.starts_with("drop:"))
                .count(),
            1,
            "the one resource is destroyed exactly once"
        );
        assert_eq!(
            interpreter.resources.borrow().records[owner.id.0 as usize].status,
            ResourceStatus::Dropped,
            "and it really is the resource that was passed in"
        );
    }

    // -- one call may not observe and take one identity -----------------
    //
    // Collected recursively from both sides of the boundary and
    // intersected, so bare resources, records, variants, generic
    // instantiations, resource-record fields and any nesting of them are
    // all covered by the one check.

    /// `f(a, b)` with `take` on whichever position `take_first` names,
    /// and a body that drops the owner and reads the observation in
    /// `drop_first` order -- the two orders a caller cannot distinguish
    /// from the signature, which is the whole reason the pairing is
    /// refused rather than reasoned about.
    fn observe_and_take_callee(
        first_ty: Ty,
        second_ty: Ty,
        take_first: bool,
        drop_first: bool,
    ) -> Function {
        let owner = if take_first { ValueId(0) } else { ValueId(1) };
        let observed = if take_first { ValueId(1) } else { ValueId(0) };
        let read = Instruction::Value {
            result: ValueId(2),
            ty: Ty::I64,
            kind: ValueKind::RecordField {
                base: observed,
                record: FILE,
                field: 0,
            },
        };
        let drop = Instruction::Drop { value: owner };
        Function {
            id: ItemId(93),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![
                Param {
                    value: ValueId(0),
                    ty: first_ty,
                    take: take_first,
                },
                Param {
                    value: ValueId(1),
                    ty: second_ty,
                    take: !take_first,
                },
            ],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: if drop_first {
                    vec![drop, read]
                } else {
                    vec![read, drop]
                },
                terminator: Terminator::Return(None),
            }],
        }
    }

    #[test]
    fn a_call_observing_and_taking_one_resource_is_refused_in_either_order() {
        for take_first in [false, true] {
            for drop_first in [false, true] {
                let module = module();
                let interpreter = Interpreter::new(&module);
                let owner = new_file(&interpreter, 1);
                let callee = observe_and_take_callee(file_ty(), file_ty(), take_first, drop_first);
                rejected_without_a_trace(
                    &interpreter,
                    "one resource may not be observed and taken by one call",
                    || {
                        interpreter
                            .call_function(
                                &callee,
                                &[],
                                vec![Value::Resource(owner), Value::Resource(owner)],
                                Vec::new(),
                            )
                            .map(|_| ())
                    },
                );
                assert_eq!(
                    interpreter.resources.borrow().records[owner.id.0 as usize].status,
                    ResourceStatus::Alive,
                    "take_first={take_first} drop_first={drop_first}: nothing was destroyed"
                );
            }
        }
    }

    /// The identity is nested inside a record on the observing side and
    /// bare on the taking side. Neither outer handle is shared, so only
    /// a recursive collection finds the overlap.
    #[test]
    fn a_call_aliasing_through_a_nested_record_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let inner = new_file(&interpreter, 1);
        let holder = Value::Record {
            item: HOLDER,
            type_args: Vec::new(),
            fields: vec![Value::Resource(inner)],
        };
        let callee = Function {
            id: ItemId(94),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![
                Param {
                    value: ValueId(0),
                    ty: Ty::Named(HOLDER, Symbol(0)),
                    take: false,
                },
                Param {
                    value: ValueId(1),
                    ty: file_ty(),
                    take: true,
                },
            ],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Drop { value: ValueId(1) }],
                terminator: Terminator::Return(None),
            }],
        };

        rejected_without_a_trace(
            &interpreter,
            "a nested identity is still the same identity",
            || {
                interpreter
                    .call_function(
                        &callee,
                        &[],
                        vec![holder.clone(), Value::Resource(inner)],
                        Vec::new(),
                    )
                    .map(|_| ())
            },
        );
    }

    /// The same through a variant payload.
    #[test]
    fn a_call_aliasing_through_a_variant_payload_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let inner = new_file(&interpreter, 1);
        // A second, distinct resource fills the other payload slot, so
        // the only repeat is *across* the two arguments. Putting `inner`
        // in both slots would be a duplicate within one graph -- a
        // different fault, already rejected by the graph walk, and it
        // would let this test pass without the boundary check running.
        let sibling = new_file(&interpreter, 2);
        let wrapped = Value::Variant {
            item: MAYBE,
            type_args: vec![file_ty()],
            case: 0,
            payload: vec![Value::Resource(inner), Value::Resource(sibling)],
        };
        let callee = Function {
            id: ItemId(95),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![
                Param {
                    value: ValueId(0),
                    ty: file_ty(),
                    take: true,
                },
                Param {
                    value: ValueId(1),
                    ty: Ty::Applied(MAYBE, vec![file_ty()]),
                    take: false,
                },
            ],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Drop { value: ValueId(0) }],
                terminator: Terminator::Return(None),
            }],
        };

        rejected_without_a_trace(
            &interpreter,
            "a payload identity is still the same identity",
            || {
                interpreter
                    .call_function(
                        &callee,
                        &[],
                        vec![Value::Resource(inner), wrapped.clone()],
                        Vec::new(),
                    )
                    .map(|_| ())
            },
        );
    }

    #[test]
    fn a_call_observing_one_resource_twice_is_accepted_at_run_time() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let callee = Function {
            id: ItemId(96),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![
                Param {
                    value: ValueId(0),
                    ty: file_ty(),
                    take: false,
                },
                Param {
                    value: ValueId(1),
                    ty: file_ty(),
                    take: false,
                },
            ],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Return(None),
            }],
        };

        interpreter
            .call_function(
                &callee,
                &[],
                vec![Value::Resource(owner), Value::Resource(owner)],
                Vec::new(),
            )
            .expect("neither observation can end the resource");
        assert_eq!(
            interpreter.resources.borrow().records[owner.id.0 as usize].status,
            ResourceStatus::Alive,
            "and the caller still owns it afterwards"
        );
    }

    #[test]
    fn a_call_observing_one_resource_and_taking_another_is_accepted_at_run_time() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let kept = new_file(&interpreter, 1);
        let given = new_file(&interpreter, 2);
        let callee = observe_and_take_callee(file_ty(), file_ty(), false, false);

        interpreter
            .call_function(
                &callee,
                &[],
                vec![Value::Resource(kept), Value::Resource(given)],
                Vec::new(),
            )
            .expect("distinct identities never alias");
        let table = interpreter.resources.borrow();
        assert_eq!(
            table.records[kept.id.0 as usize].status,
            ResourceStatus::Alive,
            "the observed resource is untouched"
        );
        assert_eq!(
            table.records[given.id.0 as usize].status,
            ResourceStatus::Dropped,
            "and the taken one was consumed"
        );
    }

    // -- `Invoke` instantiates on the same terms as `Call` ---------------
    //
    // A fallible call binds its arguments identically, so it has to
    // build the same one substitution and check every argument against
    // it. Exercised through the real `Terminator::Invoke` path, since
    // that terminator carries its own `type_args` and was ignoring them.

    /// A caller whose terminator is `invoke @callee[type_args](args)`.
    fn invoking_caller(
        callee: ItemId,
        type_args: Vec<Ty>,
        args: Vec<ValueId>,
        params: Vec<Param>,
        ok_slot_ty: Ty,
    ) -> Function {
        Function {
            id: ItemId(140),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params,
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![Instruction::Value {
                        result: ValueId(50),
                        ty: ok_slot_ty,
                        kind: ValueKind::Alloc,
                    }],
                    terminator: Terminator::Invoke {
                        callee,
                        type_args,
                        args,
                        evidence: Vec::new(),
                        ok_slot: ValueId(50),
                        ok_target: BlockId(1),
                        err_targets: Vec::new(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::Return(None),
                },
            ],
        }
    }

    #[test]
    fn an_invoke_with_consistent_generic_arguments_is_accepted() {
        let mut module = module();
        module.functions.push(same_type_twice());
        let interpreter = Interpreter::new(&module);
        let caller = invoking_caller(
            ItemId(97),
            vec![Ty::I64],
            vec![ValueId(1), ValueId(2)],
            vec![
                Param {
                    value: ValueId(1),
                    ty: Ty::Applied(BOXY, vec![Ty::I64]),
                    take: false,
                },
                Param {
                    value: ValueId(2),
                    ty: Ty::Applied(BOXY, vec![Ty::I64]),
                    take: false,
                },
            ],
            Ty::Unit,
        );

        interpreter
            .call_function(
                &caller,
                &[],
                vec![boxed(Ty::I64, Value::Int(1)), boxed(Ty::I64, Value::Int(2))],
                Vec::new(),
            )
            .expect("both arguments agree with the one instantiation");
    }

    #[test]
    fn an_invoke_with_inconsistent_generic_arguments_is_refused() {
        let mut module = module();
        module.functions.push(same_type_twice());
        let interpreter = Interpreter::new(&module);
        let caller = invoking_caller(
            ItemId(97),
            vec![Ty::I64],
            vec![ValueId(1), ValueId(2)],
            vec![
                Param {
                    value: ValueId(1),
                    ty: Ty::Applied(BOXY, vec![Ty::I64]),
                    take: false,
                },
                Param {
                    value: ValueId(2),
                    ty: Ty::Applied(BOXY, vec![Ty::Bool]),
                    take: false,
                },
            ],
            Ty::Unit,
        );

        let error = interpreter
            .call_function(
                &caller,
                &[],
                vec![
                    boxed(Ty::I64, Value::Int(1)),
                    boxed(Ty::Bool, Value::Bool(true)),
                ],
                Vec::new(),
            )
            .map(|_| ())
            .expect_err("one `T` cannot be both `i64` and `bool` in one invocation");
        assert!(
            format!("{error:?}").contains("disagrees with the concrete part"),
            "the second argument is checked against the same `T = i64` the first was, got \
             {error:?}"
        );
    }

    #[test]
    fn an_invoke_with_the_wrong_generic_arity_is_refused_without_mutating() {
        let mut module = module();
        module.functions.push(same_type_twice());
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let caller = invoking_caller(
            ItemId(97),
            // `same_type_twice` declares one parameter.
            vec![Ty::I64, Ty::Bool],
            vec![ValueId(1), ValueId(2)],
            vec![
                Param {
                    value: ValueId(1),
                    ty: Ty::Applied(BOXY, vec![Ty::I64]),
                    take: false,
                },
                Param {
                    value: ValueId(2),
                    ty: Ty::Applied(BOXY, vec![Ty::I64]),
                    take: false,
                },
            ],
            Ty::Unit,
        );

        // The *caller's* own frame is entered legitimately, so its
        // `call:` event is expected. What must not appear is the
        // callee's, and no table state may move.
        let table_before = format!("{:?}", interpreter.resources.borrow().records);
        let error = interpreter
            .call_function(
                &caller,
                &[],
                vec![boxed(Ty::I64, Value::Int(1)), boxed(Ty::I64, Value::Int(2))],
                Vec::new(),
            )
            .map(|_| ())
            .expect_err("an over-long instantiation is refused, never truncated");
        assert!(
            format!("{error:?}").contains("type parameter(s) but was instantiated with 2"),
            "got {error:?}"
        );
        assert_eq!(
            format!("{:?}", interpreter.resources.borrow().records),
            table_before,
            "a refused invoke moves no generation and destroys nothing"
        );
        assert!(
            !interpreter.event_log().iter().any(|e| e == "call:97"),
            "the callee's frame was never entered: {:?}",
            interpreter.event_log()
        );
        assert_eq!(
            interpreter.resources.borrow().records[owner.id.0 as usize].status,
            ResourceStatus::Alive,
            "nothing unrelated was touched either"
        );
    }

    /// An `Invoke` inside a generic body carries its type arguments
    /// symbolically, exactly as a `Call` does, and only the running
    /// frame knows what they resolve to.
    #[test]
    fn an_invoke_type_argument_is_resolved_through_the_frame() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let param = crate::hir::TypeParamId(0);
        let mut frame = HashMap::new();
        frame.insert(param, Ty::I64);
        let resolved = interpreter
            .resolve_type_args(
                &[Ty::Applied(BOXY, vec![Ty::Param(param, Symbol(0))])],
                &frame,
            )
            .expect("the frame's own instantiation resolves it");
        assert_eq!(resolved, vec![Ty::Applied(BOXY, vec![Ty::I64])]);
    }
    // -- a rejected frame entry changes nothing -------------------------

    /// `f(take a: File)` with no `bb0` at all. Every boundary check
    /// passes -- the argument is a live owner of the declared type --
    /// and the call is then refused for having no entry block.
    ///
    /// That refusal used to come *after* the transfer was committed, so
    /// a callee that never executed an instruction still bumped its
    /// argument's generation and left the caller holding a stale handle.
    fn callee_without_an_entry_block() -> Function {
        Function {
            id: ItemId(130),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: file_ty(),
                take: true,
            }],
            return_type: Ty::Unit,
            raises: Vec::new(),
            // `BlockId(7)`, deliberately: blocks exist, just not the
            // entry one, so this is a malformed function rather than an
            // empty one.
            blocks: vec![BasicBlock {
                id: BlockId(7),
                instructions: vec![Instruction::Drop { value: ValueId(0) }],
                terminator: Terminator::Return(None),
            }],
        }
    }

    #[test]
    fn a_callee_without_an_entry_block_is_refused_without_mutating() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let callee = callee_without_an_entry_block();

        // Snapshots every dimension a boundary rejection must leave
        // alone: identities, generations, statuses and fields (all of
        // which `runtime_state` renders), plus the event log, plus the
        // caller's own frame bindings.
        let mut frame: HashMap<ValueId, Value> = HashMap::new();
        frame.insert(ValueId(0), Value::Resource(owner));
        let frame_before = frame_state(&frame);

        rejected_without_a_trace(
            &interpreter,
            "a callee with no entry block may not consume its arguments",
            || {
                interpreter
                    .call_function(&callee, &[], vec![Value::Resource(owner)], Vec::new())
                    .map(|_| ())
            },
        );

        assert_eq!(
            frame_state(&frame),
            frame_before,
            "the caller's own bindings are untouched"
        );
        let table = interpreter.resources.borrow();
        assert_eq!(
            table.records[owner.id.0 as usize].generation, owner.generation,
            "no generation moved, so the caller's handle is still current"
        );
        assert_eq!(
            table.records[owner.id.0 as usize].status,
            ResourceStatus::Alive,
            "and nothing was destroyed"
        );
        assert!(
            table.observe(owner).is_ok(),
            "the caller can still use the argument it was never able to hand over"
        );
    }

    /// The distinction the ordering is *not* allowed to blur: a failure
    /// after the frame has genuinely been entered is observable, because
    /// whatever ran before it really did run.
    #[test]
    fn a_failure_after_frame_entry_stays_observable() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        // Enters `bb0`, destroys its argument, then branches to a block
        // that does not exist.
        let callee = Function {
            id: ItemId(131),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: file_ty(),
                take: true,
            }],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Drop { value: ValueId(0) }],
                terminator: Terminator::Branch(BlockId(9)),
            }],
        };

        interpreter
            .call_function(&callee, &[], vec![Value::Resource(owner)], Vec::new())
            .map(|_| ())
            .expect_err("branching to a block that does not exist is an error");
        let table = interpreter.resources.borrow();
        assert_eq!(
            table.records[owner.id.0 as usize].status,
            ResourceStatus::Dropped,
            "the frame was entered and its `drop` really happened -- this is not rolled back"
        );
        drop(table);
        assert!(
            interpreter
                .event_log()
                .iter()
                .any(|event| event == "call:131"),
            "and the frame entry is recorded, because it occurred: {:?}",
            interpreter.event_log()
        );
    }
    // -- self-stores at run time, judged by mode ------------------------

    /// Builds `f(take a: File)` whose body fills `%0`, loads it into
    /// `%2`, and stores `%2` back into `%0` under `mode`. The two modes
    /// are the same instruction sequence with one flag changed, which
    /// is exactly the point: the answers must differ.
    fn self_store_function(mode: OwnershipMode, tail: Vec<Instruction>) -> Function {
        let mut instructions = vec![
            Instruction::Value {
                result: ValueId(0),
                ty: file_ty(),
                kind: ValueKind::Alloc,
            },
            Instruction::Store {
                slot: ValueId(0),
                value: ValueId(1),
                mode: OwnershipMode::Transfer,
            },
            Instruction::Value {
                result: ValueId(2),
                ty: file_ty(),
                kind: ValueKind::Load(ValueId(0)),
            },
            Instruction::Store {
                slot: ValueId(0),
                value: ValueId(2),
                mode,
            },
        ];
        instructions.extend(tail);
        Function {
            id: ItemId(91),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(1),
                ty: file_ty(),
                take: true,
            }],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions,
                terminator: Terminator::Return(None),
            }],
        }
    }

    #[test]
    fn a_transferring_self_store_is_accepted_at_run_time() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let function = self_store_function(
            OwnershipMode::Transfer,
            vec![
                Instruction::Value {
                    result: ValueId(3),
                    ty: file_ty(),
                    kind: ValueKind::Load(ValueId(0)),
                },
                Instruction::Drop { value: ValueId(3) },
            ],
        );

        interpreter
            .call_function(&function, &[], vec![Value::Resource(owner)], Vec::new())
            .expect("a transferring self-store empties the slot before refilling it");
        assert_eq!(
            interpreter.resources.borrow().records[owner.id.0 as usize].status,
            ResourceStatus::Dropped,
            "the one resource is destroyed exactly once, through the slot"
        );
    }

    /// The same body with `store.observe`, which retires nothing. The
    /// loaded value keeps the owner, so overwriting the slot discards
    /// it -- and the runtime must refuse before touching anything, on
    /// the same terms the verifier reports `V0100`.
    #[test]
    fn an_observing_self_store_is_refused_at_run_time_without_mutating() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let function = self_store_function(OwnershipMode::Observe, Vec::new());

        // Two moves are lawful before the refused one, and both happen:
        // the `take` binding transfers the argument into the frame, and
        // the body's first `store.transfer` moves it into the slot. The
        // observing self-store that follows must add none.
        let before_generation =
            interpreter.resources.borrow().records[owner.id.0 as usize].generation;
        let error = interpreter
            .call_function(&function, &[], vec![Value::Resource(owner)], Vec::new())
            .map(|_| ())
            .expect_err("an observing store may not discard the owner the slot holds");
        assert!(
            format!("{error:?}").contains("still owns an undestroyed resource"),
            "the store itself must refuse, got {error:?}"
        );
        let after = interpreter.resources.borrow();
        let record = &after.records[owner.id.0 as usize];
        assert_eq!(
            record.generation,
            before_generation + 2,
            "exactly the `take` binding and the first store moved it; the refused observing \
             store moved nothing"
        );
        assert_eq!(
            record.status,
            ResourceStatus::Alive,
            "a refused store destroys nothing"
        );
    }

    /// A `Load` taken before the slot was emptied and refilled is a
    /// *historical* value, not the slot's current contents. Storing it
    /// back must not be waved through just because its canonical root
    /// matches the destination.
    #[test]
    fn a_stale_historical_load_stored_back_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let first = new_file(&interpreter, 1);
        let second = new_file(&interpreter, 2);
        let function = Function {
            id: ItemId(92),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![
                Param {
                    value: ValueId(1),
                    ty: file_ty(),
                    take: true,
                },
                Param {
                    value: ValueId(2),
                    ty: file_ty(),
                    take: true,
                },
            ],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    Instruction::Value {
                        result: ValueId(0),
                        ty: file_ty(),
                        kind: ValueKind::Alloc,
                    },
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(1),
                        mode: OwnershipMode::Transfer,
                    },
                    // Snapshot, then empty the slot and refill it with a
                    // different resource.
                    Instruction::Value {
                        result: ValueId(3),
                        ty: file_ty(),
                        kind: ValueKind::Load(ValueId(0)),
                    },
                    Instruction::Drop { value: ValueId(3) },
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(2),
                        mode: OwnershipMode::Transfer,
                    },
                    // `%3` names the destroyed first resource. Its root
                    // is still `%0`, and that must not be enough.
                    Instruction::Store {
                        slot: ValueId(0),
                        value: ValueId(3),
                        mode: OwnershipMode::Transfer,
                    },
                ],
                terminator: Terminator::Return(None),
            }],
        };

        let error = interpreter
            .call_function(
                &function,
                &[],
                vec![Value::Resource(first), Value::Resource(second)],
                Vec::new(),
            )
            .map(|_| ())
            .expect_err("a destroyed historical load may not be stored back");
        assert!(
            !format!("{error:?}").contains("still owns an undestroyed resource"),
            "the stale source itself is the fault, not the destination: {error:?}"
        );
        assert_eq!(
            interpreter.resources.borrow().records[second.id.0 as usize].status,
            ResourceStatus::Alive,
            "the resource the slot legitimately held was not destroyed by the refused store"
        );
    }

    // -- one instantiation, shared by the whole argument list ----------
    //
    // A generic body is lowered once and shared, so the only thing that
    // ties a repeated `T` together across parameters is the
    // substitution the invocation is checked under. Building one per
    // argument would let `same[T](Box[T], Box[T])` accept a `Box[i64]`
    // and a `Box[bool]`, each locally consistent and jointly
    // meaningless.

    /// `same[T](first: Box[T], second: Box[T]) -> unit`.
    fn same_type_twice() -> Function {
        let param = crate::hir::TypeParamId(0);
        let boxed = Ty::Applied(BOXY, vec![Ty::Param(param, Symbol(0))]);
        Function {
            id: ItemId(97),
            name: Symbol(0),
            type_params: vec![(param, Symbol(0))],
            requirements: Vec::new(),
            params: vec![
                Param {
                    value: ValueId(0),
                    ty: boxed.clone(),
                    take: false,
                },
                Param {
                    value: ValueId(1),
                    ty: boxed,
                    take: false,
                },
            ],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Return(None),
            }],
        }
    }

    fn boxed(inner: Ty, payload: Value) -> Value {
        Value::Record {
            item: BOXY,
            type_args: vec![inner],
            fields: vec![payload],
        }
    }

    #[test]
    fn a_generic_call_with_consistent_arguments_is_accepted() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        interpreter
            .call_function(
                &same_type_twice(),
                &[Ty::I64],
                vec![boxed(Ty::I64, Value::Int(1)), boxed(Ty::I64, Value::Int(2))],
                Vec::new(),
            )
            .expect("both arguments agree with the one instantiation");
    }

    #[test]
    fn a_generic_call_with_inconsistent_arguments_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let error = interpreter
            .call_function(
                &same_type_twice(),
                &[Ty::I64],
                vec![
                    boxed(Ty::I64, Value::Int(1)),
                    boxed(Ty::Bool, Value::Bool(true)),
                ],
                Vec::new(),
            )
            .map(|_| ())
            .expect_err("one `T` cannot be both `i64` and `bool` in one invocation");
        assert!(
            format!("{error:?}").contains("disagrees with the concrete part"),
            "the second argument is checked against the same `T = i64` the first was, got {error:?}"
        );
    }

    /// The other half of the same rule: the instantiation is what the
    /// arguments are checked against, so an argument that matches
    /// *neither* is refused even when both arguments agree with each
    /// other.
    #[test]
    fn a_generic_call_whose_arguments_ignore_the_instantiation_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let error = interpreter
            .call_function(
                &same_type_twice(),
                &[Ty::I64],
                vec![
                    boxed(Ty::Bool, Value::Bool(true)),
                    boxed(Ty::Bool, Value::Bool(false)),
                ],
                Vec::new(),
            )
            .map(|_| ())
            .expect_err("`Box[bool]` does not fill `Box[T]` under `T = i64`");
        assert!(
            format!("{error:?}").contains("disagrees with the concrete part"),
            "the instantiation is what arguments are checked against, got {error:?}"
        );
    }

    #[test]
    fn a_generic_call_with_the_wrong_outer_constructor_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let error = interpreter
            .call_function(
                &same_type_twice(),
                &[file_ty()],
                vec![
                    boxed(file_ty(), Value::Resource(owner)),
                    Value::Resource(owner),
                ],
                Vec::new(),
            )
            .map(|_| ())
            .expect_err("a bare resource does not fill a `Box[T]` position");
        assert!(
            !format!("{error:?}").is_empty(),
            "the constructor itself is checked, got {error:?}"
        );
    }

    #[test]
    fn a_generic_function_called_with_no_type_arguments_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let error = interpreter
            .call_function(
                &same_type_twice(),
                &[],
                vec![boxed(Ty::I64, Value::Int(1)), boxed(Ty::I64, Value::Int(2))],
                Vec::new(),
            )
            .map(|_| ())
            .expect_err("a generic function needs an instantiation, not a guess");
        assert!(
            format!("{error:?}").contains("type parameter(s) but was instantiated with 0"),
            "the public boundary refuses rather than inferring, got {error:?}"
        );
    }

    #[test]
    fn a_generic_function_called_with_extra_type_arguments_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let error = interpreter
            .call_function(
                &same_type_twice(),
                &[Ty::I64, Ty::Bool],
                vec![boxed(Ty::I64, Value::Int(1)), boxed(Ty::I64, Value::Int(2))],
                Vec::new(),
            )
            .map(|_| ())
            .expect_err("an over-long instantiation is refused, never truncated");
        assert!(
            format!("{error:?}").contains("type parameter(s) but was instantiated with 2"),
            "got {error:?}"
        );
    }

    #[test]
    fn a_call_site_type_argument_left_unresolved_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let param = crate::hir::TypeParamId(9);
        // No frame substitution binds `T`, so this call site names a
        // type nobody can supply.
        let error = interpreter
            .resolve_type_args(&[Ty::Param(param, Symbol(0))], &HashMap::new())
            .map(|_| ())
            .expect_err("an unresolved call-site type argument is refused");
        assert!(
            format!("{error:?}").contains("still unresolved"),
            "got {error:?}"
        );
    }

    #[test]
    fn a_call_site_type_argument_is_resolved_through_the_frame() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let param = crate::hir::TypeParamId(0);
        let mut frame = HashMap::new();
        frame.insert(param, Ty::I64);
        // `outer[i64]` calling `inner[T]` reaches `inner[i64]`.
        let resolved = interpreter
            .resolve_type_args(
                &[Ty::Applied(BOXY, vec![Ty::Param(param, Symbol(0))])],
                &frame,
            )
            .expect("the frame's own instantiation resolves it");
        assert_eq!(resolved, vec![Ty::Applied(BOXY, vec![Ty::I64])]);
    }

    #[test]
    fn a_rejected_generic_call_mutates_nothing() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let param = crate::hir::TypeParamId(0);
        // `f[T](take a: Box[T])` handed a `Box[bool]` under `T = File`.
        let callee = Function {
            id: ItemId(98),
            name: Symbol(0),
            type_params: vec![(param, Symbol(0))],
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: Ty::Applied(BOXY, vec![Ty::Param(param, Symbol(0))]),
                take: true,
            }],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Drop { value: ValueId(0) }],
                terminator: Terminator::Return(None),
            }],
        };

        rejected_without_a_trace(
            &interpreter,
            "a generic mismatch is refused before anything moves",
            || {
                interpreter
                    .call_function(
                        &callee,
                        &[file_ty()],
                        vec![boxed(Ty::Bool, Value::Bool(true))],
                        Vec::new(),
                    )
                    .map(|_| ())
            },
        );
        assert_eq!(
            interpreter.resources.borrow().records[owner.id.0 as usize].status,
            ResourceStatus::Alive,
            "and nothing unrelated was touched either"
        );
    }

    // -- a call event means the frame was entered -----------------------
    //
    // Exercised through the real `ValueKind::Call` evaluation path, not
    // by invoking `call_function` directly: the defect being guarded
    // against was an event written at the *call site* before any
    // boundary check ran, which a direct call would never have shown.

    /// A caller whose one instruction is `call @callee(args...)`, so
    /// running it drives the same path a compiled program does.
    fn caller_of(callee: ItemId, args: Vec<ValueId>, params: Vec<Param>) -> Function {
        Function {
            id: ItemId(120),
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params,
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(50),
                    ty: Ty::Unit,
                    kind: ValueKind::Call(callee, Vec::new(), args, Vec::new()),
                }],
                terminator: Terminator::Return(None),
            }],
        }
    }

    /// Every event the run produced *after* the caller's own entry, so
    /// the assertions are about the nested call rather than about the
    /// frame that made it.
    fn nested_events(interpreter: &Interpreter<'_>) -> Vec<String> {
        interpreter
            .event_log()
            .into_iter()
            .skip_while(|event| event != "call:120")
            .skip(1)
            .collect()
    }

    #[test]
    fn a_call_rejected_for_arity_records_no_call_event() {
        let mut module = module();
        module.functions.push(two_take_files());
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        // `two_take_files` wants two arguments; this call site passes one.
        let caller = caller_of(
            TWO_TAKES,
            vec![ValueId(1)],
            vec![Param {
                value: ValueId(1),
                ty: file_ty(),
                take: false,
            }],
        );

        interpreter
            .call_function(&caller, &[], vec![Value::Resource(owner)], Vec::new())
            .map(|_| ())
            .expect_err("the callee takes two arguments");
        assert!(
            nested_events(&interpreter).is_empty(),
            "a call refused at the boundary never happened: {:?}",
            interpreter.event_log()
        );
    }

    #[test]
    fn a_call_rejected_for_a_mixed_alias_records_no_call_event() {
        let mut module = module();
        module
            .functions
            .push(observe_and_take_callee(file_ty(), file_ty(), false, false));
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let caller = caller_of(
            ItemId(93),
            vec![ValueId(1), ValueId(1)],
            vec![Param {
                value: ValueId(1),
                ty: file_ty(),
                take: false,
            }],
        );

        interpreter
            .call_function(&caller, &[], vec![Value::Resource(owner)], Vec::new())
            .map(|_| ())
            .expect_err("one resource may not be observed and taken by one call");
        assert!(
            nested_events(&interpreter).is_empty(),
            "an aliasing call never entered its callee: {:?}",
            interpreter.event_log()
        );
    }

    /// Capability evidence is checked at the callee's own boundary, so
    /// a call site supplying none for a callee that requires one is
    /// rejected there -- after the caller's frame was entered, and
    /// before the callee's is.
    ///
    /// Deliberately not a stale-handle case: a stale argument is
    /// refused while binding the *caller's* parameters, so it never
    /// reaches the nested boundary and would prove nothing about where
    /// the event is written. Handle liveness at a nested boundary is
    /// covered by the transaction tests instead.
    #[test]
    fn a_call_rejected_for_missing_capability_evidence_records_no_call_event() {
        const NEEDS_EVIDENCE: ItemId = ItemId(121);
        let mut module = module();
        module.functions.push(Function {
            id: NEEDS_EVIDENCE,
            name: Symbol(0),
            type_params: Vec::new(),
            requirements: vec![crate::types::CapabilityRequirement {
                protocol: ItemId(200),
                arguments: Vec::new(),
            }],
            params: Vec::new(),
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Return(None),
            }],
        });
        let interpreter = Interpreter::new(&module);
        let caller = caller_of(NEEDS_EVIDENCE, Vec::new(), Vec::new());

        interpreter
            .call_function(&caller, &[], Vec::new(), Vec::new())
            .map(|_| ())
            .expect_err("a callee declaring a requirement needs evidence for it");
        assert!(
            nested_events(&interpreter).is_empty(),
            "a call refused for missing evidence never entered the callee: {:?}",
            interpreter.event_log()
        );
    }

    #[test]
    fn a_call_rejected_for_a_generic_mismatch_records_no_call_event() {
        let mut module = module();
        module.functions.push(same_type_twice());
        let interpreter = Interpreter::new(&module);
        // `same_type_twice` is generic, and the call site supplies no
        // type arguments -- refused before the frame is entered.
        let caller = caller_of(
            ItemId(97),
            vec![ValueId(1), ValueId(2)],
            vec![
                Param {
                    value: ValueId(1),
                    ty: Ty::Applied(BOXY, vec![Ty::I64]),
                    take: false,
                },
                Param {
                    value: ValueId(2),
                    ty: Ty::Applied(BOXY, vec![Ty::I64]),
                    take: false,
                },
            ],
        );

        interpreter
            .call_function(
                &caller,
                &[],
                vec![boxed(Ty::I64, Value::Int(1)), boxed(Ty::I64, Value::Int(2))],
                Vec::new(),
            )
            .map(|_| ())
            .expect_err("a generic callee needs an instantiation");
        assert!(
            nested_events(&interpreter).is_empty(),
            "a generic mismatch never entered the callee: {:?}",
            interpreter.event_log()
        );
    }

    #[test]
    fn a_successful_nested_call_records_exactly_one_call_event() {
        let mut module = module();
        module.functions.push(two_take_files());
        let interpreter = Interpreter::new(&module);
        let first = new_file(&interpreter, 1);
        let second = new_file(&interpreter, 2);
        let caller = caller_of(
            TWO_TAKES,
            vec![ValueId(1), ValueId(2)],
            vec![
                Param {
                    value: ValueId(1),
                    ty: file_ty(),
                    take: true,
                },
                Param {
                    value: ValueId(2),
                    ty: file_ty(),
                    take: true,
                },
            ],
        );

        interpreter
            .call_function(
                &caller,
                &[],
                vec![Value::Resource(first), Value::Resource(second)],
                Vec::new(),
            )
            .expect("two distinct live owners are a legal pair");
        assert_eq!(
            nested_events(&interpreter)
                .iter()
                .filter(|event| event.starts_with("call:"))
                .count(),
            1,
            "entering the callee once records exactly one event: {:?}",
            interpreter.event_log()
        );
    }
    // -- argument validation against the declared parameter type --------

    #[test]
    fn an_argument_disagreeing_with_a_resolved_parameter_type_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let owner = new_file(&interpreter, 1);
        let callee = two_take_files();

        // `two_take_files` declares both parameters `File`. A `Pair`
        // standing where a `File` is declared is malformed, and must be
        // refused before the *other* argument is transferred.
        rejected_without_a_trace(
            &interpreter,
            "a value of the wrong declared type may not be bound",
            || {
                interpreter
                    .call_function(
                        &callee,
                        &[],
                        vec![
                            Value::Resource(owner),
                            pair_of(Value::Int(1), Value::Int(2)),
                        ],
                        Vec::new(),
                    )
                    .map(|_| ())
            },
        );
        assert!(
            interpreter.resources.borrow().observe(owner).is_ok(),
            "the valid first argument must not have been transferred"
        );
    }

    /// The other side of the same rule, and the false positive it would
    /// be easy to introduce: a *generic* parameter has no concrete type
    /// to check against at this boundary, at any depth. `Box[T]` is
    /// declared, `Box[File]` arrives, and that is exactly correct --
    /// one parametric NIR body is shared by every instantiation
    /// (`rfcs/0008`). Comparing them would reject every generic call.
    #[test]
    fn an_argument_filling_a_generic_parameter_is_not_compared_against_it() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let param = crate::hir::TypeParamId(0);
        let owner = new_file(&interpreter, 1);

        for declared in [
            // The whole parameter is symbolic.
            Ty::Param(param, Symbol(0)),
            // Concrete constructor, symbolic argument: checking only
            // the outermost one would still reject this, because
            // `Applied`'s arguments are compared structurally.
            Ty::Applied(MAYBE, vec![Ty::Param(param, Symbol(0))]),
        ] {
            assert!(
                !fully_resolved(&declared),
                "{declared:?} carries an unresolved parameter"
            );
            let value = match &declared {
                Ty::Param(..) => Value::Resource(owner),
                _ => Value::Variant {
                    item: MAYBE,
                    type_args: vec![file_ty()],
                    case: 1,
                    payload: Vec::new(),
                },
            };
            interpreter
                .validate_argument(&value, &declared)
                .expect("a generic position accepts the instantiation that arrives at it");
        }

        // A resolved declaration is still checked, so the relaxation is
        // scoped to genuinely symbolic positions and nothing else.
        assert!(
            interpreter
                .validate_argument(&Value::Int(1), &Ty::Named(FILE, Symbol(0)))
                .is_err(),
            "a resolved position still rejects a value of the wrong kind"
        );
    }
    #[test]
    fn a_partial_generic_keeps_its_concrete_outer_constructor() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let param = crate::hir::TypeParamId(0);
        let owner = new_file(&interpreter, 1);
        let wrong_outer = Value::Record {
            item: HOLDER,
            type_args: Vec::new(),
            fields: vec![Value::Resource(owner)],
        };

        assert!(
            interpreter
                .validate_argument(
                    &wrong_outer,
                    &Ty::Applied(MAYBE, vec![Ty::Param(param, Symbol(0))]),
                )
                .is_err(),
            "a symbolic argument must not erase the concrete constructor"
        );
        assert!(interpreter.resources.borrow().observe(owner).is_ok());
    }
}

/// The verifier and the interpreter must agree about who owns what.
///
/// These reconstruct ownership from completely different material --
/// `nir::verify` from the NIR, the interpreter from runtime values and
/// its resource table -- so agreement is a real property to test, not a
/// tautology. Disagreement in either direction is a defect: the
/// verifier accepting something the interpreter refuses is an unsound
/// static answer, and the verifier refusing something the interpreter
/// accepts is a false positive that would reject a working program.
#[cfg(test)]
mod stage_agreement {
    use super::*;
    use crate::hir::ItemRegistry;
    use crate::nir::{BasicBlock, BlockId, Instruction, RecordLayout, verify_module};
    use crate::source::SourceMap;
    use crate::symbol::Interner;

    const FILE: ItemId = ItemId(70);
    const ENVELOPE: ItemId = ItemId(71);
    const MAIN: ItemId = ItemId(72);

    /// `File` (a declared `resource`) and `Envelope` (an ordinary record
    /// with one `File` field -- affine only *transitively*, and so never
    /// a key in the nominal resource lattice at all: the exact gap the
    /// laundering hid in).
    fn layouts(interner: &mut Interner) -> Vec<(ItemId, RecordLayout)> {
        let file = interner.intern("File");
        let envelope = interner.intern("Envelope");
        let field = interner.intern("f");
        vec![
            (
                FILE,
                RecordLayout {
                    name: file,
                    type_params: Vec::new(),
                    fields: vec![(field, Ty::I64)],
                    affine: true,
                },
            ),
            (
                ENVELOPE,
                RecordLayout {
                    name: envelope,
                    type_params: Vec::new(),
                    fields: vec![(field, Ty::Named(FILE, file))],
                    affine: false,
                },
            ),
        ]
    }

    /// The blocker's own reproduction, as NIR:
    ///
    /// ```text
    /// %0 = alloc Envelope
    /// %2 = Envelope(File(0))
    /// store.observe %0, %2
    /// %3 = load %0
    /// drop %3          ; destroys through a merely-observing view
    /// drop %2
    /// ```
    ///
    /// The interpreter always refused the first `drop`: `store.observe`
    /// runs the value through `to_observer_if_resource`, so `%3` carries
    /// observer handles. The verifier used to accept both drops, because
    /// its observation set only marked the slot observed when the
    /// *stored value* already was -- and `%2` was a genuine owner.
    fn laundering_module(interner: &mut Interner) -> Module {
        let name = interner.intern("main");
        let file = Ty::Named(FILE, interner.intern("File"));
        let envelope = Ty::Named(ENVELOPE, interner.intern("Envelope"));
        Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            records: layouts(interner),
            variants: Vec::new(),
            functions: vec![Function {
                id: MAIN,
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
                            ty: envelope.clone(),
                            kind: ValueKind::Alloc,
                        },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(0)),
                        },
                        Instruction::Value {
                            result: ValueId(4),
                            ty: file,
                            kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(1)]),
                        },
                        Instruction::Value {
                            result: ValueId(2),
                            ty: envelope.clone(),
                            kind: ValueKind::RecordCreate(ENVELOPE, Vec::new(), vec![ValueId(4)]),
                        },
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(2),
                            mode: OwnershipMode::Observe,
                        },
                        Instruction::Value {
                            result: ValueId(3),
                            ty: envelope,
                            kind: ValueKind::Load(ValueId(0)),
                        },
                        Instruction::Drop { value: ValueId(3) },
                        Instruction::Drop { value: ValueId(2) },
                    ],
                    terminator: Terminator::Return(None),
                }],
            }],
        }
    }

    #[test]
    fn the_verifier_and_the_interpreter_both_refuse_an_observing_store_laundered_into_an_owner() {
        let mut interner = Interner::new();
        let module = laundering_module(&mut interner);

        // The interpreter's own answer, which never changed: dropping
        // through the observing view the slot handed back is refused.
        let interpreter = Interpreter::new(&module);
        let runtime = interpreter
            .call_item(MAIN, Vec::new())
            .expect_err("destroying through an observing handle must be refused at run time");
        assert!(
            format!("{runtime:?}").contains("merely-observing"),
            "the interpreter refuses it as an observation, got {runtime:?}"
        );

        // The verifier must reach the same conclusion statically,
        // rather than accepting a program the runtime will refuse.
        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            diagnostics
                .iter()
                // `V0099` is the stable code for OBSERVER_CANNOT_TRANSFER;
                // the string is the published contract, so asserting it
                // directly is what a downstream consumer would rely on.
                .any(|d| d.code == "V0099"),
            "the verifier must statically reject what the interpreter refuses, got {:?}",
            diagnostics.iter().map(|d| d.code).collect::<Vec<_>>()
        );
    }

    /// The other direction, and the one a sticky observation would
    /// break: a slot that held a view, was finished with, and then
    /// legally received a real owner. Both stages must *accept* it.
    #[test]
    fn the_verifier_and_the_interpreter_both_accept_a_slot_reused_as_a_real_owner() {
        let mut interner = Interner::new();
        let name = interner.intern("main");
        let file_sym = interner.intern("File");
        let file = Ty::Named(FILE, file_sym);
        let int = |result: u32| Instruction::Value {
            result: ValueId(result),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(0)),
        };
        let make_file = |descriptor: u32, result: u32| Instruction::Value {
            result: ValueId(result),
            ty: Ty::Named(FILE, file_sym),
            kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(descriptor)]),
        };
        let module = Module {
            protocols: Vec::new(),
            extends: Vec::new(),
            records: layouts(&mut interner),
            variants: Vec::new(),
            functions: vec![Function {
                id: MAIN,
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
                            ty: file.clone(),
                            kind: ValueKind::Alloc,
                        },
                        int(1),
                        make_file(1, 2),
                        // A view of `%2`, read back, then `%2` is
                        // destroyed through its own owning identity.
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(2),
                            mode: OwnershipMode::Observe,
                        },
                        Instruction::Value {
                            result: ValueId(3),
                            ty: file.clone(),
                            kind: ValueKind::Load(ValueId(0)),
                        },
                        Instruction::Drop { value: ValueId(2) },
                        // The slot now owns nothing, so it may legally
                        // be given a real owner -- which this frame
                        // then destroys through the slot itself.
                        int(4),
                        make_file(4, 5),
                        Instruction::Store {
                            slot: ValueId(0),
                            value: ValueId(5),
                            mode: OwnershipMode::Transfer,
                        },
                        Instruction::Value {
                            result: ValueId(6),
                            ty: file,
                            kind: ValueKind::Load(ValueId(0)),
                        },
                        Instruction::Drop { value: ValueId(6) },
                    ],
                    terminator: Terminator::Return(None),
                }],
            }],
        };

        let mut map = SourceMap::new();
        let source = map.add_file("t.npt", "");
        let diagnostics = verify_module(&module, source, &interner, &ItemRegistry::default());
        assert!(
            diagnostics.is_empty(),
            "an observation is a fact about a path, not a life sentence on a slot: {:?}",
            diagnostics
                .iter()
                .map(|d| format!("{}: {}", d.code, d.message))
                .collect::<Vec<_>>()
        );

        let interpreter = Interpreter::new(&module);
        interpreter
            .call_item(MAIN, Vec::new())
            .expect("the interpreter must accept exactly what the verifier accepted");
        // `%3` was only ever a view, so nothing destroyed it twice and
        // exactly two resources were created and destroyed.
        assert_eq!(
            interpreter
                .event_log()
                .iter()
                .filter(|event| event.starts_with("drop:"))
                .count(),
            2,
            "each of the two real owners is destroyed exactly once"
        );
    }
}

/// Observation is *transitive* and every rejected access is atomic
/// (`rfcs/0011`, `rfcs/0012`).
///
/// Two independent properties are proven here, on the same fixture,
/// because the first one failing is what made the second one visible.
///
/// **Transitivity.** Once a traversal crosses an observer boundary, no
/// owner-capable handle may emerge anywhere in the subtree it reaches.
/// Reading a field out of an observed resource used to downgrade only a
/// handle stored *directly* in that field: a field holding a plain
/// `Box[Session]` record was handed back untouched, owning handles and
/// all, so one projection through a generic aggregate laundered an
/// observation back into ownership.
///
/// **Atomicity.** A rejected access must perform no semantic mutation.
/// The walk used to tombstone the field it reached and only afterwards
/// discover that an ancestor on the path was merely observed, leaving
/// the nested resource `Moved` behind a returned `Err`.
#[cfg(test)]
mod observed_projection_atomicity {
    use super::*;
    use crate::nir::{CaseLayout, RecordLayout, VariantLayout};
    use crate::place::{FieldId, Projection};
    use crate::symbol::Symbol;

    const FILE: ItemId = ItemId(170);
    const SESSION: ItemId = ItemId(171);
    const BOXY: ItemId = ItemId(172);
    const OUTER: ItemId = ItemId(173);
    const HOLDER: ItemId = ItemId(174);
    const MAYBE: ItemId = ItemId(175);

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
                    SESSION,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Named(FILE, name))],
                        affine: true,
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
                (
                    OUTER,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Applied(BOXY, vec![Ty::Named(SESSION, name)]))],
                        affine: true,
                    },
                ),
                (
                    HOLDER,
                    RecordLayout {
                        name,
                        type_params: Vec::new(),
                        fields: vec![(name, Ty::Applied(MAYBE, vec![Ty::Named(SESSION, name)]))],
                        affine: true,
                    },
                ),
            ],
            variants: vec![(
                MAYBE,
                VariantLayout {
                    name,
                    type_params: vec![(param, name)],
                    cases: vec![
                        CaseLayout {
                            name,
                            payload: vec![Ty::Param(param, name)],
                        },
                        CaseLayout {
                            name,
                            payload: Vec::new(),
                        },
                    ],
                },
            )],
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    /// `Outer{ Box[Session]{ Session{ File{ i64 } } } }`, with every
    /// resource owned exactly once, and every handle an owner.
    struct Fixture {
        file: ResourceHandle,
        session: ResourceHandle,
        outer: ResourceHandle,
    }

    fn build(interpreter: &Interpreter<'_>) -> Fixture {
        let name = Symbol(0);
        let file = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(7)]);
        let session = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Resource(file)]);
        let boxed = Value::Record {
            item: BOXY,
            type_args: vec![Ty::Named(SESSION, name)],
            fields: vec![Value::Resource(session)],
        };
        let outer = interpreter
            .resources
            .borrow_mut()
            .construct(OUTER, vec![boxed]);
        Fixture {
            file,
            session,
            outer,
        }
    }

    /// The same shape, but with the generic aggregate on the path being
    /// a *variant payload* rather than a record field.
    fn build_variant(interpreter: &Interpreter<'_>) -> (ResourceHandle, ResourceHandle) {
        let name = Symbol(0);
        let file = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(9)]);
        let session = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Resource(file)]);
        let payload = Value::Variant {
            item: MAYBE,
            type_args: vec![Ty::Named(SESSION, name)],
            case: 0,
            payload: vec![Value::Resource(session)],
        };
        let holder = interpreter
            .resources
            .borrow_mut()
            .construct(HOLDER, vec![payload]);
        (session, holder)
    }

    fn field_of(interpreter: &Interpreter<'_>, handle: ResourceHandle, index: usize) -> Value {
        interpreter.resources.borrow().records[handle.id.0 as usize].fields[index].clone()
    }

    fn generation_of(interpreter: &Interpreter<'_>, handle: ResourceHandle) -> u64 {
        interpreter.resources.borrow().records[handle.id.0 as usize].generation
    }

    /// Every observable fact a rejected operation must leave untouched.
    #[derive(Debug, PartialEq)]
    struct Snapshot {
        fields: Vec<Vec<Value>>,
        generations: Vec<u64>,
        statuses: Vec<ResourceStatus>,
        items: Vec<ItemId>,
        events: Vec<String>,
    }

    fn snapshot(interpreter: &Interpreter<'_>) -> Snapshot {
        let table = interpreter.resources.borrow();
        Snapshot {
            fields: table.records.iter().map(|r| r.fields.clone()).collect(),
            generations: table.records.iter().map(|r| r.generation).collect(),
            statuses: table.records.iter().map(|r| r.status.clone()).collect(),
            items: table.records.iter().map(|r| r.item).collect(),
            events: interpreter.event_log().to_vec(),
        }
    }

    fn observer(interpreter: &Interpreter<'_>, handle: ResourceHandle) -> ResourceHandle {
        interpreter
            .resources
            .borrow()
            .to_observer(handle)
            .expect("the fixture's own resources are all live")
    }

    fn field(owner: ItemId) -> Projection {
        Projection::Field {
            owner,
            field: FieldId(0),
        }
    }

    /// Every handle `value` carries inline, at any depth.
    fn collect_handles(value: &Value, out: &mut Vec<ResourceHandle>) {
        match value {
            Value::Resource(handle) => out.push(*handle),
            Value::Record { fields, .. } => {
                for field in fields {
                    collect_handles(field, out);
                }
            }
            Value::Variant { payload, .. } => {
                for slot in payload {
                    collect_handles(slot, out);
                }
            }
            _ => {}
        }
    }

    fn assert_all_observers(value: &Value, what: &str) {
        let mut found = Vec::new();
        collect_handles(value, &mut found);
        assert!(!found.is_empty(), "{what}: the fixture carries no handles");
        for handle in found {
            assert_eq!(
                handle.role,
                RuntimeOwnershipRole::Observer,
                "{what}: an owning handle emerged from an observed ancestor"
            );
        }
    }

    /// The reported defect, at its own layer: a take that crosses an
    /// observed ancestor, passes through a generic record, and reaches a
    /// field two resources deeper.
    #[test]
    fn a_take_through_an_observed_ancestor_is_refused_without_mutating_anything() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let fixture = build(&interpreter);
        let before = snapshot(&interpreter);

        let view = observer(&interpreter, fixture.outer);
        let path = [field(OUTER), field(BOXY), field(SESSION)];
        let result = interpreter.take_projections(Value::Resource(view), &path);

        assert!(
            result.is_err(),
            "a take may never cross an observed ancestor, however many aggregates intervene"
        );
        assert_eq!(
            snapshot(&interpreter),
            before,
            "a rejected take must leave every observable fact exactly as it was"
        );
    }

    /// The same defect with the observer boundary one level shallower:
    /// the session itself is observed, and the file below it is taken.
    #[test]
    fn a_take_through_a_nearer_observed_ancestor_is_refused_without_mutating_anything() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let fixture = build(&interpreter);
        let before = snapshot(&interpreter);

        let view = observer(&interpreter, fixture.session);
        let path = [field(SESSION)];
        let result = interpreter.take_projections(Value::Resource(view), &path);

        assert!(result.is_err(), "the nearer boundary is refused too");
        assert_eq!(
            snapshot(&interpreter),
            before,
            "and it mutates nothing either"
        );
    }

    /// The variant-payload spelling of the same chain: observer ->
    /// variant payload -> record -> resource.
    #[test]
    fn a_take_through_an_observed_variant_payload_is_refused_without_mutating_anything() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (_session, holder) = build_variant(&interpreter);
        let before = snapshot(&interpreter);

        let view = observer(&interpreter, holder);
        // The payload slot is reached as field 0 of the holder, then the
        // variant's own payload index 0, then the session's own field.
        let path = [
            field(HOLDER),
            Projection::VariantField {
                variant: MAYBE,
                case: crate::place::CaseId(0),
                field: FieldId(0),
            },
            field(SESSION),
        ];
        let result = interpreter.take_projections(Value::Resource(view), &path);

        assert!(
            result.is_err(),
            "a variant payload is no more a laundering route than a record field"
        );
        assert_eq!(
            snapshot(&interpreter),
            before,
            "and the rejection mutates nothing"
        );
    }

    /// The laundering itself, independent of whether anything is later
    /// taken: reading through an observer must not yield an owner at any
    /// depth, through any aggregate.
    #[test]
    fn reading_through_an_observer_yields_no_owner_at_any_depth() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let fixture = build(&interpreter);

        let view = observer(&interpreter, fixture.outer);
        let boxed = interpreter
            .resources
            .borrow()
            .observe_field(view, 0)
            .expect("reading an observed resource's own field is always legal");

        assert_all_observers(&boxed, "a `Box[Session]` read out of an observed resource");
    }

    /// The variant spelling of the same read: a field holding a
    /// `Maybe[Session]` must come back with its payload downgraded too,
    /// not just a field holding a record.
    #[test]
    fn reading_a_variant_payload_through_an_observer_yields_no_owner() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let (_session, holder) = build_variant(&interpreter);

        let view = observer(&interpreter, holder);
        let payload = interpreter
            .resources
            .borrow()
            .observe_field(view, 0)
            .expect("reading an observed resource's own field is always legal");

        assert!(
            matches!(payload, Value::Variant { .. }),
            "the fixture really does store a variant in that field"
        );
        assert_all_observers(
            &payload,
            "a `Maybe[Session]` read out of an observed resource",
        );
    }

    /// The same, through the projection walker rather than one field
    /// read, and at every depth the walk can stop at.
    #[test]
    fn observing_a_projection_through_an_observer_yields_no_owner() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let fixture = build(&interpreter);
        let view = Value::Resource(observer(&interpreter, fixture.outer));

        for depth in 1..=2 {
            let path = [field(OUTER), field(BOXY)];
            let reached = interpreter
                .observe_projections(&view, &path[..depth])
                .expect("observing is always legal through an observer");
            assert_all_observers(&reached, "a projection observed through an observer");
        }
    }

    /// A store *into* a place reached through an observed ancestor is
    /// refused, and changes nothing.
    #[test]
    fn a_store_through_an_observed_ancestor_is_refused_without_mutating_anything() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let fixture = build(&interpreter);
        // Empty the field first, through the real owner, so the store
        // would otherwise have somewhere legal to land.
        let path = [field(OUTER), field(BOXY), field(SESSION)];
        let taken = interpreter
            .take_projections(Value::Resource(fixture.outer), &path)
            .expect("the owner may empty its own nested field");
        let before = snapshot(&interpreter);

        let view = Value::Resource(observer(&interpreter, fixture.outer));
        let result = interpreter.store_projections(view, &path, taken.extracted);

        assert!(
            result.is_err(),
            "reinitializing through an observed ancestor is still an observation"
        );
        assert_eq!(
            snapshot(&interpreter),
            before,
            "and the refused store wrote nothing"
        );
    }

    /// The same path through a genuine owner still works, so the fix is
    /// a restriction on observation rather than on depth.
    #[test]
    fn the_same_path_through_a_real_owner_still_transfers() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let fixture = build(&interpreter);

        let path = [field(OUTER), field(BOXY), field(SESSION)];
        let taken = interpreter
            .take_projections(Value::Resource(fixture.outer), &path)
            .expect("an owner may take its own nested field");

        assert_eq!(
            taken.extracted,
            Value::Resource(fixture.file),
            "the owner really does receive the file it reached"
        );
        assert_eq!(
            field_of(&interpreter, fixture.session, 0),
            Value::Moved,
            "and the field it came out of is tombstoned exactly once"
        );
        assert_eq!(
            generation_of(&interpreter, fixture.file),
            0,
            "a field moved out of its owner does not change the moved value's own generation"
        );
    }

    /// Repeating a rejected operation must be deterministic: the same
    /// error, and still no mutation.
    #[test]
    fn repeating_a_rejected_take_is_deterministic() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let fixture = build(&interpreter);
        let before = snapshot(&interpreter);
        let path = [field(OUTER), field(BOXY), field(SESSION)];

        let first = interpreter
            .take_projections(
                Value::Resource(observer(&interpreter, fixture.outer)),
                &path,
            )
            .err()
            .expect("refused the first time");
        let second = interpreter
            .take_projections(
                Value::Resource(observer(&interpreter, fixture.outer)),
                &path,
            )
            .err()
            .expect("refused identically the second time");

        assert_eq!(
            format!("{first:?}"),
            format!("{second:?}"),
            "a rejected operation is deterministic"
        );
        assert_eq!(
            snapshot(&interpreter),
            before,
            "neither attempt mutated anything"
        );
    }
}

/// Runtime construction validates every value against the type its
/// declaration actually resolves to (`rfcs/0008`, `rfcs/0011`,
/// `rfcs/0012`).
///
/// `RecordCreate` and `VariantCreate` used to reach transfer planning
/// having checked only how *many* values they were handed. A hand-built
/// module could therefore construct a `File` whose one declared field is
/// `descriptor: i64` out of a live resource handle: the interpreter
/// answered `Ok`, transferred ownership into the malformed aggregate,
/// and left a resource owned by a position that declares a primitive.
///
/// The verifier remains the first line of defence. These tests drive the
/// interpreter directly, because defence in depth is only real if the
/// stage below refuses the same thing on its own.
#[cfg(test)]
mod runtime_construction_validation {
    use super::*;
    use crate::nir::{
        BasicBlock, BlockId, CaseLayout, Function, Instruction, Param, RecordLayout, Terminator,
        VariantLayout,
    };
    use crate::symbol::Symbol;

    const FILE: ItemId = ItemId(180);
    const SESSION: ItemId = ItemId(181);
    const BOXY: ItemId = ItemId(182);
    const PAIR: ItemId = ItemId(183);
    const MAYBE: ItemId = ItemId(184);
    const CALLER: ItemId = ItemId(185);

    fn name() -> Symbol {
        Symbol(0)
    }

    fn file_ty() -> Ty {
        Ty::Named(FILE, name())
    }

    fn module() -> Module {
        let param = crate::hir::TypeParamId(0);
        Module {
            functions: Vec::new(),
            records: vec![
                (
                    FILE,
                    RecordLayout {
                        name: name(),
                        type_params: Vec::new(),
                        fields: vec![(name(), Ty::I64)],
                        affine: true,
                    },
                ),
                (
                    SESSION,
                    RecordLayout {
                        name: name(),
                        type_params: Vec::new(),
                        fields: vec![(name(), file_ty())],
                        affine: true,
                    },
                ),
                (
                    BOXY,
                    RecordLayout {
                        name: name(),
                        type_params: vec![(param, name())],
                        fields: vec![(name(), Ty::Param(param, name()))],
                        affine: false,
                    },
                ),
                (
                    PAIR,
                    RecordLayout {
                        name: name(),
                        type_params: Vec::new(),
                        fields: vec![(name(), Ty::I64), (name(), Ty::Bool)],
                        affine: false,
                    },
                ),
            ],
            variants: vec![(
                MAYBE,
                VariantLayout {
                    name: name(),
                    type_params: vec![(param, name())],
                    cases: vec![
                        CaseLayout {
                            name: name(),
                            payload: vec![Ty::Param(param, name())],
                        },
                        CaseLayout {
                            name: name(),
                            payload: Vec::new(),
                        },
                    ],
                },
            )],
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    /// A function whose single `take` parameter is `param_ty`, whose body
    /// is exactly one construction of `kind`, and which returns it.
    fn constructing(param_ty: Ty, result_ty: Ty, kind: ValueKind) -> Function {
        Function {
            id: CALLER,
            name: name(),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: param_ty,
                take: true,
            }],
            return_type: result_ty.clone(),
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(1),
                    ty: result_ty,
                    kind,
                }],
                terminator: Terminator::Return(Some(ValueId(1))),
            }],
        }
    }

    /// The same shape, but taking no parameter at all: the construction's
    /// inputs are constants the body makes for itself.
    fn constructing_from_consts(
        consts: Vec<Instruction>,
        result_ty: Ty,
        kind: ValueKind,
        result: u32,
    ) -> Function {
        let mut instructions = consts;
        instructions.push(Instruction::Value {
            result: ValueId(result),
            ty: result_ty.clone(),
            kind,
        });
        Function {
            id: CALLER,
            name: name(),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: result_ty,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions,
                terminator: Terminator::Return(Some(ValueId(result))),
            }],
        }
    }

    fn int(result: u32, value: u128) -> Instruction {
        Instruction::Value {
            result: ValueId(result),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(value)),
        }
    }

    fn new_file(interpreter: &Interpreter<'_>, descriptor: i128) -> ResourceHandle {
        interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(descriptor)])
    }

    /// Everything a rejected construction must leave exactly as it was.
    #[derive(Debug, PartialEq)]
    struct Snapshot {
        records: usize,
        fields: Vec<Vec<Value>>,
        generations: Vec<u64>,
        statuses: Vec<ResourceStatus>,
        events: Vec<String>,
    }

    fn snapshot(interpreter: &Interpreter<'_>) -> Snapshot {
        let table = interpreter.resources.borrow();
        Snapshot {
            records: table.records.len(),
            fields: table.records.iter().map(|r| r.fields.clone()).collect(),
            generations: table.records.iter().map(|r| r.generation).collect(),
            statuses: table.records.iter().map(|r| r.status.clone()).collect(),
            events: interpreter.event_log(),
        }
    }

    /// Runs `function` with `args` and asserts it is refused without
    /// changing a single observable fact.
    /// Runs a parameterless `function` whose body ends in one malformed
    /// construction, and asserts both that it is refused and that the
    /// refusal left the resources its own earlier instructions legitimately
    /// created exactly as they were.
    ///
    /// Deliberately parameterless: binding a `take` parameter is itself a
    /// real ownership transfer, so a function that received one would
    /// legitimately show an advanced generation before the construction
    /// under test ever ran, and the snapshot could no longer attribute a
    /// change to the rejection.
    fn refused(function: Function, expected_resources: usize, what: &str) -> String {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let error = interpreter
            .call_function(&function, &[], Vec::new(), Vec::new())
            .map(|_| ())
            .err()
            .unwrap_or_else(|| panic!("{what}: the interpreter accepted a malformed construction"));
        let after = snapshot(&interpreter);
        assert_eq!(
            after.records, expected_resources,
            "{what}: a rejected construction creates no new runtime resource"
        );
        assert!(
            after.generations.iter().all(|generation| *generation == 0),
            "{what}: a rejected construction advances no generation, got {:?}",
            after.generations
        );
        assert!(
            after
                .statuses
                .iter()
                .all(|status| *status == ResourceStatus::Alive),
            "{what}: a rejected construction destroys nothing"
        );
        assert!(
            after
                .fields
                .iter()
                .flatten()
                .all(|field| !matches!(field, Value::Moved | Value::Dropped)),
            "{what}: a rejected construction moves no field out of anything"
        );
        format!("{error:?}")
    }

    /// Builds a valid `File` in `%result`, from a constant in
    /// `%result - 1`, as a prefix every "now feed it somewhere illegal"
    /// test shares.
    fn valid_file(descriptor: u128, konst: u32, result: u32) -> Vec<Instruction> {
        vec![
            int(konst, descriptor),
            Instruction::Value {
                result: ValueId(result),
                ty: file_ty(),
                kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(konst)]),
            },
        ]
    }

    /// The reported defect: a live resource handed to a field whose
    /// declared type is `i64`.
    #[test]
    fn a_resource_cannot_fill_a_field_declared_as_a_primitive() {
        let function = constructing_from_consts(
            valid_file(3, 0, 1),
            file_ty(),
            ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(1)]),
            2,
        );
        let error = refused(function, 1, "a resource in an `i64` field");
        assert!(
            error.contains("different kind") || error.contains("owns nothing"),
            "the rejection names the disagreement, got {error}"
        );
    }

    /// The mirror image: a primitive where a resource is declared.
    #[test]
    fn a_primitive_cannot_fill_a_field_declared_as_a_resource() {
        let function = constructing_from_consts(
            vec![int(0, 5)],
            Ty::Named(SESSION, name()),
            ValueKind::RecordCreate(SESSION, Vec::new(), vec![ValueId(0)]),
            1,
        );
        refused(function, 0, "an `i64` in a `File` field");
    }

    /// A resource of the wrong declaration, where the field's own
    /// resource type is a different one entirely.
    #[test]
    fn a_resource_of_the_wrong_declaration_cannot_fill_a_resource_field() {
        // `%2` is a valid `File`; `%3` is a valid `Session` owning it.
        // `Session`'s own field is declared `File`, so handing it that
        // `Session` is a resource of an entirely different declaration.
        let mut body = valid_file(1, 0, 1);
        body.push(Instruction::Value {
            result: ValueId(2),
            ty: Ty::Named(SESSION, name()),
            kind: ValueKind::RecordCreate(SESSION, Vec::new(), vec![ValueId(1)]),
        });
        let function = constructing_from_consts(
            body,
            Ty::Named(SESSION, name()),
            ValueKind::RecordCreate(SESSION, Vec::new(), vec![ValueId(2)]),
            3,
        );
        // The inner `File` legitimately moved into the `Session` before
        // the malformed construction ran, so this one asserts the
        // rejection directly rather than through the shared helper.
        let module = module();
        let interpreter = Interpreter::new(&module);
        let error = interpreter
            .call_function(&function, &[], Vec::new(), Vec::new())
            .map(|_| ())
            .expect_err("a `Session` is not a `File`, however alike their shapes are");
        assert!(
            format!("{error:?}").contains("different"),
            "the rejection names the disagreement, got {error:?}"
        );
        let after = snapshot(&interpreter);
        assert_eq!(
            after.records, 2,
            "the two legitimate resources exist; the malformed one was never created"
        );
        assert!(
            after
                .statuses
                .iter()
                .all(|status| *status == ResourceStatus::Alive),
            "and neither of them was destroyed"
        );
        assert_eq!(
            after.generations[1], 0,
            "the `Session` never moved: the construction that would have taken it was refused"
        );
    }

    /// Too few values for the declaration's own field list.
    #[test]
    fn a_record_cannot_be_built_with_the_wrong_arity() {
        let function = constructing_from_consts(
            vec![int(0, 1)],
            Ty::Named(PAIR, name()),
            ValueKind::RecordCreate(PAIR, Vec::new(), vec![ValueId(0)]),
            1,
        );
        refused(function, 0, "a two-field record built from one value");
    }

    /// A value of the wrong kind in the *second* field, so the first one
    /// has already been checked when the disagreement is found.
    #[test]
    fn a_later_field_of_the_wrong_kind_is_still_refused() {
        let function = constructing_from_consts(
            vec![int(0, 1), int(1, 2)],
            Ty::Named(PAIR, name()),
            ValueKind::RecordCreate(PAIR, Vec::new(), vec![ValueId(0), ValueId(1)]),
            2,
        );
        refused(function, 0, "an `i64` where `bool` is declared");
    }

    /// A payload handed to a case that declares none.
    #[test]
    fn a_payload_cannot_be_given_to_a_payload_less_case() {
        let function = constructing_from_consts(
            vec![int(0, 1)],
            Ty::Applied(MAYBE, vec![Ty::I64]),
            ValueKind::VariantCreate {
                variant: MAYBE,
                case: 1,
                type_args: vec![Ty::I64],
                payload: vec![ValueId(0)],
            },
            1,
        );
        refused(function, 0, "a payload on a payload-less case");
    }

    /// A case that declares a payload, built without one.
    #[test]
    fn a_required_payload_cannot_be_omitted() {
        let function = constructing_from_consts(
            Vec::new(),
            Ty::Applied(MAYBE, vec![Ty::I64]),
            ValueKind::VariantCreate {
                variant: MAYBE,
                case: 0,
                type_args: vec![Ty::I64],
                payload: Vec::new(),
            },
            0,
        );
        refused(function, 0, "a missing required payload");
    }

    /// A payload of the wrong type for the case's own substitution.
    #[test]
    fn a_payload_of_the_wrong_type_is_refused() {
        let function = constructing_from_consts(
            valid_file(4, 0, 1),
            Ty::Applied(MAYBE, vec![Ty::I64]),
            ValueKind::VariantCreate {
                variant: MAYBE,
                case: 0,
                type_args: vec![Ty::I64],
                payload: vec![ValueId(1)],
            },
            2,
        );
        refused(function, 1, "a resource payload where `i64` is substituted");
    }

    /// A case index the declaration does not have.
    #[test]
    fn an_unknown_variant_case_is_refused() {
        let function = constructing_from_consts(
            Vec::new(),
            Ty::Applied(MAYBE, vec![Ty::I64]),
            ValueKind::VariantCreate {
                variant: MAYBE,
                case: 7,
                type_args: vec![Ty::I64],
                payload: Vec::new(),
            },
            0,
        );
        refused(function, 0, "a case the variant does not declare");
    }

    /// The generic field, filled correctly: `Box[File]` really may hold a
    /// `File`, and the construction must still succeed.
    #[test]
    fn a_generic_field_accepts_its_own_substitution() {
        let function = constructing_from_consts(
            valid_file(1, 0, 1),
            Ty::Applied(BOXY, vec![file_ty()]),
            ValueKind::RecordCreate(BOXY, vec![file_ty()], vec![ValueId(1)]),
            2,
        );
        let module = module();
        let interpreter = Interpreter::new(&module);
        interpreter
            .call_function(&function, &[], Vec::new(), Vec::new())
            .expect("`Box[File]` really does accept a `File`");
    }

    /// The same generic field, filled with something its substitution
    /// does not permit.
    #[test]
    fn a_generic_field_refuses_the_wrong_substitution() {
        let function = constructing_from_consts(
            valid_file(2, 0, 1),
            Ty::Applied(BOXY, vec![Ty::I64]),
            ValueKind::RecordCreate(BOXY, vec![Ty::I64], vec![ValueId(1)]),
            2,
        );
        refused(function, 1, "a `File` in a `Box[i64]`");
    }

    /// A malformed aggregate nested one level down: the outer counts are
    /// right, and only the inner field disagrees.
    #[test]
    fn a_nested_malformed_aggregate_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        // A `Box[File]` whose slot actually holds an `i64`, handed to a
        // position that declares `Box[File]`.
        let malformed = Value::Record {
            item: BOXY,
            type_args: vec![file_ty()],
            fields: vec![Value::Int(0)],
        };
        let function = constructing(
            Ty::Applied(BOXY, vec![file_ty()]),
            Ty::Applied(BOXY, vec![Ty::Applied(BOXY, vec![file_ty()])]),
            ValueKind::RecordCreate(
                BOXY,
                vec![Ty::Applied(BOXY, vec![file_ty()])],
                vec![ValueId(0)],
            ),
        );
        let before = snapshot(&interpreter);
        interpreter
            .call_function(&function, &[], vec![malformed], Vec::new())
            .map(|_| ())
            .expect_err("the inner disagreement is still a disagreement");
        assert_eq!(
            snapshot(&interpreter),
            before,
            "and the outer construction changed nothing"
        );
    }

    /// A hand-built value that reaches the same resource identity twice
    /// must be refused rather than transferred twice.
    #[test]
    fn a_duplicated_identity_in_one_construction_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let file = new_file(&interpreter, 1);
        let function = Function {
            id: CALLER,
            name: name(),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![
                Param {
                    value: ValueId(0),
                    ty: file_ty(),
                    take: true,
                },
                Param {
                    value: ValueId(1),
                    ty: file_ty(),
                    take: true,
                },
            ],
            return_type: Ty::Named(SESSION, name()),
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![Instruction::Value {
                    result: ValueId(2),
                    ty: Ty::Named(SESSION, name()),
                    kind: ValueKind::RecordCreate(SESSION, Vec::new(), vec![ValueId(0)]),
                }],
                terminator: Terminator::Return(Some(ValueId(2))),
            }],
        };
        let result = interpreter.call_function(
            &function,
            &[],
            vec![Value::Resource(file), Value::Resource(file)],
            Vec::new(),
        );
        assert!(
            result.is_err(),
            "one identity bound twice is a duplicate, not two resources"
        );
        assert_eq!(
            interpreter.resources.borrow().records.len(),
            1,
            "and the refusal created no new resource"
        );
    }

    /// The whole point of the exercise: a well-formed construction still
    /// succeeds, for a record, a resource and a variant alike.
    #[test]
    fn well_formed_constructions_still_succeed() {
        let module = module();
        let interpreter = Interpreter::new(&module);

        // A plain record.
        let pair = constructing_from_consts(
            vec![
                int(0, 1),
                Instruction::Value {
                    result: ValueId(1),
                    ty: Ty::Bool,
                    kind: ValueKind::Const(Const::Bool(true)),
                },
            ],
            Ty::Named(PAIR, name()),
            ValueKind::RecordCreate(PAIR, Vec::new(), vec![ValueId(0), ValueId(1)]),
            2,
        );
        interpreter
            .call_function(&pair, &[], Vec::new(), Vec::new())
            .expect("a well-formed `Pair` is still constructible");

        // A resource.
        let file = constructing_from_consts(
            vec![int(0, 9)],
            file_ty(),
            ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(0)]),
            1,
        );
        interpreter
            .call_function(&file, &[], Vec::new(), Vec::new())
            .expect("a well-formed `File` is still constructible");

        // A variant, both cases.
        let some = constructing_from_consts(
            vec![int(0, 3)],
            Ty::Applied(MAYBE, vec![Ty::I64]),
            ValueKind::VariantCreate {
                variant: MAYBE,
                case: 0,
                type_args: vec![Ty::I64],
                payload: vec![ValueId(0)],
            },
            1,
        );
        interpreter
            .call_function(&some, &[], Vec::new(), Vec::new())
            .expect("a well-formed `Maybe[i64]::Some` is still constructible");
        let none = constructing_from_consts(
            Vec::new(),
            Ty::Applied(MAYBE, vec![Ty::I64]),
            ValueKind::VariantCreate {
                variant: MAYBE,
                case: 1,
                type_args: vec![Ty::I64],
                payload: Vec::new(),
            },
            0,
        );
        interpreter
            .call_function(&none, &[], Vec::new(), Vec::new())
            .expect("a well-formed `Maybe[i64]::None` is still constructible");
    }
}

/// Every typed boundary refuses a value that disagrees with the type its
/// destination declares, and refuses it without changing anything
/// (`rfcs/0008`, `rfcs/0011`, `rfcs/0012`).
///
/// Construction was the boundary that was reported, but it was never the
/// only one: a value enters a typed destination on a `Store`, through a
/// `StorePlace`, as a call or `take` argument, as a function's own
/// result, and when a deferred call is captured and later run. Each of
/// these is checked here directly against the interpreter, because
/// defence in depth is only real if the stage below the verifier refuses
/// the same thing on its own.
#[cfg(test)]
mod typed_boundaries {
    use super::*;
    use crate::nir::{BasicBlock, BlockId, Function, Instruction, Param, RecordLayout, Terminator};
    use crate::symbol::Symbol;

    const FILE: ItemId = ItemId(190);
    const SESSION: ItemId = ItemId(191);
    const CALLER: ItemId = ItemId(192);
    const CALLEE: ItemId = ItemId(193);

    fn name() -> Symbol {
        Symbol(0)
    }

    fn file_ty() -> Ty {
        Ty::Named(FILE, name())
    }

    fn session_ty() -> Ty {
        Ty::Named(SESSION, name())
    }

    fn module() -> Module {
        Module {
            functions: Vec::new(),
            records: vec![
                (
                    FILE,
                    RecordLayout {
                        name: name(),
                        type_params: Vec::new(),
                        fields: vec![(name(), Ty::I64)],
                        affine: true,
                    },
                ),
                (
                    SESSION,
                    RecordLayout {
                        name: name(),
                        type_params: Vec::new(),
                        fields: vec![(name(), file_ty())],
                        affine: true,
                    },
                ),
            ],
            variants: Vec::new(),
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    fn int(result: u32, value: u128) -> Instruction {
        Instruction::Value {
            result: ValueId(result),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(value)),
        }
    }

    /// `%konst` then a valid `File` in `%result`.
    fn make_file(konst: u32, result: u32) -> Vec<Instruction> {
        vec![
            int(konst, 1),
            Instruction::Value {
                result: ValueId(result),
                ty: file_ty(),
                kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(konst)]),
            },
        ]
    }

    fn function(instructions: Vec<Instruction>, terminator: Terminator, ret: Ty) -> Function {
        Function {
            id: CALLER,
            name: name(),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: ret,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions,
                terminator,
            }],
        }
    }

    /// Runs `function` and asserts it is refused with nothing destroyed
    /// and no resource left half-moved.
    fn refuse(function: &Function, args: Vec<Value>, what: &str) -> String {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let error = interpreter
            .call_function(function, &[], args, Vec::new())
            .map(|_| ())
            .expect_err(what);
        let table = interpreter.resources.borrow();
        assert!(
            table
                .records
                .iter()
                .all(|record| record.status == ResourceStatus::Alive),
            "{what}: a refused operation destroys nothing"
        );
        assert!(
            table
                .records
                .iter()
                .flat_map(|record| record.fields.iter())
                .all(|field| !matches!(field, Value::Moved | Value::Dropped)),
            "{what}: a refused operation moves no field out of anything"
        );
        format!("{error:?}")
    }

    /// A `Store` into a slot whose declared type is `File`, handed a
    /// well-formed `Session`.
    #[test]
    fn a_store_refuses_a_value_of_the_wrong_declared_type() {
        let mut body = make_file(0, 1);
        body.push(Instruction::Value {
            result: ValueId(2),
            ty: session_ty(),
            kind: ValueKind::RecordCreate(SESSION, Vec::new(), vec![ValueId(1)]),
        });
        // The slot declares `File`; the value is a `Session`.
        body.push(Instruction::Value {
            result: ValueId(3),
            ty: file_ty(),
            kind: ValueKind::Alloc,
        });
        body.push(Instruction::Store {
            slot: ValueId(3),
            value: ValueId(2),
            mode: OwnershipMode::Transfer,
        });
        let function = function(body, Terminator::Return(None), Ty::Unit);
        refuse(
            &function,
            Vec::new(),
            "a `Session` stored into a slot that declares `File`",
        );
    }

    /// The same, for an observing store: a view of the wrong type is
    /// still the wrong type.
    #[test]
    fn an_observing_store_refuses_a_value_of_the_wrong_declared_type() {
        let mut body = make_file(0, 1);
        body.push(Instruction::Value {
            result: ValueId(2),
            ty: session_ty(),
            kind: ValueKind::RecordCreate(SESSION, Vec::new(), vec![ValueId(1)]),
        });
        body.push(Instruction::Value {
            result: ValueId(3),
            ty: file_ty(),
            kind: ValueKind::Alloc,
        });
        body.push(Instruction::Store {
            slot: ValueId(3),
            value: ValueId(2),
            mode: OwnershipMode::Observe,
        });
        let function = function(body, Terminator::Return(None), Ty::Unit);
        refuse(
            &function,
            Vec::new(),
            "a `Session` observed into a slot that declares `File`",
        );
    }

    /// A function whose declared result is `File`, returning a `Session`.
    #[test]
    fn a_return_refuses_a_value_of_the_wrong_declared_type() {
        let mut body = make_file(0, 1);
        body.push(Instruction::Value {
            result: ValueId(2),
            ty: session_ty(),
            kind: ValueKind::RecordCreate(SESSION, Vec::new(), vec![ValueId(1)]),
        });
        let function = function(body, Terminator::Return(Some(ValueId(2))), file_ty());
        refuse(
            &function,
            Vec::new(),
            "a `Session` returned where `File` is declared",
        );
    }

    /// A `take` argument of the wrong declared type, at the call
    /// boundary rather than inside the callee.
    #[test]
    fn a_take_argument_of_the_wrong_declared_type_is_refused() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let file = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let session = interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Resource(file)]);
        let callee = Function {
            id: CALLEE,
            name: name(),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: file_ty(),
                take: true,
            }],
            return_type: Ty::Unit,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Return(None),
            }],
        };
        let before = interpreter.resources.borrow().records[session.id.0 as usize].generation;
        let error = interpreter
            .call_function(&callee, &[], vec![Value::Resource(session)], Vec::new())
            .map(|_| ())
            .expect_err("a `Session` is not a `File`");
        assert!(
            format!("{error:?}").contains("different") || format!("{error:?}").contains("disagree"),
            "the rejection names the disagreement, got {error:?}"
        );
        assert_eq!(
            interpreter.resources.borrow().records[session.id.0 as usize].generation,
            before,
            "a refused argument never moved"
        );
    }

    /// The well-formed spellings of each of the above still work, so the
    /// boundary checks are a restriction on malformed values rather than
    /// on the operations themselves.
    #[test]
    fn the_well_formed_spellings_still_succeed() {
        let module = module();
        let interpreter = Interpreter::new(&module);

        // Store of a `File` into a slot that declares `File`.
        let mut body = make_file(0, 1);
        body.push(Instruction::Value {
            result: ValueId(2),
            ty: file_ty(),
            kind: ValueKind::Alloc,
        });
        body.push(Instruction::Store {
            slot: ValueId(2),
            value: ValueId(1),
            mode: OwnershipMode::Transfer,
        });
        body.push(Instruction::Value {
            result: ValueId(3),
            ty: file_ty(),
            kind: ValueKind::Load(ValueId(2)),
        });
        body.push(Instruction::Drop { value: ValueId(3) });
        let stores = function(body, Terminator::Return(None), Ty::Unit);
        interpreter
            .call_function(&stores, &[], Vec::new(), Vec::new())
            .expect("a `File` really may be stored into a slot that declares `File`");

        // Return of a `File` where `File` is declared.
        let returns = function(
            make_file(0, 1),
            Terminator::Return(Some(ValueId(1))),
            file_ty(),
        );
        interpreter
            .call_function(&returns, &[], Vec::new(), Vec::new())
            .expect("a `File` really may be returned where `File` is declared");
    }
}

/// Reading a field is an *observation*, and an observation may never
/// hand back an owner (`rfcs/0011`, `rfcs/0012`).
///
/// These drive the interpreter directly, with hand-built NIR, because
/// that is the only thing the guarantee is actually about: `nir::verify`
/// rejects every one of these programs statically, so a test routed
/// through the source pipeline would pass without the interpreter ever
/// being asked. The two layers are required to agree, and
/// `the_verifier_independently_rejects_the_same_flow` asserts the other
/// half of that agreement.
#[cfg(test)]
mod observed_extraction {
    use super::*;
    use crate::nir::{
        BasicBlock, BlockId, CaseLayout, Function, Instruction, Param, RecordLayout, Terminator,
        VariantLayout,
    };
    use crate::symbol::Symbol;

    const FILE: ItemId = ItemId(190);
    const SESSION: ItemId = ItemId(191);
    const BOXY: ItemId = ItemId(192);
    const MAYBE: ItemId = ItemId(193);
    const STEAL: ItemId = ItemId(194);
    const HOLDER: ItemId = ItemId(195);
    const CRATE: ItemId = ItemId(196);
    const VAULT: ItemId = ItemId(197);
    const SINK: ItemId = ItemId(198);

    fn name() -> Symbol {
        Symbol(0)
    }

    fn param() -> crate::hir::TypeParamId {
        crate::hir::TypeParamId(0)
    }

    fn file_ty() -> Ty {
        Ty::Named(FILE, name())
    }

    fn session_ty() -> Ty {
        Ty::Named(SESSION, name())
    }

    /// `resource File { descriptor: i64 }`,
    /// `resource Session { file: File }`,
    /// `resource Crate { boxed: Box[File] }`,
    /// `resource Vault { slot: Maybe[File] }`,
    /// `record Holder { file: File }`,
    /// `record Box[T] { item: T }`,
    /// `variant Maybe[T] { Some(T), None }`,
    /// plus `func sink(take file: File) -> i64`, the one callee with a
    /// `take` parameter these tests hand an observation to.
    fn module() -> Module {
        Module {
            functions: vec![Function {
                id: SINK,
                name: name(),
                type_params: Vec::new(),
                requirements: Vec::new(),
                params: vec![Param {
                    value: ValueId(0),
                    ty: file_ty(),
                    take: true,
                }],
                return_type: Ty::I64,
                raises: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        Instruction::Drop { value: ValueId(0) },
                        Instruction::Value {
                            result: ValueId(1),
                            ty: Ty::I64,
                            kind: ValueKind::Const(Const::Int(0)),
                        },
                    ],
                    terminator: Terminator::Return(Some(ValueId(1))),
                }],
            }],
            records: vec![
                (
                    FILE,
                    RecordLayout {
                        name: name(),
                        type_params: Vec::new(),
                        fields: vec![(name(), Ty::I64)],
                        affine: true,
                    },
                ),
                (
                    SESSION,
                    RecordLayout {
                        name: name(),
                        type_params: Vec::new(),
                        fields: vec![(name(), file_ty())],
                        affine: true,
                    },
                ),
                (
                    HOLDER,
                    RecordLayout {
                        name: name(),
                        type_params: Vec::new(),
                        fields: vec![(name(), file_ty())],
                        affine: false,
                    },
                ),
                (
                    CRATE,
                    RecordLayout {
                        name: name(),
                        type_params: Vec::new(),
                        fields: vec![(name(), Ty::Applied(BOXY, vec![file_ty()]))],
                        affine: true,
                    },
                ),
                (
                    VAULT,
                    RecordLayout {
                        name: name(),
                        type_params: Vec::new(),
                        fields: vec![(name(), Ty::Applied(MAYBE, vec![file_ty()]))],
                        affine: true,
                    },
                ),
                (
                    BOXY,
                    RecordLayout {
                        name: name(),
                        type_params: vec![(param(), name())],
                        fields: vec![(name(), Ty::Param(param(), name()))],
                        affine: false,
                    },
                ),
            ],
            variants: vec![(
                MAYBE,
                VariantLayout {
                    name: name(),
                    type_params: vec![(param(), name())],
                    cases: vec![
                        CaseLayout {
                            name: name(),
                            payload: vec![Ty::Param(param(), name())],
                        },
                        CaseLayout {
                            name: name(),
                            payload: Vec::new(),
                        },
                    ],
                },
            )],
            protocols: Vec::new(),
            extends: Vec::new(),
        }
    }

    /// A one-block function with a single *non-`take`* parameter: an
    /// ordinary call-scoped observation of something the caller still
    /// owns.
    fn observing(
        param_ty: Ty,
        return_type: Ty,
        body: Vec<Instruction>,
        tail: Terminator,
    ) -> Function {
        Function {
            id: STEAL,
            name: name(),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: vec![Param {
                value: ValueId(0),
                ty: param_ty,
                take: false,
            }],
            return_type,
            raises: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: body,
                terminator: tail,
            }],
        }
    }

    fn field_of(result: u32, base: u32, record: ItemId, field: usize, ty: Ty) -> Instruction {
        Instruction::Value {
            result: ValueId(result),
            ty,
            kind: ValueKind::RecordField {
                base: ValueId(base),
                record,
                field,
            },
        }
    }

    /// Everything a refused observation must leave exactly as it was.
    #[derive(Debug, PartialEq)]
    struct Snapshot {
        records: usize,
        items: Vec<ItemId>,
        fields: Vec<Vec<Value>>,
        generations: Vec<u64>,
        statuses: Vec<ResourceStatus>,
    }

    fn snapshot(interpreter: &Interpreter<'_>) -> Snapshot {
        let table = interpreter.resources.borrow();
        Snapshot {
            records: table.records.len(),
            items: table.records.iter().map(|r| r.item).collect(),
            fields: table.records.iter().map(|r| r.fields.clone()).collect(),
            generations: table.records.iter().map(|r| r.generation).collect(),
            statuses: table.records.iter().map(|r| r.status.clone()).collect(),
        }
    }

    /// Binds `owner` the way a non-`take` parameter is bound -- as an
    /// observation -- and reads field `field` of `record` out of it,
    /// exactly as `ValueKind::RecordField` does in a real frame.
    fn read_field_through_observation(
        interpreter: &Interpreter<'_>,
        owner: ResourceHandle,
        record: ItemId,
        field: usize,
    ) -> Value {
        let observed = interpreter
            .to_observer_if_resource(Value::Resource(owner))
            .expect("binding a non-take parameter is an observation");
        let mut values = HashMap::new();
        values.insert(ValueId(0), observed);
        interpreter
            .eval(
                &ValueKind::RecordField {
                    base: ValueId(0),
                    record,
                    field,
                },
                &values,
                &[],
                &HashMap::new(),
            )
            .expect("reading a field of a live observation is legal")
    }

    /// A live `Session` owning a live `File`; the returned handle owns
    /// the session.
    fn live_session(interpreter: &Interpreter<'_>) -> ResourceHandle {
        let file = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(7)]);
        interpreter
            .resources
            .borrow_mut()
            .construct(SESSION, vec![Value::Resource(file)])
    }

    /// Runs `function` against a freshly-built live `Session`, requires
    /// it to be refused with a structured error, and requires the
    /// refusal to have changed nothing observable: no generation moved,
    /// no field was replaced, nothing was destroyed or added, and the
    /// extraction appended no event of its own -- the single `call:`
    /// entry is the frame entry, which really did happen.
    ///
    /// Returns the diagnostic, after proving on a second, independent
    /// interpreter that it is exactly reproducible.
    fn refused(function: &Function, what: &str) -> String {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let session = live_session(&interpreter);
        let before = snapshot(&interpreter);

        // Mapped to `()` before it is matched on: `Outcome` deliberately
        // carries no `Debug`, and a test is not a reason to give one to
        // a runtime type.
        let outcome = interpreter
            .call_function(function, &[], vec![Value::Resource(session)], Vec::new())
            .map(|_| ());
        let message = match outcome {
            Err(InterpreterError::InvalidOperation(message)) => message,
            Err(other) => panic!("{what}: expected a structured InvalidOperation, got {other:?}"),
            Ok(()) => {
                panic!("{what}: the interpreter accepted an observation laundered into an owner")
            }
        };

        assert_eq!(
            snapshot(&interpreter),
            before,
            "{what}: a refused observation must leave every generation, field, status and record \
             exactly as it found them"
        );
        assert_eq!(
            interpreter.event_log(),
            vec![format!("call:{}", STEAL.0)],
            "{what}: a refused observation must append no event of its own"
        );
        assert!(
            interpreter.resources.borrow().observe(session).is_ok(),
            "{what}: the observed resource must still be alive and its handle still current"
        );

        let again = Interpreter::new(&module);
        let session_again = live_session(&again);
        let repeat = again
            .call_function(
                function,
                &[],
                vec![Value::Resource(session_again)],
                Vec::new(),
            )
            .map(|_| ());
        match repeat {
            Err(InterpreterError::InvalidOperation(second)) => assert_eq!(
                second, message,
                "{what}: repeating the operation must produce the identical diagnostic"
            ),
            other => panic!("{what}: repeating the operation did not fail identically: {other:?}"),
        }
        message
    }

    /// The reproduction: a non-`take` parameter is bound as an observer,
    /// `RecordField` reads the nested `File` out of it, and the result is
    /// returned as an ownership transfer. Before the repair the read
    /// cloned the stored field straight out of the resource table, so
    /// what came back was `ResourceHandle { generation: 0, role: Owner }`
    /// -- an observation laundered into ownership by one projection.
    #[test]
    fn a_field_read_through_an_observed_resource_cannot_be_returned_as_an_owner() {
        let steal = observing(
            session_ty(),
            file_ty(),
            vec![field_of(1, 0, SESSION, 0, file_ty())],
            Terminator::Return(Some(ValueId(1))),
        );
        refused(
            &steal,
            "returning a field read through an observed resource",
        );
    }

    /// The extraction itself must already be an observer, whatever is
    /// done with it afterwards. Asserted directly on the value the
    /// instruction produces, so the guarantee does not rest on `Return`
    /// happening to reject it.
    #[test]
    fn the_extracted_value_is_an_observer_before_anything_consumes_it() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let session = live_session(&interpreter);
        let observed = interpreter
            .to_observer_if_resource(Value::Resource(session))
            .expect("binding a non-take parameter is an observation");

        let mut values = HashMap::new();
        values.insert(ValueId(0), observed);
        let extracted = interpreter
            .eval(
                &ValueKind::RecordField {
                    base: ValueId(0),
                    record: SESSION,
                    field: 0,
                },
                &values,
                &[],
                &HashMap::new(),
            )
            .expect("reading a field of a live observation is legal");

        match extracted {
            Value::Resource(handle) => assert_eq!(
                handle.role,
                RuntimeOwnershipRole::Observer,
                "a field read out of an observation must itself be an observation, got {handle:?}"
            ),
            other => panic!("expected a resource handle, got {other:?}"),
        }
    }

    // -- Every depth an observation can reach through ------------------

    /// A resource whose field is a *generic* aggregate: reading it out
    /// of an observation must downgrade the handle nested inside the
    /// aggregate too, not merely hand back the aggregate untouched.
    #[test]
    fn a_generic_aggregate_read_through_an_observed_resource_is_all_observers() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let file = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let boxed = Value::Record {
            item: BOXY,
            type_args: vec![file_ty()],
            fields: vec![Value::Resource(file)],
        };
        let crate_handle = interpreter
            .resources
            .borrow_mut()
            .construct(CRATE, vec![boxed]);

        match read_field_through_observation(&interpreter, crate_handle, CRATE, 0) {
            Value::Record { fields, .. } => match fields.as_slice() {
                [Value::Resource(inner)] => assert_eq!(
                    inner.role,
                    RuntimeOwnershipRole::Observer,
                    "a resource one generic aggregate deep must still be an observation"
                ),
                other => panic!("expected one nested resource, got {other:?}"),
            },
            other => panic!("expected the generic aggregate, got {other:?}"),
        }
    }

    /// The same, one variant payload deep.
    #[test]
    fn a_variant_read_through_an_observed_resource_is_all_observers() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let file = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let held = Value::Variant {
            item: MAYBE,
            type_args: vec![file_ty()],
            case: 0,
            payload: vec![Value::Resource(file)],
        };
        let vault = interpreter
            .resources
            .borrow_mut()
            .construct(VAULT, vec![held]);

        match read_field_through_observation(&interpreter, vault, VAULT, 0) {
            Value::Variant { payload, .. } => match payload.as_slice() {
                [Value::Resource(inner)] => assert_eq!(
                    inner.role,
                    RuntimeOwnershipRole::Observer,
                    "a resource one variant payload deep must still be an observation"
                ),
                other => panic!("expected one payload resource, got {other:?}"),
            },
            other => panic!("expected the variant, got {other:?}"),
        }
    }

    /// An *inline* aggregate bound as an observation: the binding
    /// already rebuilt it as a view, so the field read must not undo
    /// that by reaching back into anything.
    #[test]
    fn a_resource_nested_in_an_observed_inline_aggregate_stays_an_observation() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let file = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let holder = interpreter
            .to_observer_if_resource(Value::Record {
                item: HOLDER,
                type_args: Vec::new(),
                fields: vec![Value::Resource(file)],
            })
            .expect("binding a non-take parameter is an observation");

        let mut values = HashMap::new();
        values.insert(ValueId(0), holder);
        let extracted = interpreter
            .eval(
                &ValueKind::RecordField {
                    base: ValueId(0),
                    record: HOLDER,
                    field: 0,
                },
                &values,
                &[],
                &HashMap::new(),
            )
            .expect("reading a field of a live observation is legal");
        match extracted {
            Value::Resource(handle) => assert_eq!(
                handle.role,
                RuntimeOwnershipRole::Observer,
                "a resource inside an observed inline aggregate must stay an observation"
            ),
            other => panic!("expected a resource handle, got {other:?}"),
        }
    }

    /// `PlaceRead { Observe }` answers the same question `RecordField`
    /// does and must answer it the same way -- through an observation,
    /// and through an owner alike. `observe_field` downgrades only when
    /// the handle it reads through is already an observer, which is
    /// right for that helper (it also walks the intermediates of a real
    /// transfer, where an owning intermediate is exactly what makes the
    /// final `take_field` legal). The opcode is where `Observe` is
    /// known to mean "repeatable read", and a repeatable read cannot
    /// hand back an owner: two repeats would be two owners of one
    /// resource.
    #[test]
    fn an_observing_place_read_never_hands_back_an_owner() {
        for through_an_observation in [true, false] {
            let module = module();
            let interpreter = Interpreter::new(&module);
            let session = live_session(&interpreter);
            let root = if through_an_observation {
                interpreter
                    .to_observer_if_resource(Value::Resource(session))
                    .expect("an observation of a live resource is legal")
            } else {
                Value::Resource(session)
            };

            let mut values = HashMap::new();
            values.insert(ValueId(0), root);
            let place = Place::root(ValueId(0)).field(SESSION, crate::place::FieldId(0));
            let seen = interpreter
                .access_place(
                    &mut values,
                    &HashMap::new(),
                    &place,
                    crate::nir::OwnershipMode::Observe,
                )
                .expect("observing a live field is legal");
            match seen {
                Value::Resource(handle) => assert_eq!(
                    handle.role,
                    RuntimeOwnershipRole::Observer,
                    "an observing place read must never hand back an owner \
                     (through an observation: {through_an_observation})"
                ),
                other => panic!("expected a resource handle, got {other:?}"),
            }
            // And it really was only a read: the field is untouched and
            // the resource is still alive and current.
            assert!(
                interpreter.resources.borrow().observe(session).is_ok(),
                "an observing read must leave its own root alive and current"
            );
        }
    }

    // -- Everything that must refuse the observed extraction -----------

    /// Destroying something reached only through an observation would
    /// destroy what the caller still owns.
    #[test]
    fn dropping_a_field_read_through_an_observation_is_refused() {
        let steal = observing(
            session_ty(),
            Ty::I64,
            vec![
                field_of(1, 0, SESSION, 0, file_ty()),
                Instruction::Drop { value: ValueId(1) },
                Instruction::Value {
                    result: ValueId(2),
                    ty: Ty::I64,
                    kind: ValueKind::Const(Const::Int(0)),
                },
            ],
            Terminator::Return(Some(ValueId(2))),
        );
        refused(&steal, "dropping a field read through an observation");
    }

    /// An explicit `Move` is the ownership-transfer opcode, and an
    /// observation has no ownership to give it.
    #[test]
    fn moving_a_field_read_through_an_observation_is_refused() {
        let steal = observing(
            session_ty(),
            file_ty(),
            vec![
                field_of(1, 0, SESSION, 0, file_ty()),
                Instruction::Value {
                    result: ValueId(2),
                    ty: file_ty(),
                    kind: ValueKind::Move { source: ValueId(1) },
                },
            ],
            Terminator::Return(Some(ValueId(2))),
        );
        refused(&steal, "moving a field read through an observation");
    }

    /// Handing it to a `take` parameter is the same transfer by another
    /// route: the callee would destroy what the caller still owns.
    #[test]
    fn handing_a_field_read_through_an_observation_to_a_take_parameter_is_refused() {
        let steal = observing(
            session_ty(),
            Ty::I64,
            vec![
                field_of(1, 0, SESSION, 0, file_ty()),
                Instruction::Value {
                    result: ValueId(2),
                    ty: Ty::I64,
                    kind: ValueKind::Call(SINK, Vec::new(), vec![ValueId(1)], Vec::new()),
                },
            ],
            Terminator::Return(Some(ValueId(2))),
        );
        refused(
            &steal,
            "handing a field read through an observation to a `take` parameter",
        );
    }

    /// Reinitializing through an observation would write into storage
    /// the caller owns.
    #[test]
    fn reinitializing_through_an_observation_is_refused() {
        let steal = observing(
            session_ty(),
            Ty::I64,
            vec![
                Instruction::Value {
                    result: ValueId(1),
                    ty: Ty::I64,
                    kind: ValueKind::Const(Const::Int(3)),
                },
                Instruction::Value {
                    result: ValueId(2),
                    ty: file_ty(),
                    kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(1)]),
                },
                Instruction::StorePlace {
                    place: Place::root(ValueId(0)).field(SESSION, crate::place::FieldId(0)),
                    value: ValueId(2),
                },
                Instruction::Value {
                    result: ValueId(3),
                    ty: Ty::I64,
                    kind: ValueKind::Const(Const::Int(0)),
                },
            ],
            Terminator::Return(Some(ValueId(3))),
        );
        // This one legitimately creates a resource of its own before it
        // is refused, so the shared `refused` snapshot (which requires
        // the table to be untouched) does not apply; what matters is
        // that the store is refused and the observed session's own
        // field is left exactly as it was.
        let module = module();
        let interpreter = Interpreter::new(&module);
        let session = live_session(&interpreter);
        let before = interpreter.resources.borrow().records[session.id.0 as usize]
            .fields
            .clone();
        let outcome = interpreter
            .call_function(&steal, &[], vec![Value::Resource(session)], Vec::new())
            .map(|_| ());
        assert!(
            matches!(outcome, Err(InterpreterError::InvalidOperation(_))),
            "reinitializing a field of an observation must be refused, got {outcome:?}"
        );
        assert_eq!(
            interpreter.resources.borrow().records[session.id.0 as usize].fields,
            before,
            "a refused reinitialization must leave the observed field exactly as it was"
        );
    }

    // -- What must keep working ---------------------------------------

    /// The ownership-transfer opcode still transfers. `Observe` and
    /// `Transfer` are different instructions for a reason, and the
    /// repair must not have collapsed them.
    #[test]
    fn the_transferring_place_read_still_hands_back_a_real_owner() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let session = live_session(&interpreter);

        let mut values = HashMap::new();
        values.insert(ValueId(0), Value::Resource(session));
        let place = Place::root(ValueId(0)).field(SESSION, crate::place::FieldId(0));
        let moved = interpreter
            .access_place(
                &mut values,
                &HashMap::new(),
                &place,
                crate::nir::OwnershipMode::Transfer,
            )
            .expect("moving a field out of an owned resource is legal");
        match moved {
            Value::Resource(handle) => assert_eq!(
                handle.role,
                RuntimeOwnershipRole::Owner,
                "an explicit transfer must still produce an owner"
            ),
            other => panic!("expected a resource handle, got {other:?}"),
        }
        assert_eq!(
            interpreter.resources.borrow().records[session.id.0 as usize].fields,
            vec![Value::Moved],
            "a transfer must tombstone the storage it took from"
        );
    }

    /// `VariantPayload` is deliberately left alone: it is the read a
    /// `DecomposeVariant` later hands ownership *of*, so downgrading it
    /// would break decomposition outright. It preserves observation
    /// already, because its own input was recursively downgraded at the
    /// boundary -- which is what this proves, rather than assuming it.
    #[test]
    fn a_payload_read_of_an_observed_variant_is_already_an_observation() {
        let module = module();
        let interpreter = Interpreter::new(&module);
        let file = interpreter
            .resources
            .borrow_mut()
            .construct(FILE, vec![Value::Int(1)]);
        let owned = Value::Variant {
            item: MAYBE,
            type_args: vec![file_ty()],
            case: 0,
            payload: vec![Value::Resource(file)],
        };

        let payload = ValueKind::VariantPayload {
            base: ValueId(0),
            variant: MAYBE,
            case: 0,
            index: 0,
        };

        // Off an owned variant it still yields an owner: that is the
        // value a `DecomposeVariant` transfers ownership to.
        let mut owned_values = HashMap::new();
        owned_values.insert(ValueId(0), owned.clone());
        match interpreter
            .eval(&payload, &owned_values, &[], &HashMap::new())
            .expect("reading a payload of an owned variant is legal")
        {
            Value::Resource(handle) => assert_eq!(
                handle.role,
                RuntimeOwnershipRole::Owner,
                "decomposition still needs a real owner to hand ownership to"
            ),
            other => panic!("expected a resource handle, got {other:?}"),
        }

        // Off an observed one it yields an observer, because the
        // observation boundary already rebuilt the whole payload.
        let mut observed_values = HashMap::new();
        observed_values.insert(
            ValueId(0),
            interpreter
                .to_observer_if_resource(owned)
                .expect("an observation of a live variant is legal"),
        );
        match interpreter
            .eval(&payload, &observed_values, &[], &HashMap::new())
            .expect("reading a payload of an observed variant is legal")
        {
            Value::Resource(handle) => assert_eq!(
                handle.role,
                RuntimeOwnershipRole::Observer,
                "a payload read through an observation must stay an observation"
            ),
            other => panic!("expected a resource handle, got {other:?}"),
        }
    }

    /// The other half of the agreement these tests exist for. The
    /// interpreter refuses this flow on its own, and so does the
    /// verifier -- neither is standing in for the other, which is
    /// exactly why the interpreter tests above drive it directly
    /// instead of going through the source pipeline.
    #[test]
    fn the_verifier_independently_rejects_the_same_flow() {
        let steal = observing(
            session_ty(),
            file_ty(),
            vec![field_of(1, 0, SESSION, 0, file_ty())],
            Terminator::Return(Some(ValueId(1))),
        );
        let mut module = module();
        module.functions = vec![steal];

        let mut map = crate::source::SourceMap::new();
        let source = map.add_file("t.npt", "");
        // Every name in this fixture is `Symbol(0)`, so the interner
        // this verifier renders messages through has to actually hold
        // one: a `Symbol` is an index into the interner that minted it.
        let mut interner = crate::symbol::Interner::new();
        assert_eq!(interner.intern("steal"), name(), "the fixture's own name");
        let diagnostics = crate::nir::verify::verify_module(
            &module,
            source,
            &interner,
            &crate::hir::ItemRegistry::default(),
        );
        let codes: Vec<&str> = diagnostics.iter().map(|d| d.code).collect();
        // `V0099`, `OBSERVER_CANNOT_TRANSFER` (`spec/0006`, `rfcs/0012`)
        // -- spelled out rather than imported, because `nir::verify`'s
        // own `codes` module is private to it and widening that purely
        // for a test would be the wrong trade. The code itself is
        // published in the spec and is what a user actually sees.
        assert!(
            codes.contains(&"V0099"),
            "the verifier must reject the same observer-to-owner flow statically, got {codes:?}"
        );
    }
}
