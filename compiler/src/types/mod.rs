//! The Napitia type representation.

pub mod generics;
pub mod numeric;
pub mod primitive;

pub use generics::{
    CapabilityRequirement, Evidence, GenericInstanceKey, checked_substitution, substitute,
};
pub use numeric::{ArithFailure, IntDomain, IntOp, domain_of, is_executable_numeric};
pub use primitive::{Ty, TyVar, display_ty, is_integer, is_numeric, primitive_from_name};
