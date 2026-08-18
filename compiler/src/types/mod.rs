//! The Napitia type representation.

pub mod generics;
pub mod primitive;

pub use generics::{CapabilityRequirement, Evidence, GenericInstanceKey, substitute};
pub use primitive::{Ty, TyVar, display_ty, is_integer, is_numeric, primitive_from_name};
