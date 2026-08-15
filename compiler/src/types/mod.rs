//! The Napitia type representation.

pub mod primitive;

pub use primitive::{Ty, TyVar, display_ty, is_integer, is_numeric, primitive_from_name};
