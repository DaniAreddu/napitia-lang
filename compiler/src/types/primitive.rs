//! Primitive types and the checker's internal type representation.

use crate::hir::ItemId;
use crate::symbol::{Interner, Symbol};

/// A type variable, solved during unification (`typeck::unify`). Only
/// integer and float literals allocate one, since those are the only
/// expressions in this milestone whose type is not immediately known
/// (`spec/0003`'s literal inference).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TyVar(pub(crate) u32);

/// The checker's internal type representation. Distinct from
/// [`crate::syntax::ast::Type`] (a named-identifier surface type): `Ty`
/// is what unification actually operates over.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
    F32,
    F64,
    Bool,
    Char,
    Str,
    Unit,
    /// The type of an expression that provably never produces a value
    /// (`return`/`break`/`continue`). Unifies with anything.
    Never,
    Var(TyVar),
    /// A resolved reference to a declared `record` or `variant` name.
    /// Two `Named` types are the same type iff they carry the same
    /// `ItemId` — nominal comparison, matching RFC 0001's rejection of
    /// structural typing. The `Symbol` is carried only so diagnostics
    /// can print the name without a separate lookup table; it is not
    /// itself part of the type's identity for comparison purposes,
    /// since it is always the declaration's own name. Field access and
    /// construction are not executable yet (`spec/0003`); a `Named`
    /// type may be name-resolved and compared, but NIR lowering
    /// rejects it explicitly rather than guessing a representation.
    Named(ItemId, Symbol),
    /// An unknown named type, or the result of an earlier error, is not
    /// allowed to *silently* become `Error`: every `Error` a program can
    /// observe must trace back to a diagnostic already recorded at the
    /// point it was introduced (an unresolved name, a malformed
    /// expression, an unknown type name). `Error` itself unifies with
    /// anything so that already-reported problem doesn't cascade into
    /// unrelated diagnostics.
    Error,
}

pub fn primitive_from_name(name: &str) -> Option<Ty> {
    Some(match name {
        "i8" => Ty::I8,
        "i16" => Ty::I16,
        "i32" => Ty::I32,
        "i64" => Ty::I64,
        "isize" => Ty::Isize,
        "u8" => Ty::U8,
        "u16" => Ty::U16,
        "u32" => Ty::U32,
        "u64" => Ty::U64,
        "usize" => Ty::Usize,
        "f32" => Ty::F32,
        "f64" => Ty::F64,
        "bool" => Ty::Bool,
        "char" => Ty::Char,
        "str" => Ty::Str,
        "unit" => Ty::Unit,
        "never" => Ty::Never,
        _ => return None,
    })
}

pub fn is_integer(ty: &Ty) -> bool {
    matches!(
        ty,
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
}

pub fn is_numeric(ty: &Ty) -> bool {
    is_integer(ty) || matches!(ty, Ty::F32 | Ty::F64)
}

/// The name this type is written as in Napitia source, for diagnostics.
pub fn display_ty(ty: &Ty, interner: &Interner) -> String {
    match ty {
        Ty::I8 => "i8".to_string(),
        Ty::I16 => "i16".to_string(),
        Ty::I32 => "i32".to_string(),
        Ty::I64 => "i64".to_string(),
        Ty::Isize => "isize".to_string(),
        Ty::U8 => "u8".to_string(),
        Ty::U16 => "u16".to_string(),
        Ty::U32 => "u32".to_string(),
        Ty::U64 => "u64".to_string(),
        Ty::Usize => "usize".to_string(),
        Ty::F32 => "f32".to_string(),
        Ty::F64 => "f64".to_string(),
        Ty::Bool => "bool".to_string(),
        Ty::Char => "char".to_string(),
        Ty::Str => "str".to_string(),
        Ty::Unit => "unit".to_string(),
        Ty::Never => "never".to_string(),
        Ty::Var(_) => "_".to_string(),
        Ty::Named(_, name) => interner.resolve(*name).to_string(),
        Ty::Error => "<unknown>".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recognizes_every_primitive_name() {
        for name in [
            "i8", "i16", "i32", "i64", "isize", "u8", "u16", "u32", "u64", "usize", "f32", "f64",
            "bool", "char", "str", "unit", "never",
        ] {
            assert!(
                primitive_from_name(name).is_some(),
                "{name} should be primitive"
            );
        }
    }

    #[test]
    fn unknown_name_is_not_primitive() {
        assert_eq!(primitive_from_name("Point"), None);
    }

    #[test]
    fn integer_types_are_numeric_but_bool_is_not() {
        assert!(is_integer(&Ty::I64));
        assert!(is_numeric(&Ty::I64));
        assert!(is_numeric(&Ty::F64));
        assert!(!is_integer(&Ty::F64));
        assert!(!is_numeric(&Ty::Bool));
    }

    #[test]
    fn display_matches_source_spelling() {
        let interner = Interner::new();
        assert_eq!(display_ty(&Ty::I64, &interner), "i64");
        assert_eq!(display_ty(&Ty::Bool, &interner), "bool");
    }

    #[test]
    fn display_of_a_named_type_resolves_its_symbol() {
        let mut interner = Interner::new();
        let name = interner.intern("Point");
        assert_eq!(display_ty(&Ty::Named(ItemId(0), name), &interner), "Point");
    }
}
