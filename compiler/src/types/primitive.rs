//! Primitive types and the checker's internal type representation.

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
    /// A type that is not checked further in this milestone: an unknown
    /// named type (most likely a `record`/`variant`/`protocol` name,
    /// none of which are deeply type-checked yet — `spec/0003`) or the
    /// result of an earlier error. Unifies with anything so one
    /// unchecked or malformed expression does not cascade into
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
pub fn display_ty(ty: &Ty) -> &'static str {
    match ty {
        Ty::I8 => "i8",
        Ty::I16 => "i16",
        Ty::I32 => "i32",
        Ty::I64 => "i64",
        Ty::Isize => "isize",
        Ty::U8 => "u8",
        Ty::U16 => "u16",
        Ty::U32 => "u32",
        Ty::U64 => "u64",
        Ty::Usize => "usize",
        Ty::F32 => "f32",
        Ty::F64 => "f64",
        Ty::Bool => "bool",
        Ty::Char => "char",
        Ty::Str => "str",
        Ty::Unit => "unit",
        Ty::Never => "never",
        Ty::Var(_) => "_",
        Ty::Error => "<unknown>",
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
        assert_eq!(display_ty(&Ty::I64), "i64");
        assert_eq!(display_ty(&Ty::Bool), "bool");
    }
}
