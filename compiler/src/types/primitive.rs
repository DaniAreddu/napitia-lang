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
///
/// `PartialEq`/`Eq`/`Hash` are hand-written, not derived, because
/// `Named`'s nominal-identity contract (see its own doc comment) can't
/// be expressed by a derive: two `Named` types must compare equal, and
/// hash equally, based on their `ItemId` alone, ignoring the `Symbol`
/// they also carry.
#[derive(Clone, Debug)]
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

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        use Ty::*;
        match (self, other) {
            (I8, I8)
            | (I16, I16)
            | (I32, I32)
            | (I64, I64)
            | (Isize, Isize)
            | (U8, U8)
            | (U16, U16)
            | (U32, U32)
            | (U64, U64)
            | (Usize, Usize)
            | (F32, F32)
            | (F64, F64)
            | (Bool, Bool)
            | (Char, Char)
            | (Str, Str)
            | (Unit, Unit)
            | (Never, Never)
            | (Error, Error) => true,
            (Var(a), Var(b)) => a == b,
            // Nominal identity: two `Named` types are the same type iff
            // they carry the same `ItemId`. The `Symbol` is display-only
            // (see the variant's own doc comment) and deliberately
            // excluded here.
            (Named(a, _), Named(b, _)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Ty {}

impl std::hash::Hash for Ty {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Ty::Var(v) => v.hash(state),
            // Only the `ItemId` participates in the hash, matching
            // `PartialEq`'s nominal-by-`ItemId` comparison: hashing the
            // `Symbol` too would risk two types that compare equal
            // hashing unequally, which silently breaks any
            // `HashMap`/`HashSet` keyed on `Ty`.
            Ty::Named(item, _) => item.hash(state),
            _ => {}
        }
    }
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

    #[test]
    fn named_types_compare_equal_by_item_id_alone() {
        let mut interner = Interner::new();
        let point = interner.intern("Point");
        // Same `ItemId`, same `Symbol`: the ordinary case (the same
        // declaration resolved at two different use sites).
        assert_eq!(Ty::Named(ItemId(0), point), Ty::Named(ItemId(0), point));
    }

    #[test]
    fn named_types_with_different_item_ids_are_distinct_even_with_identical_fields() {
        // Two records that happen to be declared with the exact same
        // shape must still be different types -- Napitia rejects
        // structural typing (RFC 0001), so identity has to come from
        // *which declaration* a name resolved to, not what it looks
        // like.
        let mut interner = Interner::new();
        let point = interner.intern("Point");
        let vector = interner.intern("Vector");
        assert_ne!(Ty::Named(ItemId(0), point), Ty::Named(ItemId(1), vector));
    }

    #[test]
    fn named_type_identity_ignores_the_symbol_not_just_by_construction() {
        // Directly exercises the documented contract: even if two
        // `Named` values somehow carried different symbols for the same
        // `ItemId` (which never happens through normal resolution, but
        // the type itself makes no such guarantee), they must still
        // compare -- and hash -- as the same type.
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut interner = Interner::new();
        let a_name = interner.intern("Point");
        let b_name = interner.intern("NotPoint");
        let a = Ty::Named(ItemId(0), a_name);
        let b = Ty::Named(ItemId(0), b_name);
        assert_eq!(a, b, "identity must be ItemId-only, ignoring the symbol");

        let hash_of = |ty: &Ty| {
            let mut hasher = DefaultHasher::new();
            ty.hash(&mut hasher);
            hasher.finish()
        };
        assert_eq!(
            hash_of(&a),
            hash_of(&b),
            "equal Ty values must hash equally, or HashMap/HashSet keyed on Ty breaks"
        );
    }
}
