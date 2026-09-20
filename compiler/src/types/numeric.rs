//! The one authoritative description of Napitia's numeric semantics.
//!
//! Every range rule and every overflow rule in the compiler is stated
//! here exactly once, and read from here by the checker, by NIR
//! lowering, by the NIR verifier and by the interpreter. Nothing
//! re-derives "what fits in an `i64`" locally: `rfcs/0015` is the
//! specification, and this module is its single implementation.
//!
//! # The layers this module keeps apart
//!
//! A number passes through five different representations on its way
//! from source text to a machine register, and conflating any two of
//! them is exactly how Alpha 0.2.0 ended up executing a 128-bit
//! integer under the name `i64`:
//!
//! 1. a **source literal magnitude** -- unsigned, because `-5` is a
//!    negation applied to `5` and the lexer has no sign to record;
//! 2. a **resolved numeric type** -- a [`Ty`], decided by unification;
//! 3. a **validated typed constant** -- the signed value a magnitude
//!    denotes *in a particular type*, which is what [`IntDomain::literal`]
//!    produces and what NIR carries;
//! 4. a **runtime integer value** -- an `i64`, the only integer domain
//!    this milestone executes, which is what the functions at the
//!    bottom of this module operate on;
//! 5. a **native machine representation** -- Cranelift's `I64`, which
//!    is the backend's own business.
//!
//! The native backend cannot call the Rust functions here -- it emits
//! machine code rather than running it -- so it re-expresses the same
//! rules as overflow tests in Cranelift IR. That is the one deliberate
//! restatement in the compiler, and the differential tests between
//! `napitia run` and a built executable exist to keep the two honest.

use super::Ty;

/// A fixed-width integer domain: the exact set of mathematical integers
/// one Napitia integer type can hold.
///
/// Held as a width and a signedness rather than as a precomputed
/// min/max pair so that a domain cannot be constructed inconsistently
/// with itself.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct IntDomain {
    name: &'static str,
    signed: bool,
    bits: u32,
}

impl IntDomain {
    /// This domain's Napitia spelling.
    pub const fn name(self) -> &'static str {
        self.name
    }

    /// The smallest value this domain holds.
    ///
    /// Returned as `i128` because that is the narrowest Rust integer
    /// that holds every Napitia integer domain's bounds at once -- it
    /// is a *bound*, never a value the language executes.
    pub const fn min(self) -> i128 {
        if self.signed {
            -(1i128 << (self.bits - 1))
        } else {
            0
        }
    }

    /// The largest value this domain holds.
    pub const fn max(self) -> i128 {
        if self.signed {
            (1i128 << (self.bits - 1)) - 1
        } else {
            (1i128 << self.bits) - 1
        }
    }

    /// Whether `value` is in this domain.
    pub const fn contains(self, value: i128) -> bool {
        self.min() <= value && value <= self.max()
    }

    /// The typed constant a source literal denotes in this domain, or
    /// `None` when the literal does not fit.
    ///
    /// `magnitude` is the unsigned number the lexer read; `negated` says
    /// whether a unary `-` is applied directly to that literal. The two
    /// are kept separate all the way to here precisely because of the
    /// minimum: `9223372036854775808` is not an `i64`, and
    /// `-9223372036854775808` is, so the answer genuinely depends on the
    /// sign the literal was written with. Nothing here inspects source
    /// text, and nothing represents the magnitude as a positive value of
    /// the target type first and negates it afterwards -- that is the
    /// step that cannot work at the boundary.
    pub const fn literal(self, magnitude: u128, negated: bool) -> Option<i128> {
        let limit = if negated {
            self.min().unsigned_abs()
        } else {
            self.max() as u128
        };
        if magnitude > limit {
            return None;
        }
        // `magnitude <= limit` and every domain's bounds fit in `i128`,
        // so this conversion cannot lose anything.
        let value = magnitude as i128;
        Some(if negated { -value } else { value })
    }
}

/// The `i64` domain: `rfcs/0015`'s subject, and the only integer domain
/// this milestone executes.
pub const I64: IntDomain = IntDomain {
    name: "i64",
    signed: true,
    bits: 64,
};

/// `ty`'s integer domain, or `None` when `ty` is not an integer type.
///
/// Exhaustive by construction: every [`Ty`] variant is named, so a type
/// added later cannot silently acquire a domain through a wildcard.
///
/// `isize`/`usize` are described as 64-bit. The one target this compiler
/// has is 64-bit, so that is not an assumption; it is the width. They
/// are refused before execution regardless (see
/// [`is_executable_numeric`]), so no program depends on it yet.
pub fn domain_of(ty: &Ty) -> Option<IntDomain> {
    let (name, signed, bits) = match ty {
        Ty::I8 => ("i8", true, 8),
        Ty::I16 => ("i16", true, 16),
        Ty::I32 => ("i32", true, 32),
        Ty::I64 => ("i64", true, 64),
        Ty::Isize => ("isize", true, 64),
        Ty::U8 => ("u8", false, 8),
        Ty::U16 => ("u16", false, 16),
        Ty::U32 => ("u32", false, 32),
        Ty::U64 => ("u64", false, 64),
        Ty::Usize => ("usize", false, 64),
        Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Char
        | Ty::Str
        | Ty::Unit
        | Ty::Never
        | Ty::Var(_)
        | Ty::Named(_, _)
        | Ty::Param(_, _)
        | Ty::Applied(_, _)
        | Ty::Error => return None,
    };
    Some(IntDomain { name, signed, bits })
}

/// Whether `ty` is a numeric type this milestone actually executes.
///
/// `i64` and `f64` are implemented in the interpreter over their whole
/// domains (`rfcs/0015`). Every other numeric name in `spec/0003`
/// parses and resolves, and is then refused before it can reach a
/// fabricated runtime value: no narrowing, no width-aware arithmetic
/// and no single-precision rounding exists to give it honest behavior.
///
/// A non-numeric type answers `true`: this predicate exists to separate
/// *implemented* numeric types from *unimplemented* ones, and has
/// nothing to say about `bool`, `str` or a record.
pub fn is_executable_numeric(ty: &Ty) -> bool {
    !matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::Isize
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::Usize
            | Ty::F32
    )
}

/// One checked integer operation, spelled the way NIR spells it.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntOp {
    Add,
    Sub,
    Mul,
    Neg,
    Div,
    Rem,
    Shl,
    Shr,
}

impl IntOp {
    /// This operation's NIR mnemonic, which is also how a runtime
    /// failure names it. One spelling, so an interpreter diagnostic and
    /// a native one cannot drift apart.
    pub const fn as_str(self) -> &'static str {
        match self {
            IntOp::Add => "add",
            IntOp::Sub => "sub",
            IntOp::Mul => "mul",
            IntOp::Neg => "neg",
            IntOp::Div => "div",
            IntOp::Rem => "rem",
            IntOp::Shl => "shl",
            IntOp::Shr => "shr",
        }
    }

    /// Every operation, in a fixed order, for tests and for emitting one
    /// native failure path per operation.
    pub const ALL: [IntOp; 8] = [
        IntOp::Add,
        IntOp::Sub,
        IntOp::Mul,
        IntOp::Neg,
        IntOp::Div,
        IntOp::Rem,
        IntOp::Shl,
        IntOp::Shr,
    ];
}

/// Why a checked integer operation produced no value.
///
/// Every variant is a *Napitia* outcome with its own stable meaning,
/// never a host condition leaking through: there is no "wrapped",
/// no "saturated" and no "trapped".
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ArithFailure {
    /// The exact mathematical result is outside [`I64`].
    Overflow(IntOp),
    /// `div` or `rem` with a zero divisor.
    DivisionByZero(IntOp),
    /// A shift count outside `0..64`, carried so a diagnostic can name
    /// the count that was actually asked for.
    ShiftAmount(i64),
}

/// The number of bits a shift count may name, exclusive.
const SHIFT_BITS: i64 = 64;

pub fn add(a: i64, b: i64) -> Result<i64, ArithFailure> {
    a.checked_add(b).ok_or(ArithFailure::Overflow(IntOp::Add))
}

pub fn sub(a: i64, b: i64) -> Result<i64, ArithFailure> {
    a.checked_sub(b).ok_or(ArithFailure::Overflow(IntOp::Sub))
}

pub fn mul(a: i64, b: i64) -> Result<i64, ArithFailure> {
    a.checked_mul(b).ok_or(ArithFailure::Overflow(IntOp::Mul))
}

pub fn neg(a: i64) -> Result<i64, ArithFailure> {
    a.checked_neg().ok_or(ArithFailure::Overflow(IntOp::Neg))
}

/// Truncating division.
///
/// Two distinct failures, never conflated: a zero divisor has no
/// quotient at all, and `i64::MIN / -1` has one -- `9223372036854775808`
/// -- that is simply not an `i64`.
pub fn div(a: i64, b: i64) -> Result<i64, ArithFailure> {
    if b == 0 {
        return Err(ArithFailure::DivisionByZero(IntOp::Div));
    }
    a.checked_div(b).ok_or(ArithFailure::Overflow(IntOp::Div))
}

/// Remainder, taking the sign of the dividend.
///
/// `i64::MIN % -1` is `0`, not an overflow. The exact remainder is `0`,
/// which is an `i64`, so nothing leaves the domain -- unlike the
/// quotient of the same pair. Rust's own `checked_rem` answers `None`
/// there because it mirrors the hardware instruction that computes both
/// at once; Napitia answers the arithmetic question instead.
pub fn rem(a: i64, b: i64) -> Result<i64, ArithFailure> {
    if b == 0 {
        return Err(ArithFailure::DivisionByZero(IntOp::Rem));
    }
    Ok(a.wrapping_rem(b))
}

/// Left shift. Bits shifted off the top are discarded -- that is what a
/// shift is, and it is not an overflow.
pub fn shl(a: i64, count: i64) -> Result<i64, ArithFailure> {
    check_shift(count)?;
    Ok(a.wrapping_shl(count as u32))
}

/// Arithmetic right shift: the sign bit is replicated, so a negative
/// value stays negative.
pub fn shr(a: i64, count: i64) -> Result<i64, ArithFailure> {
    check_shift(count)?;
    Ok(a.wrapping_shr(count as u32))
}

/// A shift count is itself an `i64`, because Napitia has no executable
/// unsigned integer type -- so a negative count is expressible, and it
/// is a failure rather than something to mask away.
fn check_shift(count: i64) -> Result<(), ArithFailure> {
    if (0..SHIFT_BITS).contains(&count) {
        Ok(())
    } else {
        Err(ArithFailure::ShiftAmount(count))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_i64_domain_is_exactly_two_s_complement_64_bit() {
        assert_eq!(I64.min(), -9223372036854775808);
        assert_eq!(I64.max(), 9223372036854775807);
        assert_eq!(I64.min(), i64::MIN as i128);
        assert_eq!(I64.max(), i64::MAX as i128);
    }

    #[test]
    fn every_integer_type_reports_the_domain_its_name_promises() {
        for (ty, min, max) in [
            (Ty::I8, i8::MIN as i128, i8::MAX as i128),
            (Ty::I16, i16::MIN as i128, i16::MAX as i128),
            (Ty::I32, i32::MIN as i128, i32::MAX as i128),
            (Ty::I64, i64::MIN as i128, i64::MAX as i128),
            (Ty::Isize, i64::MIN as i128, i64::MAX as i128),
            (Ty::U8, 0, u8::MAX as i128),
            (Ty::U16, 0, u16::MAX as i128),
            (Ty::U32, 0, u32::MAX as i128),
            (Ty::U64, 0, u64::MAX as i128),
            (Ty::Usize, 0, u64::MAX as i128),
        ] {
            let domain = domain_of(&ty).expect("an integer type has a domain");
            assert_eq!(domain.min(), min, "{} minimum", domain.name());
            assert_eq!(domain.max(), max, "{} maximum", domain.name());
        }
    }

    #[test]
    fn a_non_integer_type_has_no_integer_domain() {
        for ty in [
            Ty::F32,
            Ty::F64,
            Ty::Bool,
            Ty::Char,
            Ty::Str,
            Ty::Unit,
            Ty::Never,
            Ty::Error,
        ] {
            assert_eq!(domain_of(&ty), None);
        }
    }

    #[test]
    fn a_domain_contains_its_own_bounds_and_nothing_past_them() {
        assert!(I64.contains(I64.min()));
        assert!(I64.contains(I64.max()));
        assert!(I64.contains(0));
        assert!(!I64.contains(I64.min() - 1));
        assert!(!I64.contains(I64.max() + 1));
    }

    /// The whole reason magnitude and sign travel separately.
    #[test]
    fn the_minimum_is_accepted_only_when_the_literal_is_negated() {
        let magnitude = 9223372036854775808u128;
        assert_eq!(I64.literal(magnitude, true), Some(i64::MIN as i128));
        assert_eq!(
            I64.literal(magnitude, false),
            None,
            "the magnitude alone is one past the maximum"
        );
    }

    #[test]
    fn both_boundaries_are_accepted_and_neither_neighbour_is() {
        assert_eq!(
            I64.literal(9223372036854775807, false),
            Some(i64::MAX as i128)
        );
        assert_eq!(I64.literal(9223372036854775808, false), None);
        assert_eq!(
            I64.literal(9223372036854775808, true),
            Some(i64::MIN as i128)
        );
        assert_eq!(I64.literal(9223372036854775809, true), None);
    }

    #[test]
    fn a_magnitude_far_past_the_domain_is_refused_rather_than_wrapped() {
        assert_eq!(I64.literal(u128::MAX, false), None);
        assert_eq!(I64.literal(u128::MAX, true), None);
    }

    #[test]
    fn an_unsigned_domain_accepts_no_negative_literal_but_still_accepts_zero() {
        let u8_domain = domain_of(&Ty::U8).expect("u8 has a domain");
        assert_eq!(u8_domain.literal(0, true), Some(0));
        assert_eq!(u8_domain.literal(1, true), None);
        assert_eq!(u8_domain.literal(255, false), Some(255));
        assert_eq!(u8_domain.literal(256, false), None);
    }

    #[test]
    fn exactly_i64_and_f64_are_executable_numerics() {
        for ty in [Ty::I64, Ty::F64] {
            assert!(is_executable_numeric(&ty), "{ty:?} is implemented");
        }
        for ty in [
            Ty::I8,
            Ty::I16,
            Ty::I32,
            Ty::Isize,
            Ty::U8,
            Ty::U16,
            Ty::U32,
            Ty::U64,
            Ty::Usize,
            Ty::F32,
        ] {
            assert!(!is_executable_numeric(&ty), "{ty:?} is not implemented");
        }
    }

    #[test]
    fn a_non_numeric_type_is_not_what_this_predicate_is_about() {
        for ty in [Ty::Bool, Ty::Char, Ty::Str, Ty::Unit, Ty::Never, Ty::Error] {
            assert!(is_executable_numeric(&ty));
        }
    }

    #[test]
    fn arithmetic_that_stays_in_the_domain_produces_the_exact_result() {
        assert_eq!(add(i64::MAX - 1, 1), Ok(i64::MAX));
        assert_eq!(sub(i64::MIN + 1, 1), Ok(i64::MIN));
        assert_eq!(mul(i64::MAX, 1), Ok(i64::MAX));
        assert_eq!(mul(-1, i64::MAX), Ok(-i64::MAX));
        assert_eq!(neg(i64::MAX), Ok(-i64::MAX));
        assert_eq!(neg(i64::MIN + 1), Ok(i64::MAX));
        assert_eq!(add(0, 0), Ok(0));
    }

    #[test]
    fn arithmetic_that_leaves_the_domain_overflows_instead_of_wrapping() {
        assert_eq!(add(i64::MAX, 1), Err(ArithFailure::Overflow(IntOp::Add)));
        assert_eq!(add(i64::MIN, -1), Err(ArithFailure::Overflow(IntOp::Add)));
        assert_eq!(sub(i64::MIN, 1), Err(ArithFailure::Overflow(IntOp::Sub)));
        assert_eq!(sub(i64::MAX, -1), Err(ArithFailure::Overflow(IntOp::Sub)));
        assert_eq!(mul(i64::MAX, 2), Err(ArithFailure::Overflow(IntOp::Mul)));
        assert_eq!(mul(i64::MIN, -1), Err(ArithFailure::Overflow(IntOp::Mul)));
        assert_eq!(neg(i64::MIN), Err(ArithFailure::Overflow(IntOp::Neg)));
    }

    #[test]
    fn division_separates_a_missing_quotient_from_one_outside_the_domain() {
        assert_eq!(div(1, 0), Err(ArithFailure::DivisionByZero(IntOp::Div)));
        assert_eq!(div(0, 0), Err(ArithFailure::DivisionByZero(IntOp::Div)));
        assert_eq!(
            div(i64::MIN, -1),
            Err(ArithFailure::Overflow(IntOp::Div)),
            "the exact quotient is one past the maximum"
        );
        assert_eq!(div(7, 2), Ok(3));
        assert_eq!(div(-7, 2), Ok(-3), "division truncates toward zero");
    }

    #[test]
    fn remainder_takes_the_dividends_sign_and_has_no_overflow_at_the_minimum() {
        assert_eq!(rem(1, 0), Err(ArithFailure::DivisionByZero(IntOp::Rem)));
        assert_eq!(
            rem(i64::MIN, -1),
            Ok(0),
            "the exact remainder is zero, which is an i64"
        );
        assert_eq!(rem(7, 2), Ok(1));
        assert_eq!(rem(-7, 2), Ok(-1));
        assert_eq!(rem(7, -2), Ok(1));
    }

    #[test]
    fn shifts_refuse_a_count_outside_the_width_instead_of_masking_it() {
        assert_eq!(shl(1, 64), Err(ArithFailure::ShiftAmount(64)));
        assert_eq!(shr(1, 64), Err(ArithFailure::ShiftAmount(64)));
        assert_eq!(shl(1, -1), Err(ArithFailure::ShiftAmount(-1)));
        assert_eq!(shr(1, -1), Err(ArithFailure::ShiftAmount(-1)));
        assert_eq!(
            shl(1, i64::MIN),
            Err(ArithFailure::ShiftAmount(i64::MIN)),
            "a count that is not even a plausible u32 is still just a bad count"
        );
    }

    #[test]
    fn shifts_inside_the_width_discard_bits_and_replicate_the_sign() {
        assert_eq!(shl(1, 0), Ok(1));
        assert_eq!(shl(1, 63), Ok(i64::MIN), "the top bit is the sign bit");
        assert_eq!(
            shr(i64::MIN, 63),
            Ok(-1),
            "an arithmetic shift, not logical"
        );
        assert_eq!(shr(-8, 1), Ok(-4));
        assert_eq!(shr(-1, 63), Ok(-1));
    }

    #[test]
    fn every_operation_has_a_distinct_stable_mnemonic() {
        let names: Vec<&str> = IntOp::ALL.iter().map(|op| op.as_str()).collect();
        let mut sorted = names.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), names.len(), "no two operations share a name");
        assert_eq!(
            names,
            vec!["add", "sub", "mul", "neg", "div", "rem", "shl", "shr"]
        );
    }
}
