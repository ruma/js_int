//! Crate `js_int` provides JavaScript-interoperable integer types.
//!
//! JavaScript does not have native integers. Instead it represents all numeric values with a
//! single `Number` type which is represented as an [IEEE 754
//! floating-point](https://en.wikipedia.org/wiki/IEEE_754) value. Rust's `i64` and `u64` types
//! can contain values outside the range of what can be represented in a JavaScript `Number`.
//!
//! This crate provides the types `Int` and `UInt` which wrap `i64` and `u64`, respectively. These
//! types add bounds checking to ensure the contained value is within the range representable by a
//! JavaScript `Number`. They provide useful trait implementations to easily convert from Rust's
//! primitive integer types.
//!
//! # `#![no_std]`
//!
//! The `js_int` crate does not use Rust's standard library, and is compatible with `#![no_std]`
//! programs.
//!
//! # Features
//!
//! * `serde`: Serialization and deserialization support via [serde](https://serde.rs). Disabled by
//! default. `js_int` is still `#![no_std]`-compatible with this feature enabled.
//! * `std`: Enable `std::error::Error` implementations for `ParseIntError`, `TryFromIntError`.
//! Enabled by default.

#![deny(missing_debug_implementations, missing_docs, warnings)]
#![cfg_attr(not(feature = "std"), no_std)]

use core::{
    convert::{From, TryFrom},
    fmt::{self, Debug, Display, Formatter},
    num::{ParseIntError as StdParseIntError, TryFromIntError as StdTryFromIntError},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign},
};

#[cfg(feature = "serde")]
use serde::{de::Visitor, Deserialize, Deserializer, Serialize};

/// The largest integer value that can be represented exactly by an f64.
pub const MAX_SAFE_INT: i64 = 0x001F_FFFF_FFFF_FFFF;
/// The smallest integer value that can be represented exactly by an f64.
pub const MIN_SAFE_INT: i64 = -MAX_SAFE_INT;

/// The same as `MAX_SAFE_INT`, but with `u64` as the type.
pub const MAX_SAFE_UINT: u64 = 0x001F_FFFF_FFFF_FFFF;

/// An integer limited to the range of integers that can be represented exactly by an f64.
#[derive(Clone, Copy, Default, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize))]
pub struct Int(i64);

impl Int {
    /// Try to create an `Int` from the provided `i64`, returning `None` if it is smaller than
    /// `MIN_SAFE_INT` or larger than `MAX_SAFE_INT`.
    ///
    /// This is the same as the `TryFrom<u64>` implementation for `Int`, except that it returns
    /// an `Option` instead of a `Result`.
    pub fn new(val: i64) -> Option<Self> {
        if val >= MIN_SAFE_INT && val <= MAX_SAFE_INT {
            Some(Self(val))
        } else {
            None
        }
    }

    // TODO: make public if name is deemed sensible, rename and make public otherwise.
    fn new_saturating(val: i64) -> Self {
        if val < MIN_SAFE_INT {
            Self::min_value()
        } else if val > MAX_SAFE_INT {
            Self::max_value()
        } else {
            Self(val)
        }
    }

    /// Converts a string slice in a given base to an integer.
    ///
    /// The string is expected to be an optional `+` or `-` sign followed by digits.
    /// Leading and trailing whitespace represent an error. Digits are a subset of these characters,
    /// depending on `radix`:
    ///
    /// * `0-9`
    /// * `a-z`
    /// * `A-Z`
    ///
    /// # Panics
    ///
    /// This function panics if `radix` is not in the range from 2 to 36.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::Int;
    /// assert_eq!(Int::from_str_radix("A", 16), Ok(Int::from(10)));
    /// ```
    pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        let val = i64::from_str_radix(src, radix)?;
        if val < MIN_SAFE_INT {
            Err(ParseIntError {
                kind: ParseIntErrorKind::Underflow,
            })
        } else if val > MAX_SAFE_INT {
            Err(ParseIntError {
                kind: ParseIntErrorKind::Overflow,
            })
        } else {
            Ok(Self(val))
        }
    }

    /// Returns the smallest value that can be represented by this integer type.
    pub const fn min_value() -> Self {
        Self(MIN_SAFE_INT)
    }

    /// Returns the largest value that can be represented by this integer type.
    pub const fn max_value() -> Self {
        Self(MAX_SAFE_INT)
    }

    /// Computes the absolute value of `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::Int;
    /// assert_eq!(Int::from(10).abs(), Int::from(10));
    /// assert_eq!(Int::from(-10).abs(), Int::from(10));
    ///
    /// // Differently from i8 / i16 / i32 / i128, Int's min_value is its max_value negated
    /// assert_eq!(Int::min_value().abs(), Int::max_value());
    /// ```
    pub fn abs(self) -> Self {
        Self(self.0.abs())
    }

    /// Returns `true` if `self` is positive and `false` if the number is zero or negative.
    pub const fn is_positive(self) -> bool {
        self.0.is_positive()
    }

    /// Returns `true` if `self` is negative and `false` if the number is zero or positive.
    pub const fn is_negative(self) -> bool {
        self.0.is_negative()
    }

    /// Checked integer addition. Computes `self + rhs`, returning `None` if overflow
    /// occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::Int;
    /// assert_eq!(
    ///     (Int::max_value() - Int::from(1)).checked_add(Int::from(1)),
    ///     Some(Int::max_value())
    /// );
    ///
    /// assert_eq!(
    ///     (Int::max_value() - Int::from(1)).checked_add(Int::from(2)),
    ///     None
    /// );
    /// ```
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).and_then(Self::new)
    }

    /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow
    /// occurred.
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).and_then(Self::new)
    }

    /// Checked integer multiplication. Computes `self * rhs`, returning `None` if overflow
    /// occurred.
    pub fn checked_mul(self, rhs: Self) -> Option<Self> {
        self.0.checked_mul(rhs.0).and_then(Self::new)
    }

    /// Checked integer division. Computes `self / rhs`, returning `None` if `rhs == 0`.
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        // TODO: Range checks from Self::new shouldn't be necessary here since this type
        // has MIN_VALUE = -MAX_VALUE, different from i8, i16, i32, i64. There needs to be
        // a test before implementing this though.
        self.0.checked_div(rhs.0).and_then(Self::new)
    }

    /// Checked integer remainder. Computes `self % rhs`, returning `None` if `rhs == 0`.
    pub fn checked_rem(self, rhs: Self) -> Option<Self> {
        // Comment from checked_div also applies here
        self.0.checked_rem(rhs.0).and_then(Self::new)
    }

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None` if overflow or
    /// underflow occurred.
    pub fn checked_pow(self, exp: u32) -> Option<Self> {
        self.0.checked_pow(exp).and_then(Self::new)
    }

    /// Saturating integer addition. Computes `self + rhs`, saturating at the numeric bounds
    /// instead of overflowing.
    pub fn saturating_add(self, rhs: Self) -> Self {
        self.checked_add(rhs).unwrap_or_else(Self::max_value)
    }

    /// Saturating integer subtraction. Computes `self - rhs`, saturating at the numeric
    /// bounds instead of underflowing.
    pub fn saturating_sub(self, rhs: Self) -> Self {
        self.checked_sub(rhs).unwrap_or_else(Self::min_value)
    }

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at the numeric
    /// bounds instead of overflowing.
    pub fn saturating_mul(self, rhs: Self) -> Self {
        self.checked_mul(rhs).unwrap_or_else(Self::max_value)
    }

    /// Saturating integer exponentiation. Computes `self.pow(exp)`, saturating at the
    /// numeric bounds instead of overflowing or underflowing.
    pub fn saturating_pow(self, exp: u32) -> Self {
        Self::new_saturating(self.0.saturating_pow(exp))
    }

    // TODO: wrapping_* methods, overflowing_* methods
}

macro_rules! int_op_impl {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        impl $trait for Int {
            type Output = Self;

            fn $method(self, rhs: Self) -> Self {
                let result = <i64 as $trait>::$method(self.0, rhs.0);
                assert!(result >= MIN_SAFE_INT);
                assert!(result <= MAX_SAFE_INT);

                Self(result)
            }
        }

        impl $assign_trait for Int {
            fn $assign_method(&mut self, other: Self) {
                let result = <i64 as $trait>::$method(self.0, other.0);
                assert!(result >= MIN_SAFE_INT);
                assert!(result <= MAX_SAFE_INT);

                *self = Self(result);
            }
        }
    };
}

int_op_impl!(Add, add, AddAssign, add_assign);
int_op_impl!(Sub, sub, SubAssign, sub_assign);
int_op_impl!(Mul, mul, MulAssign, mul_assign);
int_op_impl!(Div, div, DivAssign, div_assign);
int_op_impl!(Rem, rem, RemAssign, rem_assign);

impl Neg for Int {
    type Output = Self;

    fn neg(self) -> Self {
        Self(-self.0)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Int {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct IntVisitor;

        impl<'de> Visitor<'de> for IntVisitor {
            type Value = Int;

            fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
                formatter.write_str("a signed integer between -(2**53) + 1 and (2**53) - 1")
            }

            fn visit_i8<E>(self, value: i8) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Int::from(value))
            }

            fn visit_i16<E>(self, value: i16) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Int::from(value))
            }

            fn visit_i32<E>(self, value: i32) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Int::from(value))
            }

            fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Int::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_u8<E>(self, value: u8) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Int::from(value))
            }

            fn visit_u16<E>(self, value: u16) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Int::from(value))
            }

            fn visit_u32<E>(self, value: u32) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Int::from(value))
            }

            fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Int::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }
        }

        deserializer.deserialize_any(IntVisitor)
    }
}

/// An integer limited to the range of non-negative integers that can be represented
/// exactly by an f64.
#[derive(Clone, Copy, Default, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize))]
pub struct UInt(u64);

impl UInt {
    /// Try to create a `UInt` from the provided `u64`, returning `None` if it is larger than
    /// `MAX_SAFE_UINT`.
    ///
    /// This is the same as the `TryFrom<u64>` implementation for `UInt`, except that it returns
    /// an `Option` instead of a `Result`.
    pub fn new(val: u64) -> Option<Self> {
        if val <= MAX_SAFE_UINT {
            Some(Self(val))
        } else {
            None
        }
    }

    /// Create a `UInt` from the provided `u64`, wrapping at `MAX_SAFE_UINT`.
    pub fn new_wrapping(val: u64) -> Self {
        Self(val & MAX_SAFE_UINT)
    }

    // TODO: make public if name is deemed sensible, rename and make public otherwise.
    fn new_saturating(val: u64) -> Self {
        if val <= MAX_SAFE_UINT {
            Self(val)
        } else {
            Self::max_value()
        }
    }

    /// Returns the smallest value that can be represented by this integer type.
    pub const fn min_value() -> Self {
        Self(0)
    }

    /// Returns the largest value that can be represented by this integer type.
    pub const fn max_value() -> Self {
        Self(MAX_SAFE_UINT)
    }

    /// Returns true if and only if `self == 2^k` for some `k`.
    pub fn is_power_of_two(self) -> bool {
        self.0.is_power_of_two()
    }

    /// Returns the smallest power of two greater than or equal to `n`. If the next power of two is
    /// greater than the type's maximum value, `None` is returned, otherwise the power of two is
    /// wrapped in `Some`.
    pub fn checked_next_power_of_two(self) -> Option<Self> {
        self.0.checked_next_power_of_two().and_then(Self::new)
    }

    /// Converts a string slice in a given base to an integer.
    ///
    /// The string is expected to be an optional `+` sign followed by digits. Leading and trailing
    /// whitespace represent an error. Digits are a subset of these characters, depending on
    /// `radix`:
    ///
    /// * `0-9`
    /// * `a-z`
    /// * `A-Z`
    ///
    /// # Panics
    ///
    /// This function panics if `radix` is not in the range from 2 to 36.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from_str_radix("A", 16), Ok(UInt::from(10u32)));
    /// ```
    pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        let val = u64::from_str_radix(src, radix)?;
        if val > MAX_SAFE_UINT {
            Err(ParseIntError {
                kind: ParseIntErrorKind::Overflow,
            })
        } else {
            Ok(Self(val))
        }
    }

    /// Checked integer addition. Computes `self + rhs`, returning `None` if overflow
    /// occurred.
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).and_then(Self::new)
    }

    /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow
    /// occurred.
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).and_then(Self::new)
    }

    /// Checked integer multiplication. Computes `self * rhs`, returning `None` if overflow
    /// occurred.
    pub fn checked_mul(self, rhs: Self) -> Option<Self> {
        self.0.checked_mul(rhs.0).and_then(Self::new)
    }

    /// Checked integer division. Computes `self / rhs`, returning `None` if `rhs == 0`.
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        // TODO: Range checks from Self::new shouldn't be necessary here since this type
        // has MIN_VALUE = -MAX_VALUE, different from i8, i16, i32, i64. There needs to be
        // a test before implementing this though.
        self.0.checked_div(rhs.0).and_then(Self::new)
    }

    /// Checked integer remainder. Computes `self % rhs`, returning `None` if `rhs == 0`.
    pub fn checked_rem(self, rhs: Self) -> Option<Self> {
        // Comment from checked_div also applies here
        self.0.checked_rem(rhs.0).and_then(Self::new)
    }

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None` if overflow or
    /// underflow occurred.
    pub fn checked_pow(self, exp: u32) -> Option<Self> {
        self.0.checked_pow(exp).and_then(Self::new)
    }

    /// Saturating integer addition. Computes `self + rhs`, saturating at the numeric bounds
    /// instead of overflowing.
    pub fn saturating_add(self, rhs: Self) -> Self {
        self.checked_add(rhs).unwrap_or_else(Self::max_value)
    }

    /// Saturating integer subtraction. Computes `self - rhs`, saturating at the numeric
    /// bounds instead of underflowing.
    pub fn saturating_sub(self, rhs: Self) -> Self {
        self.checked_sub(rhs).unwrap_or_else(Self::min_value)
    }

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at the numeric
    /// bounds instead of overflowing.
    pub fn saturating_mul(self, rhs: Self) -> Self {
        self.checked_mul(rhs).unwrap_or_else(Self::max_value)
    }

    /// Saturating integer exponentiation. Computes `self.pow(exp)`, saturating at the
    /// numeric bounds instead of overflowing or underflowing.
    pub fn saturating_pow(self, exp: u32) -> Self {
        Self::new_saturating(self.0.saturating_pow(exp))
    }

    // TODO: wrapping_* methods, overflowing_* methods
}

macro_rules! uint_op_impl {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        impl $trait for UInt {
            type Output = Self;

            fn $method(self, rhs: Self) -> Self {
                let result = <u64 as $trait>::$method(self.0, rhs.0);

                if cfg!(debug_assertions) {
                    assert!(result <= MAX_SAFE_UINT);
                    Self(result)
                } else {
                    Self::new_wrapping(result)
                }
            }
        }

        impl $assign_trait for UInt {
            fn $assign_method(&mut self, other: Self) {
                let result = <u64 as $trait>::$method(self.0, other.0);

                if cfg!(debug_assertions) {
                    assert!(result <= MAX_SAFE_UINT);
                    *self = Self(result);
                } else {
                    *self = Self::new_wrapping(result);
                }
            }
        }
    };
}

uint_op_impl!(Add, add, AddAssign, add_assign);
uint_op_impl!(Sub, sub, SubAssign, sub_assign);
uint_op_impl!(Mul, mul, MulAssign, mul_assign);
uint_op_impl!(Div, div, DivAssign, div_assign);
uint_op_impl!(Rem, rem, RemAssign, rem_assign);

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for UInt {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct UIntVisitor;

        impl<'de> Visitor<'de> for UIntVisitor {
            type Value = UInt;

            fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
                formatter.write_str("an unsigned integer between 0 and (2**53) - 1")
            }

            fn visit_i8<E>(self, value: i8) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(UInt::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_i16<E>(self, value: i16) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(UInt::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_i32<E>(self, value: i32) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(UInt::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(UInt::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_u8<E>(self, value: u8) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(UInt::from(value))
            }

            fn visit_u16<E>(self, value: u16) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(UInt::from(value))
            }

            fn visit_u32<E>(self, value: u32) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(UInt::from(value))
            }

            fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(UInt::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }
        }

        deserializer.deserialize_any(UIntVisitor)
    }
}

macro_rules! fmt_impls {
    ($type:ident) => {
        impl Display for $type {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl Debug for $type {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                write!(f, "{}", self.0)
            }
        }
    };
}

fmt_impls!(Int);
fmt_impls!(UInt);

/// The error type returned when when parsing an integer fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseIntError {
    kind: ParseIntErrorKind,
}

// When https://github.com/rust-lang/rust/issues/22639 is resolved, the error kind can be provided
// publicly as well. For now, distinguishing between overflow / underflow and anything else doesn't
// seem very useful.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ParseIntErrorKind {
    Overflow,
    Underflow,
    Unknown(StdParseIntError),
}

impl From<StdParseIntError> for ParseIntError {
    fn from(e: StdParseIntError) -> Self {
        ParseIntError {
            kind: ParseIntErrorKind::Unknown(e),
        }
    }
}

impl Display for ParseIntError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match &self.kind {
            ParseIntErrorKind::Overflow => f.write_str("number too large to fit in target type"),
            ParseIntErrorKind::Underflow => f.write_str("number too small to fit in target type"),
            ParseIntErrorKind::Unknown(e) => write!(f, "{}", e),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseIntError {}

/// The error type returned when a checked integral type conversion fails.
#[derive(Clone)]
pub struct TryFromIntError {
    _private: (),
}

impl TryFromIntError {
    fn new() -> Self {
        Self { _private: () }
    }
}

impl Display for TryFromIntError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("out of range integral type conversion attempted")
    }
}

impl Debug for TryFromIntError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("TryFromIntError")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TryFromIntError {}

macro_rules! convert_impls {
    ($type:ident, $t8:ident, $t16:ident, $t32:ident, $t64:ident) => {
        impl From<$t8> for $type {
            fn from(val: $t8) -> Self {
                Self($t64::from(val))
            }
        }

        impl From<$t16> for $type {
            fn from(val: $t16) -> Self {
                Self($t64::from(val))
            }
        }

        impl From<$t32> for $type {
            fn from(val: $t32) -> Self {
                Self($t64::from(val))
            }
        }

        impl TryFrom<$t64> for $type {
            type Error = TryFromIntError;

            fn try_from(val: $t64) -> Result<Self, TryFromIntError> {
                Self::new(val).ok_or_else(TryFromIntError::new)
            }
        }

        impl TryFrom<$type> for $t8 {
            type Error = StdTryFromIntError;

            fn try_from(val: $type) -> Result<Self, StdTryFromIntError> {
                Self::try_from(val.0)
            }
        }

        impl TryFrom<$type> for $t16 {
            type Error = StdTryFromIntError;

            fn try_from(val: $type) -> Result<Self, StdTryFromIntError> {
                Self::try_from(val.0)
            }
        }

        impl TryFrom<$type> for $t32 {
            type Error = StdTryFromIntError;

            fn try_from(val: $type) -> Result<Self, StdTryFromIntError> {
                Self::try_from(val.0)
            }
        }

        impl From<$type> for $t64 {
            fn from(val: $type) -> Self {
                val.0
            }
        }

        impl From<$type> for f64 {
            fn from(val: $type) -> Self {
                val.0 as f64
            }
        }
    };
}

convert_impls!(Int, i8, i16, i32, i64);
convert_impls!(UInt, u8, u16, u32, u64);

impl From<u8> for Int {
    fn from(val: u8) -> Self {
        Self(i64::from(val))
    }
}

impl From<u16> for Int {
    fn from(val: u16) -> Self {
        Self(i64::from(val))
    }
}

impl From<u32> for Int {
    fn from(val: u32) -> Self {
        Self(i64::from(val))
    }
}

impl TryFrom<u64> for Int {
    type Error = TryFromIntError;

    fn try_from(val: u64) -> Result<Self, TryFromIntError> {
        if val <= MAX_SAFE_UINT {
            Ok(Self(val as i64))
        } else {
            Err(TryFromIntError::new())
        }
    }
}

impl TryFrom<i8> for UInt {
    type Error = TryFromIntError;

    fn try_from(val: i8) -> Result<Self, TryFromIntError> {
        if val >= 0 {
            Ok(Self(val as u64))
        } else {
            Err(TryFromIntError::new())
        }
    }
}

impl TryFrom<i16> for UInt {
    type Error = TryFromIntError;

    fn try_from(val: i16) -> Result<Self, TryFromIntError> {
        if val >= 0 {
            Ok(Self(val as u64))
        } else {
            Err(TryFromIntError::new())
        }
    }
}

impl TryFrom<i32> for UInt {
    type Error = TryFromIntError;

    fn try_from(val: i32) -> Result<Self, TryFromIntError> {
        if val >= 0 {
            Ok(Self(val as u64))
        } else {
            Err(TryFromIntError::new())
        }
    }
}

impl TryFrom<i64> for UInt {
    type Error = TryFromIntError;

    fn try_from(val: i64) -> Result<Self, TryFromIntError> {
        if val >= 0 && val <= MAX_SAFE_INT {
            Ok(Self(val as u64))
        } else {
            Err(TryFromIntError::new())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Int, UInt, MAX_SAFE_INT, MAX_SAFE_UINT, MIN_SAFE_INT};

    #[test]
    fn limits() {
        assert_eq!(MAX_SAFE_INT, 9_007_199_254_740_991);
        assert_eq!(MIN_SAFE_INT, -9_007_199_254_740_991);
        assert_eq!(MAX_SAFE_UINT, 9_007_199_254_740_991);

        assert_eq!(f64::from(Int::min_value()) as i64, MIN_SAFE_INT);
        assert_eq!(f64::from(Int::max_value()) as i64, MAX_SAFE_INT);
        assert_eq!(f64::from(UInt::max_value()) as u64, MAX_SAFE_UINT);
    }

    #[test]
    #[should_panic]
    fn int_underflow_panic() {
        let _ = Int::min_value() - Int::from(1);
    }

    #[test]
    #[should_panic]
    fn int_overflow_panic() {
        let _ = Int::max_value() + Int::from(1);
    }

    #[test]
    fn uint_wrapping_new() {
        assert_eq!(UInt::new_wrapping(MAX_SAFE_UINT + 1), UInt::from(0u32));
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore)]
    fn uint_underflow_wrap() {
        assert_eq!(UInt::from(0u32) - UInt::from(1u32), UInt::max_value());
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore)]
    fn uint_overflow_wrap() {
        assert_eq!(UInt::max_value() + UInt::from(1u32), UInt::from(0u32));
        assert_eq!(UInt::max_value() + UInt::from(5u32), UInt::from(4u32));
    }

    #[test]
    #[should_panic]
    #[cfg_attr(not(debug_assertions), ignore)]
    fn uint_underflow_panic() {
        let _ = UInt::from(0u32) - UInt::from(1u32);
    }

    #[test]
    #[should_panic]
    #[cfg_attr(not(debug_assertions), ignore)]
    fn uint_overflow_panic() {
        let _ = UInt::max_value() + UInt::from(1u32);
    }
}
