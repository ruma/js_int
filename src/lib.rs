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

#![deny(missing_debug_implementations, missing_docs, warnings)]
#![no_std]

use core::{
    convert::{From, TryFrom},
    fmt::{self, Debug, Display, Formatter},
    num::TryFromIntError as StdTryFromIntError,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
};

#[cfg(feature = "serde")]
use core::fmt::Result as FmtResult;

#[cfg(feature = "serde")]
use serde::{de::Visitor, Deserialize, Deserializer, Serialize};

/// The largest integer value that can be represented exactly by an f64.
pub const MAX_SAFE_INT: i64 = 0x1FFFFFFFFFFFFF;
/// The smallest integer value that can be represented exactly by an f64.
pub const MIN_SAFE_INT: i64 = -MAX_SAFE_INT;

/// The same as `MAX_SAFE_INT`, but with `u64` as the type.
pub const MAX_SAFE_UINT: u64 = 0x1FFFFFFFFFFFFF;

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

    /// Returns the smallest value that can be represented by this integer type.
    pub const fn min_value() -> i64 {
        MIN_SAFE_INT
    }

    /// Returns the largest value that can be represented by this integer type.
    pub const fn max_value() -> i64 {
        MAX_SAFE_INT
    }
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

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Int {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>
    {
        struct IntVisitor;

        impl<'de> Visitor<'de> for IntVisitor {
            type Value = Int;

            fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
                formatter.write_str("a signed integer between -(2**53) + 1 and (2**53) - 1")
            }

            fn visit_i8<E>(self, value: i8) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(Int(i64::from(value)))
            }

            fn visit_i16<E>(self, value: i16) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(Int(i64::from(value)))
            }

            fn visit_i32<E>(self, value: i32) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(Int(i64::from(value)))
            }

            fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(Int::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_u8<E>(self, value: u8) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(Int::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_u16<E>(self, value: u16) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(Int::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_u32<E>(self, value: u32) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(Int::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(Int::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }
        }

        deserializer.deserialize_any(IntVisitor)
    }
}

/// An integer limited to the range of positive integers (including zero) that can be represented
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

    /// Returns the smallest value that can be represented by this integer type.
    pub const fn min_value() -> u64 {
        0
    }

    /// Returns the largest value that can be represented by this integer type.
    pub const fn max_value() -> u64 {
        MAX_SAFE_UINT
    }
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

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for UInt {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>
    {
        struct UIntVisitor;

        impl<'de> Visitor<'de> for UIntVisitor {
            type Value = UInt;

            fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
                formatter.write_str("an unsigned integer between 0 and (2**53) - 1")
            }

            fn visit_i8<E>(self, value: i8) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(UInt::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_i16<E>(self, value: i16) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(UInt::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_i32<E>(self, value: i32) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(UInt::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(UInt::try_from(value).map_err(|_| E::custom("out of bounds"))?)
            }

            fn visit_u8<E>(self, value: u8) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(UInt(u64::from(value)))
            }

            fn visit_u16<E>(self, value: u16) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(UInt(u64::from(value)))
            }

            fn visit_u32<E>(self, value: u32) -> Result<Self::Value, E>
            where
                E: serde::de::Error
            {
                Ok(UInt(u64::from(value)))
            }

            fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
            where
                E: serde::de::Error
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

/// The error type returned when a checked integral type conversion fails.
#[derive(Clone, Debug, PartialEq)]
pub struct TryFromIntError {
    _private: (),
}

impl TryFromIntError {
    fn new() -> Self {
        Self { _private: () }
    }
}

macro_rules! convert_impls {
    ($type:ident, $t8:ident, $t16:ident, $t32:ident, $t64:ident) => {
        impl From<$t8> for $type {
            fn from(val: $t8) -> Self {
                Self(val as $t64)
            }
        }

        impl From<$t16> for $type {
            fn from(val: $t16) -> Self {
                Self(val as $t64)
            }
        }

        impl From<$t32> for $type {
            fn from(val: $t32) -> Self {
                Self(val as $t64)
            }
        }

        impl TryFrom<$t64> for $type {
            type Error = TryFromIntError;

            fn try_from(val: $t64) -> Result<Self, TryFromIntError> {
                Self::new(val).ok_or_else(|| TryFromIntError::new())
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
    };
}

convert_impls!(Int, i8, i16, i32, i64);
convert_impls!(UInt, u8, u16, u32, u64);

impl From<u8> for Int {
    fn from(val: u8) -> Self {
        Self(val as i64)
    }
}

impl From<u16> for Int {
    fn from(val: u16) -> Self {
        Self(val as i64)
    }
}

impl From<u32> for Int {
    fn from(val: u32) -> Self {
        Self(val as i64)
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
    use super::{MAX_SAFE_INT, MAX_SAFE_UINT, MIN_SAFE_INT};

    #[test]
    fn limits() {
        assert_eq!(MAX_SAFE_INT, 9007199254740991);
        assert_eq!(MIN_SAFE_INT, -9007199254740991);
        assert_eq!(MAX_SAFE_UINT, 9007199254740991);
    }
}

#[cfg(all(test, feature = "serde"))]
mod serde_tests {
    use core::convert::TryFrom;

    use serde_json::{from_str, to_string};

    use super::{Int, UInt};

    #[test]
    fn serialize_int() {
        assert_eq!(to_string(&Int::try_from(100i64).unwrap()).unwrap(), "100");
        assert_eq!(to_string(&Int::try_from(100u64).unwrap()).unwrap(), "100");
        assert_eq!(to_string(&Int::try_from(0i64).unwrap()).unwrap(), "0");
        assert_eq!(to_string(&Int::try_from(0u64).unwrap()).unwrap(), "0");
        assert_eq!(to_string(&Int::try_from(-100i64).unwrap()).unwrap(), "-100");
    }

    #[test]
    fn deserialize_int() {
        assert_eq!(from_str::<Int>("100").unwrap(), Int::try_from(100i64).unwrap());
        assert_eq!(from_str::<Int>("100").unwrap(), Int::try_from(100u64).unwrap());
        assert_eq!(from_str::<Int>("0").unwrap(), Int::try_from(0i64).unwrap());
        assert_eq!(from_str::<Int>("0").unwrap(), Int::try_from(0u64).unwrap());
        assert_eq!(from_str::<Int>("-100").unwrap(), Int::try_from(-100i64).unwrap());
        assert!(from_str::<Int>("9007199254740992").is_err());
        assert!(from_str::<Int>("-9007199254740992").is_err());
    }

    #[test]
    fn serialize_uint() {
        assert_eq!(to_string(&UInt::try_from(100i64).unwrap()).unwrap(), "100");
        assert_eq!(to_string(&UInt::try_from(100u64).unwrap()).unwrap(), "100");
        assert_eq!(to_string(&UInt::try_from(0i64).unwrap()).unwrap(), "0");
        assert_eq!(to_string(&UInt::try_from(0u64).unwrap()).unwrap(), "0");
    }

    #[test]
    fn deserialize_uint() {
        assert_eq!(from_str::<UInt>("100").unwrap(), UInt::try_from(100i64).unwrap());
        assert_eq!(from_str::<UInt>("100").unwrap(), UInt::try_from(100u64).unwrap());
        assert_eq!(from_str::<UInt>("0").unwrap(), UInt::try_from(0i64).unwrap());
        assert_eq!(from_str::<UInt>("0").unwrap(), UInt::try_from(0u64).unwrap());
        assert!(from_str::<UInt>("9007199254740992").is_err());
    }
}
