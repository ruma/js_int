use core::{
    convert::TryFrom,
    iter,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign},
    str::FromStr,
};

#[cfg(feature = "serde")]
use serde::{
    de::{Error as _, Unexpected},
    Deserialize, Deserializer, Serialize,
};

use crate::{
    error::{ParseIntError, ParseIntErrorKind, TryFromIntError},
    MAX_SAFE_INT,
};

/// The same as `MAX_SAFE_INT`, but with `u64` as the type.
pub const MAX_SAFE_UINT: u64 = 0x001F_FFFF_FFFF_FFFF;

/// An integer limited to the range of non-negative integers that can be represented exactly by an
/// f64.
#[derive(Clone, Copy, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize))]
pub struct UInt(u64);

impl UInt {
    /// The smallest value that can be represented by this integer type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::MIN, UInt::from(0u32));
    /// ```
    pub const MIN: Self = Self(0);

    /// The largest value that can be represented by this integer type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use {core::convert::TryFrom, js_int::UInt};
    /// assert_eq!(UInt::MAX, UInt::try_from(9_007_199_254_740_991u64).unwrap());
    /// ```
    pub const MAX: Self = Self(MAX_SAFE_UINT);

    /// Try to create a `UInt` from the provided `u64`, returning `None` if it is larger than
    /// `MAX_SAFE_UINT`.
    ///
    /// This is the same as the `TryFrom<u64>` implementation for `UInt`, except that it returns
    /// an `Option` instead of a `Result`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::new(js_int::MAX_SAFE_UINT), Some(UInt::MAX));
    /// assert_eq!(UInt::new(js_int::MAX_SAFE_UINT + 1), None);
    /// ```
    #[must_use]
    pub fn new(val: u64) -> Option<Self> {
        if val <= MAX_SAFE_UINT {
            Some(Self(val))
        } else {
            None
        }
    }

    /// Create a `UInt` from the provided `u64`, wrapping at `MAX_SAFE_UINT`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::new_wrapping(js_int::MAX_SAFE_UINT), UInt::MAX);
    /// assert_eq!(UInt::new_wrapping(js_int::MAX_SAFE_UINT + 1), UInt::from(0u32));
    /// ```
    #[must_use]
    pub fn new_wrapping(val: u64) -> Self {
        Self(val & MAX_SAFE_UINT)
    }

    // TODO: make public if name is deemed sensible, rename and make public otherwise.
    #[must_use]
    fn new_saturating(val: u64) -> Self {
        if val <= MAX_SAFE_UINT {
            Self(val)
        } else {
            Self::MAX
        }
    }

    /// The constructor used for arithmetic operations
    #[must_use]
    fn new_(val: u64) -> Self {
        if cfg!(debug_assertions) {
            assert!(val <= MAX_SAFE_UINT);
            Self(val)
        } else {
            Self::new_wrapping(val)
        }
    }

    /// Helper function for mutable arithmetic operations (`+=`, `-=`, …)
    fn assign_(&mut self, val: u64) {
        if cfg!(debug_assertions) {
            assert!(val <= MAX_SAFE_UINT);
            *self = Self(val);
        } else {
            *self = Self::new_wrapping(val);
        }
    }

    /// Returns the smallest value that can be represented by this integer type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::min_value(), UInt::from(0u32));
    /// ```
    #[must_use]
    #[deprecated = "Use `UInt::MIN` instead."]
    pub const fn min_value() -> Self {
        Self(0)
    }

    /// Returns the largest value that can be represented by this integer type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use {core::convert::TryFrom, js_int::UInt};
    /// assert_eq!(UInt::max_value(), UInt::try_from(9_007_199_254_740_991u64).unwrap());
    /// ```
    #[must_use]
    #[deprecated = "Use `UInt::MAX` instead."]
    pub const fn max_value() -> Self {
        Self(MAX_SAFE_UINT)
    }

    /// Returns true if and only if `self == 2^k` for some `k`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert!(UInt::from(16u32).is_power_of_two());
    /// assert!(!UInt::from(10u32).is_power_of_two());
    /// ```
    #[must_use]
    pub fn is_power_of_two(self) -> bool {
        self.0.is_power_of_two()
    }

    /// Returns the smallest power of two greater than or equal to `n`. If the next power of two is
    /// greater than the type's maximum value, `None` is returned, otherwise the power of two is
    /// wrapped in `Some`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from(2u32).checked_next_power_of_two(), Some(UInt::from(2u32)));
    /// assert_eq!(UInt::from(3u32).checked_next_power_of_two(), Some(UInt::from(4u32)));
    /// assert_eq!(UInt::MAX.checked_next_power_of_two(), None);
    /// ```
    #[must_use]
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

    /// Checked integer addition. Computes `self + rhs`, returning `None` if overflow occurred.
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(
    ///     (UInt::MAX - UInt::from(2u32)).checked_add(UInt::from(1u32)),
    ///     Some(UInt::MAX - UInt::from(1u32))
    /// );
    /// assert_eq!((UInt::MAX - UInt::from(2u32)).checked_add(UInt::from(3u32)), None);
    /// ```
    #[must_use]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).and_then(Self::new)
    }

    /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from(1u32).checked_sub(UInt::from(1u32)), Some(UInt::from(0u32)));
    /// assert_eq!(UInt::from(0u32).checked_sub(UInt::from(1u32)), None);
    /// ```
    #[must_use]
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).and_then(Self::new)
    }

    /// Checked integer multiplication. Computes `self * rhs`, returning `None` if overflow
    /// occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from(5u32).checked_mul(UInt::from(1u32)), Some(UInt::from(5u32)));
    /// assert_eq!(UInt::MAX.checked_mul(UInt::from(2u32)), None);
    /// ```
    #[must_use]
    pub fn checked_mul(self, rhs: Self) -> Option<Self> {
        self.0.checked_mul(rhs.0).and_then(Self::new)
    }

    /// Checked integer division. Computes `self / rhs`, returning `None` if `rhs == 0`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from(128u32).checked_div(UInt::from(2u32)), Some(UInt::from(64u32)));
    /// assert_eq!(UInt::from(1u32).checked_div(UInt::from(0u32)), None);
    /// ```
    #[must_use]
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        self.0.checked_div(rhs.0).map(Self)
    }

    /// Checked integer remainder. Computes `self % rhs`, returning `None` if `rhs == 0`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from(5u32).checked_rem(UInt::from(2u32)), Some(UInt::from(1u32)));
    /// assert_eq!(UInt::from(5u32).checked_rem(UInt::from(0u32)), None);
    /// ```
    #[must_use]
    pub fn checked_rem(self, rhs: Self) -> Option<Self> {
        self.0.checked_rem(rhs.0).map(Self)
    }

    /// Checked negation. Computes `-self`, returning None unless `self == 0`.
    ///
    /// Note that negating any positive integer will overflow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from(0u32).checked_neg(), Some(UInt::from(0u32)));
    /// assert_eq!(UInt::from(1u32).checked_neg(), None);
    /// ```
    #[must_use]
    pub fn checked_neg(self) -> Option<Self> {
        self.0.checked_neg().map(Self)
    }

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None` if overflow or
    /// underflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from(0u32).checked_pow(2), Some(UInt::from(0u32)));
    /// assert_eq!(UInt::from(8u32).checked_pow(2), Some(UInt::from(64u32)));
    /// assert_eq!(UInt::from(1_000_000_000u32).checked_pow(2), None);
    /// assert_eq!(UInt::MAX.checked_pow(2), None);
    /// ```
    #[must_use]
    pub fn checked_pow(self, exp: u32) -> Option<Self> {
        self.0.checked_pow(exp).and_then(Self::new)
    }

    /// Saturating integer addition. Computes `self + rhs`, saturating at the numeric bounds
    /// instead of overflowing.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from(100u32).saturating_add(UInt::from(1u32)), UInt::from(101u32));
    /// assert_eq!(UInt::MAX.saturating_add(UInt::from(1u32)), UInt::MAX);
    /// ```
    #[must_use]
    pub fn saturating_add(self, rhs: Self) -> Self {
        self.checked_add(rhs).unwrap_or(Self::MAX)
    }

    /// Saturating integer subtraction. Computes `self - rhs`, saturating at the numeric
    /// bounds instead of underflowing.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from(100u32).saturating_sub(UInt::from(1u32)), UInt::from(99u32));
    /// assert_eq!(UInt::from(1u32).saturating_sub(UInt::from(2u32)), UInt::from(0u32));
    /// ```
    #[must_use]
    pub fn saturating_sub(self, rhs: Self) -> Self {
        self.checked_sub(rhs).unwrap_or(Self::MIN)
    }

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at the numeric
    /// bounds instead of overflowing.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from(100u32).saturating_mul(UInt::from(2u32)), UInt::from(200u32));
    /// assert_eq!(UInt::MAX.saturating_mul(UInt::from(2u32)), UInt::MAX);
    /// assert_eq!(UInt::MAX.saturating_mul(UInt::MAX), UInt::MAX);
    /// ```
    #[must_use]
    pub fn saturating_mul(self, rhs: Self) -> Self {
        self.checked_mul(rhs).unwrap_or(Self::MAX)
    }

    /// Saturating integer exponentiation. Computes `self.pow(exp)`, saturating at the
    /// numeric bounds instead of overflowing or underflowing.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::UInt;
    /// assert_eq!(UInt::from(5u32).saturating_pow(2), UInt::from(25u32));
    /// assert_eq!(UInt::MAX.saturating_pow(2), UInt::MAX);
    /// ```
    #[must_use]
    pub fn saturating_pow(self, exp: u32) -> Self {
        Self::new_saturating(self.0.saturating_pow(exp))
    }

    // TODO: wrapping_* methods, overflowing_* methods
}

fmt_impls!(UInt);
convert_impls!(UInt, u8, u16, u32, u64, u128);

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

impl TryFrom<i128> for UInt {
    type Error = TryFromIntError;

    fn try_from(val: i128) -> Result<Self, TryFromIntError> {
        if val >= 0 && val <= i128::from(MAX_SAFE_INT) {
            Ok(Self(val as u64))
        } else {
            Err(TryFromIntError::new())
        }
    }
}

macro_rules! uint_op_impl {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        impl $trait for UInt {
            type Output = Self;

            fn $method(self, rhs: Self) -> Self {
                Self::new_(<u64 as $trait>::$method(self.0, rhs.0))
            }
        }

        impl $assign_trait for UInt {
            fn $assign_method(&mut self, other: Self) {
                self.assign_(<u64 as $trait>::$method(self.0, other.0));
            }
        }
    };
}

uint_op_impl!(Add, add, AddAssign, add_assign);
uint_op_impl!(Sub, sub, SubAssign, sub_assign);
uint_op_impl!(Mul, mul, MulAssign, mul_assign);
uint_op_impl!(Div, div, DivAssign, div_assign);
uint_op_impl!(Rem, rem, RemAssign, rem_assign);

impl iter::Sum for UInt {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = UInt>,
    {
        Self::new_(iter.map(|x| x.0).sum())
    }
}

impl<'a> iter::Sum<&'a UInt> for UInt {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a UInt>,
    {
        Self::new_(iter.map(|x| x.0).sum())
    }
}

impl iter::Product for UInt {
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = UInt>,
    {
        Self::new_(iter.map(|x| x.0).product())
    }
}

impl<'a> iter::Product<&'a UInt> for UInt {
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a UInt>,
    {
        Self::new_(iter.map(|x| x.0).product())
    }
}

impl FromStr for UInt {
    type Err = ParseIntError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        let val = u64::from_str(src)?;
        if val > MAX_SAFE_UINT {
            Err(ParseIntError {
                kind: ParseIntErrorKind::Overflow,
            })
        } else {
            Ok(Self(val))
        }
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for UInt {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let val = u64::deserialize(deserializer)?;
        Self::new(val).ok_or_else(|| {
            D::Error::invalid_value(
                Unexpected::Unsigned(val),
                &"an integer between 0 and 2^53 - 1",
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{UInt, MAX_SAFE_UINT};

    #[test]
    fn uint_ops() {
        assert_eq!(UInt::from(5u32) + UInt::from(3u32), UInt::from(8u32));
        assert_eq!(UInt::from(2u32) - UInt::from(1u32), UInt::from(1u32));
        assert_eq!(UInt::from(4u32) * UInt::from(2u32), UInt::from(8u32));
        assert_eq!(UInt::from(5u32) / UInt::from(2u32), UInt::from(2u32));
        assert_eq!(UInt::from(11u32) % UInt::from(4u32), UInt::from(3u32));
    }

    #[test]
    fn uint_assign_ops() {
        let mut uint = UInt::from(1u32);

        uint += UInt::from(3u32);
        assert_eq!(uint, UInt::from(4u32));

        uint -= UInt::from(1u32);
        assert_eq!(uint, UInt::from(3u32));

        uint *= UInt::from(3u32);
        assert_eq!(uint, UInt::from(9u32));

        uint /= UInt::from(3u32);
        assert_eq!(uint, UInt::from(3u32));

        uint %= UInt::from(2u32);
        assert_eq!(uint, UInt::from(1u32));
    }

    #[test]
    fn uint_wrapping_new() {
        assert_eq!(UInt::new_wrapping(MAX_SAFE_UINT + 1), UInt::from(0u32));
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore)]
    fn uint_underflow_wrap() {
        assert_eq!(UInt::from(0u32) - UInt::from(1u32), UInt::MAX);
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore)]
    fn uint_overflow_wrap() {
        assert_eq!(UInt::MAX + UInt::from(1u32), UInt::from(0u32));
        assert_eq!(UInt::MAX + UInt::from(5u32), UInt::from(4u32));
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
        let _ = UInt::MAX + UInt::from(1u32);
    }
}