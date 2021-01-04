use core::{
    convert::TryFrom,
    iter,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign},
    str::FromStr,
};

#[cfg(feature = "serde")]
use serde::{
    de::{Error as _, Unexpected},
    Deserialize, Deserializer, Serialize,
};

use crate::{
    error::{ParseIntError, ParseIntErrorKind, TryFromIntError},
    UInt, MAX_SAFE_UINT,
};

/// The largest integer value that can be represented exactly by an f64.
pub const MAX_SAFE_INT: i64 = 0x001F_FFFF_FFFF_FFFF;
/// The smallest integer value that can be represented exactly by an f64.
pub const MIN_SAFE_INT: i64 = -MAX_SAFE_INT;

/// An integer limited to the range of integers that can be represented exactly by an f64.
#[derive(Clone, Copy, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize))]
pub struct Int(i64);

impl Int {
    /// The smallest value that can be represented by this integer type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use {core::convert::TryFrom, js_int::Int};
    /// assert_eq!(Int::MIN, Int::try_from(-9_007_199_254_740_991i64).unwrap());
    /// ```
    pub const MIN: Self = Self(MIN_SAFE_INT);

    /// The largest value that can be represented by this integer type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use {core::convert::TryFrom, js_int::Int};
    /// assert_eq!(Int::MAX, Int::try_from(9_007_199_254_740_991i64).unwrap());
    /// ```
    pub const MAX: Self = Self(MAX_SAFE_INT);

    /// Try to create an `Int` from the provided `i64`, returning `None` if it is smaller than
    /// `MIN_SAFE_INT` or larger than `MAX_SAFE_INT`.
    ///
    /// This is the same as the `TryFrom<u64>` implementation for `Int`, except that it returns
    /// an `Option` instead of a `Result`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::Int;
    /// assert_eq!(Int::new(js_int::MIN_SAFE_INT), Some(Int::MIN));
    /// assert_eq!(Int::new(js_int::MAX_SAFE_INT), Some(Int::MAX));
    /// assert_eq!(Int::new(js_int::MIN_SAFE_INT - 1), None);
    /// assert_eq!(Int::new(js_int::MAX_SAFE_INT + 1), None);
    /// ```
    #[must_use]
    pub fn new(val: i64) -> Option<Self> {
        if (MIN_SAFE_INT..=MAX_SAFE_INT).contains(&val) {
            Some(Self(val))
        } else {
            None
        }
    }

    // TODO: make public if name is deemed sensible, rename and make public otherwise.
    #[must_use]
    fn new_saturating(val: i64) -> Self {
        if val < MIN_SAFE_INT {
            Self::MIN
        } else if val > MAX_SAFE_INT {
            Self::MAX
        } else {
            Self(val)
        }
    }

    /// The constructor used for arithmetic operations
    #[must_use]
    fn new_(val: i64) -> Self {
        assert!(val >= MIN_SAFE_INT);
        assert!(val <= MAX_SAFE_INT);

        Self(val)
    }

    /// Helper function for mutable arithmetic operations (`+=`, `-=`, …)
    fn assign_(&mut self, val: i64) {
        assert!(val >= MIN_SAFE_INT);
        assert!(val <= MAX_SAFE_INT);

        *self = Self(val);
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
    /// # use js_int::{int, Int};
    /// assert_eq!(Int::from_str_radix("A", 16), Ok(int!(10)));
    /// ```
    pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        let val = i64::from_str_radix(src, radix)?;
        if val < MIN_SAFE_INT {
            Err(ParseIntError { kind: ParseIntErrorKind::Underflow })
        } else if val > MAX_SAFE_INT {
            Err(ParseIntError { kind: ParseIntErrorKind::Overflow })
        } else {
            Ok(Self(val))
        }
    }

    /// Returns the smallest value that can be represented by this integer type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use {core::convert::TryFrom, js_int::Int};
    /// assert_eq!(Int::min_value(), Int::try_from(-9_007_199_254_740_991i64).unwrap());
    /// ```
    #[must_use]
    #[deprecated = "Use `UInt::MIN` instead."]
    pub const fn min_value() -> Self {
        Self(MIN_SAFE_INT)
    }

    /// Returns the largest value that can be represented by this integer type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use {core::convert::TryFrom, js_int::Int};
    /// assert_eq!(Int::max_value(), Int::try_from(9_007_199_254_740_991i64).unwrap());
    /// ```
    #[must_use]
    #[deprecated = "Use `Int::MAX` instead."]
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
    /// # use js_int::{int, Int};
    /// assert_eq!(int!(10).abs(), int!(10));
    /// assert_eq!(int!(-10).abs(), int!(10));
    ///
    /// // Differently from i8 / i16 / i32 / i128, Int's min_value is its max_value negated
    /// assert_eq!(Int::MIN.abs(), Int::MAX);
    /// ```
    #[must_use]
    pub fn abs(self) -> Self {
        Self(self.0.abs())
    }

    /// Returns `true` if `self` is positive and `false` if the number is zero or negative.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::int;
    /// assert!(int!(10).is_positive());
    /// assert!(!int!(0).is_positive());
    /// assert!(!int!(-10).is_positive());
    /// ```
    #[must_use]
    pub const fn is_positive(self) -> bool {
        self.0.is_positive()
    }

    /// Returns `true` if `self` is negative and `false` if the number is zero or positive.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::int;
    /// assert!(int!(-10).is_negative());
    /// assert!(!int!(0).is_negative());
    /// assert!(!int!(10).is_negative());
    /// ```
    #[must_use]
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
    /// # use js_int::{int, Int};
    /// assert_eq!(
    ///     (Int::MAX - int!(1)).checked_add(int!(1)),
    ///     Some(Int::MAX)
    /// );
    /// assert_eq!((Int::MAX - int!(1)).checked_add(int!(2)), None);
    /// ```
    #[must_use]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).and_then(Self::new)
    }

    /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow
    /// occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::{int, Int};
    /// assert_eq!(
    ///     (Int::MIN + int!(2)).checked_sub(int!(1)),
    ///     Some(Int::MIN + int!(1))
    /// );
    /// assert_eq!((Int::MIN + int!(2)).checked_sub(int!(3)), None);
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
    /// # use js_int::{int, Int};
    /// assert_eq!(int!(5).checked_mul(int!(1)), Some(int!(5)));
    /// assert_eq!(Int::MAX.checked_mul(int!(2)), None);
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
    /// # use js_int::{int, Int};
    /// assert_eq!(Int::MIN.checked_div(int!(-1)), Some(Int::MAX));
    /// assert_eq!(int!(1).checked_div(int!(0)), None);
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
    /// # use js_int::{int, Int};
    /// assert_eq!(int!(5).checked_rem(int!(2)), Some(int!(1)));
    /// assert_eq!(int!(5).checked_rem(int!(0)), None);
    /// assert_eq!(Int::MIN.checked_rem(int!(-1)), Some(int!(0)));
    /// ```
    #[must_use]
    pub fn checked_rem(self, rhs: Self) -> Option<Self> {
        self.0.checked_rem(rhs.0).map(Self)
    }

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None` if overflow or
    /// underflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::{int, Int};
    /// assert_eq!(int!(8).checked_pow(2), Some(int!(64)));
    /// assert_eq!(Int::MAX.checked_pow(2), None);
    /// assert_eq!(Int::MIN.checked_pow(2), None);
    /// assert_eq!(int!(1_000_000_000).checked_pow(2), None);
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
    /// # use js_int::{int, Int};
    /// assert_eq!(int!(100).saturating_add(int!(1)), int!(101));
    /// assert_eq!(Int::MAX.saturating_add(int!(1)), Int::MAX);
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
    /// # use js_int::{int, Int};
    /// assert_eq!(int!(100).saturating_sub(int!(1)), int!(99));
    /// assert_eq!(Int::MIN.saturating_sub(int!(1)), Int::MIN);
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
    /// # use js_int::{int, Int};
    /// assert_eq!(int!(100).saturating_mul(int!(2)), int!(200));
    /// assert_eq!(Int::MAX.saturating_mul(int!(2)), Int::MAX);
    /// assert_eq!(Int::MAX.saturating_mul(Int::MAX), Int::MAX);
    /// assert_eq!(Int::MAX.saturating_mul(Int::MIN), Int::MIN);
    /// ```
    #[must_use]
    pub fn saturating_mul(self, rhs: Self) -> Self {
        Self::new_saturating(self.0.saturating_mul(rhs.0))
    }

    /// Saturating integer exponentiation. Computes `self.pow(exp)`, saturating at the
    /// numeric bounds instead of overflowing or underflowing.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use js_int::{int, Int};
    /// assert_eq!(int!(5).saturating_pow(2), int!(25));
    /// assert_eq!(int!(-2).saturating_pow(3), int!(-8));
    /// assert_eq!(Int::MAX.saturating_pow(2), Int::MAX);
    /// assert_eq!(Int::MIN.saturating_pow(2), Int::MAX);
    /// ```
    #[must_use]
    pub fn saturating_pow(self, exp: u32) -> Self {
        Self::new_saturating(self.0.saturating_pow(exp))
    }

    // TODO: wrapping_* methods, overflowing_* methods
}

fmt_impls!(Int);
convert_impls!(Int, i8, i16, i32, i64, i128, u8, u16, u32);

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

impl From<UInt> for Int {
    fn from(val: UInt) -> Self {
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

impl TryFrom<u128> for Int {
    type Error = TryFromIntError;

    fn try_from(val: u128) -> Result<Self, TryFromIntError> {
        if val <= u128::from(MAX_SAFE_UINT) {
            Ok(Self(val as i64))
        } else {
            Err(TryFromIntError::new())
        }
    }
}

macro_rules! int_op_impl {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        impl $trait for Int {
            type Output = Self;

            fn $method(self, rhs: Self) -> Self {
                Self::new_(<i64 as $trait>::$method(self.0, rhs.0))
            }
        }

        impl $assign_trait for Int {
            fn $assign_method(&mut self, other: Self) {
                self.assign_(<i64 as $trait>::$method(self.0, other.0));
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

impl iter::Sum for Int {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Int>,
    {
        Self::new_(iter.map(|x| x.0).sum())
    }
}

impl<'a> iter::Sum<&'a Int> for Int {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a Int>,
    {
        Self::new_(iter.map(|x| x.0).sum())
    }
}

impl iter::Product for Int {
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = Int>,
    {
        Self::new_(iter.map(|x| x.0).product())
    }
}

impl<'a> iter::Product<&'a Int> for Int {
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a Int>,
    {
        Self::new_(iter.map(|x| x.0).product())
    }
}

impl FromStr for Int {
    type Err = ParseIntError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        let val = i64::from_str(src)?;
        if val < MIN_SAFE_INT {
            Err(ParseIntError { kind: ParseIntErrorKind::Underflow })
        } else if val > MAX_SAFE_INT {
            Err(ParseIntError { kind: ParseIntErrorKind::Overflow })
        } else {
            Ok(Self(val))
        }
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Int {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[cfg(not(feature = "lax_deserialize"))]
        {
            let val = i64::deserialize(deserializer)?;

            Self::new(val).ok_or_else(|| {
                D::Error::invalid_value(
                    Unexpected::Signed(val),
                    &"an integer between -2^53 + 1 and 2^53 - 1",
                )
            })
        }

        #[cfg(feature = "lax_deserialize")]
        {
            let val = f64::deserialize(deserializer)?;

            if val > MAX_SAFE_INT as f64 || val < MIN_SAFE_INT as f64 {
                Err(D::Error::invalid_value(
                    Unexpected::Float(val),
                    &"a number between -2^53 + 1 and 2^53 - 1",
                ))
            } else {
                Ok(Self(val as i64))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Int;

    #[test]
    fn int_ops() {
        assert_eq!(int!(5) + int!(3), int!(8));
        assert_eq!(int!(1) - int!(2), int!(-1));
        assert_eq!(int!(4) * int!(-7), int!(-28));
        assert_eq!(int!(5) / int!(2), int!(2));
        assert_eq!(int!(9) % int!(3), int!(0));
    }

    #[test]
    fn int_assign_ops() {
        let mut int = int!(1);

        int += int!(1);
        assert_eq!(int, int!(2));

        int -= int!(-1);
        assert_eq!(int, int!(3));

        int *= int!(3);
        assert_eq!(int, int!(9));

        int /= int!(3);
        assert_eq!(int, int!(3));

        int %= int!(2);
        assert_eq!(int, int!(1));
    }

    #[test]
    #[should_panic]
    fn int_underflow_panic() {
        let _ = Int::MIN - int!(1);
    }

    #[test]
    #[should_panic]
    fn int_overflow_panic() {
        let _ = Int::MAX + int!(1);
    }
    
    #[test]
    fn try_from_int_for_u_n() {
        use std::convert::TryFrom;
        let u8_max = u8::MAX as i64;
        let u16_max = u16::MAX as i64;
        let u32_max = u32::MAX as i64;
        
        assert_eq!(u8::try_from(Int(0)), Ok(0));
        assert_eq!(u8::try_from(Int(10)), Ok(10));
        assert_eq!(u8::try_from(Int(u8_max)), Ok(u8::MAX));
        assert!(u8::try_from(Int(u8_max+1)).is_err());
        assert!(u8::try_from(Int(-1)).is_err());
        assert!(u8::try_from(Int(-10)).is_err());
        
        assert_eq!(u16::try_from(Int(0)), Ok(0));
        assert_eq!(u16::try_from(Int(1000)), Ok(1000));
        assert_eq!(u16::try_from(Int(u8_max+1)), Ok((u8_max+1) as u16));
        assert_eq!(u16::try_from(Int(u16_max)), Ok(u16::MAX));
        assert!(u16::try_from(Int(u16_max+1)).is_err());
        assert!(u16::try_from(Int(-1)).is_err());
        assert!(u16::try_from(Int(-10)).is_err());
        
        assert_eq!(u32::try_from(Int(0)), Ok(0));
        assert_eq!(u32::try_from(Int(1000)), Ok(1000));
        assert_eq!(u32::try_from(Int(u16_max+1)), Ok((u16_max+1) as u32));
        assert_eq!(u32::try_from(Int(u32_max)), Ok(u32::MAX));
        assert!(u32::try_from(Int(u32_max+1)).is_err());
        assert!(u32::try_from(Int(-1)).is_err());
        assert!(u32::try_from(Int(-10)).is_err());
    }
}
