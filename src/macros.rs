/// Creates an `Int` from a numeric literal.
#[macro_export]
macro_rules! int {
    ($n:literal) => {
        <$crate::Int as ::core::convert::From<i32>>::from($n)
    };
}

/// Creates a `UInt` from a numeric literal.
#[macro_export]
macro_rules! uint {
    ($n:literal) => {
        <$crate::UInt as ::core::convert::From<u32>>::from($n)
    };
}

macro_rules! fmt_impls {
    ($type:ident) => {
        impl ::core::fmt::Display for $type {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl ::core::fmt::Debug for $type {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                write!(f, "{:?}", self.0)
            }
        }
    };
}

macro_rules! convert_impls {
    ($type:ident, $t8:ident, $t16:ident, $t32:ident, $t64:ident, $t128:ident, $ot8:ident, $ot16:ident, $ot32:ident) => {
        impl ::core::convert::From<$t8> for $type {
            fn from(val: $t8) -> Self {
                Self($t64::from(val))
            }
        }

        impl ::core::convert::From<$t16> for $type {
            fn from(val: $t16) -> Self {
                Self($t64::from(val))
            }
        }

        impl ::core::convert::From<$t32> for $type {
            fn from(val: $t32) -> Self {
                Self($t64::from(val))
            }
        }

        impl ::core::convert::TryFrom<$t64> for $type {
            type Error = crate::error::TryFromIntError;

            fn try_from(val: $t64) -> Result<Self, crate::error::TryFromIntError> {
                Self::new(val).ok_or_else(crate::error::TryFromIntError::new)
            }
        }

        impl ::core::convert::TryFrom<$t128> for $type {
            type Error = crate::error::TryFromIntError;

            fn try_from(val: $t128) -> Result<Self, crate::error::TryFromIntError> {
                $t64::try_from(val)
                    .map_err(|_| crate::error::TryFromIntError::new())
                    .and_then($type::try_from)
            }
        }

        impl ::core::convert::TryFrom<$type> for $t8 {
            type Error = ::core::num::TryFromIntError;

            fn try_from(val: $type) -> Result<Self, ::core::num::TryFromIntError> {
                Self::try_from(val.0)
            }
        }
        
        impl ::core::convert::TryFrom<$type> for $ot8 {
            type Error = ::core::num::TryFromIntError;

            fn try_from(val: $type) -> Result<Self, ::core::num::TryFromIntError> {
                Self::try_from(val.0)
            }
        }

        impl ::core::convert::TryFrom<$type> for $t16 {
            type Error = ::core::num::TryFromIntError;

            fn try_from(val: $type) -> Result<Self, ::core::num::TryFromIntError> {
                Self::try_from(val.0)
            }
        }
        
        impl ::core::convert::TryFrom<$type> for $ot16 {
            type Error = ::core::num::TryFromIntError;

            fn try_from(val: $type) -> Result<Self, ::core::num::TryFromIntError> {
                Self::try_from(val.0)
            }
        }

        impl ::core::convert::TryFrom<$type> for $t32 {
            type Error = ::core::num::TryFromIntError;

            fn try_from(val: $type) -> Result<Self, ::core::num::TryFromIntError> {
                Self::try_from(val.0)
            }
        }
        
        impl ::core::convert::TryFrom<$type> for $ot32 {
            type Error = ::core::num::TryFromIntError;

            fn try_from(val: $type) -> Result<Self, ::core::num::TryFromIntError> {
                Self::try_from(val.0)
            }
        }

        impl ::core::convert::From<$type> for $t64 {
            fn from(val: $type) -> Self {
                val.0
            }
        }

        impl ::core::convert::From<$type> for $t128 {
            fn from(val: $type) -> Self {
                $t128::from(val.0)
            }
        }

        impl ::core::convert::From<$type> for f64 {
            fn from(val: $type) -> Self {
                val.0 as f64
            }
        }
    };
}
