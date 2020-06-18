macro_rules! fmt_impls {
    ($type:ident) => {
        impl ::std::fmt::Display for $type {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl ::std::fmt::Debug for $type {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                write!(f, "{:?}", self.0)
            }
        }
    };
}

macro_rules! convert_impls {
    ($type:ident, $t8:ident, $t16:ident, $t32:ident, $t64:ident, $t128:ident) => {
        impl ::std::convert::From<$t8> for $type {
            fn from(val: $t8) -> Self {
                Self($t64::from(val))
            }
        }

        impl ::std::convert::From<$t16> for $type {
            fn from(val: $t16) -> Self {
                Self($t64::from(val))
            }
        }

        impl ::std::convert::From<$t32> for $type {
            fn from(val: $t32) -> Self {
                Self($t64::from(val))
            }
        }

        impl ::std::convert::TryFrom<$t64> for $type {
            type Error = crate::error::TryFromIntError;

            fn try_from(val: $t64) -> Result<Self, crate::error::TryFromIntError> {
                Self::new(val).ok_or_else(crate::error::TryFromIntError::new)
            }
        }

        impl ::std::convert::TryFrom<$t128> for $type {
            type Error = crate::error::TryFromIntError;

            fn try_from(val: $t128) -> Result<Self, crate::error::TryFromIntError> {
                $t64::try_from(val)
                    .map_err(|_| crate::error::TryFromIntError::new())
                    .and_then($type::try_from)
            }
        }

        impl ::std::convert::TryFrom<$type> for $t8 {
            type Error = ::std::num::TryFromIntError;

            fn try_from(val: $type) -> Result<Self, ::std::num::TryFromIntError> {
                Self::try_from(val.0)
            }
        }

        impl ::std::convert::TryFrom<$type> for $t16 {
            type Error = ::std::num::TryFromIntError;

            fn try_from(val: $type) -> Result<Self, ::std::num::TryFromIntError> {
                Self::try_from(val.0)
            }
        }

        impl ::std::convert::TryFrom<$type> for $t32 {
            type Error = ::std::num::TryFromIntError;

            fn try_from(val: $type) -> Result<Self, ::std::num::TryFromIntError> {
                Self::try_from(val.0)
            }
        }

        impl ::std::convert::From<$type> for $t64 {
            fn from(val: $type) -> Self {
                val.0
            }
        }

        impl ::std::convert::From<$type> for $t128 {
            fn from(val: $type) -> Self {
                $t128::from(val.0)
            }
        }

        impl ::std::convert::From<$type> for f64 {
            fn from(val: $type) -> Self {
                val.0 as f64
            }
        }
    };
}
