//! Crate `js_int` provides JavaScript-interoperable integer types.
//!
//! JavaScript does not have native integers. Instead it represents all numeric values with a
//! single `Number` type which is represented as an [IEEE 754
//! floating-point](https://en.wikipedia.org/wiki/IEEE_754) value.\* Rust's `i64` and `u64` types
//! can contain values outside the range of what can be represented in a JavaScript `Number`.
//!
//! This crate provides the types `Int` and `UInt` which wrap `i64` and `u64`, respectively. These
//! types add bounds checking to ensure the contained value is within the range representable by a
//! JavaScript `Number`. They provide useful trait implementations to easily convert from Rust's
//! primitive integer types.
//!
//! <small>* In the upcoming ECMAScript 2020, JavaScript will probably gain support for integers.
//! There is a proposal for a [`BigInt`][mdn] type type that is not far from becoming part of the
//! JavaScript specification. It won't make this crate obsolete in any way though, since there will
//! still be lots of JS code using `Number`, and code in other languages that assumes its use.
//! </small>
//!
//! [mdn]: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/BigInt
//!
//! # `#![no_std]`
//!
//! The `js_int` crate does not use Rust's standard library, and is compatible with `#![no_std]`
//! programs.
//!
//! # Features
//!
//! * `rocket_04`: Deserialization support from form values (`impl FromFormValue`) and path segments
//!   (`impl FromParam`) for users of the Rocket web framework version 0.4. Disabled by default.
//! * `serde`: Serialization and deserialization support via [serde](https://serde.rs). Disabled by
//!   default. You can use `js_int` + `serde` in `#![no_std]` contexts if you use
//!   `default-features = false` for both.
//! * `lax_deserialize`: Deserialize via `f64`, not via `u64`. If the input has a fraction, it is
//!   discarded. Please be aware that `serde_json` doesn't losslessly parse large floats with a
//!   fractional part by default (even if the fractional part is `.0`). To fix that, enable its
//!   `float_roundtrip` feature.
//! * `std`: Enable `std::error::Error` implementations for `ParseIntError`, `TryFromIntError`.
//!   Enabled by default.

#![deny(missing_debug_implementations, missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
mod macros;
mod error;
mod int;
mod uint;

pub use self::{
    error::{ParseIntError, TryFromIntError},
    int::{Int, MAX_SAFE_INT, MIN_SAFE_INT},
    uint::{UInt, MAX_SAFE_UINT},
};

#[cfg(feature = "rocket_04")]
macro_rules! rocket_04_impls {
    ($type:ident) => {
        impl<'v> rocket_04::request::FromFormValue<'v> for $type {
            type Error = &'v rocket_04::http::RawStr;

            fn from_form_value(
                form_value: &'v rocket_04::http::RawStr,
            ) -> Result<Self, Self::Error> {
                form_value.parse::<$type>().map_err(|_| form_value)
            }
        }

        impl<'r> rocket_04::request::FromParam<'r> for $type {
            type Error = &'r rocket_04::http::RawStr;

            fn from_param(param: &'r rocket_04::http::RawStr) -> Result<Self, Self::Error> {
                param.parse::<$type>().map_err(|_| param)
            }
        }
    };
}

#[cfg(feature = "rocket_04")]
rocket_04_impls!(Int);
#[cfg(feature = "rocket_04")]
rocket_04_impls!(UInt);
