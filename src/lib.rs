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
//! * `serde`: Serialization and deserialization support via [serde](https://serde.rs). Disabled by
//!   default. You can use `js_int` + `serde` in `#![no_std]` contexts if you use
//!   `default-features = false` for both.
//! * `float_deserialize`: Deserialize via `f64`, not via `u64`. If the input has a fraction,
//!   deserialization will fail.
//! * `lax_deserialize`: Like `float_deserialize`, but if the input has a fraction, it is
//!   deserialized with the fractional part discarded.
//!   Please be aware that `serde_json` doesn't losslessly parse large floats with a fractional part
//!   by default (even if the fractional part is `.0`). To fix that, enable its `float_roundtrip`
//!   feature.
//! * `std`: Enable `std::error::Error` implementations for `ParseIntError`, `TryFromIntError`.
//!   Enabled by default.

#![deny(missing_debug_implementations, missing_docs)]
#![allow(clippy::cast_lossless)] // Not useful in this crate
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

#[cfg(feature = "float_deserialize")]
#[inline(always)]
pub(crate) fn is_acceptable_float(float: f64) -> bool {
    #[cfg(not(feature = "lax_deserialize"))]
    {
        if float.fract() != 0.0 {
            return false;
        }
    }

    !float.is_nan()
}
