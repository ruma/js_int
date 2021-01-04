# js_int

[![Build Status](https://travis-ci.org/jplatte/js_int.svg?branch=main)][travis]
[![Latest Version](https://img.shields.io/crates/v/js_int.svg)][crates-io]
[![Docs](https://docs.rs/js_int/badge.svg)][docs-rs]

Crate `js_int` provides JavaScript-interoperable integer types.

JavaScript does not have native integers. Instead it represents all numeric
values with a single `Number` type which is represented as an
[IEEE 754 floating-point](https://en.wikipedia.org/wiki/IEEE_754) value.\*
Rust's `i64` and `u64` types can contain values outside the range of what can be
represented in a JavaScript `Number`.

This crate provides the types `Int` and `UInt` which wrap `i64` and `u64`,
respectively. These types add bounds checking to ensure the contained value is
within the range representable by a JavaScript `Number`. They provide useful
trait implementations to easily convert from Rust's primitive integer types.

<small>* In the upcoming ECMAScript 2020, JavaScript will probably gain support
for integers. There is a proposal for a [`BigInt`][mdn] type type that is not
far from becoming part of the JavaScript specification. It won't make this crate
obsolete in any way though, since there will still be lots of JS code using
`Number`, and code in other languages that assumes its use.
</small>

This crate requires rustc >= 1.35.

This crate is `no_std`-compatible with `default-features = false`. This will
disable the `std` feature, which at the time of writing will only omit the
implementations of `std::error::Error` for `ParseIntError` and
`TryFromIntError`.

(De-)Serialization via `serde` is supported via the `serde` feature, even
without the `std` feature.

Deserialization can be routed through `f64` instead of `u64` with the
`lax_deserialize` feature. If a deserialized number is fractional, the
fractional part is discarded. Please be aware that `serde_json` doesn't
losslessly parse large floats with a fractional part by default (even if the
fractional part is `.0`). To fix that, enable its `float_roundtrip` feature.

[travis]: https://travis-ci.org/jplatte/js_int
[crates-io]: https://crates.io/crates/js_int
[docs-rs]: https://docs.rs/js_int
[mdn]: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/BigInt
