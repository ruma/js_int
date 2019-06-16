# js_int

[![Build Status](https://travis-ci.org/jplatte/js_int.svg?branch=master)](https://travis-ci.org/jplatte/js_int)
[![Latest Version](https://img.shields.io/crates/v/js_int.svg)](https://crates.io/crates/js_int)
[![Docs](https://docs.rs/js_int/badge.svg)](https://docs.rs/js_int)

Crate `js_int` provides JavaScript-interoperable integer types.

JavaScript does not have native integers. Instead it represents all numeric values with a single `Number` type which is represented as an [IEEE 754 floating-point](https://en.wikipedia.org/wiki/IEEE_754) value. Rust's `i64` and `u64` types can contain values outside the range of what can be represented in a JavaScript `Number`.

This crate provides the types `Int` and `UInt` which wrap `i64` and `u64`, respectively. These types add bounds checking to ensure the contained value is within the range representable by a JavaScript `Number`. They provide useful trait implementations to easily convert from Rust's primitive integer types.
