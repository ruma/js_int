# 0.2.2

* Consider negative values in saturating add / sub
* `impl TryFrom<UInt> for iN` for N = [8, 16, 32]
* `impl TryFrom<Int> for uN` for N = [8, 16, 32]
* Fix lax_deserialize accepting NaN
* Support deserializing floats without fractional component
* Add `usize` and `isize` `TryFrom` implementations

# 0.2.1

* Update crate metadata

# 0.2.0

* Bump MSRV to 1.35
* Drop support for the `rocket_04` Cargo feature (Rocket 0.4 `FromFormValue` / `FromParam`
  implementations)

# 0.1.9

* Add a new Cargo feature: `lax_deserialize`
  * See the crate documentation or [README.md](README.md) for what it does.

# 0.1.8

* Update the documentation to use the macros introduced in 0.1.6.

# 0.1.7

* Fix building without the `std` feature

# 0.1.6

* Introduce `int!` and `uint!` macros as shorthand for `Int::from(Ni32)` and `UInt::from(Nu32)`

# 0.1.5

* Introduce `Int::MIN`, `Int::MAX`, `UInt::MIN`, `UInt::MAX` and deprecate `const fn min_value` and
  `const fn max_value`s.

# 0.1.4

* Allow deserialization of `Int`s and `UInt`s from non-self-describing formats

# 0.1.3

* Add conversions to / from 128 bit integer types

# 0.1.2

* Implement `std::iter::Sum` and `std::iter::Product` for `Int` and `UInt`
* Mention JavaScript's propsed BigInt type in documentation

# 0.1.1

* Add doctests for every inherent method of `Int` and `UInt`
* Fix buggy implementation of `Int::saturating_mul`
* Add (optional) implementations of `rocket::{FromFormValue, FromParam}` (for rocket 0.4)

# 0.1.0

Initial release containing the `Int` and `UInt` types, `serde` support and many of the methods that
`std`'s integer types provide.
