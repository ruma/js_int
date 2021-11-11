#![cfg(feature = "serde")]

use core::convert::TryFrom;
use js_int::{int, Int};
use serde::{de::IntoDeserializer, Deserialize};
use serde_test::{assert_ser_tokens, Token};

#[test]
fn serialize() {
    assert_serialize(100);
    assert_serialize(0);
    assert_serialize(-100);
}

fn assert_serialize(number: i32) {
    assert_ser_tokens(
        &Int::from(number),
        &[Token::NewtypeStruct { name: "Int" }, Token::I64(number as _)],
    )
}

#[test]
fn deserialize() {
    assert_eq!(deserialize_from(100).unwrap(), int!(100));
    assert_eq!(deserialize_from(0).unwrap(), int!(0));
    assert_eq!(deserialize_from(-100).unwrap(), int!(-100));
    assert_eq!(deserialize_from(-9007199254740991i64).unwrap(), Int::MIN);
    assert_eq!(deserialize_from(9007199254740991i64).unwrap(), Int::MAX);
    assert!(deserialize_from(9007199254740992i64).is_err());
    assert!(deserialize_from(-9007199254740992i64).is_err());
}

#[test]
#[cfg_attr(feature = "float_deserialize", ignore)]
fn dont_deserialize_integral_float() {
    assert!(deserialize_from(-10.0).is_err());
    assert!(deserialize_from(-0.0).is_err());
    assert!(deserialize_from(1.0).is_err());
    assert!(deserialize_from(9007199254740991.0).is_err());
    assert!(deserialize_from(9007199254740992.0).is_err());
}

#[test]
#[cfg_attr(feature = "lax_deserialize", ignore)]
fn dont_deserialize_fractional_float() {
    assert!(deserialize_from(0.5).is_err());
    assert!(deserialize_from(42.1337).is_err());
    assert!(deserialize_from(-42.1337).is_err());
}

#[test]
#[cfg_attr(not(feature = "float_deserialize"), ignore)]
fn deserialize_integral_float() {
    assert_eq!(deserialize_from(-10.0).unwrap(), int!(-10));
    assert_eq!(deserialize_from(-0.0).unwrap(), int!(0));
    assert_eq!(deserialize_from(1.0).unwrap(), int!(1));
    assert_eq!(deserialize_from(9007199254740991.0).unwrap(), Int::MAX);
    assert!(deserialize_from(9007199254740992.0).is_err());
    // NOTE: This still ends up as integral because the .49 exceeds the representable range of f64
    assert_eq!(
        deserialize_from(9007199254740991.49).unwrap(),
        Int::try_from(9007199254740991i64).unwrap()
    );

    assert!(deserialize_from(f64::NAN).is_err());
    assert!(deserialize_from(f64::INFINITY).is_err());
    assert!(deserialize_from(f64::NEG_INFINITY).is_err());
}

#[test]
#[cfg_attr(not(feature = "lax_deserialize"), ignore)]
fn deserialize_fractional_float() {
    assert_eq!(deserialize_from(0.5).unwrap(), int!(0));
    assert_eq!(deserialize_from(42.1337).unwrap(), int!(42));
    assert_eq!(deserialize_from(-42.1337).unwrap(), int!(-42));
}

fn deserialize_from<'de, Value: IntoDeserializer<'de>>(
    value: Value,
) -> Result<Int, serde::de::value::Error> {
    Int::deserialize(value.into_deserializer())
}
