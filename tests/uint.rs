#![cfg(feature = "serde")]

use core::convert::TryFrom;
use js_int::{uint, UInt};
use serde::{de::IntoDeserializer, Deserialize};
use serde_test::{assert_ser_tokens, Token};

#[test]
fn serialize() {
    assert_serialize(100);
    assert_serialize(0);
}

fn assert_serialize(number: u32) {
    assert_ser_tokens(
        &UInt::from(number),
        &[Token::NewtypeStruct { name: "UInt" }, Token::U64(number as _)],
    )
}

#[test]
fn deserialize() {
    assert_eq!(deserialize_from(100).unwrap(), uint!(100));
    assert_eq!(deserialize_from(0).unwrap(), uint!(0));
    assert_eq!(deserialize_from(9007199254740991i64).unwrap(), UInt::MAX);
    assert!(deserialize_from(9007199254740992i64).is_err());
}

#[test]
#[cfg_attr(feature = "float_deserialize", ignore)]
fn dont_deserialize_integral_float() {
    assert!(deserialize_from(1.0).is_err());
    assert!(deserialize_from(9007199254740991.0).is_err());
    assert!(deserialize_from(9007199254740992.0).is_err());
}

#[test]
#[cfg_attr(feature = "lax_deserialize", ignore)]
fn dont_deserialize_fractional_float() {
    assert!(deserialize_from(0.5).is_err());
    assert!(deserialize_from(42.1337).is_err());
}

#[test]
#[cfg_attr(not(feature = "float_deserialize"), ignore)]
fn deserialize_integral_float() {
    assert_eq!(deserialize_from(1.0).unwrap(), uint!(1));
    assert_eq!(deserialize_from(9007199254740991.0).unwrap(), UInt::MAX);
    assert!(deserialize_from(9007199254740992.0).is_err());
    // NOTE: This still ends up as integral because the .49 exceeds the representable range of f64
    assert_eq!(
        deserialize_from(9007199254740991.49).unwrap(),
        UInt::try_from(9007199254740991i64).unwrap()
    );

    assert!(deserialize_from(f64::NAN).is_err());
    assert!(deserialize_from(f64::INFINITY).is_err());
    assert!(deserialize_from(f64::NEG_INFINITY).is_err());
}

#[test]
#[cfg_attr(not(feature = "lax_deserialize"), ignore)]
fn deserialize_fractional_float() {
    assert_eq!(deserialize_from(0.5).unwrap(), uint!(0));
    assert_eq!(deserialize_from(42.1337).unwrap(), uint!(42));
}

fn deserialize_from<'de, Value: IntoDeserializer<'de>>(
    value: Value,
) -> Result<UInt, serde::de::value::Error> {
    UInt::deserialize(value.into_deserializer())
}
