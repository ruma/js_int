#![cfg(feature = "serde")]

use js_int::{uint, UInt};
use serde::{de::IntoDeserializer, Deserialize};
use serde_test::{assert_ser_tokens, Token};

#[test]
fn serialize_uint() {
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
fn deserialize_uint() {
    assert_eq!(deserialize_uint_from(100).unwrap(), uint!(100));
    assert_eq!(deserialize_uint_from(0).unwrap(), uint!(0));
    assert_eq!(deserialize_uint_from(9007199254740991i64).unwrap(), UInt::MAX);
    assert!(deserialize_uint_from(9007199254740992i64).is_err());
}

#[test]
#[cfg_attr(feature = "lax_deserialize", ignore)]
fn strict_deserialize_uint() {
    assert!(deserialize_uint_from(0.5).is_err());
    assert!(deserialize_uint_from(1.0).is_err());
    assert!(deserialize_uint_from(9007199254740991.0).is_err());
    assert!(deserialize_uint_from(9007199254740991.49).is_err());
    assert!(deserialize_uint_from(9007199254740992.0).is_err());
}

#[test]
#[cfg_attr(not(feature = "lax_deserialize"), ignore)]
fn lax_deserialize_uint() {
    assert_eq!(deserialize_uint_from(0.5).unwrap(), uint!(0));
    assert_eq!(deserialize_uint_from(1.0).unwrap(), uint!(1));
    assert_eq!(deserialize_uint_from(9007199254740991.0).unwrap(), UInt::MAX);
    assert_eq!(deserialize_uint_from(9007199254740991.49).unwrap(), UInt::MAX);
    assert!(deserialize_uint_from(9007199254740992.0).is_err());

    assert!(deserialize_uint_from(f64::NAN).is_err());
    assert!(deserialize_uint_from(f64::INFINITY).is_err());
    assert!(deserialize_uint_from(f64::NEG_INFINITY).is_err());
}

fn deserialize_uint_from<'de, Value: IntoDeserializer<'de>>(
    value: Value,
) -> Result<UInt, serde::de::value::Error> {
    UInt::deserialize(value.into_deserializer())
}
