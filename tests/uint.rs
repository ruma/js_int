#![cfg(feature = "serde")]
mod test_serializer;

use js_int::{uint, UInt};
use serde::{de::IntoDeserializer, Deserialize, Serialize};

use crate::test_serializer::{Serialized, TestSerializer};

#[test]
fn serialize_uint() {
    assert_eq!(uint!(100).serialize(TestSerializer).unwrap(), Serialized::Unsigned(100));
    assert_eq!(uint!(0).serialize(TestSerializer).unwrap(), Serialized::Unsigned(0));
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
