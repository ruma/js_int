#![cfg(feature = "serde")]

use crate::test_serializer::{Number, TestSerializer};
use core::convert::TryFrom;
use js_int::{int, Int};
use serde::{de::IntoDeserializer, Deserialize, Serialize};

mod test_serializer;

#[test]
fn serialize() {
    assert_serialize(100);
    assert_serialize(0);
    assert_serialize(-100);
}

fn assert_serialize(number: i32) {
    let serialized = Int::from(number).serialize(TestSerializer).expect("Failed to serialize UInt");

    assert_eq!(Number::I64(number.into()), serialized);
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
fn dont_deserialize_integral_float() {
    assert!(deserialize_from(-10.0).is_err());
    assert!(deserialize_from(-0.0).is_err());
    assert!(deserialize_from(1.0).is_err());
    assert!(deserialize_from(9007199254740991.0).is_err());
    assert!(deserialize_from(9007199254740992.0).is_err());
}

#[test]
fn dont_deserialize_fractional_float() {
    assert!(deserialize_from(0.5).is_err());
    assert!(deserialize_from(42.1337).is_err());
    assert!(deserialize_from(-42.1337).is_err());
}

#[test]
fn deserialize_integral_float() {
    assert_eq!(deserialize_via_float(-10.0).unwrap(), int!(-10));
    assert_eq!(deserialize_via_float(-0.0).unwrap(), int!(0));
    assert_eq!(deserialize_via_float(1.0).unwrap(), int!(1));
    assert_eq!(deserialize_via_float(9007199254740991.0).unwrap(), Int::MAX);
    assert!(deserialize_via_float(9007199254740992.0).is_err());
    // NOTE: This still ends up as integral because the .49 exceeds the representable range of f64
    assert_eq!(
        deserialize_via_float(9007199254740991.49).unwrap(),
        Int::try_from(9007199254740991i64).unwrap()
    );

    assert!(deserialize_via_float(f64::NAN).is_err());
    assert!(deserialize_via_float(f64::INFINITY).is_err());
    assert!(deserialize_via_float(f64::NEG_INFINITY).is_err());

    fn deserialize_via_float<'de, Value: IntoDeserializer<'de>>(
        value: Value,
    ) -> Result<Int, serde::de::value::Error> {
        Int::deserialize_via_float(value.into_deserializer())
    }
}

fn deserialize_from<'de, Value: IntoDeserializer<'de>>(
    value: Value,
) -> Result<Int, serde::de::value::Error> {
    Int::deserialize(value.into_deserializer())
}
