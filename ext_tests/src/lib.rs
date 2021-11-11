#[cfg(test)]
mod tests {
    use serde::{de::IntoDeserializer, Deserialize};
    use serde_json::{from_str as from_json_str, to_string as to_json_string};

    use js_int::{int, uint, Int, UInt};

    #[test]
    fn serialize_int() {
        assert_eq!(to_json_string(&int!(100)).unwrap(), "100");
        assert_eq!(to_json_string(&int!(0)).unwrap(), "0");
        assert_eq!(to_json_string(&int!(-100)).unwrap(), "-100");
    }

    #[test]
    fn deserialize_int() {
        assert_eq!(deserialize_int_from(100).unwrap(), int!(100));
        assert_eq!(deserialize_int_from(0).unwrap(), int!(0));
        assert_eq!(deserialize_int_from(-100).unwrap(), int!(-100));
        assert_eq!(deserialize_int_from(-9007199254740991i64).unwrap(), Int::MIN);
        assert_eq!(deserialize_int_from(9007199254740991i64).unwrap(), Int::MAX);
        assert!(deserialize_int_from(9007199254740992i64).is_err());
        assert!(deserialize_int_from(-9007199254740992i64).is_err());
    }

    #[test]
    fn serialize_uint() {
        assert_eq!(to_json_string(&uint!(100)).unwrap(), "100");
        assert_eq!(to_json_string(&uint!(0)).unwrap(), "0");
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
    fn strict_deserialize_int() {
        assert!(deserialize_int_from(-10.0).is_err());
        assert!(deserialize_int_from(-0.0).is_err());
        assert!(deserialize_int_from(0.5).is_err());
        assert!(deserialize_int_from(1.0).is_err());
        assert!(deserialize_int_from(9007199254740991.0).is_err());
        assert!(deserialize_int_from(9007199254740991.49).is_err());
        assert!(deserialize_int_from(9007199254740992.0).is_err());
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
    fn lax_deserialize_int() {
        assert_eq!(deserialize_int_from(-10.0).unwrap(), int!(-10));
        assert_eq!(deserialize_int_from(-0.0).unwrap(), int!(0));
        assert_eq!(deserialize_int_from(0.5).unwrap(), int!(0));
        assert_eq!(deserialize_int_from(1.0).unwrap(), int!(1));
        assert_eq!(deserialize_int_from(9007199254740991.0).unwrap(), Int::MAX);
        assert_eq!(deserialize_int_from(9007199254740991.49).unwrap(), Int::MAX);
        assert!(deserialize_int_from(9007199254740992.0).is_err());

        assert!(deserialize_int_from(f64::NAN).is_err());
        assert!(deserialize_int_from(f64::INFINITY).is_err());
        assert!(deserialize_int_from(f64::NEG_INFINITY).is_err());
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

    fn deserialize_int_from<'de, Value: IntoDeserializer<'de>>(
        value: Value,
    ) -> Result<Int, serde::de::value::Error> {
        Int::deserialize(value.into_deserializer())
    }

    fn deserialize_uint_from<'de, Value: IntoDeserializer<'de>>(
        value: Value,
    ) -> Result<UInt, serde::de::value::Error> {
        UInt::deserialize(value.into_deserializer())
    }
}
