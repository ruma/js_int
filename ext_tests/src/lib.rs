#[cfg(test)]
mod tests {
    use core::convert::TryFrom;

    use serde_json::{from_str, to_string};

    use js_int::{Int, UInt};

    #[test]
    fn serialize_int() {
        assert_eq!(to_string(&Int::try_from(100i64).unwrap()).unwrap(), "100");
        assert_eq!(to_string(&Int::try_from(100u64).unwrap()).unwrap(), "100");
        assert_eq!(to_string(&Int::try_from(0i64).unwrap()).unwrap(), "0");
        assert_eq!(to_string(&Int::try_from(0u64).unwrap()).unwrap(), "0");
        assert_eq!(to_string(&Int::try_from(-100i64).unwrap()).unwrap(), "-100");
    }

    #[test]
    fn deserialize_int() {
        assert_eq!(
            from_str::<Int>("100").unwrap(),
            Int::try_from(100i64).unwrap()
        );
        assert_eq!(
            from_str::<Int>("100").unwrap(),
            Int::try_from(100u64).unwrap()
        );
        assert_eq!(from_str::<Int>("0").unwrap(), Int::try_from(0i64).unwrap());
        assert_eq!(from_str::<Int>("0").unwrap(), Int::try_from(0u64).unwrap());
        assert_eq!(
            from_str::<Int>("-100").unwrap(),
            Int::try_from(-100i64).unwrap()
        );
        assert!(from_str::<Int>("9007199254740992").is_err());
        assert!(from_str::<Int>("-9007199254740992").is_err());
    }

    #[test]
    fn serialize_uint() {
        assert_eq!(to_string(&UInt::try_from(100i64).unwrap()).unwrap(), "100");
        assert_eq!(to_string(&UInt::try_from(100u64).unwrap()).unwrap(), "100");
        assert_eq!(to_string(&UInt::try_from(0i64).unwrap()).unwrap(), "0");
        assert_eq!(to_string(&UInt::try_from(0u64).unwrap()).unwrap(), "0");
    }

    #[test]
    fn deserialize_uint() {
        assert_eq!(
            from_str::<UInt>("100").unwrap(),
            UInt::try_from(100i64).unwrap()
        );
        assert_eq!(
            from_str::<UInt>("100").unwrap(),
            UInt::try_from(100u64).unwrap()
        );
        assert_eq!(
            from_str::<UInt>("0").unwrap(),
            UInt::try_from(0i64).unwrap()
        );
        assert_eq!(
            from_str::<UInt>("0").unwrap(),
            UInt::try_from(0u64).unwrap()
        );
        assert!(from_str::<UInt>("9007199254740992").is_err());
    }
}
