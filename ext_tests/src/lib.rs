#[cfg(test)]
mod tests {
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
        assert_eq!(from_json_str::<Int>("100").unwrap(), int!(100));
        assert_eq!(from_json_str::<Int>("0").unwrap(), int!(0));
        assert_eq!(from_json_str::<Int>("-100").unwrap(), int!(-100));
        assert!(from_json_str::<Int>("9007199254740992").is_err());
        assert!(from_json_str::<Int>("-9007199254740992").is_err());
    }

    #[test]
    fn serialize_uint() {
        assert_eq!(to_json_string(&uint!(100)).unwrap(), "100");
        assert_eq!(to_json_string(&uint!(0)).unwrap(), "0");
    }

    #[test]
    fn deserialize_uint() {
        assert_eq!(from_json_str::<UInt>("100").unwrap(), uint!(100));
        assert_eq!(from_json_str::<UInt>("0").unwrap(), uint!(0));
        assert!(from_json_str::<UInt>("9007199254740992").is_err());
    }
}
