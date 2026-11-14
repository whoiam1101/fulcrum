//! `serde`: exact decimal strings in human-readable formats (JSON), the raw
//! integer in binary formats (bincode); integers are accepted exactly,
//! floating-point numbers only with `float-convert`.

#![cfg(feature = "serde")]

use fulcrum::{ff16, ff64, ff8, FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};

#[test]
fn json_is_the_exact_decimal_string() {
    let x = ff64!(12.5);
    assert_eq!(serde_json::to_string(&x).unwrap(), "\"12.5\"");
    assert_eq!(
        serde_json::to_string(&ff64!(0.1)).unwrap(),
        "\"0.1000000000931322574615478515625\""
    );
    assert_eq!(serde_json::to_string(&ff8!(-1.25)).unwrap(), "\"-1.25\"");
}

#[test]
fn json_round_trips_every_fixed16_value() {
    for raw in i16::MIN..=i16::MAX {
        let x = FixedFloat16::from_bits(raw);
        let text = serde_json::to_string(&x).unwrap();
        assert_eq!(
            serde_json::from_str::<FixedFloat16>(&text).unwrap(),
            x,
            "{}",
            text
        );
    }
}

#[test]
fn json_accepts_decimal_strings_and_integers() {
    assert_eq!(
        serde_json::from_str::<FixedFloat64>("\"12.6\"").unwrap(),
        ff64!(12.6)
    );
    assert_eq!(
        serde_json::from_str::<FixedFloat64>("-7").unwrap(),
        ff64!(-7)
    );
    assert_eq!(serde_json::from_str::<FixedFloat8>("7").unwrap(), ff8!(7));
    assert!(serde_json::from_str::<FixedFloat8>("8").is_err());
    assert!(serde_json::from_str::<FixedFloat8>("\"8\"").is_err());
    assert!(serde_json::from_str::<FixedFloat32>("\"1.2.3\"").is_err());
    assert!(serde_json::from_str::<FixedFloat32>("true").is_err());
    assert!(serde_json::from_str::<FixedFloat32>("18446744073709551615").is_err());
}

#[cfg(not(feature = "float-convert"))]
#[test]
fn json_rejects_float_numbers_without_float_convert() {
    assert!(serde_json::from_str::<FixedFloat64>("12.6").is_err());
    assert!(serde_json::from_str::<FixedFloat64>("0.5").is_err());
}

#[cfg(feature = "float-convert")]
#[test]
fn json_float_numbers_round_like_from_f64() {
    assert_eq!(
        serde_json::from_str::<FixedFloat64>("12.6").unwrap(),
        FixedFloat64::checked_from_f64(12.6).unwrap()
    );
    assert_eq!(
        serde_json::from_str::<FixedFloat16>("0.5").unwrap(),
        ff16!(0.5)
    );
    assert!(serde_json::from_str::<FixedFloat8>("8.0").is_err());
}

#[test]
fn binary_is_the_raw_integer() {
    let x = ff64!(-1.25);
    let bytes = bincode::serialize(&x).unwrap();
    assert_eq!(bytes, bincode::serialize(&x.to_bits()).unwrap());
    assert_eq!(bytes, x.to_le_bytes());
    assert_eq!(bincode::deserialize::<FixedFloat64>(&bytes).unwrap(), x);
    for raw in i8::MIN..=i8::MAX {
        let x = FixedFloat8::from_bits(raw);
        let bytes = bincode::serialize(&x).unwrap();
        assert_eq!(bytes, [raw as u8]);
        assert_eq!(bincode::deserialize::<FixedFloat8>(&bytes).unwrap(), x);
    }
}

#[test]
fn inside_a_struct() {
    #[derive(serde::Serialize, serde::Deserialize, PartialEq, Debug)]
    struct Unit {
        x: FixedFloat32,
        speed: FixedFloat64,
    }
    let u = Unit {
        x: FixedFloat32::from_bits(-3),
        speed: ff64!(12.6),
    };
    let json = serde_json::to_string(&u).unwrap();
    assert_eq!(serde_json::from_str::<Unit>(&json).unwrap(), u);
    let bin = bincode::serialize(&u).unwrap();
    assert_eq!(bin.len(), 12);
    assert_eq!(bincode::deserialize::<Unit>(&bin).unwrap(), u);
}
