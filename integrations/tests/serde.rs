//! `serde`: exact decimal strings in human-readable formats (JSON), the raw
//! integer in binary formats (postcard); integers are accepted exactly,
//! floating-point numbers only with `float-convert`.

#![cfg(feature = "serde")]

use fulcrum::{ff64, ff8, FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};

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
        fulcrum::ff16!(0.5)
    );
    assert!(serde_json::from_str::<FixedFloat8>("8.0").is_err());
}

#[test]
fn binary_is_the_raw_integer() {
    let x = ff64!(-1.25);
    let bytes = postcard::to_stdvec(&x).unwrap();
    assert_eq!(bytes, postcard::to_stdvec(&x.to_bits()).unwrap());
    assert_eq!(postcard::from_bytes::<FixedFloat64>(&bytes).unwrap(), x);
    for raw in i8::MIN..=i8::MAX {
        let x = FixedFloat8::from_bits(raw);
        let bytes = postcard::to_stdvec(&x).unwrap();
        assert_eq!(bytes, [raw as u8]);
        assert_eq!(postcard::from_bytes::<FixedFloat8>(&bytes).unwrap(), x);
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
    let bin = postcard::to_stdvec(&u).unwrap();
    let raws = postcard::to_stdvec(&(u.x.to_bits(), u.speed.to_bits())).unwrap();
    assert_eq!(bin, raws);
    assert_eq!(postcard::from_bytes::<Unit>(&bin).unwrap(), u);
}

#[test]
fn vectors_are_tuples_of_components() {
    use fulcrum::{ff32, Vec2f32, Vec3f64};
    let v = Vec2f32::new(ff32!(1.5), ff32!(-2));
    assert_eq!(serde_json::to_string(&v).unwrap(), "[\"1.5\",\"-2\"]");
    assert_eq!(serde_json::from_str::<Vec2f32>("[\"1.5\", -2]").unwrap(), v);
    assert!(serde_json::from_str::<Vec2f32>("[\"1.5\"]").is_err());
    let w = Vec3f64::new(ff64!(0.1), ff64!(-7), FixedFloat64::MIN);
    let text = serde_json::to_string(&w).unwrap();
    assert_eq!(serde_json::from_str::<Vec3f64>(&text).unwrap(), w);
    let bytes = postcard::to_stdvec(&w).unwrap();
    assert_eq!(postcard::from_bytes::<Vec3f64>(&bytes).unwrap(), w);
    let bytes = postcard::to_stdvec(&v).unwrap();
    assert_eq!(postcard::from_bytes::<Vec2f32>(&bytes).unwrap(), v);
}
