//! `serde` support, behind the `serde` feature.
//!
//! Human-readable formats (JSON, YAML, TOML) get the exact decimal string of
//! `Display`, such as `"12.6"` for `ff64!(12.6)` written with its full
//! expansion; parsing it back gives the same bits. They also accept an
//! integer number, converted exactly, and, only together with the
//! `float-convert` feature, a floating-point number (a YAML or JSON number
//! without quotes), rounded like `checked_from_f64`. Binary formats get the
//! raw storage integer.

macro_rules! impl_serde {
    ($Name:ident, $Bits:ty) => {
        impl serde::Serialize for $Name {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                if serializer.is_human_readable() {
                    serializer.collect_str(self)
                } else {
                    serde::Serialize::serialize(&self.raw, serializer)
                }
            }
        }

        impl<'de> serde::Deserialize<'de> for $Name {
            fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                struct Visitor;

                impl<'de> serde::de::Visitor<'de> for Visitor {
                    type Value = $Name;

                    fn expecting(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                        f.write_str(concat!(
                            "a decimal string such as \"12.6\" or an integer in the range of ",
                            stringify!($Name)
                        ))
                    }

                    fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<$Name, E> {
                        v.parse().map_err(E::custom)
                    }

                    fn visit_i64<E: serde::de::Error>(self, v: i64) -> Result<$Name, E> {
                        $Name::checked_from_int(v as i128)
                            .ok_or_else(|| E::custom(crate::OverflowError))
                    }

                    fn visit_u64<E: serde::de::Error>(self, v: u64) -> Result<$Name, E> {
                        $Name::checked_from_int(v as i128)
                            .ok_or_else(|| E::custom(crate::OverflowError))
                    }

                    #[cfg(feature = "float-convert")]
                    serde_visit_float!($Name);
                }

                if deserializer.is_human_readable() {
                    deserializer.deserialize_any(Visitor)
                } else {
                    <$Bits as serde::Deserialize>::deserialize(deserializer).map($Name::from_bits)
                }
            }
        }
    };
}
