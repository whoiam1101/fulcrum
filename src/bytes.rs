//! Stable serialization: the raw value as little- or big-endian bytes.
//! The layout never depends on the platform.

macro_rules! impl_bytes {
    ($Name:ident, $Bits:ty, $NB:literal) => {
        impl $Name {
            /// Raw value as little-endian bytes. This is the canonical format
            /// for snapshots, replays and checksums.
            #[inline]
            pub const fn to_le_bytes(self) -> [u8; $NB] {
                self.raw.to_le_bytes()
            }

            /// Inverse of [`Self::to_le_bytes`].
            #[inline]
            pub const fn from_le_bytes(bytes: [u8; $NB]) -> Self {
                Self {
                    raw: <$Bits>::from_le_bytes(bytes),
                }
            }

            /// Raw value as big-endian bytes.
            #[inline]
            pub const fn to_be_bytes(self) -> [u8; $NB] {
                self.raw.to_be_bytes()
            }

            /// Inverse of [`Self::to_be_bytes`].
            #[inline]
            pub const fn from_be_bytes(bytes: [u8; $NB]) -> Self {
                Self {
                    raw: <$Bits>::from_be_bytes(bytes),
                }
            }
        }
    };
}
