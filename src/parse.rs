//! Exact decimal parsing, rounded to nearest with ties toward `+∞`.
//!
//! Grammar: `[+-]? digits? ('.' digits?)?` with at least one digit; no
//! exponent. `ff8!` … `ff64!` additionally accept `_` between digits.
//!
//! The fractional digits are converted exactly: the decimal fraction is doubled
//! `F + 1` times, each carry out of the first digit is the next binary digit.
//! Only the first `F + 1` decimal digits can change the rounded result, because
//! every rounding boundary `m / 2^(F+1)` has at most `F + 1` decimal digits;
//! later digits only matter through a "sticky" non-zero flag.

use crate::error::ParseErrorKind;

const MAX_FRAC_BITS: usize = 64;
const INT_CAP: u128 = 1 << 63;

pub(crate) const fn parse_magnitude(
    s: &[u8],
    frac_bits: u32,
    underscores: bool,
    negate: bool,
) -> Result<(bool, u128), ParseErrorKind> {
    let len = s.len();
    let mut i = 0usize;
    let mut negative = negate;
    if len > 0 && (s[0] == b'-' || s[0] == b'+') {
        if negate {
            return Err(ParseErrorKind::InvalidDigit);
        }
        negative = s[0] == b'-';
        i = 1;
    }
    let body_start = i;

    let mut any_digit = false;
    let mut int: u128 = 0;
    let mut int_overflow = false;
    while i < len {
        let c = s[i];
        if c >= b'0' && c <= b'9' {
            any_digit = true;
            if !int_overflow {
                int = int * 10 + (c - b'0') as u128;
                if int > INT_CAP {
                    int_overflow = true;
                }
            }
        } else if !(c == b'_' && underscores && any_digit) {
            break;
        }
        i += 1;
    }

    let keep = frac_bits as usize + 1;
    let mut digits = [0u8; MAX_FRAC_BITS + 1];
    let mut k = 0usize;
    let mut sticky = false;
    if i < len && s[i] == b'.' {
        i += 1;
        let frac_start = i;
        while i < len {
            let c = s[i];
            if c >= b'0' && c <= b'9' {
                any_digit = true;
                let d = c - b'0';
                if k < keep {
                    digits[k] = d;
                    k += 1;
                } else if d != 0 {
                    sticky = true;
                }
            } else if !(c == b'_' && underscores && i > frac_start) {
                return Err(ParseErrorKind::InvalidDigit);
            }
            i += 1;
        }
    }
    if i < len {
        return Err(ParseErrorKind::InvalidDigit);
    }
    if !any_digit {
        return Err(if body_start == len {
            ParseErrorKind::Empty
        } else {
            ParseErrorKind::InvalidDigit
        });
    }
    if int_overflow {
        return Err(ParseErrorKind::Overflow);
    }

    let mut bits: u128 = 0;
    let mut b = 0usize;
    while b < keep {
        let mut carry = 0u8;
        let mut j = k;
        while j > 0 {
            j -= 1;
            let v = digits[j] * 2 + carry;
            if v >= 10 {
                digits[j] = v - 10;
                carry = 1;
            } else {
                digits[j] = v;
                carry = 0;
            }
        }
        bits = (bits << 1) | carry as u128;
        b += 1;
    }
    let mut j = 0usize;
    while j < k {
        if digits[j] != 0 {
            sticky = true;
        }
        j += 1;
    }

    let half = bits & 1 == 1;
    let up = if negative { half && sticky } else { half };
    let magnitude = (int << frac_bits) + (bits >> 1) + up as u128;
    Ok((negative, magnitude))
}

macro_rules! impl_parse {
    ($Name:ident, $Bits:ty, $F:literal) => {
        impl $Name {
            const fn parse_bytes(
                s: &[u8],
                underscores: bool,
                negate: bool,
            ) -> Result<Self, crate::ParseError> {
                match crate::parse::parse_magnitude(s, $F, underscores, negate) {
                    Err(kind) => Err(crate::ParseError::new(kind)),
                    Ok((negative, magnitude)) => {
                        let max = <$Bits>::MAX as u128;
                        if negative {
                            if magnitude > max + 1 {
                                Err(crate::ParseError::new(crate::ParseErrorKind::Overflow))
                            } else {
                                Ok(Self {
                                    raw: (magnitude as $Bits).wrapping_neg(),
                                })
                            }
                        } else if magnitude > max {
                            Err(crate::ParseError::new(crate::ParseErrorKind::Overflow))
                        } else {
                            Ok(Self {
                                raw: magnitude as $Bits,
                            })
                        }
                    }
                }
            }

            /// Parses a decimal string such as `"-12.625"`, exactly, rounding
            /// to nearest with ties toward `+∞`. No exponent, no `_`.
            #[inline]
            pub const fn parse(s: &str) -> Result<Self, crate::ParseError> {
                Self::parse_bytes(s.as_bytes(), false, false)
            }

            #[doc(hidden)]
            pub const fn __lit(s: &str, negate: bool) -> Self {
                match Self::parse_bytes(s.as_bytes(), true, negate) {
                    Ok(v) => v,
                    Err(_) => panic!("invalid or out of range fixed-point literal"),
                }
            }
        }

        impl core::str::FromStr for $Name {
            type Err = crate::ParseError;
            #[inline]
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                Self::parse(s)
            }
        }
    };
}
