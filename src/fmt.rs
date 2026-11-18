//! `Display` (exact decimal expansion, honours precision, width, fill,
//! alignment, `+` and `0` flags) and `Debug` (value plus raw bits in hex).
//!
//! A binary fraction with `F` bits always has a finite decimal expansion of at
//! most `F` digits, so without a precision the output is exact. With a
//! precision the value is rounded to nearest, ties to even, like the standard
//! floating-point formatting.

use core::fmt::{self, Write};

const MAX_INT_DIGITS: usize = 20;
const MAX_FRAC_DIGITS: usize = 32;

/// Adds one unit of the last place to the ASCII decimal digits; `true` when
/// the carry leaves the first digit (every digit was 9 and is now 0).
fn increment(digits: &mut [u8]) -> bool {
    for d in digits.iter_mut().rev() {
        if *d == b'9' {
            *d = b'0';
        } else {
            *d += 1;
            return false;
        }
    }
    true
}

/// Writes `±magnitude / 2^frac_bits` for `magnitude ≤ 2^63` and
/// `1 ≤ frac_bits ≤ 32`, so every step fits `u64`: `frac · 10 < 2^36`. The
/// integer digits end at `MAX_INT_DIGITS`, the buffer holds `.` there, and the
/// fraction digits follow from `frac_start`; one `write_str` writes them.
pub(crate) fn write_fixed(
    f: &mut fmt::Formatter<'_>,
    negative: bool,
    magnitude: u64,
    frac_bits: u32,
) -> fmt::Result {
    let mask = (1u64 << frac_bits) - 1;
    let mut int = magnitude >> frac_bits;
    let mut frac = magnitude & mask;

    let mut buf = [b'.'; MAX_INT_DIGITS + 1 + MAX_FRAC_DIGITS];
    let frac_start = MAX_INT_DIGITS + 1;
    let mut n = 0usize;
    let mut zeros = 0usize;

    match f.precision() {
        None => {
            while frac != 0 {
                frac *= 10;
                buf[frac_start + n] = b'0' + (frac >> frac_bits) as u8;
                frac &= mask;
                n += 1;
            }
        }
        Some(p) => {
            let exact = frac_bits as usize;
            let take = if p < exact { p } else { exact };
            while n < take {
                frac *= 10;
                buf[frac_start + n] = b'0' + (frac >> frac_bits) as u8;
                frac &= mask;
                n += 1;
            }
            if p > take {
                zeros = p - take;
            } else {
                let half = 1u64 << (frac_bits - 1);
                let last_odd = if n > 0 {
                    buf[frac_start + n - 1] & 1 == 1
                } else {
                    int & 1 == 1
                };
                if (frac > half || (frac == half && last_odd))
                    && increment(&mut buf[frac_start..frac_start + n])
                {
                    int += 1;
                }
            }
        }
    }

    let mut first = MAX_INT_DIGITS;
    loop {
        first -= 1;
        buf[first] = b'0' + (int % 10) as u8;
        int /= 10;
        if int == 0 {
            break;
        }
    }
    let has_dot = n > 0 || zeros > 0;
    let last = if has_dot {
        frac_start + n
    } else {
        MAX_INT_DIGITS
    };
    let body = match core::str::from_utf8(&buf[first..last]) {
        Ok(body) => body,
        Err(_) => return Err(fmt::Error),
    };

    let sign = if negative {
        "-"
    } else if f.sign_plus() {
        "+"
    } else {
        ""
    };
    let len = sign.len() + body.len() + zeros;
    let pad = f.width().unwrap_or(0).saturating_sub(len);
    let fill = f.fill();
    let (pre, post, zero_pad) = if f.sign_aware_zero_pad() {
        (0, 0, pad)
    } else {
        match f.align() {
            Some(fmt::Alignment::Left) => (0, pad, 0),
            Some(fmt::Alignment::Center) => (pad / 2, pad - pad / 2, 0),
            _ => (pad, 0, 0),
        }
    };

    for _ in 0..pre {
        f.write_char(fill)?;
    }
    f.write_str(sign)?;
    for _ in 0..zero_pad {
        f.write_char('0')?;
    }
    f.write_str(body)?;
    for _ in 0..zeros {
        f.write_char('0')?;
    }
    for _ in 0..post {
        f.write_char(fill)?;
    }
    Ok(())
}

macro_rules! impl_fmt {
    ($Name:ident, $UBits:ty, $NB:literal) => {
        impl core::fmt::Display for $Name {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                crate::fmt::write_fixed(
                    f,
                    self.raw < 0,
                    u64::from(self.raw.unsigned_abs()),
                    Self::FRAC_BITS,
                )
            }
        }

        impl core::fmt::Debug for $Name {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "{} (0x{:0w$x})", self, self.raw as $UBits, w = 2 * $NB)
            }
        }
    };
}
