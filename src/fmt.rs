//! `Display` (exact decimal expansion, honours precision, width, fill,
//! alignment, `+` and `0` flags) and `Debug` (value plus raw bits in hex).
//!
//! A binary fraction with `F` bits always has a finite decimal expansion of at
//! most `F` digits, so without a precision the output is exact. With a
//! precision the value is rounded to nearest, ties to even, like the standard
//! floating-point formatting.

use core::fmt::{self, Write};

const MAX_FRAC_DIGITS: usize = 64;
const MAX_INT_DIGITS: usize = 40;

pub(crate) fn write_fixed(
    f: &mut fmt::Formatter<'_>,
    negative: bool,
    magnitude: u128,
    frac_bits: u32,
) -> fmt::Result {
    let mask = (1u128 << frac_bits) - 1;
    let mut int = magnitude >> frac_bits;
    let mut frac = magnitude & mask;

    let mut digits = [0u8; MAX_FRAC_DIGITS];
    let mut n = 0usize;
    let mut zeros = 0usize;

    match f.precision() {
        None => {
            while frac != 0 {
                frac *= 10;
                digits[n] = (frac >> frac_bits) as u8;
                frac &= mask;
                n += 1;
            }
        }
        Some(p) => {
            let exact = frac_bits as usize;
            let take = if p < exact { p } else { exact };
            while n < take {
                frac *= 10;
                digits[n] = (frac >> frac_bits) as u8;
                frac &= mask;
                n += 1;
            }
            if p > take {
                zeros = p - take;
            } else {
                let half = 1u128 << (frac_bits - 1);
                let last_odd = if n > 0 {
                    digits[n - 1] & 1 == 1
                } else {
                    int & 1 == 1
                };
                if frac > half || (frac == half && last_odd) {
                    let mut i = n;
                    let mut carry = true;
                    while carry && i > 0 {
                        i -= 1;
                        if digits[i] == 9 {
                            digits[i] = 0;
                        } else {
                            digits[i] += 1;
                            carry = false;
                        }
                    }
                    if carry {
                        int += 1;
                    }
                }
            }
        }
    }

    let mut int_digits = [0u8; MAX_INT_DIGITS];
    let mut il = 0usize;
    loop {
        int_digits[il] = b'0' + (int % 10) as u8;
        int /= 10;
        il += 1;
        if int == 0 {
            break;
        }
    }

    let sign = if negative {
        "-"
    } else if f.sign_plus() {
        "+"
    } else {
        ""
    };
    let has_dot = n > 0 || zeros > 0;
    let len = sign.len() + il + has_dot as usize + n + zeros;
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
    for i in (0..il).rev() {
        f.write_char(int_digits[i] as char)?;
    }
    if has_dot {
        f.write_char('.')?;
        for &d in &digits[..n] {
            f.write_char((b'0' + d) as char)?;
        }
        for _ in 0..zeros {
            f.write_char('0')?;
        }
    }
    for _ in 0..post {
        f.write_char(fill)?;
    }
    Ok(())
}

macro_rules! impl_fmt {
    ($Name:ident, $UBits:ty, $NB:literal) => {
        impl core::fmt::Display for $Name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                crate::fmt::write_fixed(
                    f,
                    self.raw < 0,
                    self.raw.unsigned_abs() as u128,
                    Self::FRAC_BITS,
                )
            }
        }

        impl core::fmt::Debug for $Name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "{} (0x{:0w$x})", self, self.raw as $UBits, w = 2 * $NB)
            }
        }
    };
}
