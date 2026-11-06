//! Error types.

use core::fmt;

/// What went wrong while parsing a decimal string.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ParseErrorKind {
    /// The input is empty or has no digits.
    Empty,
    /// The input contains a character that is not part of a decimal number.
    InvalidDigit,
    /// The value does not fit into the target type.
    Overflow,
}

/// Error returned when parsing a fixed-point number from a string fails.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ParseError {
    kind: ParseErrorKind,
}

impl ParseError {
    pub(crate) const fn new(kind: ParseErrorKind) -> Self {
        Self { kind }
    }

    /// The reason of the failure.
    pub const fn kind(&self) -> ParseErrorKind {
        self.kind
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self.kind {
            ParseErrorKind::Empty => "cannot parse fixed-point number from empty string",
            ParseErrorKind::InvalidDigit => "invalid digit found in fixed-point number",
            ParseErrorKind::Overflow => "fixed-point number out of range",
        })
    }
}

/// Error returned when a value does not fit into the target type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct OverflowError;

impl fmt::Display for OverflowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("value out of range of the target fixed-point type")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {}

#[cfg(feature = "std")]
impl std::error::Error for OverflowError {}
