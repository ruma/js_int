use core::{
    fmt::{self, Debug, Display, Formatter},
    num::ParseIntError as StdParseIntError,
};

/// The error type returned when when parsing an integer fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseIntError {
    pub(crate) kind: ParseIntErrorKind,
}

// When https://github.com/rust-lang/rust/issues/22639 is resolved, the error kind can be provided
// publicly as well. For now, distinguishing between overflow / underflow and anything else doesn't
// seem very useful.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ParseIntErrorKind {
    Overflow,
    Underflow,
    Unknown(StdParseIntError),
}

impl From<StdParseIntError> for ParseIntError {
    fn from(e: StdParseIntError) -> Self {
        ParseIntError { kind: ParseIntErrorKind::Unknown(e) }
    }
}

impl Display for ParseIntError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match &self.kind {
            ParseIntErrorKind::Overflow => f.write_str("number too large to fit in target type"),
            ParseIntErrorKind::Underflow => f.write_str("number too small to fit in target type"),
            ParseIntErrorKind::Unknown(e) => write!(f, "{}", e),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseIntError {}

/// The error type returned when a checked integral type conversion fails.
#[derive(Clone)]
pub struct TryFromIntError {
    _private: (),
}

impl TryFromIntError {
    pub(crate) fn new() -> Self {
        Self { _private: () }
    }
}

impl Display for TryFromIntError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("out of range integral type conversion attempted")
    }
}

impl Debug for TryFromIntError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("TryFromIntError")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TryFromIntError {}
