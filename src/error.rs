//! Error type for the crate.

use core::{
    fmt::{self, Display},
    result,
};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::boxed::Box;
#[cfg(feature = "std")]
use std::{boxed::Box, error};

/// Alias for a [`Result`][result::Result] with an [Error] error type.
pub type Result<T> = result::Result<T, Error>;

/// Errors when evaluating a query.
pub struct Error {
    inner: Box<ErrorImpl>,
}

impl Error {
    /// Constructs an error with the kind.
    #[must_use]
    #[inline]
    fn new(kind: ErrorKind) -> Self {
        Self {
            inner: Box::new(ErrorImpl { kind }),
        }
    }

    #[must_use]
    #[inline]
    pub(crate) fn with_kind(kind: ErrorKind) -> Self {
        Self::new(kind)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.inner, f)
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.inner, f)
    }
}

struct ErrorImpl {
    kind: ErrorKind,
}

impl Display for ErrorImpl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.kind, f)
    }
}

impl fmt::Debug for ErrorImpl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Error").field("kind", &self.kind).finish()
    }
}

/// All possible crate errors.
#[allow(clippy::module_name_repetitions)]
pub(crate) enum ErrorKind {
    /// Cannot convert to a bool
    InvalidBoolValue,
    /// Cannot convert to a number ID
    InvalidNumId,
    /// Cannot convert to a string ID
    InvalidStringId,
}

#[cfg(feature = "std")]
impl error::Error for ErrorKind {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            ErrorKind::InvalidBoolValue | ErrorKind::InvalidNumId | ErrorKind::InvalidStringId => {
                None
            }
        }
    }
}

impl Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::InvalidBoolValue => f.write_str("should be a boolean reference"),
            ErrorKind::InvalidNumId => f.write_str("should be a number reference ID"),
            ErrorKind::InvalidStringId => f.write_str("should be a string reference ID"),
        }
    }
}

impl fmt::Debug for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::InvalidBoolValue => f.write_str("should be a boolean reference"),
            ErrorKind::InvalidNumId => f.write_str("should be a number reference ID"),
            ErrorKind::InvalidStringId => f.write_str("should be a string reference ID"),
        }
    }
}
