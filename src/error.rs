//! Error type for the crate.

use core::{
    fmt::{self, Display},
    result,
};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::boxed::Box;
#[cfg(feature = "std")]
use std::{boxed::Box, error};

use crate::utils::QueryResultError;

/// Alias for a [`Result`][result::Result] with an [Error] error type.
pub type Result<T> = result::Result<T, Error>;

/// Errors when evaluating a query.
#[derive(PartialEq)]
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

    #[cfg(test)]
    #[must_use]
    #[inline]
    pub(crate) fn is_schema_error(&self) -> bool {
        match self.inner.kind {
            ErrorKind::InvalidBoolValue
            | ErrorKind::InvalidNumId
            | ErrorKind::InvalidStringId
            | ErrorKind::InvalidScalarId
            | ErrorKind::QueryResultError(_)
            | ErrorKind::MultipleMatchingFacts
            | ErrorKind::DuplicateSchema => false,
            ErrorKind::UnknownPredicate | ErrorKind::MismatchSchemaTys => true,
        }
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

impl From<QueryResultError> for Error {
    fn from(value: QueryResultError) -> Self {
        Self::with_kind(ErrorKind::QueryResultError(value))
    }
}

#[derive(PartialEq)]
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
#[derive(PartialEq)]
pub(crate) enum ErrorKind {
    /// Cannot convert to a bool
    InvalidBoolValue,
    /// Cannot convert to a number ID
    InvalidNumId,
    /// Cannot convert to a string ID
    InvalidStringId,
    /// Cannot convert to a scalar ID
    InvalidScalarId,
    /// Query result error
    QueryResultError(QueryResultError),
    /// If there are multiple matching facts
    MultipleMatchingFacts,
    /// If a schema has already been added for a predicate
    DuplicateSchema,
    /// If a predicate is not in the schema
    UnknownPredicate,
    /// The given types do not match the schema
    MismatchSchemaTys,
}

#[cfg(feature = "std")]
impl error::Error for ErrorKind {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            ErrorKind::InvalidBoolValue
            | ErrorKind::InvalidNumId
            | ErrorKind::InvalidStringId
            | ErrorKind::InvalidScalarId
            | ErrorKind::MultipleMatchingFacts
            | ErrorKind::DuplicateSchema
            | ErrorKind::UnknownPredicate
            | ErrorKind::MismatchSchemaTys => None,
            ErrorKind::QueryResultError(e) => Some(e),
        }
    }
}

impl Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::InvalidBoolValue => f.write_str("should be a boolean reference"),
            ErrorKind::InvalidNumId => f.write_str("should be a number reference ID"),
            ErrorKind::InvalidStringId => f.write_str("should be a string reference ID"),
            ErrorKind::InvalidScalarId => f.write_str("should be a scalar reference ID"),
            ErrorKind::MultipleMatchingFacts => f.write_str("should be a single matching fact"),
            ErrorKind::QueryResultError(e) => Display::fmt(e, f),
            ErrorKind::DuplicateSchema => {
                f.write_str("schema for predicate should only be added once")
            }
            ErrorKind::UnknownPredicate => f.write_str("predicate should be in the schema"),
            ErrorKind::MismatchSchemaTys => f.write_str("types should match schema"),
        }
    }
}

impl fmt::Debug for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::InvalidBoolValue => f.write_str("should be a boolean reference"),
            ErrorKind::InvalidNumId => f.write_str("should be a number reference ID"),
            ErrorKind::InvalidStringId => f.write_str("should be a string reference ID"),
            ErrorKind::InvalidScalarId => f.write_str("should be a scalar reference ID"),
            ErrorKind::MultipleMatchingFacts => f.write_str("should be a single matching fact"),
            ErrorKind::QueryResultError(e) => fmt::Debug::fmt(e, f),
            ErrorKind::DuplicateSchema => {
                f.write_str("schema for predicate should only be added once")
            }
            ErrorKind::UnknownPredicate => f.write_str("predicate should be in the schema"),
            ErrorKind::MismatchSchemaTys => f.write_str("types should match schema"),
        }
    }
}
