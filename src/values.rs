//! Values are stored in a `Context` and are indirectly referenced by various
//! identifier types. Values are immutable.
//!
//! # Limitations
//!
//! Values are not constructed during a program's execution. For instance,
//! strings are not concatenated. Values have to be added explicitly to the
//! context before execution via facts or rules.
//!
//! Due to the limitations on a HTTP cookie/header value's length, there is an
//! absolute limit to the amount of data that can be encoded.

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{borrow::Cow, string::String, vec::Vec};
use core::fmt;
#[cfg(feature = "std")]
use std::{borrow::Cow, error, string::String, vec::Vec};

use crate::error::{Error, ErrorKind, Result};

const BOOL_FALSE_INDEX: u16 = 0;
const BOOL_TRUE_INDEX: u16 = 1;
const BYTES_START_INDEX: u16 = 32;
const BYTES_INCLUSIVE_END_INDEX: u16 = 513;
const BYTES_INDEX_RANGE: core::ops::RangeInclusive<u16> =
    BYTES_START_INDEX..=BYTES_INCLUSIVE_END_INDEX;
const NUMBER_START_INDEX: u16 = 514;
const NUMBER_INCLUSIVE_END_INDEX: u16 = 765;
const NUMBER_INDEX_RANGE: core::ops::RangeInclusive<u16> =
    NUMBER_START_INDEX..=NUMBER_INCLUSIVE_END_INDEX;

#[inline]
const fn is_bool_ref(value: u16) -> bool {
    value == BOOL_FALSE_INDEX || value == BOOL_TRUE_INDEX
}

#[inline]
fn is_bytes_ref(value: u16) -> bool {
    BYTES_INDEX_RANGE.contains(&value)
}

#[inline]
fn is_number_ref(value: u16) -> bool {
    NUMBER_INDEX_RANGE.contains(&value)
}

#[inline]
fn is_scalar_ref(value: u16) -> bool {
    is_bool_ref(value) || is_bytes_ref(value) || is_number_ref(value)
}

impl TryFrom<ScalarId> for bool {
    type Error = Error;

    fn try_from(value: ScalarId) -> Result<Self> {
        match value.0 {
            BOOL_FALSE_INDEX => Ok(false),
            BOOL_TRUE_INDEX => Ok(true),
            _ => Err(Error::with_kind(ErrorKind::InvalidBoolValue)),
        }
    }
}

/// An interned bytes reference.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct BytesId(pub(crate) u16);

impl TryFrom<ScalarId> for BytesId {
    type Error = Error;

    fn try_from(value: ScalarId) -> Result<Self> {
        if is_bytes_ref(value.0) {
            Ok(BytesId(value.0))
        } else {
            Err(Error::with_kind(ErrorKind::InvalidBytesId))
        }
    }
}

/// An interned number reference.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct NumId(pub(crate) u16);

impl TryFrom<ScalarId> for NumId {
    type Error = Error;

    fn try_from(value: ScalarId) -> Result<Self> {
        if is_number_ref(value.0) {
            Ok(NumId(value.0))
        } else {
            Err(Error::with_kind(ErrorKind::InvalidNumId))
        }
    }
}

/// A scalar reference.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ScalarId(u16);

impl From<bool> for ScalarId {
    fn from(value: bool) -> Self {
        if value {
            Self(1)
        } else {
            Self(0)
        }
    }
}

impl From<NumId> for ScalarId {
    fn from(value: NumId) -> Self {
        debug_assert!(is_number_ref(value.0));
        Self(value.0)
    }
}

impl From<BytesId> for ScalarId {
    fn from(value: BytesId) -> Self {
        debug_assert!(is_bytes_ref(value.0));
        Self(value.0)
    }
}

impl TryFrom<ConstantId> for ScalarId {
    type Error = Error;

    fn try_from(value: ConstantId) -> Result<Self> {
        if is_scalar_ref(value.0) {
            return Ok(ScalarId(value.0));
        }

        Err(Error::with_kind(ErrorKind::InvalidScalarId))
    }
}

/// A constant reference
#[derive(Debug, Default, Clone, Copy, Hash, PartialEq, Eq)]
pub struct ConstantId(pub(crate) u16);

impl From<bool> for ConstantId {
    fn from(value: bool) -> Self {
        Self(ScalarId::from(value).0)
    }
}

impl From<NumId> for ConstantId {
    fn from(value: NumId) -> Self {
        debug_assert!(is_number_ref(value.0));
        Self(value.0)
    }
}

impl From<BytesId> for ConstantId {
    fn from(value: BytesId) -> Self {
        debug_assert!(is_bytes_ref(value.0));
        Self(value.0)
    }
}

impl From<ScalarId> for ConstantId {
    fn from(value: ScalarId) -> Self {
        Self(value.0)
    }
}

/// A constant value.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Constant<'a> {
    /// Boolean
    Bool(bool),
    /// Number
    Num(i64),
    /// Byte string
    Bytes(Cow<'a, [u8]>),
}

impl<'a> Default for Constant<'a> {
    fn default() -> Self {
        Self::Bool(false)
    }
}

impl<'a> From<bool> for Constant<'a> {
    fn from(value: bool) -> Self {
        Constant::Bool(value)
    }
}

impl<'a> From<i64> for Constant<'a> {
    fn from(value: i64) -> Self {
        Constant::Num(value)
    }
}

impl<'a> From<&'a str> for Constant<'a> {
    fn from(value: &'a str) -> Self {
        Constant::Bytes(Cow::from(value.as_bytes()))
    }
}

impl<'a> From<String> for Constant<'a> {
    fn from(value: String) -> Self {
        Constant::Bytes(Cow::from(value.into_bytes()))
    }
}

impl<'a> From<Cow<'a, str>> for Constant<'a> {
    fn from(value: Cow<'a, str>) -> Self {
        match value {
            Cow::Borrowed(value) => Constant::Bytes(Cow::from(value.as_bytes())),
            Cow::Owned(value) => Constant::Bytes(Cow::from(value.into_bytes())),
        }
    }
}

impl<'a> From<&'a [u8]> for Constant<'a> {
    fn from(value: &'a [u8]) -> Self {
        Constant::Bytes(Cow::from(value))
    }
}

impl<'a> From<Vec<u8>> for Constant<'a> {
    fn from(value: Vec<u8>) -> Self {
        Constant::Bytes(Cow::from(value))
    }
}

impl<'a> From<Cow<'a, [u8]>> for Constant<'a> {
    fn from(value: Cow<'a, [u8]>) -> Self {
        Constant::Bytes(value)
    }
}

/// Cannot convert constant value to type.
#[derive(Clone, Copy)]
pub struct InvalidType;

#[cfg(feature = "std")]
impl error::Error for InvalidType {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl fmt::Display for InvalidType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid type")
    }
}

impl fmt::Debug for InvalidType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid type")
    }
}

impl<'a> TryFrom<Constant<'a>> for Cow<'a, str> {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> core::result::Result<Self, Self::Error> {
        match value {
            Constant::Bool(_) | Constant::Num(_) => Err(InvalidType),
            Constant::Bytes(bytes) => match bytes {
                Cow::Borrowed(bytes) => Ok(Cow::from(
                    core::str::from_utf8(bytes).map_err(|_| InvalidType)?,
                )),
                Cow::Owned(bytes) => Ok(Cow::from(
                    String::from_utf8(bytes).map_err(|_| InvalidType)?,
                )),
            },
        }
    }
}

impl<'a> TryFrom<Constant<'a>> for String {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> core::result::Result<Self, Self::Error> {
        match value {
            Constant::Bool(_) | Constant::Num(_) => Err(InvalidType),
            Constant::Bytes(bytes) => {
                Ok(String::from_utf8(bytes.into_owned()).map_err(|_| InvalidType)?)
            }
        }
    }
}

impl<'a> TryFrom<Constant<'a>> for Cow<'a, [u8]> {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> core::result::Result<Self, Self::Error> {
        match value {
            Constant::Bool(_) | Constant::Num(_) => Err(InvalidType),
            Constant::Bytes(bytes) => Ok(bytes),
        }
    }
}

impl<'a> TryFrom<Constant<'a>> for Vec<u8> {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> core::result::Result<Self, Self::Error> {
        match value {
            Constant::Bool(_) | Constant::Num(_) => Err(InvalidType),
            Constant::Bytes(bytes) => Ok(bytes.into_owned()),
        }
    }
}

impl<'a> TryFrom<Constant<'a>> for i64 {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> core::result::Result<Self, Self::Error> {
        match value {
            Constant::Bool(_) | Constant::Bytes(_) => Err(InvalidType),
            Constant::Num(n) => Ok(n),
        }
    }
}

impl<'a> TryFrom<Constant<'a>> for bool {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> core::result::Result<Self, Self::Error> {
        match value {
            Constant::Bool(b) => Ok(b),
            Constant::Num(_) | Constant::Bytes(_) => Err(InvalidType),
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct Context {
    /// The bytes which a [`BytesId`] indexes into
    bytes: Vec<Vec<u8>>,
    /// The numbers which a [`NumId`] indexes into
    numbers: Vec<i64>,
}

impl Context {
    /// Create an empty context.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            bytes: Vec::new(),
            numbers: Vec::new(),
        }
    }

    /// Given a slice of bytes, returns the existing [`BytesId`], if the byte slice exists in the context.
    #[must_use]
    pub(crate) fn bytes_id(&self, needle: &[u8]) -> Option<BytesId> {
        self.bytes.iter().position(|s| s == needle).map(|pos| {
            BytesId(
                BYTES_START_INDEX
                    + u16::try_from(pos).expect("greater than u16::MAX byte slices in context"),
            )
        })
    }

    /// Returns the slice of bytes given the [`BytesId`].
    #[must_use]
    pub(crate) fn bytes(&self, id: BytesId) -> &[u8] {
        assert!(is_bytes_ref(id.0));
        &self.bytes[usize::from(id.0 - BYTES_START_INDEX)]
    }

    /// Given a slice of bytes, returns a [`BytesId`].
    ///
    /// If the slice of bytes value already exists in the context, it will return the
    /// existing assigned [`BytesId`]. If the slice of bytes value does not exist in
    /// the context, a unique [`BytesId`] will be assigned and returned.
    pub(crate) fn get_or_insert_bytes_id(&mut self, needle: Cow<'_, [u8]>) -> BytesId {
        if let Some(bytes_id) = self.bytes_id(&needle) {
            bytes_id
        } else {
            self.bytes.push(needle.into_owned());
            BytesId(
                BYTES_START_INDEX
                    + u16::try_from(self.bytes.len() - 1)
                        .expect("greater than u16::MAX byte slices in context"),
            )
        }
    }

    /// Given a `i64` value, returns the existing [`NumId`], if the `i64` exists in the context.
    #[must_use]
    pub(crate) fn num_id(&self, needle: i64) -> Option<NumId> {
        self.numbers.iter().position(|s| *s == needle).map(|pos| {
            NumId(
                NUMBER_START_INDEX
                    + u16::try_from(pos).expect("greater than u16::MAX numbers in context"),
            )
        })
    }

    /// Returns the number value given the [`NumId`].
    #[must_use]
    pub(crate) fn num(&self, id: NumId) -> i64 {
        assert!(is_number_ref(id.0));
        self.numbers[usize::from(id.0 - NUMBER_START_INDEX)]
    }

    /// Given a number, returns a [`NumId`].
    ///
    /// If the number value already exists in the context, it will return the
    /// existing assigned [`NumId`]. If the number value does not exist in
    /// the context, a unique [`NumId`] will be assigned and returned.
    pub(crate) fn get_or_insert_num_id(&mut self, needle: i64) -> NumId {
        if let Some(id) = self.num_id(needle) {
            id
        } else {
            self.numbers.push(needle);
            NumId(
                NUMBER_START_INDEX
                    + u16::try_from(self.numbers.len() - 1)
                        .expect("greater than u16::MAX numbers in context"),
            )
        }
    }

    /// Returns the value given the context.
    pub(crate) fn constant<T>(&self, id: T) -> Constant<'_>
    where
        ConstantId: From<T>,
    {
        let id = ConstantId::from(id);

        let Ok(id) = ScalarId::try_from(id) else {
            panic!()
        };

        if let Ok(value) = <bool>::try_from(id) {
            return Constant::Bool(value);
        }

        if let Ok(id) = <NumId>::try_from(id) {
            return Constant::Num(self.num(id));
        }

        if let Ok(id) = <BytesId>::try_from(id) {
            return Constant::Bytes(Cow::from(self.bytes(id)));
        }

        panic!()
    }
}
