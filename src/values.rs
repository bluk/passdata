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
#[cfg(feature = "std")]
use std::{borrow::Cow, string::String, vec::Vec};

use crate::error::{Error, ErrorKind, Result};

const BOOL_FALSE_INDEX: u16 = 0;
const BOOL_TRUE_INDEX: u16 = 1;
const STRING_START_INDEX: u16 = 32;
const STRING_INCLUSIVE_END_INDEX: u16 = 513;
const STRING_INDEX_RANGE: core::ops::RangeInclusive<u16> =
    STRING_START_INDEX..=STRING_INCLUSIVE_END_INDEX;
const NUMBER_START_INDEX: u16 = 514;
const NUMBER_INCLUSIVE_END_INDEX: u16 = 765;
const NUMBER_INDEX_RANGE: core::ops::RangeInclusive<u16> =
    NUMBER_START_INDEX..=NUMBER_INCLUSIVE_END_INDEX;

#[inline]
fn is_bool_ref(value: u16) -> bool {
    value == BOOL_FALSE_INDEX || value == BOOL_TRUE_INDEX
}

#[inline]
fn is_string_ref(value: u16) -> bool {
    STRING_INDEX_RANGE.contains(&value)
}

#[inline]
fn is_number_ref(value: u16) -> bool {
    NUMBER_INDEX_RANGE.contains(&value)
}

#[inline]
fn is_scalar_ref(value: u16) -> bool {
    is_bool_ref(value) || is_string_ref(value) || is_number_ref(value)
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

/// An interned string ID reference.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct StringId(pub(crate) u16);

impl TryFrom<ScalarId> for StringId {
    type Error = Error;

    fn try_from(value: ScalarId) -> Result<Self> {
        if is_string_ref(value.0) {
            Ok(StringId(value.0))
        } else {
            Err(Error::with_kind(ErrorKind::InvalidStringId))
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

impl From<StringId> for ScalarId {
    fn from(value: StringId) -> Self {
        debug_assert!(is_string_ref(value.0));
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
pub(crate) struct ConstantId(pub(crate) u16);

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

impl From<StringId> for ConstantId {
    fn from(value: StringId) -> Self {
        debug_assert!(is_string_ref(value.0));
        Self(value.0)
    }
}

impl From<ScalarId> for ConstantId {
    fn from(value: ScalarId) -> Self {
        Self(value.0)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct Context {
    /// The strings which a [`StringId`] indexes into
    strings: Vec<String>,
    /// The numbers which a [`NumId`] indexes into
    numbers: Vec<i64>,
}

impl Context {
    /// Given a string, returns the existing [`StringId`], if the string exists in the context.
    #[must_use]
    pub(crate) fn string_id(&self, needle: &str) -> Option<StringId> {
        self.strings.iter().position(|s| s == needle).map(|pos| {
            StringId(
                STRING_START_INDEX
                    + u16::try_from(pos).expect("greater than u16::MAX strings in context"),
            )
        })
    }

    /// Returns the string representation given the [`StringId`].
    #[must_use]
    pub(crate) fn str(&self, id: StringId) -> &str {
        assert!(is_string_ref(id.0));
        &self.strings[usize::from(id.0 - STRING_START_INDEX)]
    }

    /// Given a string, returns a [`StringId`].
    ///
    /// If the string value already exists in the context, it will return the
    /// existing assigned [`StringId`]. If the string value does not exist in
    /// the context, a unique [`StringId`] will be assigned and returned.
    pub(crate) fn get_or_insert_string_id(&mut self, needle: Cow<'_, str>) -> StringId {
        if let Some(str_id) = self.string_id(&needle) {
            str_id
        } else {
            self.strings.push(needle.into_owned());
            StringId(
                STRING_START_INDEX
                    + u16::try_from(self.strings.len() - 1)
                        .expect("greater than u16::MAX strings in context"),
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
}
