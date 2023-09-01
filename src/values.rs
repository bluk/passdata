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
use alloc::borrow::Cow;
use core::fmt;
#[cfg(feature = "std")]
use std::{borrow::Cow, error};

use crate::{
    error::{Error, ErrorKind},
    ConstantTy, Section, SectionMut,
};

const BOOL_FALSE_INDEX: u16 = 0;
const BOOL_TRUE_INDEX: u16 = 1;

const MAX_DATA_LEN: usize = 4096;
const BYTES_TY_BITMASK: u16 = 3 << 13;
const NUM_TY_BITMASK: u16 = 2 << 13;

/// An interned bytes reference.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct BytesId(pub(crate) u16);

/// An interned number reference.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct NumId(pub(crate) u16);

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
        Self(value.0)
    }
}

impl From<BytesId> for ScalarId {
    fn from(value: BytesId) -> Self {
        Self(value.0)
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
        Self(value.0)
    }
}

impl From<BytesId> for ConstantId {
    fn from(value: BytesId) -> Self {
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
    Bytes(&'a [u8]),
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
        Constant::Bytes(value.as_bytes())
    }
}

impl<'a> From<&'a [u8]> for Constant<'a> {
    fn from(value: &'a [u8]) -> Self {
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

impl<'a> TryFrom<Constant<'a>> for &'a [u8] {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> Result<Self, Self::Error> {
        match value {
            Constant::Bool(_) | Constant::Num(_) => Err(InvalidType),
            Constant::Bytes(bytes) => Ok(bytes),
        }
    }
}

impl<'a> TryFrom<Constant<'a>> for Cow<'a, [u8]> {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> Result<Self, Self::Error> {
        match value {
            Constant::Bool(_) | Constant::Num(_) => Err(InvalidType),
            Constant::Bytes(bytes) => Ok(Cow::from(bytes)),
        }
    }
}

impl<'a> TryFrom<Constant<'a>> for &'a str {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> Result<Self, Self::Error> {
        match value {
            Constant::Bool(_) | Constant::Num(_) => Err(InvalidType),
            Constant::Bytes(bytes) => Ok(core::str::from_utf8(bytes).map_err(|_| InvalidType)?),
        }
    }
}

impl<'a> TryFrom<Constant<'a>> for Cow<'a, str> {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> Result<Self, Self::Error> {
        match value {
            Constant::Bool(_) | Constant::Num(_) => Err(InvalidType),
            Constant::Bytes(bytes) => Ok(Cow::Borrowed(
                core::str::from_utf8(bytes).map_err(|_| InvalidType)?,
            )),
        }
    }
}

impl<'a> TryFrom<Constant<'a>> for i64 {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> Result<Self, Self::Error> {
        match value {
            Constant::Bool(_) | Constant::Bytes(_) => Err(InvalidType),
            Constant::Num(n) => Ok(n),
        }
    }
}

impl<'a> TryFrom<Constant<'a>> for bool {
    type Error = InvalidType;

    fn try_from(value: Constant<'a>) -> Result<Self, Self::Error> {
        match value {
            Constant::Bool(b) => Ok(b),
            Constant::Num(_) | Constant::Bytes(_) => Err(InvalidType),
        }
    }
}

#[derive(Debug)]
pub(crate) struct Iter<'a> {
    data: &'a [u8],
}

fn iter<'a>(ctx: &Section<'a>) -> Iter<'a> {
    let data = ctx.data();
    if data.is_empty() {
        return Iter { data: &[] };
    }
    Iter { data: &data[2..] }
}

impl<'a> Iterator for Iter<'a> {
    type Item = (ConstantTy, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        if self.data.is_empty() {
            return None;
        }

        let first_len_byte = self.data[0];
        let ty = match first_len_byte >> 5 {
            2 => ConstantTy::Num,
            3 => ConstantTy::Bytes,
            _ => unreachable!(),
        };

        let first_len_byte = first_len_byte & 0x1F;
        let len = u16::from_be_bytes([first_len_byte, self.data[1]]);

        let len = usize::from(len);
        let slice = &self.data[2..2 + len];
        self.data = &self.data[2 + len..];

        Some((ty, slice))
    }
}

const SECTION_INIT: [u8; 5] = [1, 0, 2, 0, 0];

#[must_use]
#[inline]
fn elem_len(section: &SectionMut<'_>) -> u16 {
    u16::from_be_bytes([
        section.data[section.start + 3],
        section.data[section.start + 4],
    ])
}

#[inline]
fn set_elem_len(section: &mut SectionMut<'_>, len: u16) {
    let len_bytes = len.to_be_bytes();
    section.data[section.start + 3] = len_bytes[0];
    section.data[section.start + 4] = len_bytes[1];
}

#[must_use]
pub(crate) fn bytes_id(ctx: &Section<'_>, needle: &[u8]) -> Option<BytesId> {
    iter(ctx)
        .position(|(ty, value)| ty == ConstantTy::Bytes && value == needle)
        .map(|pos| {
            BytesId(2 + u16::try_from(pos).expect("greater than u16::MAX byte slices in context"))
        })
}

/// Returns the slice of bytes given the [`BytesId`].
#[must_use]
pub(crate) fn bytes<'a>(ctx: &Section<'a>, id: BytesId) -> &'a [u8] {
    let idx = usize::from(id.0 - 2);
    let Some((ty, value)) = iter(ctx).nth(idx) else {
        unreachable!()
    };
    assert_eq!(ty, ConstantTy::Bytes);
    value
}

/// Given a slice of bytes, returns a [`BytesId`].
///
/// If the slice of bytes value already exists in the context, it will return the
/// existing assigned [`BytesId`]. If the slice of bytes value does not exist in
/// the context, a unique [`BytesId`] will be assigned and returned.
pub(crate) fn get_or_insert_bytes_id(
    ctx: &mut SectionMut<'_>,
    needle: &[u8],
) -> Result<BytesId, Error> {
    if needle.len() > MAX_DATA_LEN {
        return Err(Error::with_kind(ErrorKind::InvalidContextValue));
    }

    if let Some(bytes_id) = bytes_id(&ctx.as_ref(), needle) {
        Ok(bytes_id)
    } else {
        ctx.init(&SECTION_INIT);

        let len = elem_len(ctx);
        if len >= u16::MAX - 2 {
            return Err(Error::with_kind(ErrorKind::ContextFull));
        }
        let len = len + 1;

        let needle_len = needle.len();
        assert!(needle_len <= 4096);
        let needle_len_with_ty = u16::try_from(needle_len).unwrap() | BYTES_TY_BITMASK;
        ctx.splice(needle_len_with_ty.to_be_bytes());
        ctx.splice(needle.iter().copied());

        set_elem_len(ctx, len);
        ctx.update_len();

        Ok(BytesId(2 + len - 1))
    }
}

/// Given a `i64` value, returns the existing [`NumId`], if the `i64` exists in the context.
#[must_use]
fn num_id(ctx: &Section<'_>, needle: i64) -> Option<NumId> {
    iter(ctx)
        .position(|(ty, value)| {
            ty == ConstantTy::Num
                && i64::from_be_bytes(<[u8; 8]>::try_from(value).unwrap()) == needle
        })
        .map(|pos| NumId(2 + u16::try_from(pos).expect("greater than u16::MAX numbers in context")))
}

/// Returns the number value given the [`NumId`].
#[must_use]
#[allow(unused)]
fn num(ctx: &Section<'_>, id: NumId) -> i64 {
    let idx = usize::from(id.0 - 2);
    let Some((ty, value)) = iter(ctx).nth(idx) else {
        unreachable!()
    };
    assert_eq!(ty, ConstantTy::Num);
    i64::from_be_bytes(<[u8; 8]>::try_from(value).unwrap())
}

/// Given a number, returns a [`NumId`].
///
/// If the number value already exists in the context, it will return the
/// existing assigned [`NumId`]. If the number value does not exist in
/// the context, a unique [`NumId`] will be assigned and returned.
pub(crate) fn get_or_insert_num_id(ctx: &mut SectionMut<'_>, needle: i64) -> Result<NumId, Error> {
    if let Some(id) = num_id(&ctx.as_ref(), needle) {
        Ok(id)
    } else {
        ctx.init(&SECTION_INIT);

        let len = elem_len(ctx);
        if len >= u16::MAX - 2 {
            return Err(Error::with_kind(ErrorKind::ContextFull));
        }
        let len = len + 1;

        let needle_len = 8u16;
        let needle_len = needle_len | NUM_TY_BITMASK;
        ctx.splice(needle_len.to_be_bytes());
        ctx.splice(needle.to_be_bytes());

        set_elem_len(ctx, len);
        ctx.update_len();

        Ok(NumId(2 + len - 1))
    }
}

/// Returns the value given the context.
pub(crate) fn constant<'a, T>(ctx: &Section<'a>, id: T) -> Constant<'a>
where
    ConstantId: From<T>,
{
    let id = ConstantId::from(id);

    if id.0 == BOOL_FALSE_INDEX {
        return Constant::Bool(false);
    }

    if id.0 == BOOL_TRUE_INDEX {
        return Constant::Bool(true);
    }

    let Some((ty, value)) = iter(ctx).nth(usize::from(id.0 - 2)) else {
        unreachable!()
    };

    match ty {
        ConstantTy::Unknown | ConstantTy::Bool => unreachable!(),
        ConstantTy::Num => Constant::Num(i64::from_be_bytes(<[u8; 8]>::try_from(value).unwrap())),
        ConstantTy::Bytes => Constant::Bytes(value),
    }
}
