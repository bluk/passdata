#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{borrow::Cow, string::String};
use core::fmt::{self, Display};
#[cfg(feature = "std")]
use std::{borrow::Cow, error, string::String};

use generic_array::{ArrayLength, GenericArray};
use typenum::U1;

use crate::values::{self, InvalidType};

macro_rules! count_ident {
    ($i0:ident) => {1};
    ($i0:ident, $($I:ident),*) => {1 + count_ident!($($I),*)};
}

macro_rules! count_ident_typenum {
    ($i0:ident) => {U1};
    ($i0:ident, $($I:ident),*) => {<U1 as core::ops::Add<count_ident_typenum!($($I),*)>>::Output};
}

macro_rules! ignore_ident {
    ($id:ident, $($t:tt)*) => {
        $($t)*
    };
}

/// Converts data into an array.
pub trait IntoArray<T>: Sized {
    /// Length of the generic array.
    type Length: ArrayLength<T>;

    /// Converts `self` into an array.
    fn into_array(self) -> GenericArray<T, Self::Length>;
}

macro_rules! impl_into_array_single_ty {
    ($i0:ty) => {
        impl<'a> IntoArray<values::Constant<'a>> for $i0
        {
            type Length = U1;

            fn into_array(self) -> GenericArray<values::Constant<'a>, Self::Length> {
                [values::Constant::from(self)].into()
            }
        }
    };
    ($i0:ty, $($I:ty),+) => {
      impl_into_array_single_ty!($i0);

      impl_into_array_single_ty!($($I),+);
    };
}

impl_into_array_single_ty!(bool, i64, String, &'a str, Cow<'a, str>);

macro_rules! impl_into_array_tuple {
    ($i0:ident) => {};
    ($i0:ident, $($I:ident),+) => {
        impl_into_array_tuple!($($I),+);

        impl<T, $($I),+> IntoArray<T> for ($($I,)+)
            where $(T: From<$I>,)+
        {
            type Length = count_ident_typenum!($($I),+);

            fn into_array(self) -> GenericArray<T, Self::Length> {
                #[allow(non_snake_case)]
                let ($($I,)+) = self;

                [$(T::from($I)),+].into()
            }
        }

        impl<T, S> IntoArray<S> for [T; { count_ident!($($I),+) }]
            where S: From<T>,
        {
            type Length = count_ident_typenum!($($I),+);

            fn into_array(self) -> GenericArray<S, Self::Length>  {
                #[allow(non_snake_case)]
                let [$($I,)+] = self;

                [$(S::from($I)),+].into()
            }
        }
    };
}

impl_into_array_tuple!(dummy, T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12);

/// Expected value used in a query.
pub trait QueryValue {
    /// The expected type to match.
    type Ty<'a>: TryFrom<values::Constant<'a>>;

    /// Determines if the found value matches the expected value.
    fn is_match(&self, other: &Self::Ty<'_>) -> bool;
}

impl QueryValue for bool {
    type Ty<'a> = bool;

    fn is_match(&self, other: &Self::Ty<'_>) -> bool {
        *self == *other
    }
}

/// Any boolean value.
#[derive(Debug, Clone, Copy)]
pub struct AnyBool;

impl QueryValue for AnyBool {
    type Ty<'a> = bool;

    fn is_match(&self, _other: &Self::Ty<'_>) -> bool {
        true
    }
}

impl QueryValue for i64 {
    type Ty<'a> = i64;

    fn is_match(&self, other: &Self::Ty<'_>) -> bool {
        *self == *other
    }
}

/// Any number value.
#[derive(Debug, Clone, Copy)]
pub struct AnyNum;

impl QueryValue for AnyNum {
    type Ty<'a> = i64;

    fn is_match(&self, _other: &Self::Ty<'_>) -> bool {
        true
    }
}

impl<'b> QueryValue for &'b str {
    type Ty<'a> = Cow<'a, str>;

    fn is_match(&self, other: &Self::Ty<'_>) -> bool {
        *self == *other
    }
}

/// Any string value.
#[derive(Debug, Clone, Copy)]
pub struct AnyStr;

impl QueryValue for AnyStr {
    type Ty<'a> = Cow<'a, str>;

    fn is_match(&self, _other: &Self::Ty<'_>) -> bool {
        true
    }
}

/// Errors in converting to a tuple.
#[derive(Clone, Copy, PartialEq)]
pub enum QueryResultError {
    /// Missing an element for the tuple
    MissingElement,
    /// Invalid arity
    InvalidLength,
    /// Invalid type for element
    InvalidType,
}

#[cfg(feature = "std")]
impl error::Error for QueryResultError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl Display for QueryResultError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingElement => f.write_str("missing element"),
            Self::InvalidLength => f.write_str("invalid length"),
            Self::InvalidType => f.write_str("invalid element type"),
        }
    }
}

impl fmt::Debug for QueryResultError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingElement => f.write_str("missing element"),
            Self::InvalidLength => f.write_str("invalid length"),
            Self::InvalidType => f.write_str("invalid element type"),
        }
    }
}

impl From<InvalidType> for QueryResultError {
    fn from(_value: InvalidType) -> Self {
        Self::InvalidType
    }
}

/// Converts data into a query result.
pub trait QueryResult<'a>
where
    Self: Sized,
{
    /// Length of a `lang::Constant` generic array.
    type Length: ArrayLength<values::Constant<'a>>;

    /// Result type.
    type ResultTy;

    /// If the given values matches the expected values.
    fn is_match(&self, other: &Self::ResultTy) -> bool;

    /// Converts values into a tuple.
    ///
    /// # Errors
    ///
    /// If the given `GenericArray` is not the correct length, is missing an
    /// element, or cannot convert a type.
    fn into_tuple(
        values: GenericArray<values::Constant<'a>, Self::Length>,
    ) -> Result<Self::ResultTy, QueryResultError>;
}

impl<'a, T> QueryResult<'a> for T
where
    T::Ty<'a>: TryFrom<values::Constant<'a>, Error = InvalidType>,
    T: QueryValue,
{
    type Length = U1;

    type ResultTy = T::Ty<'a>;

    fn is_match(&self, other: &Self::ResultTy) -> bool {
        self.is_match(other)
    }

    fn into_tuple(
        values: GenericArray<values::Constant<'a>, Self::Length>,
    ) -> Result<Self::ResultTy, QueryResultError> {
        let mut iter = values.into_iter();

        let t = <T::Ty<'a>>::try_from(iter.next().ok_or(QueryResultError::MissingElement)?)?;

        if iter.next().is_some() {
            return Err(QueryResultError::InvalidLength);
        }

        Ok(t)
    }
}

macro_rules! impl_query_result {
    ($i0:ident) => {};
    ($i0:ident, $($I:ident),+) => {
        impl_query_result!($($I),+);

        impl<'a, $($I),+> QueryResult<'a> for ($($I,)+)
            where $($I::Ty<'a> : TryFrom<values::Constant<'a>, Error = InvalidType>),+,
            $($I: QueryValue),+,
            Self: Sized
        {
            type Length = count_ident_typenum!($($I),+);

            type ResultTy = ($($I::Ty<'a>,)+);

            fn is_match(&self, other: &Self::ResultTy) -> bool {
                paste::paste! {
                #[allow(non_snake_case)]
                let ($([<a_ $I>],)+) = self;
                #[allow(non_snake_case)]
                let ($([<b_ $I>],)+) = other;

                $(
                    if ![<a_ $I>].is_match([<b_ $I>]) {
                        return false;
                    }
                )+
                };

                true
            }

            fn into_tuple(values: GenericArray<values::Constant<'a>, Self::Length>) -> Result<Self::ResultTy, QueryResultError> {
                let mut iter = values.into_iter();

                let t = (
                    $(
                        {
                            let ignore_ident!($I, a) = <$I::Ty<'a>>::try_from(iter.next().ok_or_else(|| QueryResultError::MissingElement)?)?;
                            a
                        }
                    ,)+
                );

                if iter.next().is_some() {
                    return Err(QueryResultError::InvalidLength);
                }

                Ok(t)
            }
        }
    };
}

impl_query_result!(dummy, T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12);
