#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{borrow::Cow, string::String, vec::Vec};
use core::{
    convert::Infallible,
    fmt::{self, Display},
};
#[cfg(feature = "std")]
use std::{borrow::Cow, error, string::String, vec::Vec};

use generic_array::{ArrayLength, GenericArray};

use crate::{
    values::{self, InvalidType},
    ConstantTy,
};

macro_rules! count_ident {
    ($i0:ident) => {1};
    ($i0:ident, $($I:ident),*) => {1 + count_ident!($($I),*)};
}

macro_rules! count_ident_typenum {
    ($i0:ident) => {typenum::U1};
    ($i0:ident, $($I:ident),*) => {<typenum::U1 as core::ops::Add<count_ident_typenum!($($I),*)>>::Output};
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
            type Length = typenum::U1;

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

impl_into_array_single_ty!(bool, i64, &'a str, &'a [u8]);

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

/// Represents a value in a fact.
///
/// The argument can be an exact value such as `true`, `42`, or `&[1, 2, 3]`. A
/// query will then find facts which have the same exact value.
///
/// The argument can also be more relaxed such as [`AnyBool`], [`AnyNum`],
/// [`AnyBytes`], [`AnyStr`], or [`AnyConstant`] which match values which match
/// the named type.
pub trait QueryArg {
    /// The result type. A tuple argument is converted into the `Value` type
    /// from a [`values::Constant`].
    type Value<'a>: TryFrom<values::Constant<'a>>;

    /// The argument's type. Used to verify the argument matches the actual schema type.
    fn ty(&self) -> ConstantTy;

    /// Determines if the found value matches the expected argument. In most
    /// cases, the method is implemented by doing a simple equality comparision.
    ///
    /// In more relaxes cases, the argument could return true depending on the
    /// value in the fact.
    fn is_match(&self, other: &Self::Value<'_>) -> bool;
}

impl<'a> QueryArg for values::Constant<'a> {
    type Value<'b> = values::Constant<'b>;

    fn ty(&self) -> ConstantTy {
        match self {
            values::Constant::Bool(_) => ConstantTy::Bool,
            values::Constant::Num(_) => ConstantTy::Num,
            values::Constant::Bytes(_) => ConstantTy::Bytes,
        }
    }

    fn is_match(&self, other: &Self::Value<'_>) -> bool {
        *self == *other
    }
}

impl QueryArg for bool {
    type Value<'a> = bool;

    fn ty(&self) -> ConstantTy {
        ConstantTy::Bool
    }

    fn is_match(&self, other: &Self::Value<'_>) -> bool {
        *self == *other
    }
}

/// Any boolean value.
#[derive(Debug, Clone, Copy)]
pub struct AnyBool;

impl QueryArg for AnyBool {
    type Value<'a> = bool;

    fn ty(&self) -> ConstantTy {
        ConstantTy::Bool
    }

    fn is_match(&self, _other: &Self::Value<'_>) -> bool {
        true
    }
}

impl QueryArg for i64 {
    type Value<'a> = i64;

    fn ty(&self) -> ConstantTy {
        ConstantTy::Num
    }

    fn is_match(&self, other: &Self::Value<'_>) -> bool {
        *self == *other
    }
}

/// Any number value.
#[derive(Debug, Clone, Copy)]
pub struct AnyNum;

impl QueryArg for AnyNum {
    type Value<'a> = i64;

    fn ty(&self) -> ConstantTy {
        ConstantTy::Num
    }

    fn is_match(&self, _other: &Self::Value<'_>) -> bool {
        true
    }
}

impl<'b> QueryArg for &'b str {
    type Value<'a> = &'a str;

    fn ty(&self) -> ConstantTy {
        ConstantTy::Bytes
    }

    fn is_match(&self, other: &Self::Value<'_>) -> bool {
        self == other
    }
}

impl QueryArg for String {
    type Value<'a> = &'a str;

    fn ty(&self) -> ConstantTy {
        ConstantTy::Bytes
    }

    fn is_match(&self, other: &Self::Value<'_>) -> bool {
        self == *other
    }
}

impl<'b> QueryArg for Cow<'b, str> {
    type Value<'a> = &'a str;

    fn ty(&self) -> ConstantTy {
        ConstantTy::Bytes
    }

    fn is_match(&self, other: &Self::Value<'_>) -> bool {
        self == *other
    }
}

impl<'b> QueryArg for &'b [u8] {
    type Value<'a> = &'a [u8];

    fn ty(&self) -> ConstantTy {
        ConstantTy::Bytes
    }

    fn is_match(&self, other: &Self::Value<'_>) -> bool {
        self == other
    }
}

impl QueryArg for Vec<u8> {
    type Value<'a> = &'a [u8];

    fn ty(&self) -> ConstantTy {
        ConstantTy::Bytes
    }

    fn is_match(&self, other: &Self::Value<'_>) -> bool {
        self == other
    }
}

impl<'b> QueryArg for Cow<'b, [u8]> {
    type Value<'a> = &'a [u8];

    fn ty(&self) -> ConstantTy {
        ConstantTy::Bytes
    }

    fn is_match(&self, other: &Self::Value<'_>) -> bool {
        *self == *other
    }
}

/// Any string value.
#[derive(Debug, Clone, Copy)]
pub struct AnyStr;

impl QueryArg for AnyStr {
    type Value<'a> = &'a str;

    fn ty(&self) -> ConstantTy {
        ConstantTy::Bytes
    }

    fn is_match(&self, _other: &Self::Value<'_>) -> bool {
        true
    }
}

/// Any string value.
#[derive(Debug, Clone, Copy)]
pub struct AnyBytes;

impl QueryArg for AnyBytes {
    type Value<'a> = &'a [u8];

    fn ty(&self) -> ConstantTy {
        ConstantTy::Bytes
    }

    fn is_match(&self, _other: &Self::Value<'_>) -> bool {
        true
    }
}

/// Any constant value.
#[derive(Debug, Clone, Copy)]
pub struct AnyConstant;

impl QueryArg for AnyConstant {
    type Value<'a> = crate::values::Constant<'a>;

    fn ty(&self) -> ConstantTy {
        ConstantTy::Unknown
    }

    fn is_match(&self, _other: &Self::Value<'_>) -> bool {
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

impl From<Infallible> for QueryResultError {
    fn from(_: Infallible) -> Self {
        unreachable!()
    }
}

/// Converts data into a query result.
pub trait QueryResult<'a>
where
    Self: Sized,
{
    /// Number of arguments in the fact.
    type Length: ArrayLength<ConstantTy>;

    /// Result type.
    type ResultTy;

    fn tys(&self) -> GenericArray<ConstantTy, Self::Length>;

    /// If the given values matches the expected values.
    fn is_match(&self, other: &Self::ResultTy) -> bool;
}

impl<'a, T, E> QueryResult<'a> for T
where
    T::Value<'a>: TryFrom<values::Constant<'a>, Error = E>,
    T: QueryArg,
    QueryResultError: From<E>,
    T::Value<'a>: TryFromConstantArray<'a, Length = typenum::U1, Error = QueryResultError>,
{
    type Length = typenum::U1;

    type ResultTy = T::Value<'a>;

    fn tys(&self) -> GenericArray<ConstantTy, Self::Length> {
        generic_array::arr![ConstantTy; self.ty()]
    }

    fn is_match(&self, other: &Self::ResultTy) -> bool {
        self.is_match(other)
    }
}

macro_rules! impl_query_result {
    ($i0:ident) => {};
    ($i0:ident, $($I:ident),+) => {
        impl_query_result!($($I),+);

        paste::paste! {

        impl<'a, $($I),+, $([<E $I>]),+> QueryResult<'a> for ($($I,)+)
            where $($I::Value<'a> : TryFrom<values::Constant<'a>, Error =  [<E $I>]>),+,
            $($I: QueryArg),+,
            $(QueryResultError: From<[<E $I>]>),+,
            Self: Sized
        {
            type Length = count_ident_typenum!($($I),+);

            type ResultTy = ($($I::Value<'a>,)+);

            fn tys(&self) -> GenericArray<ConstantTy, Self::Length> {
                #[allow(non_snake_case)]
                let ($([<a_ $I>],)+) = self;

                generic_array::arr![ConstantTy; $([<a_ $I>].ty()),+]
            }

            fn is_match(&self, other: &Self::ResultTy) -> bool {
                #[allow(non_snake_case)]
                let ($([<a_ $I>],)+) = self;
                #[allow(non_snake_case)]
                let ($([<b_ $I>],)+) = other;

                $(
                    if ![<a_ $I>].is_match([<b_ $I>]) {
                        return false;
                    }
                )+

                true
            }
        }

        }
    };
}

impl_query_result!(dummy, T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12);

pub trait TryFromConstantArray<'a>: Sized {
    type Length: ArrayLength<values::Constant<'a>>;

    type Error;

    fn try_from_constants(
        value: GenericArray<values::Constant<'a>, Self::Length>,
    ) -> Result<Self, Self::Error>;
}

impl<'a, T, E> TryFromConstantArray<'a> for T
where
    T: TryFrom<values::Constant<'a>, Error = E>,
    QueryResultError: From<E>,
{
    type Length = typenum::U1;

    type Error = QueryResultError;

    fn try_from_constants(
        value: GenericArray<values::Constant<'a>, Self::Length>,
    ) -> Result<Self, Self::Error> {
        let mut iter = value.into_iter();

        let t = <T>::try_from(iter.next().ok_or(QueryResultError::MissingElement)?)?;

        if iter.next().is_some() {
            return Err(QueryResultError::InvalidLength);
        }

        Ok(t)
    }
}

impl<'a, T, E, L> TryFromConstantArray<'a> for GenericArray<T, L>
where
    T: TryFrom<values::Constant<'a>, Error = E>,
    QueryResultError: From<E>,
    L: ArrayLength<values::Constant<'a>> + ArrayLength<T>,
{
    type Length = L;

    type Error = QueryResultError;

    fn try_from_constants(
        value: GenericArray<values::Constant<'a>, Self::Length>,
    ) -> Result<Self, Self::Error> {
        // TODO: There is an allocation here. Instead a custom written Iterator
        // can be used which keeps producing `T` elements by using try_from and
        // iterating through the `value` array.
        //
        // If an error is encountered, return None for that element and store the error.
        // The from_exact_iter() should fail because the exact number of elements is not returned.
        // Then, the error should be returned.
        let values = value
            .into_iter()
            .map(|x| <T>::try_from(x))
            .collect::<Result<Vec<_>, _>>()?;
        GenericArray::from_exact_iter(values).ok_or(QueryResultError::InvalidLength)
    }
}

macro_rules! impl_try_from_constant_array_tuple {
    ($i0:ident) => {};
    ($i0:ident, $($I:ident),+) => {
        impl_try_from_constant_array_tuple!($($I),+);

        paste::paste! {

        impl<'a, $($I),+, $([<E $I>]),+> TryFromConstantArray<'a> for ($($I,)+)
        where
            $($I : TryFrom<values::Constant<'a>, Error =  [<E $I>]>),+,
            $(QueryResultError: From<[<E $I>]>),+,
        {
            type Length = count_ident_typenum!($($I),+);

            type Error = QueryResultError;

            fn try_from_constants(
                value: GenericArray<values::Constant<'a>, Self::Length>,
            ) -> Result<Self, Self::Error> {
                let mut iter = value.into_iter();

                let t = (
                    $(
                        {
                            let ignore_ident!($I, a) = <$I as TryFrom<values::Constant<'a>>>::try_from(iter.next().ok_or_else(|| QueryResultError::MissingElement)?)?;
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

        }
    };
}

impl_try_from_constant_array_tuple!(dummy, T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12);
