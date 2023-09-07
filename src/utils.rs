#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{borrow::Cow, string::String, vec::Vec};
use core::{
    convert::Infallible,
    fmt::{self, Display},
    marker::PhantomData,
};
#[cfg(feature = "std")]
use std::{borrow::Cow, error, string::String, vec::Vec};

use generic_array::{arr, ArrayLength, GenericArray};

use crate::values::{self, InvalidType};

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

#[derive(Debug, Clone, Copy)]
pub enum ExpectedConstantTy {
    /// Boolean
    Bool,
    /// Byte slice
    Bytes,
    /// Number
    Num,
    /// Any value type
    Any,
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
    /// The argument's expected type. Used to verify the argument matches the
    /// actual schema type.
    fn ty(&self) -> ExpectedConstantTy;

    /// Determines if the found value matches the expected argument. In most
    /// cases, the method is implemented by doing a simple equality comparision.
    ///
    /// In more relaxes cases, the argument could return true depending on the
    /// value in the fact.
    fn is_match(&self, other: values::Constant<'_>) -> bool;
}

impl<'a> QueryArg for values::Constant<'a> {
    fn ty(&self) -> ExpectedConstantTy {
        match self {
            values::Constant::Bool(_) => ExpectedConstantTy::Bool,
            values::Constant::Num(_) => ExpectedConstantTy::Num,
            values::Constant::Bytes(_) => ExpectedConstantTy::Bytes,
        }
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        *self == other
    }
}

impl QueryArg for bool {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Bool
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Bool(other) => *self == other,
            crate::Constant::Num(_) | crate::Constant::Bytes(_) => false,
        }
    }
}

/// Any boolean value.
#[derive(Debug, Clone, Copy)]
pub struct AnyBool;

impl QueryArg for AnyBool {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Bool
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Bool(_) => true,
            crate::Constant::Num(_) | crate::Constant::Bytes(_) => false,
        }
    }
}

impl QueryArg for i64 {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Num
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Num(other) => *self == other,
            crate::Constant::Bool(_) | crate::Constant::Bytes(_) => false,
        }
    }
}

/// Any number value.
#[derive(Debug, Clone, Copy)]
pub struct AnyNum;

impl QueryArg for AnyNum {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Num
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Num(_) => true,
            crate::Constant::Bool(_) | crate::Constant::Bytes(_) => false,
        }
    }
}

impl<'b> QueryArg for &'b str {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Bytes
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Bytes(other) => self.as_bytes() == other,
            crate::Constant::Bool(_) | crate::Constant::Num(_) => false,
        }
    }
}

impl QueryArg for String {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Bytes
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Bytes(other) => self.as_bytes() == other,
            crate::Constant::Bool(_) | crate::Constant::Num(_) => false,
        }
    }
}

impl<'b> QueryArg for Cow<'b, str> {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Bytes
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Bytes(other) => self.as_bytes() == other,
            crate::Constant::Bool(_) | crate::Constant::Num(_) => false,
        }
    }
}

impl<'b> QueryArg for &'b [u8] {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Bytes
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Bytes(other) => *self == other,
            crate::Constant::Bool(_) | crate::Constant::Num(_) => false,
        }
    }
}

impl QueryArg for Vec<u8> {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Bytes
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Bytes(other) => *self == other,
            crate::Constant::Bool(_) | crate::Constant::Num(_) => false,
        }
    }
}

impl<'b> QueryArg for Cow<'b, [u8]> {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Bytes
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Bytes(other) => *self == other,
            crate::Constant::Bool(_) | crate::Constant::Num(_) => false,
        }
    }
}

/// Any string value.
#[derive(Debug, Clone, Copy)]
pub struct AnyStr;

impl QueryArg for AnyStr {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Bytes
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Bytes(other) => core::str::from_utf8(other).is_ok(),
            crate::Constant::Bool(_) | crate::Constant::Num(_) => false,
        }
    }
}

/// Any string value.
#[derive(Debug, Clone, Copy)]
pub struct AnyBytes;

impl QueryArg for AnyBytes {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Bytes
    }

    fn is_match(&self, other: values::Constant<'_>) -> bool {
        match other {
            crate::Constant::Bytes(_) => true,
            crate::Constant::Bool(_) | crate::Constant::Num(_) => false,
        }
    }
}

/// Any constant value.
#[derive(Debug, Clone, Copy)]
pub struct AnyConstant;

impl QueryArg for AnyConstant {
    fn ty(&self) -> ExpectedConstantTy {
        ExpectedConstantTy::Any
    }

    fn is_match(&self, _: values::Constant<'_>) -> bool {
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
pub trait QueryArgs<'a>
where
    Self: Sized,
{
    /// Number of arguments in the fact.
    type Length: ArrayLength<ExpectedConstantTy> + ArrayLength<values::Constant<'a>>;

    fn tys(&self) -> GenericArray<ExpectedConstantTy, Self::Length>;

    /// If the given values matches the expected values.
    fn is_match(&self, other: &GenericArray<values::Constant<'a>, Self::Length>) -> bool;
}

impl<'a, T> QueryArgs<'a> for T
where
    T: QueryArg,
{
    type Length = typenum::U1;

    fn tys(&self) -> GenericArray<ExpectedConstantTy, Self::Length> {
        generic_array::arr![ExpectedConstantTy; self.ty()]
    }

    fn is_match(&self, other: &GenericArray<values::Constant<'a>, Self::Length>) -> bool {
        self.is_match(other[0])
    }
}

macro_rules! impl_query_result {
    ($i0:ident) => {};
    ($i0:ident, $($I:ident),+) => {
        impl_query_result!($($I),+);

        paste::paste! {

        impl<'a, $($I),+,> QueryArgs<'a> for ($($I,)+)
            where
            $($I: QueryArg),+,
            Self: Sized
        {
            type Length = count_ident_typenum!($($I),+);

            fn tys(&self) -> GenericArray<ExpectedConstantTy, Self::Length> {
                #[allow(non_snake_case)]
                let ($([<a_ $I>],)+) = self;

                generic_array::arr![ExpectedConstantTy; $([<a_ $I>].ty()),+]
            }

            fn is_match(&self, other: &GenericArray<values::Constant<'a>, Self::Length>) -> bool {
                #[allow(non_snake_case)]
                let ($([<a_ $I>],)+) = self;
                #[allow(non_snake_case)]
                let mut iter = other.iter().copied();

                $(
                    let Some(other) = iter.next() else {
                        return false;
                    };
                    if ![<a_ $I>].is_match(other) {
                        return false;
                    }
                )+

                if iter.next().is_some() {
                    return false;
                }

                true
            }
        }

        }
    };
}

impl_query_result!(dummy, T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12);

pub trait Value {
    fn supported_ty() -> ExpectedConstantTy;
}

impl Value for bool {
    fn supported_ty() -> ExpectedConstantTy {
        ExpectedConstantTy::Bool
    }
}

impl Value for i64 {
    fn supported_ty() -> ExpectedConstantTy {
        ExpectedConstantTy::Num
    }
}

impl<'a> Value for &'a [u8] {
    fn supported_ty() -> ExpectedConstantTy {
        ExpectedConstantTy::Bytes
    }
}

impl<'a> Value for &'a str {
    fn supported_ty() -> ExpectedConstantTy {
        ExpectedConstantTy::Bytes
    }
}

impl<'a> Value for values::Constant<'a> {
    fn supported_ty() -> ExpectedConstantTy {
        ExpectedConstantTy::Any
    }
}

pub trait TryFromConstantArray<'a>: Sized {
    type Length: ArrayLength<ExpectedConstantTy> + ArrayLength<values::Constant<'a>>;

    type Error;

    /// Return the types which are required to convert from.
    fn required_tys() -> GenericArray<ExpectedConstantTy, Self::Length>;

    fn try_from_constants(
        value: GenericArray<values::Constant<'a>, Self::Length>,
    ) -> Result<Self, Self::Error>;
}

pub(crate) struct VoidResult<L> {
    ty: PhantomData<L>,
}

impl<'a, L> TryFromConstantArray<'a> for VoidResult<L>
where
    L: ArrayLength<ExpectedConstantTy> + ArrayLength<values::Constant<'a>>,
{
    type Length = L;

    type Error = Infallible;

    fn required_tys() -> GenericArray<ExpectedConstantTy, Self::Length> {
        GenericArray::from_exact_iter(
            core::iter::repeat(ExpectedConstantTy::Any).take(Self::Length::to_usize()),
        )
        .unwrap()
    }

    fn try_from_constants(
        _: GenericArray<values::Constant<'a>, Self::Length>,
    ) -> Result<Self, Self::Error> {
        Ok(VoidResult { ty: PhantomData })
    }
}

impl<'a, T, E> TryFromConstantArray<'a> for T
where
    T: TryFrom<values::Constant<'a>, Error = E> + Value,
    QueryResultError: From<E>,
{
    type Length = typenum::U1;

    type Error = QueryResultError;

    fn required_tys() -> GenericArray<ExpectedConstantTy, Self::Length> {
        arr![ExpectedConstantTy; T::supported_ty()]
    }

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
    T: TryFrom<values::Constant<'a>, Error = E> + Value,
    QueryResultError: From<E>,
    L: ArrayLength<ExpectedConstantTy> + ArrayLength<values::Constant<'a>> + ArrayLength<T>,
{
    type Length = L;

    type Error = QueryResultError;

    fn required_tys() -> GenericArray<ExpectedConstantTy, Self::Length> {
        GenericArray::from_exact_iter(
            core::iter::repeat(T::supported_ty()).take(Self::Length::to_usize()),
        )
        .unwrap()
    }

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
            $($I : TryFrom<values::Constant<'a>, Error =  [<E $I>]> + Value),+,
            $(QueryResultError: From<[<E $I>]>),+,
        {
            type Length = count_ident_typenum!($($I),+);

            type Error = QueryResultError;

            fn required_tys() -> GenericArray<ExpectedConstantTy, Self::Length> {
                generic_array::arr![ExpectedConstantTy; $($I::supported_ty()),+]
            }

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
