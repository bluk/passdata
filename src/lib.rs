//! # Passdata
//!
//! `Passdata` is authentication and authorization data expressed in a logic
//! programming language. Data should fit within the limits of a HTTP cookie or
//! header. The language is limited in order to guarantee properties during
//! execution.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(
    missing_copy_implementations,
    missing_debug_implementations,
    missing_docs,
    rust_2018_idioms,
    unused_lifetimes,
    unused_qualifications
)]
#![feature(impl_trait_projections)]

#[cfg(all(feature = "alloc", not(feature = "std")))]
extern crate alloc;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::borrow::Cow;
use core::iter;
#[cfg(feature = "std")]
use std::borrow::Cow;

use either::Either;
use generic_array::{ArrayLength, GenericArray};

pub mod error;
pub(crate) mod facts;
pub(crate) mod utils;
pub(crate) mod values;

use crate::{
    error::{Error, ErrorKind, Result},
    facts::{Facts, PredicateId},
    utils::{IntoArray, QueryResult},
    values::{ConstantId, Context, ScalarId, StringId},
};

pub use utils::{AnyBool, AnyConstant, AnyNum, AnyStr};
pub use values::Constant;

/// Data for the logic program.
#[derive(Debug, Default)]
pub struct Passdata {
    /// Values in context
    context: Context,
    /// Facts explictly added to the data
    edb: Facts,
}

impl Passdata {
    /// Constructs with empty data.
    #[must_use]
    pub fn new() -> Self {
        Self {
            context: Context::default(),
            edb: Facts::default(),
        }
    }

    /// Iterator over predicates.
    pub fn predicates_iter(&self) -> impl Iterator<Item = &str> + '_ {
        self.edb
            .pred_iter()
            .map(|id| self.context.str(StringId::from(id)))
    }

    /// Add a fact explicitly.
    pub fn add_fact<'a, P, T>(&mut self, predicate: P, constants: T)
    where
        P: Into<Cow<'a, str>>,
        T: IntoArray<Constant<'a>>,
        <T as IntoArray<Constant<'a>>>::Length: ArrayLength<ConstantId>,
    {
        let constants = constants.into_array();
        let mut v: GenericArray<ConstantId, T::Length> = GenericArray::default();

        let pred = PredicateId::from(self.context.get_or_insert_string_id(predicate.into()));

        for (idx, c) in constants.into_iter().enumerate() {
            v[idx] = match c {
                Constant::Bool(value) => ScalarId::from(value).into(),
                Constant::Num(value) => self.context.get_or_insert_num_id(value).into(),
                Constant::String(value) => self.context.get_or_insert_string_id(value).into(),
            };
        }

        self.edb.push(pred, v);
    }

    /// Query for an explictly declared fact.
    ///
    /// # Errors
    ///
    /// If the expected types are not compatible with the types in the data.
    pub fn query_edb<'a, T>(
        &'a self,
        pred: &str,
        values: T,
    ) -> impl Iterator<Item = Result<T::ResultTy>> + 'a
    where
        T: QueryResult<'a> + 'a,
        <T as QueryResult<'a>>::Length: ArrayLength<ConstantId>,
    {
        let Some(pred) = self.context.string_id(pred).map(PredicateId::from) else {
            return Either::Left(iter::empty());
        };

        let Some(iter) = self.edb.terms_iter::<T::Length>(pred) else {
            return Either::Left(iter::empty());
        };

        Either::Right(iter.filter_map(move |cs| {
            let mut r = GenericArray::default();
            for (idx, v) in cs.iter().enumerate() {
                r[idx] = self.context.constant(*v);
            }

            let res = match T::into_tuple(r) {
                Ok(res) => res,
                Err(e) => {
                    return Some(Err(Error::from(e)));
                }
            };

            if !values.is_match(&res) {
                return None;
            }

            Some(Ok(res))
        }))
    }

    /// Determines if there is any explicitly declared fact which matches the given parameters.
    pub fn contains_edb<'a, T>(&'a self, pred: &str, values: T) -> bool
    where
        T: QueryResult<'a> + 'a,
        <T as QueryResult<'a>>::Length: ArrayLength<ConstantId>,
    {
        self.query_edb(pred, values).any(|v| v.is_ok())
    }

    /// Queries the data for an explicitly declared fact, and only returns a
    /// success if there is a single matching fact.
    ///
    /// # Errors
    ///
    /// - If the expected types are not compatible with the types in the data.
    /// - If there are multiple matching facts
    pub fn query_only_one_edb<'a, T>(&'a self, pred: &str, values: T) -> Result<Option<T::ResultTy>>
    where
        T: QueryResult<'a> + 'a,
        <T as QueryResult<'a>>::Length: ArrayLength<ConstantId>,
    {
        let mut iter = self.query_edb(pred, values);
        let Some(first) = iter.next() else {
            return Ok(None);
        };

        match first {
            Ok(first) => {
                if iter.next().is_some() {
                    return Err(Error::with_kind(ErrorKind::MultipleMatchingFacts));
                }

                Ok(Some(first))
            }
            Err(error) => Err(error),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(all(feature = "alloc", not(feature = "std")))]
    use alloc::string::String;
    #[cfg(feature = "std")]
    use std::string::String;

    use crate::utils::{AnyBool, AnyNum, AnyStr};

    #[test]
    fn query_edb() {
        let mut data = Passdata::new();

        data.add_fact("a", true);
        data.add_fact("a2", 1);
        data.add_fact("a3", "xyz");
        data.add_fact("a4", ["xyz"]);
        data.add_fact("b", (1, 2));
        data.add_fact("b2", [1, 2]);
        data.add_fact("c", ("xyz", 1234, false));
        data.add_fact("c", ["abc".into(), 7.into(), Constant::from(true)]);

        let mut y = data.query_edb("c", (AnyStr, AnyNum, AnyBool));
        assert_eq!(y.next(), Some(Ok(("xyz".into(), 1234, false))));
        assert_eq!(y.next(), Some(Ok(("abc".into(), 7, true))));
        assert_eq!(y.next(), None);

        let mut y = data.query_edb("c", ("xyz", 1234, false));
        assert_eq!(y.next(), Some(Ok(("xyz".into(), 1234, false))));
        assert_eq!(y.next(), None);

        let mut y = data.query_edb("c", ("xyz", 7, AnyBool));
        assert_eq!(y.next(), None);

        let mut y = data.query_edb("c", (AnyConstant, AnyConstant, AnyConstant));
        assert_eq!(
            y.next(),
            Some(Ok(("xyz".into(), 1234.into(), false.into())))
        );
        assert_eq!(y.next(), Some(Ok(("abc".into(), 7.into(), true.into()))));
        assert_eq!(y.next(), None);

        let mut y = data.query_edb("c", ("abc", AnyConstant, AnyConstant));
        assert_eq!(y.next(), Some(Ok(("abc".into(), 7.into(), true.into()))));
        assert_eq!(y.next(), None);
    }

    #[test]
    fn contains_edb() {
        let mut data = Passdata::new();

        data.add_fact("a", true);
        data.add_fact("b", ("xyz", 1234, false));
        data.add_fact("b", ("xyz", 5678, true));

        assert!(data.contains_edb("a", (true,)));
        assert!(data.contains_edb("a", (AnyBool,)));
        assert!(!data.contains_edb("a", (false,)));

        assert!(!data.contains_edb("b", ("xyz", 5678, false)));
        assert!(data.contains_edb("b", ("xyz", 5678, true)));
        assert!(data.contains_edb("b", ("xyz", 5678, AnyBool)));

        assert!(data.contains_edb("b", ("xyz", AnyNum, false)));
        assert!(!data.contains_edb("b", (AnyStr, 5678, false)));
        assert!(!data.contains_edb("b", (AnyStr, 1234, true)));
    }

    #[test]
    fn query_only_one_edb() {
        let mut data = Passdata::new();

        data.add_fact("a", true);
        data.add_fact("b", ("xyz", 1234, false));
        data.add_fact("b", ("xyz", 5678, true));
        data.add_fact("c", 1234);
        data.add_fact("d", "xyz");

        assert_eq!(data.query_only_one_edb("a", (true,)), Ok(Some((true,))));
        assert_eq!(data.query_only_one_edb("a", true), Ok(Some(true)));
        assert_eq!(data.query_only_one_edb("a", AnyBool), Ok(Some(true)));

        assert_eq!(
            data.query_only_one_edb("b", ("xyz", 1234, false)),
            Ok(Some(("xyz".into(), 1234, false)))
        );
        assert_eq!(
            data.query_only_one_edb("b", ("xyz", 1234, AnyBool)),
            Ok(Some(("xyz".into(), 1234, false)))
        );
        assert_eq!(
            data.query_only_one_edb("b", ("xyz", AnyNum, AnyBool)),
            Err(Error::with_kind(ErrorKind::MultipleMatchingFacts))
        );

        assert_eq!(data.query_only_one_edb("c", AnyNum), Ok(Some(1234)));
        assert_eq!(data.query_only_one_edb("c", 5678), Ok(None));

        assert_eq!(data.query_only_one_edb("d", AnyStr), Ok(Some("xyz".into())));
        assert_eq!(data.query_only_one_edb("d", "abc"), Ok(None));
        assert_eq!(data.query_only_one_edb("d", "xyz"), Ok(Some("xyz".into())));
        assert_eq!(
            data.query_only_one_edb("d", String::from("xyz")),
            Ok(Some("xyz".into()))
        );

        assert_eq!(
            data.query_only_one_edb("d", AnyConstant),
            Ok(Some("xyz".into()))
        );
    }
}
