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
    error::{Error, Result},
    facts::{Facts, PredicateId},
    utils::{IntoArray, QueryResult},
    values::{Constant, ConstantId, Context, ScalarId},
};

pub use utils::{AnyBool, AnyNum, AnyStr};

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
}

#[cfg(test)]
mod tests {
    use crate::utils::{AnyBool, AnyNum, AnyStr};

    use super::*;

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
        assert_eq!(y.next().unwrap().unwrap(), ("xyz".into(), 1234, false));
        assert_eq!(y.next().unwrap().unwrap(), ("abc".into(), 7, true));
        assert!(y.next().is_none());

        let mut y = data.query_edb("c", ("xyz", 1234, false));
        assert_eq!(y.next().unwrap().unwrap(), ("xyz".into(), 1234, false));
        assert!(y.next().is_none());

        let mut y = data.query_edb("c", ("xyz", 7, AnyBool));
        assert!(y.next().is_none());
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
}
