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

use core::iter;

use either::Either;
use generic_array::{functional::FunctionalSequence, ArrayLength, GenericArray};
use typenum::Unsigned;

pub mod error;
pub(crate) mod facts;
pub(crate) mod schema;
pub(crate) mod utils;
pub(crate) mod values;

use crate::{
    error::{Error, ErrorKind, Result},
    facts::{FactTerms, Facts, PredicateId},
    utils::{IntoArray, QueryResult},
    values::{BytesId, ConstantId, Context, ScalarId},
};

pub use schema::{ConstantTy, Schema};
pub use utils::{AnyBool, AnyConstant, AnyNum, AnyStr};
pub use values::Constant;

/// Data for the logic program.
#[derive(Debug)]
pub struct Passdata<'s, 'c> {
    /// The program's types
    schema: &'s Schema<'s>,
    /// Values in context
    context: Context<'c>,
    /// Facts explictly added to the data
    edb: Facts,
}

impl<'s, 'c> Passdata<'s, 'c> {
    /// Constructs with empty data.
    #[must_use]
    pub const fn new(schema: &'s Schema<'s>) -> Self {
        Self {
            schema,
            context: Context::new(),
            edb: Facts::new(),
        }
    }

    /// Iterator over predicates.
    pub fn predicates_iter(&self) -> impl Iterator<Item = &str> + '_ {
        self.edb.pred_iter().map(|id| {
            let bytes = self.context.bytes(BytesId::from(id));
            let Ok(p) = core::str::from_utf8(bytes) else {
                unreachable!("predicate should be a UTF-8 string")
            };
            p
        })
    }

    /// Iterator over facts.
    ///
    /// # Errors
    ///
    /// - if the predicate is unknown.
    pub fn edb_iter(
        &self,
        predicate: &str,
    ) -> Result<impl Iterator<Item = FactTerms<'_, '_>> + '_> {
        let Some(tys) = self.schema.get_tys(predicate) else {
            return Err(Error::with_kind(ErrorKind::UnknownPredicate));
        };

        let Some(pred) = self
            .context
            .bytes_id(predicate.as_bytes())
            .map(PredicateId::from)
        else {
            return Ok(Either::Left(iter::empty()));
        };

        let Some(iter) = self.edb.terms_iter(pred, tys.len()) else {
            return Ok(Either::Left(iter::empty()));
        };

        Ok(Either::Right(iter.map(|constants| FactTerms {
            constants,
            context: &self.context,
        })))
    }

    /// Add a fact explicitly.
    ///
    /// # Errors
    ///
    /// Returns an error if the values do not match the expected types for the predicate.
    pub fn add_fact<'a, T>(&mut self, predicate: &str, constants: T) -> Result<()>
    where
        T: IntoArray<Constant<'a>>,
        <T as IntoArray<Constant<'a>>>::Length: ArrayLength<ConstantTy>,
        <T as IntoArray<Constant<'a>>>::Length: ArrayLength<ConstantId>,
    {
        let constants = constants.into_array();

        let tys = constants.clone().map(ConstantTy::from);
        self.schema.validate_tys(predicate, &tys)?;

        let mut v: GenericArray<ConstantId, T::Length> = GenericArray::default();

        let pred = PredicateId::from(self.context.get_or_insert_bytes_id(predicate.as_bytes()));

        for (idx, c) in constants.into_iter().enumerate() {
            v[idx] = match c {
                Constant::Bool(value) => ScalarId::from(value).into(),
                Constant::Num(value) => self.context.get_or_insert_num_id(value).into(),
                Constant::Bytes(value) => self.context.get_or_insert_bytes_id(value).into(),
            };
        }

        self.edb.push(pred, v);

        Ok(())
    }

    /// Query for an explictly declared fact.
    ///
    /// # Errors
    ///
    /// If the expected types are not compatible with the types in the data.
    pub fn query_edb<'a, T>(
        &'a self,
        predicate: &str,
        values: T,
    ) -> Result<impl Iterator<Item = T::ResultTy> + 'a>
    where
        T: QueryResult<'a> + 'a,
    {
        self.schema.validate_tys(predicate, &T::tys())?;

        let Some(pred) = self
            .context
            .bytes_id(predicate.as_bytes())
            .map(PredicateId::from)
        else {
            return Ok(Either::Left(iter::empty()));
        };

        let Some(iter) = self.edb.terms_iter(pred, T::Length::USIZE) else {
            return Ok(Either::Left(iter::empty()));
        };

        Ok(Either::Right(iter.filter_map(move |cs| {
            let mut r = GenericArray::default();
            for (idx, v) in cs.iter().enumerate() {
                r[idx] = self.context.constant(*v);
            }

            let res = match T::into_tuple(r) {
                Ok(res) => res,
                Err(e) => {
                    unreachable!("{e}")
                }
            };

            if !values.is_match(&res) {
                return None;
            }

            Some(res)
        })))
    }

    /// Determines if there is any explicitly declared fact which matches the given parameters.
    ///
    /// # Errors
    ///
    /// If the expected types are not compatible with the types in the data.
    pub fn contains_edb<'a, T>(&'a self, pred: &str, values: T) -> Result<bool>
    where
        T: QueryResult<'a> + 'a,
    {
        self.query_edb(pred, values)
            .map(|mut values| values.next().is_some())
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
    {
        let mut iter = self.query_edb(pred, values)?;
        let Some(first) = iter.next() else {
            return Ok(None);
        };

        if iter.next().is_some() {
            return Err(Error::with_kind(ErrorKind::MultipleMatchingFacts));
        }

        Ok(Some(first))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(all(feature = "alloc", not(feature = "std")))]
    use alloc::{string::String, vec};
    #[cfg(feature = "std")]
    use std::{string::String, vec};

    use crate::utils::{AnyBool, AnyBytes, AnyNum, AnyStr};

    #[test]
    fn edb_iter() -> Result<()> {
        let mut schema = Schema::new();
        schema.insert_tys("a", &[ConstantTy::Bool])?;
        schema.insert_tys("b", &[ConstantTy::Bytes, ConstantTy::Num, ConstantTy::Bool])?;

        let mut data = Passdata::new(&schema);

        let mut iter = data.edb_iter("a")?;
        assert_eq!(iter.next(), None);
        drop(iter);

        data.add_fact("a", true)?;
        data.add_fact("b", ("xyz", 1234, false))?;
        data.add_fact("b", ("xyz", 5678, true))?;

        let mut iter = data.edb_iter("a")?;
        assert_eq!(
            iter.next().map(|t| t.to_vec()),
            Some(vec![Constant::Bool(true)])
        );
        assert_eq!(iter.next(), None);

        let mut iter = data.edb_iter("b")?;
        assert_eq!(
            iter.next().map(|t| t.to_vec()),
            Some(vec![
                Constant::Bytes("xyz".as_bytes()),
                Constant::Num(1234),
                Constant::Bool(false)
            ])
        );
        assert_eq!(
            iter.next().map(|t| t.to_vec()),
            Some(vec![
                Constant::Bytes("xyz".as_bytes()),
                Constant::Num(5678),
                Constant::Bool(true)
            ])
        );
        assert_eq!(iter.next(), None);

        let mut values: [Constant<'_>; 8] = [
            Constant::Bool(false),
            Constant::Bool(false),
            Constant::Bool(false),
            Constant::Bool(false),
            Constant::Bool(false),
            Constant::Bool(false),
            Constant::Bool(false),
            Constant::Bool(false),
        ];

        let mut iter = data.edb_iter("b")?;
        let dst = iter.next().unwrap().fill_buf(&mut values)?;
        assert_eq!(
            dst,
            vec![
                Constant::Bytes("xyz".as_bytes()),
                Constant::Num(1234),
                Constant::Bool(false)
            ]
        );

        let dst = iter.next().unwrap().fill_buf(&mut values)?;
        assert_eq!(
            dst,
            &[
                Constant::Bytes("xyz".as_bytes()),
                Constant::Num(5678),
                Constant::Bool(true)
            ]
        );
        assert_eq!(iter.next(), None);

        Ok(())
    }

    #[test]
    fn query_edb() -> Result<()> {
        let mut schema = Schema::default();
        schema.insert_tys("a", &[ConstantTy::Bool])?;
        schema.insert_tys("a2", &[ConstantTy::Num])?;
        schema.insert_tys("a3", &[ConstantTy::Bytes])?;
        schema.insert_tys("a4", &[ConstantTy::Bytes])?;
        schema.insert_tys("b", &[ConstantTy::Num, ConstantTy::Num])?;
        schema.insert_tys("b2", &[ConstantTy::Num, ConstantTy::Num])?;
        schema.insert_tys("c", &[ConstantTy::Bytes, ConstantTy::Num, ConstantTy::Bool])?;

        let mut data = Passdata::new(&schema);

        data.add_fact("a", true)?;
        data.add_fact("a2", 1)?;
        data.add_fact("a3", "xyz")?;
        data.add_fact("a4", ["xyz"])?;
        data.add_fact("b", (1, 2))?;
        data.add_fact("b2", [1, 2])?;
        data.add_fact("c", ("xyz", 1234, false))?;
        data.add_fact("c", ["abc".into(), 7.into(), Constant::from(true)])?;

        let mut y = data.query_edb("c", (AnyStr, AnyNum, AnyBool))?;
        assert_eq!(y.next(), Some(("xyz", 1234, false)));
        assert_eq!(y.next(), Some(("abc", 7, true)));
        assert_eq!(y.next(), None);

        let mut y = data.query_edb("c", (AnyBytes, AnyNum, AnyBool))?;
        assert_eq!(y.next(), Some(("xyz".as_bytes(), 1234, false)));
        assert_eq!(y.next(), Some(("abc".as_bytes(), 7, true)));
        assert_eq!(y.next(), None);

        let mut y = data.query_edb("c", ("xyz", 1234, false))?;
        assert_eq!(y.next(), Some(("xyz", 1234, false)));
        assert_eq!(y.next(), None);

        let mut y = data.query_edb("c", ("xyz", 7, AnyBool))?;
        assert_eq!(y.next(), None);

        let mut y = data.query_edb("c", (AnyConstant, AnyConstant, AnyConstant))?;
        assert_eq!(y.next(), Some(("xyz".into(), 1234.into(), false.into())));
        assert_eq!(y.next(), Some(("abc".into(), 7.into(), true.into())));
        assert_eq!(y.next(), None);

        let mut y = data.query_edb("c", ("abc", AnyConstant, AnyConstant))?;
        assert_eq!(y.next(), Some(("abc", 7.into(), true.into())));
        assert_eq!(y.next(), None);

        Ok(())
    }

    #[test]
    fn contains_edb() -> Result<()> {
        let mut schema = Schema::new();
        schema.insert_tys("a", &[ConstantTy::Bool])?;
        schema.insert_tys("b", &[ConstantTy::Bytes, ConstantTy::Num, ConstantTy::Bool])?;

        let mut data = Passdata::new(&schema);

        data.add_fact("a", true)?;
        data.add_fact("b", ("xyz", 1234, false))?;
        data.add_fact("b", ("xyz", 5678, true))?;

        assert!(data.contains_edb("a", (true,))?);
        assert!(data.contains_edb("a", (AnyBool,))?);
        assert!(!data.contains_edb("a", (false,))?);

        assert!(!data.contains_edb("b", ("xyz", 5678, false))?);
        assert!(data.contains_edb("b", ("xyz", 5678, true))?);
        assert!(data.contains_edb("b", ("xyz", 5678, AnyBool))?);

        assert!(data.contains_edb("b", ("xyz", AnyNum, false))?);
        assert!(!data.contains_edb("b", (AnyStr, 5678, false))?);
        assert!(!data.contains_edb("b", (AnyStr, 1234, true))?);

        Ok(())
    }

    lazy_static::lazy_static! {
        static ref QUERY_ONLY_ONE_EDB_SCHEMA: Schema<'static> = {
            let mut schema = Schema::new();
            schema.insert_tys("a", &[ConstantTy::Bool]).unwrap();
            schema.insert_tys("b", &[ConstantTy::Bytes, ConstantTy::Num, ConstantTy::Bool]).unwrap();
            schema.insert_tys("c", &[ConstantTy::Num]).unwrap();
            schema.insert_tys("d", &[ConstantTy::Bytes]).unwrap();
            schema
        };
    }

    #[test]
    fn query_only_one_edb() -> Result<()> {
        let mut data = Passdata::new(&QUERY_ONLY_ONE_EDB_SCHEMA);

        data.add_fact("a", true)?;
        data.add_fact("b", ("xyz", 1234, false))?;
        data.add_fact("b", ("xyz", 5678, true))?;
        data.add_fact("c", 1234)?;
        data.add_fact("d", "xyz")?;

        assert_eq!(data.query_only_one_edb("a", (true,)), Ok(Some((true,))));
        assert_eq!(data.query_only_one_edb("a", true), Ok(Some(true)));
        assert_eq!(data.query_only_one_edb("a", AnyBool), Ok(Some(true)));

        assert_eq!(
            data.query_only_one_edb("b", ("xyz", 1234, false)),
            Ok(Some(("xyz", 1234, false)))
        );
        assert_eq!(
            data.query_only_one_edb("b", ("xyz", 1234, AnyBool)),
            Ok(Some(("xyz", 1234, false)))
        );
        assert_eq!(
            data.query_only_one_edb("b", ("xyz", AnyNum, AnyBool)),
            Err(Error::with_kind(ErrorKind::MultipleMatchingFacts))
        );

        assert_eq!(data.query_only_one_edb("c", AnyNum), Ok(Some(1234)));
        assert_eq!(data.query_only_one_edb("c", 5678), Ok(None));

        assert_eq!(data.query_only_one_edb("d", AnyStr), Ok(Some("xyz")));
        assert_eq!(
            data.query_only_one_edb("d", AnyBytes),
            Ok(Some("xyz".as_bytes()))
        );
        assert_eq!(data.query_only_one_edb("d", "abc"), Ok(None));
        assert_eq!(data.query_only_one_edb("d", "xyz"), Ok(Some("xyz")));
        assert_eq!(
            data.query_only_one_edb("d", String::from("xyz")),
            Ok(Some("xyz"))
        );

        assert_eq!(
            data.query_only_one_edb("d", AnyConstant),
            Ok(Some("xyz".into()))
        );

        Ok(())
    }

    #[test]
    fn missing_predicate_schema_errors() {
        let schema = Schema::new();
        let mut data = Passdata::new(&schema);

        let error = match data.query_edb("c", ("abc", AnyConstant, AnyConstant)) {
            Ok(_) => panic!("should have had a schema error"),
            Err(e) => e,
        };
        assert!(error.is_schema_error());

        let error = data.add_fact("a", true).unwrap_err();
        assert!(error.is_schema_error());

        let error = data.contains_edb("a", (true,)).unwrap_err();
        assert!(error.is_schema_error());

        let error = data.query_only_one_edb("a", AnyBool).unwrap_err();
        assert!(error.is_schema_error());
    }

    #[test]
    fn unexpected_predicate_tys_length_schema_errors() -> Result<()> {
        let mut schema = Schema::new();
        schema.insert_tys("a", &[ConstantTy::Bool])?;
        schema.insert_tys("b", &[ConstantTy::Bytes, ConstantTy::Num, ConstantTy::Bool])?;

        let mut data = Passdata::new(&schema);

        let error = match data.query_edb("b", (AnyConstant, AnyConstant)) {
            Ok(_) => panic!("should have had a schema error"),
            Err(e) => e,
        };
        assert!(error.is_schema_error());

        let error = data.add_fact("a", (true, 1)).unwrap_err();
        assert!(error.is_schema_error());

        let error = data.contains_edb("a", (true, AnyConstant)).unwrap_err();
        assert!(error.is_schema_error());

        let error = data
            .query_only_one_edb("a", (AnyBool, AnyConstant))
            .unwrap_err();
        assert!(error.is_schema_error());

        Ok(())
    }

    #[test]
    fn mistmatched_predicate_tys_schema_errors() -> Result<()> {
        let mut schema = Schema::new();
        schema.insert_tys("a", &[ConstantTy::Bool])?;
        schema.insert_tys("b", &[ConstantTy::Bytes, ConstantTy::Num, ConstantTy::Bool])?;

        let mut data = Passdata::new(&schema);

        let error = match data.query_edb("b", (AnyConstant, AnyConstant, 1)) {
            Ok(_) => panic!("should have had a schema error"),
            Err(e) => e,
        };
        assert!(error.is_schema_error());

        let error = data.add_fact("a", (1,)).unwrap_err();
        assert!(error.is_schema_error());

        let error = data.contains_edb("a", (AnyStr,)).unwrap_err();
        assert!(error.is_schema_error());

        let error = data.query_only_one_edb("a", "xyz").unwrap_err();
        assert!(error.is_schema_error());

        Ok(())
    }
}
