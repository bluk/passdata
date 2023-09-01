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
use alloc::vec::Vec;
use core::iter;
#[cfg(feature = "std")]
use std::vec::Vec;

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
    facts::{FactTerms, PredicateId},
    utils::{IntoArray, QueryResult},
    values::{BytesId, ConstantId, ScalarId},
};

pub use schema::{ConstantTy, Schema};
pub use utils::{AnyBool, AnyConstant, AnyNum, AnyStr};
pub use values::Constant;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SectionId {
    Unknown,
    Context,
    Edb,
}

impl From<u8> for SectionId {
    fn from(value: u8) -> Self {
        match value {
            1 => SectionId::Context,
            2 => SectionId::Edb,
            _ => SectionId::Unknown,
        }
    }
}

impl From<SectionId> for u8 {
    fn from(value: SectionId) -> Self {
        match value {
            SectionId::Context => 1,
            SectionId::Edb => 2,
            SectionId::Unknown => 0,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Section<'a> {
    start: usize,
    end: usize,
    data: &'a [u8],
}

impl<'a> Section<'a> {
    #[must_use]
    #[inline]
    fn data(self) -> &'a [u8] {
        if self.start == self.end {
            &[]
        } else {
            &self.data[self.start + 3..self.end]
        }
    }
}

#[derive(Debug)]
pub(crate) struct SectionMut<'a> {
    start: usize,
    end: usize,
    data: &'a mut Vec<u8>,
}

impl<'a> SectionMut<'a> {
    #[inline]
    fn as_ref(&self) -> Section<'_> {
        Section {
            start: self.start,
            end: self.end,
            data: self.data,
        }
    }

    #[inline]
    fn init(&mut self, init: &[u8]) {
        if self.start == self.end {
            self.data.splice(self.end..self.end, init.iter().copied());
            self.end += init.len();
        }
    }

    #[inline]
    fn update_len(&mut self) {
        let len = self.end - self.start - 3;
        let len = u16::try_from(len).unwrap();
        let len = len.to_be_bytes();
        self.data[self.start + 1] = len[0];
        self.data[self.start + 2] = len[1];
    }

    #[inline]
    fn splice<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = u8>,
    {
        let ext = self.data.len();
        self.data.splice(self.end..self.end, iter);
        self.end += self.data.len() - ext;
    }
}

/// Data for the logic program.
#[derive(Debug)]
pub struct Passdata<'s> {
    /// The program's types
    schema: &'s Schema<'s>,
    /// Encoded data
    data: Vec<u8>,
}

impl<'s> Passdata<'s> {
    /// Constructs with empty data.
    #[must_use]
    pub const fn new(schema: &'s Schema<'s>) -> Self {
        Self {
            schema,
            data: Vec::new(),
        }
    }

    fn section_rng(&self, section: SectionId) -> Option<(usize, usize)> {
        let mut offset = 0;
        loop {
            if offset == self.data.len() {
                return None;
            }
            debug_assert!(offset < self.data.len());

            let len = usize::from(u16::from_be_bytes([
                self.data[offset + 1],
                self.data[offset + 2],
            ]));

            let cur_sec = SectionId::from(self.data[offset]);
            if cur_sec == section {
                return Some((offset, offset + 3 + len));
            }

            offset += 3 + len;
        }
    }

    fn section(&self, section: SectionId) -> Section<'_> {
        let Some((start, end)) = self.section_rng(section) else {
            return Section {
                start: self.data.len(),
                end: self.data.len(),
                data: &self.data,
            };
        };

        Section {
            start,
            end,
            data: &self.data,
        }
    }

    #[must_use]
    #[inline]
    fn section_mut(&mut self, section: SectionId) -> SectionMut<'_> {
        let Some((start, end)) = self.section_rng(section) else {
            return SectionMut {
                start: self.data.len(),
                end: self.data.len(),
                data: &mut self.data,
            };
        };

        SectionMut {
            start,
            end,
            data: &mut self.data,
        }
    }

    /// Iterator over predicates.
    pub fn predicates_iter(&self) -> impl Iterator<Item = &str> + '_ {
        let ctx = self.section(SectionId::Context);
        facts::pred_iter(self.section(SectionId::Edb)).map(move |id| {
            let bytes = values::bytes(&ctx, BytesId::from(id));
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
    pub fn edb_iter(&self, predicate: &str) -> Result<impl Iterator<Item = FactTerms<'_>> + '_> {
        let Some(tys) = self.schema.get_tys(predicate) else {
            return Err(Error::with_kind(ErrorKind::UnknownPredicate));
        };

        let ctx = self.section(SectionId::Context);

        let Some(pred) = values::bytes_id(&ctx, predicate.as_bytes()).map(PredicateId::from) else {
            return Ok(Either::Left(iter::empty()));
        };

        Ok(Either::Right(
            facts::terms_iter(&self.section(SectionId::Edb), pred, tys.len()).map(
                move |constants| FactTerms {
                    constants,
                    context: ctx,
                },
            ),
        ))
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

        let mut ctx = self.section_mut(SectionId::Context);

        let pred = PredicateId::from(values::get_or_insert_bytes_id(
            &mut ctx,
            predicate.as_bytes(),
        )?);

        for (idx, c) in constants.into_iter().enumerate() {
            v[idx] = match c {
                Constant::Bool(value) => ScalarId::from(value).into(),
                Constant::Num(value) => values::get_or_insert_num_id(&mut ctx, value)?.into(),
                Constant::Bytes(value) => values::get_or_insert_bytes_id(&mut ctx, value)?.into(),
            };
        }

        facts::push(self.section_mut(SectionId::Edb), pred, v);

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

        let ctx = self.section(SectionId::Context);

        let Some(pred) = values::bytes_id(&ctx, predicate.as_bytes()).map(PredicateId::from) else {
            return Ok(Either::Left(iter::empty()));
        };

        Ok(Either::Right(
            facts::terms_iter(&self.section(SectionId::Edb), pred, T::Length::USIZE).filter_map(
                move |cs| {
                    let mut r = GenericArray::default();
                    for (idx, v) in cs.enumerate() {
                        r[idx] = values::constant(&ctx, v);
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
                },
            ),
        ))
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
        assert!(iter.next().is_none());
        drop(iter);

        data.add_fact("a", true)?;
        data.add_fact("b", ("xyz", 1234, false))?;
        data.add_fact("b", ("xyz", 5678, true))?;

        let mut iter = data.edb_iter("a")?;
        assert_eq!(
            iter.next().map(|t| t.to_vec()),
            Some(vec![Constant::Bool(true)])
        );
        assert!(iter.next().is_none());

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
        assert!(iter.next().is_none());

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
        assert!(iter.next().is_none());

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
