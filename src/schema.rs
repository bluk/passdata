//! Schemas define the types in the context of the program.
//!
//! Schemas are expected to be constant.

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::collections::{BTreeMap, BTreeSet};
#[cfg(feature = "std")]
use std::collections::{BTreeMap, BTreeSet};

use crate::{
    error::{Error, ErrorKind, Result},
    utils::ExpectedConstantTy,
    Constant,
};

/// Type of a constant
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstantTy {
    /// Boolean
    Bool,
    /// Number
    Num,
    /// Bytes
    Bytes,
}

impl<'a> From<Constant<'a>> for ConstantTy {
    fn from(value: Constant<'a>) -> Self {
        match value {
            Constant::Bool(_) => ConstantTy::Bool,
            Constant::Num(_) => ConstantTy::Num,
            Constant::Bytes(_) => ConstantTy::Bytes,
        }
    }
}

impl ConstantTy {
    pub(crate) fn is_match(self, other: ConstantTy) -> bool {
        self == other
    }

    pub(crate) fn is_supported(self, other: ExpectedConstantTy) -> bool {
        match (self, other) {
            (_, ExpectedConstantTy::Any)
            | (ConstantTy::Bool, ExpectedConstantTy::Bool)
            | (ConstantTy::Bytes, ExpectedConstantTy::Bytes)
            | (ConstantTy::Num, ExpectedConstantTy::Num) => true,
            (ConstantTy::Bool | ConstantTy::Num, ExpectedConstantTy::Bytes)
            | (ConstantTy::Bool | ConstantTy::Bytes, ExpectedConstantTy::Num)
            | (ConstantTy::Num | ConstantTy::Bytes, ExpectedConstantTy::Bool) => false,
        }
    }
}

/// Schema for a program.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Schema<'a> {
    tys: BTreeMap<&'a str, &'a [ConstantTy]>,
    exclusive: BTreeSet<&'a str>,
}

impl<'a> Schema<'a> {
    /// Constructs an empty schema.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            tys: BTreeMap::new(),
            exclusive: BTreeSet::new(),
        }
    }

    /// Returns an iterator for all predicates.
    pub fn predicates_iter(&self) -> impl Iterator<Item = &str> + '_ {
        self.tys.keys().copied()
    }

    /// Returns the types for a predicate.
    #[must_use]
    pub fn get_tys(&self, pred: &str) -> Option<&[ConstantTy]> {
        self.tys.get(pred).copied()
    }

    /// Insert the types for a predicate.
    ///
    /// # Errors
    ///
    /// - If there is an existing non-equal schema for the predicate.
    pub fn insert_tys(&mut self, pred: &'a str, tys: &'a [ConstantTy]) -> Result<()> {
        if let Some(existing_tys) = self.tys.get(pred) {
            if *existing_tys == tys {
                return Ok(());
            }
            return Err(Error::with_kind(ErrorKind::DuplicateSchema));
        }

        self.tys.insert(pred, tys);

        Ok(())
    }

    /// Returns true if the exclusive bit is set for a predicate.
    #[must_use]
    pub fn is_exclusive(&self, predicate: &str) -> bool {
        self.exclusive.contains(predicate)
    }

    /// Sets a predicate to be an exclusive fact.
    ///
    /// At most one fact can be added with the given predicate.
    ///
    /// # Errors
    ///
    /// If the predicate's schema types does not exist
    pub fn set_exclusive(&mut self, predicate: &'a str) -> Result<()> {
        if !self.tys.contains_key(predicate) {
            return Err(Error::with_kind(ErrorKind::MismatchSchemaTys));
        }

        self.exclusive.insert(predicate);

        Ok(())
    }

    pub(crate) fn validate_tys(&self, predicate: &'a str, actual_tys: &[ConstantTy]) -> Result<()> {
        let Some(tys) = self.get_tys(predicate) else {
            return Err(Error::with_kind(ErrorKind::UnknownPredicate));
        };

        if tys.len() != actual_tys.len() {
            return Err(Error::with_kind(ErrorKind::MismatchSchemaTys));
        }

        for (expected_ty, actual_ty) in tys.iter().zip(actual_tys) {
            if !expected_ty.is_match(*actual_ty) {
                return Err(Error::with_kind(ErrorKind::MismatchSchemaTys));
            }
        }

        Ok(())
    }

    pub(crate) fn validate_conversions(
        &self,
        predicate: &'a str,
        actual_tys: &[ExpectedConstantTy],
    ) -> Result<()> {
        let Some(tys) = self.get_tys(predicate) else {
            return Err(Error::with_kind(ErrorKind::UnknownPredicate));
        };

        if tys.len() != actual_tys.len() {
            return Err(Error::with_kind(ErrorKind::MismatchSchemaTys));
        }

        for (actual_ty, value_ty) in tys.iter().zip(actual_tys) {
            if !actual_ty.is_supported(*value_ty) {
                return Err(Error::with_kind(ErrorKind::MismatchSchemaTys));
            }
        }

        Ok(())
    }
}
