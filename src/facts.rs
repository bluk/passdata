//! Facts are a fundamental concept of the logic programming language.
//!
//! Facts are a labeled tuple with constant values. For example, `user(1234)` is
//! a fact stating there is a single element tuple with the value `1234` and a
//! `user` label. `permission("write", "/a")` is a two element tuple with the
//! values "write" and "/a" with the "permission" label. The label is referred
//! to as a `predicate`.
//!
//! Facts are either added explicitly or are inferred from rules.

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{collections::BTreeMap, vec::Vec};
use core::fmt;
#[cfg(feature = "std")]
use std::{collections::BTreeMap, error, vec::Vec};

use generic_array::{ArrayLength, GenericArray};

use crate::{
    error::Error,
    values::{BytesId, ConstantId, Context, ScalarId},
    Constant,
};

/// An interned predicate reference.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct PredicateId(pub(crate) u16);

impl From<BytesId> for PredicateId {
    fn from(value: BytesId) -> Self {
        Self(value.0)
    }
}

impl From<PredicateId> for BytesId {
    fn from(value: PredicateId) -> Self {
        Self(value.0)
    }
}

impl TryFrom<ConstantId> for PredicateId {
    type Error = Error;

    fn try_from(value: ConstantId) -> Result<Self, Self::Error> {
        Ok(Self::from(BytesId::try_from(ScalarId::try_from(value)?)?))
    }
}

#[derive(Debug, Default, Clone, Hash, PartialEq, Eq)]
pub(crate) struct Facts {
    terms: BTreeMap<PredicateId, Vec<ConstantId>>,
}

impl Facts {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            terms: BTreeMap::new(),
        }
    }

    /// An iterator over the predicates.
    pub(crate) fn pred_iter(&self) -> impl Iterator<Item = PredicateId> + '_ {
        self.terms.keys().copied()
    }

    /// An iterator for terms for a given predicate.
    pub(crate) fn terms_iter(
        &self,
        pred: PredicateId,
        pred_len: usize,
    ) -> Option<impl Iterator<Item = &[ConstantId]> + '_> {
        self.terms
            .get(&pred)
            .map(|constants| constants.chunks_exact(pred_len))
    }

    /// Returns true if the fact already exists.
    #[must_use]
    #[inline]
    pub(crate) fn contains_terms(
        &self,
        pred: PredicateId,
        pred_len: usize,
        terms: &[ConstantId],
    ) -> bool {
        self.terms_iter(pred, pred_len)
            .map_or(false, |mut i| i.any(|existing_fact| existing_fact == terms))
    }

    /// Pushes a new tuple value for a predicate.
    pub(crate) fn push<N: ArrayLength<ConstantId>>(
        &mut self,
        pred: PredicateId,
        constants: GenericArray<ConstantId, N>,
    ) {
        assert!(!constants.is_empty());

        if !self.contains_terms(pred, constants.len(), constants.as_slice()) {
            self.terms.entry(pred).or_default().extend(constants);
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FactTermsError {
    InvalidLength,
}

impl fmt::Debug for FactTermsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLength => f.write_str("invalid length"),
        }
    }
}

impl fmt::Display for FactTermsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLength => f.write_str("invalid length"),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for FactTermsError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Self::InvalidLength => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FactTerms<'a> {
    pub(crate) constants: &'a [ConstantId],
    pub(crate) context: &'a Context,
}

impl<'a> FactTerms<'a> {
    #[must_use]
    pub fn to_vec(&self) -> Vec<Constant<'a>> {
        self.constants
            .iter()
            .map(|c| self.context.constant(*c))
            .collect::<Vec<_>>()
    }

    pub fn fill_buf<'b>(
        &self,
        dst: &'b mut [Constant<'a>],
    ) -> Result<&'b [Constant<'a>], FactTermsError> {
        let expected_len = self.constants.len();
        if dst.len() < expected_len {
            return Err(FactTermsError::InvalidLength);
        }

        for (idx, id) in self.constants.iter().enumerate() {
            dst[idx] = self.context.constant(*id);
        }

        Ok(&dst[..expected_len])
    }

    #[must_use]
    #[inline]
    pub const fn len(&self) -> usize {
        self.constants.len()
    }
}
