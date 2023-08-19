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
#[cfg(feature = "std")]
use std::{collections::BTreeMap, vec::Vec};

use generic_array::{ArrayLength, GenericArray};

use crate::{
    error::Error,
    values::{ConstantId, ScalarId, StringId},
};

/// An interned predicate reference.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct PredicateId(pub(crate) u16);

impl From<StringId> for PredicateId {
    fn from(value: StringId) -> Self {
        Self(value.0)
    }
}

impl From<PredicateId> for StringId {
    fn from(value: PredicateId) -> Self {
        Self(value.0)
    }
}

impl TryFrom<ConstantId> for PredicateId {
    type Error = Error;

    fn try_from(value: ConstantId) -> Result<Self, Self::Error> {
        Ok(Self::from(StringId::try_from(ScalarId::try_from(value)?)?))
    }
}

#[derive(Debug, Default, Clone, Hash, PartialEq, Eq)]
pub(crate) struct Facts {
    terms: BTreeMap<PredicateId, Vec<ConstantId>>,
}

impl Facts {
    /// An iterator over the predicates.
    pub(crate) fn pred_iter(&self) -> impl Iterator<Item = PredicateId> + '_ {
        self.terms.keys().copied()
    }

    /// An iterator for terms for a given predicate.
    pub(crate) fn terms_iter<N: ArrayLength<ConstantId>>(
        &self,
        pred: PredicateId,
    ) -> Option<impl Iterator<Item = GenericArray<ConstantId, N>> + '_> {
        self.terms.get(&pred).map(|constants| {
            assert_eq!(constants.len() % N::USIZE, 0);
            constants
                .chunks_exact(N::USIZE)
                .map(|cs| <GenericArray<ConstantId, N>>::clone_from_slice(cs))
        })
    }

    /// Returns true if the fact already exists.
    #[must_use]
    #[inline]
    pub(crate) fn contains_terms<N: ArrayLength<ConstantId>>(
        &self,
        pred: PredicateId,
        terms: &GenericArray<ConstantId, N>,
    ) -> bool {
        self.terms_iter(pred).map_or(false, |mut i| {
            i.any(|existing_fact| existing_fact == *terms)
        })
    }

    /// Pushes a new tuple value for a predicate.
    pub(crate) fn push<N: ArrayLength<ConstantId>>(
        &mut self,
        pred: PredicateId,
        constants: GenericArray<ConstantId, N>,
    ) {
        assert!(!constants.is_empty());

        if !self.contains_terms(pred, &constants) {
            self.terms.entry(pred).or_default().extend(constants);
        }
    }
}
