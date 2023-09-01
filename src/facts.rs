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
use alloc::vec::Vec;
use core::fmt;
#[cfg(feature = "std")]
use std::{error, vec::Vec};

use generic_array::{ArrayLength, GenericArray};

use crate::{
    values::{BytesId, ConstantId, Context},
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

#[derive(Debug)]
pub(crate) struct PredIter<'a> {
    data: &'a [u8],
}

impl<'a> Iterator for PredIter<'a> {
    type Item = PredicateId;

    fn next(&mut self) -> Option<Self::Item> {
        if self.data.is_empty() {
            return None;
        }

        let predicate = u16::from_be_bytes([self.data[0], self.data[1]]);
        let len = usize::from(u16::from_be_bytes([self.data[2], self.data[3]])) * 2;

        self.data = &self.data[4 + len..];

        Some(PredicateId(predicate))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct TermIter<'a> {
    data: &'a [u8],
}

impl<'a> TermIter<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data }
    }
}

impl<'a> Iterator for TermIter<'a> {
    type Item = ConstantId;

    fn next(&mut self) -> Option<Self::Item>
    where
        Self: 'a,
    {
        if self.data.is_empty() {
            return None;
        }

        let id = ConstantId(u16::from_be_bytes([self.data[0], self.data[1]]));

        self.data = &self.data[2..];

        Some(id)
    }
}

#[derive(Debug)]
pub(crate) struct FactTermsIter<'a> {
    len: usize,
    data: &'a [u8],
}

impl<'a> FactTermsIter<'a> {
    fn new(data: &'a [u8], len: usize) -> Self {
        Self { len, data }
    }
}

impl<'a> Iterator for FactTermsIter<'a> {
    type Item = TermIter<'a>;

    fn next(&mut self) -> Option<Self::Item>
    where
        Self: 'a,
    {
        if self.data.is_empty() {
            return None;
        }

        let iter = TermIter::new(&self.data[..self.len * 2]);

        self.data = &self.data[self.len * 2..];

        Some(iter)
    }
}

#[derive(Debug, Default, Clone, Hash, PartialEq, Eq)]
pub(crate) struct Facts {
    data: Vec<u8>,
}

impl Facts {
    #[must_use]
    pub const fn new() -> Self {
        Self { data: Vec::new() }
    }

    /// An iterator over the predicates.
    pub(crate) fn pred_iter(&self) -> impl Iterator<Item = PredicateId> + '_ {
        PredIter { data: &self.data }
    }

    /// An iterator for terms for a given predicate.
    pub(crate) fn terms_iter(
        &self,
        pred: PredicateId,
        pred_len: usize,
    ) -> impl Iterator<Item = TermIter<'_>> + '_ {
        let mut data = self.data.as_slice();

        loop {
            if data.is_empty() {
                return FactTermsIter::new(data, pred_len);
            }

            let predicate = PredicateId(u16::from_be_bytes([data[0], data[1]]));
            let len = usize::from(u16::from_be_bytes([data[2], data[3]])) * 2;

            if predicate == pred {
                return FactTermsIter::new(&data[4..4 + len], pred_len);
            }

            data = &data[4 + len..];
        }
    }

    /// Returns true if the fact already exists.
    #[must_use]
    #[inline]
    #[allow(unused)]
    pub(crate) fn contains_terms(
        &self,
        pred: PredicateId,
        pred_len: usize,
        terms: &[ConstantId],
    ) -> bool {
        self.terms_iter(pred, pred_len).any(|existing_fact| {
            for (t1, t2) in existing_fact.zip(terms) {
                if t1 != *t2 {
                    return false;
                }
            }
            true
        })
    }

    /// Pushes a new tuple value for a predicate.
    pub(crate) fn push<N: ArrayLength<ConstantId>>(
        &mut self,
        pred: PredicateId,
        constants: GenericArray<ConstantId, N>,
    ) {
        /// An iterator of the constants serialized as [u8]s.
        ///
        /// Structure exists to give the correct `size_hint`.
        struct ConstantBytesIter<T> {
            iter: T,
            size_hint: usize,
        }

        impl<T> Iterator for ConstantBytesIter<T>
        where
            T: Iterator<Item = u8>,
        {
            type Item = u8;

            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next()
            }

            // Gives an exact size_hint so that a splice call will be optimal.
            fn size_hint(&self) -> (usize, Option<usize>) {
                (self.size_hint, Some(self.size_hint))
            }
        }

        assert!(!constants.is_empty());

        let constants_len = constants.len();
        let mut pos = 0;

        loop {
            if pos == self.data.len() {
                break;
            }
            debug_assert!(pos < self.data.len());

            let pred_start_pos = pos;
            let predicate = PredicateId(u16::from_be_bytes([self.data[pos], self.data[pos + 1]]));
            let mut len = usize::from(u16::from_be_bytes([self.data[pos + 2], self.data[pos + 3]]));
            pos += 4;

            if predicate != pred {
                pos += len * 2;
                continue;
            }

            loop {
                if len == 0 {
                    break;
                }

                let mut is_equal = true;
                for i in 0..constants.len() {
                    let existing_constant = ConstantId(u16::from_be_bytes([
                        self.data[pos + (i * 2)],
                        self.data[pos + (i * 2) + 1],
                    ]));
                    if existing_constant != constants[i] {
                        is_equal = false;
                        break;
                    }
                }

                if is_equal {
                    // Found an equivalent term already
                    return;
                }

                len = len.checked_sub(constants.len()).unwrap();
                // len -= constants.len();
                pos += constants.len() * 2;
            }

            let len =
                u16::from_be_bytes([self.data[pred_start_pos + 2], self.data[pred_start_pos + 3]])
                    .checked_add(u16::try_from(constants_len).unwrap())
                    .unwrap();
            let len_bytes = len.to_be_bytes();
            self.data[pred_start_pos + 2] = len_bytes[0];
            self.data[pred_start_pos + 3] = len_bytes[1];

            let size_hint = constants.len() * 2;
            let constants = constants.into_iter().flat_map(|c| c.0.to_be_bytes());

            self.data.splice(
                pos..pos,
                ConstantBytesIter {
                    iter: constants,
                    size_hint,
                },
            );
            return;
        }

        debug_assert_eq!(pos, self.data.len());

        self.data.extend(pred.0.to_be_bytes());
        self.data
            .extend(u16::try_from(constants_len).unwrap().to_be_bytes());
        self.data
            .extend(constants.into_iter().flat_map(|c| c.0.to_be_bytes()));
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

#[derive(Debug, Clone, PartialEq)]
pub struct FactTerms<'a> {
    pub(crate) constants: TermIter<'a>,
    pub(crate) context: &'a Context,
}

impl<'a> FactTerms<'a> {
    #[must_use]
    pub fn to_vec(&self) -> Vec<Constant<'a>> {
        self.constants
            .clone()
            .map(|c| self.context.constant(c))
            .collect::<Vec<_>>()
    }

    pub fn fill_buf<'b>(
        &self,
        dst: &'b mut [Constant<'a>],
    ) -> Result<&'b [Constant<'a>], FactTermsError> {
        let mut idx = 0;

        for id in self.constants.clone() {
            if let Some(v) = dst.get_mut(idx) {
                *v = self.context.constant(id);
            } else {
                return Err(FactTermsError::InvalidLength);
            }
            idx += 1;
        }

        Ok(&dst[..idx])
    }
}
