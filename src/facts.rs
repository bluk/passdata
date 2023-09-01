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
    values::{self, BytesId, ConstantId},
    Constant, Section, SectionMut,
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

/// An iterator over the predicates.
#[derive(Debug)]
struct PredIter<'a> {
    data: &'a [u8],
}

pub(crate) fn pred_iter(facts: Section<'_>) -> impl Iterator<Item = PredicateId> + '_ {
    PredIter { data: facts.data() }
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
struct FactTermsIter<'a> {
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

/// An iterator for terms for a given predicate.
pub(crate) fn terms_iter<'a>(
    facts: &Section<'a>,
    pred: PredicateId,
    pred_len: usize,
) -> impl Iterator<Item = TermIter<'a>> + 'a {
    let mut data = facts.data();

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

const SECTION_INIT: [u8; 3] = [2, 0, 0];

/// Pushes a new tuple value for a predicate.
pub(crate) fn push<N: ArrayLength<ConstantId>>(
    mut facts: SectionMut<'_>,
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

    facts.init(&SECTION_INIT);

    let constants_len = constants.len();
    let mut pos = facts.start + 3;

    loop {
        if pos == facts.end {
            break;
        }
        debug_assert!(pos < facts.end);

        let pred_start_pos = pos;
        let predicate = PredicateId(u16::from_be_bytes([facts.data[pos], facts.data[pos + 1]]));
        let mut len = usize::from(u16::from_be_bytes([
            facts.data[pos + 2],
            facts.data[pos + 3],
        ]));
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
                    facts.data[pos + (i * 2)],
                    facts.data[pos + (i * 2) + 1],
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
            pos += constants.len() * 2;
        }

        let len = u16::from_be_bytes([
            facts.data[pred_start_pos + 2],
            facts.data[pred_start_pos + 3],
        ])
        .checked_add(u16::try_from(constants_len).unwrap())
        .unwrap();
        let len_bytes = len.to_be_bytes();
        facts.data[pred_start_pos + 2] = len_bytes[0];
        facts.data[pred_start_pos + 3] = len_bytes[1];

        let size_hint = constants.len() * 2;
        let constants = constants.into_iter().flat_map(|c| c.0.to_be_bytes());

        facts.data.splice(
            pos..pos,
            ConstantBytesIter {
                iter: constants,
                size_hint,
            },
        );

        facts.end += size_hint;
        facts.update_len();

        return;
    }

    debug_assert_eq!(pos, facts.end);

    facts
        .data
        .splice(facts.end..facts.end, pred.0.to_be_bytes());
    facts.end += 2;
    facts.data.splice(
        facts.end..facts.end,
        u16::try_from(constants_len).unwrap().to_be_bytes(),
    );
    facts.end += 2;

    let size_hint = constants.len() * 2;
    let constants = constants.into_iter().flat_map(|c| c.0.to_be_bytes());

    facts.data.splice(
        facts.end..facts.end,
        ConstantBytesIter {
            iter: constants,
            size_hint,
        },
    );
    facts.end += size_hint;
    facts.update_len();
}

/// Errors returned when using [`FactTerms`] methods.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FactTermsError {
    /// The destination buffer's length is less than the number of terms
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

/// Terms for a fact.
#[derive(Debug)]
pub struct FactTerms<'a> {
    pub(crate) constants: TermIter<'a>,
    pub(crate) context: Section<'a>,
}

impl<'a> FactTerms<'a> {
    /// Returns the terms as a [`Vec`].
    #[must_use]
    pub fn to_vec(&self) -> Vec<Constant<'a>> {
        self.constants
            .clone()
            .map(|c| values::constant(&self.context, c))
            .collect::<Vec<_>>()
    }

    /// Fills a buffer with the [`Constant`] values of the fact's terms.
    ///
    /// Returns the slice of buffer used.
    ///
    /// # Errors
    ///
    /// If the destination buffer's length is less than the number of terms, an error is returned.
    pub fn fill_buf<'c>(
        &self,
        dst: &'c mut [Constant<'a>],
    ) -> Result<&'c [Constant<'a>], FactTermsError> {
        let mut idx = 0;

        for id in self.constants.clone() {
            if let Some(v) = dst.get_mut(idx) {
                *v = values::constant(&self.context, id);
            } else {
                return Err(FactTermsError::InvalidLength);
            }
            idx += 1;
        }

        Ok(&dst[..idx])
    }
}
