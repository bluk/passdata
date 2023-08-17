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

#[cfg(all(feature = "alloc", not(feature = "std")))]
extern crate alloc;

pub mod error;
pub(crate) mod values;
