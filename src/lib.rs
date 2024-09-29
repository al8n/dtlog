#![doc = include_str!("../README.md")]
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]

#[cfg(not(any(feature = "std", feature = "alloc")))]
compile_error!("This crate can only be used with 'std' or 'alloc' feature is enabled.");

#[cfg(all(feature = "std", not(feature = "alloc")))]
extern crate std;

mod log;
pub use log::*;

mod options;
pub use options::*;

/// Error types
pub mod error;

#[cfg(test)]
mod tests;
