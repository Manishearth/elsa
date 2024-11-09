//! _🎵 Immutability never bothered me anyway 🎶_
//!
//! This crate provides various "Frozen" collections.
//!
//! These are append-only collections where references to entries can be held
//! on to even across insertions. This is safe because these collections only
//! support storing data that's present behind some indirection -- i.e. `String`,
//! `Vec<T>`, `Box<T>`, etc, and they only yield references to the data behind the
//! allocation (`&str`, `&[T]`, and `&T` respectively)
//!
//! The typical use case is having a global cache of strings or other data which the rest of the program borrows from.

pub mod map;
#[cfg(feature = "hash-set")]
pub mod set;
pub mod vec;

#[cfg(feature = "indexmap")]
pub mod index_map;
#[cfg(feature = "indexmap")]
pub mod index_set;

pub mod sync;

pub use map::{FrozenBTreeMap, FrozenMap};
#[cfg(feature = "hash-set")]
pub use set::{FrozenBTreeSet, FrozenSet};
pub use vec::FrozenVec;

#[cfg(feature = "indexmap")]
pub use index_map::FrozenIndexMap;
#[cfg(feature = "indexmap")]
pub use index_set::FrozenIndexSet;
