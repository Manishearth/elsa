//! This crate provides various "Frozen" collections.
//!
//! These are append-only collections where references to entries can be held
//! on to even across insertions. This is safe because these collections only
//! support storing data that's present behind some indirection -- i.e. `String`,
//! `Vec<T>`, `Box<T>`, etc, and they only yield references to the data behind the
//! allocation (`&str`, `&[T]`, and `&T` respectively)
//!
//! The typical use case is having a global cache of strings or other data which the rest of the program borrows from.

use std::cell::UnsafeCell;
use std::iter::FromIterator;
use std::ops::Index;

use stable_deref_trait::StableDeref;

mod map;

pub use map::FrozenMap;

/// Append-only version of `std::vec::Vec` where
/// insertion does not require mutable access
pub struct FrozenVec<T> {
    vec: UnsafeCell<Vec<T>>,
    // XXXManishearth do we need a reentrancy guard here as well?
    // StableDeref may not guarantee that there are no side effects
}

// safety: UnsafeCell implies !Sync

impl<T: StableDeref> FrozenVec<T> {
    pub fn new() -> Self {
        Self {
            vec: UnsafeCell::new(Default::default()),
        }
    }

    // these should never return &T
    // these should never delete any entries

    pub fn push(&self, val: T) {
        unsafe {
            let vec = self.vec.get();
            (*vec).push(val)
        }
    }

    pub fn get(&self, index: usize) -> Option<&T::Target> {
        unsafe {
            let vec = self.vec.get();
            (*vec).get(index).map(|x| &**x)
        }
    }

    pub fn len(&self) -> usize {
        unsafe {
            let vec = self.vec.get();
            (*vec).len()
        }
    }

    // TODO add more
}


impl<T> From<Vec<T>> for FrozenVec<T> {
    fn from(vec: Vec<T>) -> Self {
        Self {
            vec: UnsafeCell::new(vec)
        }
    }
}

impl<T: StableDeref> Index<usize> for FrozenVec<T> {
    type Output = T::Target;
    fn index(&self, idx: usize) -> &T::Target {
        self.get(idx)
            .unwrap_or_else(|| panic!("index out of bounds: the len is {} but the index is {}", self.len(), idx))
    }
}

impl<A> FromIterator<A> for FrozenVec<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = A> {
        let vec: Vec<_> = iter.into_iter().collect();
        vec.into()
    }
}
