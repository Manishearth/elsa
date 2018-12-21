//! **This crate is unfinished, please don't use it yet!**

//! This crate provides various "Frozen" collections.
//!
//! These are append-only collections where references to entries can be held
//! on to even across insertions. This is safe because these collections only
//! support storing data that's present behind some indirection -- i.e. `String`,
//! `Vec<T>`, `Box<T>`, etc, and they only yield references to the data behind the
//! allocation (`&str`, `&[T]`, and `&T` respectively)
//!
//! The typical use case is having a global cache of strings or other data which the rest of the program borrows from.
//!
//! I haven't completely thought out the safety aspects of this, use at your own risk.

use std::borrow::Borrow;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::hash::Hash;

use stable_deref_trait::StableDeref;

/// Append-only version of `std::collections::HashMap` where
/// insertion does not require mutable access
pub struct FrozenMap<K, V> {
    map: UnsafeCell<HashMap<K, V>>,
}

// safety: UnsafeCell implies !Sync

impl<K: Eq + Hash, V: StableDeref> FrozenMap<K, V> {
    // these should never return &K or &V
    // these should never delete any entries

    pub fn new() -> Self {
        Self {
            map: UnsafeCell::new(Default::default()),
        }
    }

    pub fn insert(&self, k: K, v: V) -> &V::Target {
        unsafe {
            let map = self.map.get();
            &*(*map).entry(k).or_insert(v)
        }
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&V::Target>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        unsafe {
            let map = self.map.get();
            (*map).get(k).map(|x| &**x)
        }
    }

    // TODO add more
}

/// Append-only version of `std::vec::Vec` where
/// insertion does not require mutable access
pub struct FrozenVec<T> {
    vec: UnsafeCell<Vec<T>>,
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

    // TODO add more
}
