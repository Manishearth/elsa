//! This crate provides various "Frozen" collections.
//!
//! These are append-only collections where references to entries can be held
//! on to even across insertions. This is safe because these collections only
//! support storing data that's present behind some indirection -- i.e. `String`,
//! `Vec<T>`, `Box<T>`, etc, and they only yield references to the data behind the
//! allocation (`&str`, `&[T]`, and `&T` respectively)
//!
//! The typical use case is having a global cache of strings or other data which the rest of the program borrows from.

use std::borrow::Borrow;
use std::cell::{Cell, UnsafeCell};
use std::collections::HashMap;
use std::hash::Hash;
use std::ops::Index;

use stable_deref_trait::StableDeref;

/// Append-only version of `std::collections::HashMap` where
/// insertion does not require mutable access
pub struct FrozenMap<K, V> {
    map: UnsafeCell<HashMap<K, V>>,
    /// Eq/Hash implementations can have side-effects, and using Rc it is possible
    /// for FrozenMap::insert to be called on a key that itself contains the same 
    /// `FrozenMap`, whose `eq` implementation also calls FrozenMap::insert
    ///
    /// We use this `in_use` flag to guard against any reentrancy.
    in_use: Cell<bool>,
}

// safety: UnsafeCell implies !Sync

impl<K: Eq + Hash, V: StableDeref> FrozenMap<K, V> {
    // these should never return &K or &V
    // these should never delete any entries

    pub fn new() -> Self {
        Self {
            map: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false)
        }
    }

    pub fn insert(&self, k: K, v: V) -> &V::Target {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let map = self.map.get();
            &*(*map).entry(k).or_insert(v)
        };
        self.in_use.set(false);
        ret
    }

    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V::Target>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let map = self.map.get();
            (*map).get(k).map(|x| &**x)
        };
        self.in_use.set(false);
        ret
    }

    // TODO add more
}

impl<K, V> From<HashMap<K, V>> for FrozenMap<K, V> {
    fn from(map: HashMap<K, V>) -> Self {
        Self {
            map: UnsafeCell::new(map),
            in_use: Cell::new(false)
        }
    }
}

impl<K: Eq + Hash, V: StableDeref> Index<K> for FrozenMap<K, V> {
    type Output = V::Target;
    fn index(&self, idx: K) -> &V::Target {
        self.get(&idx).expect("attempted to index FrozenMap with unknown key")
    }
}

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
