use std::borrow::Borrow;
use std::cell::{Cell, UnsafeCell};
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::Index;

use indexmap::IndexMap;
use stable_deref_trait::StableDeref;

/// Append-only version of `indexmap::IndexMap` where
/// insertion does not require mutable access
pub struct FrozenIndexMap<K, V> {
    map: UnsafeCell<IndexMap<K, V>>,
    /// Eq/Hash implementations can have side-effects, and using Rc it is possible
    /// for FrozenIndexMap::insert to be called on a key that itself contains the same
    /// `FrozenIndexMap`, whose `eq` implementation also calls FrozenIndexMap::insert
    ///
    /// We use this `in_use` flag to guard against any reentrancy.
    in_use: Cell<bool>,
}

// safety: UnsafeCell implies !Sync

impl<K: Eq + Hash, V> FrozenIndexMap<K, V> {
    pub fn new() -> Self {
        Self {
            map: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false),
        }
    }
}

impl<K: Eq + Hash, V: StableDeref> FrozenIndexMap<K, V> {
    // these should never return &K or &V
    // these should never delete any entries
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

    // these should never return &K or &V
    // these should never delete any entries
    pub fn insert_full(&self, k: K, v: V) -> (usize, &V::Target) {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let map = self.map.get();
            let entry = (*map).entry(k);
            let index = entry.index();
            (index, &**entry.or_insert(v))
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

    pub fn into_map(self) -> IndexMap<K, V> {
        self.map.into_inner()
    }

    /// Get mutable access to the underlying [`IndexMap`].
    ///
    /// This is safe, as it requires a `&mut self`, ensuring nothing is using
    /// the 'frozen' contents.
    pub fn as_mut(&mut self) -> &mut IndexMap<K, V> {
        unsafe { &mut *self.map.get() }
    }

    /// Returns true if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let map = self.map.get();
            (*map).is_empty()
        };
        self.in_use.set(false);
        ret
    }
}

impl<K, V> From<IndexMap<K, V>> for FrozenIndexMap<K, V> {
    fn from(map: IndexMap<K, V>) -> Self {
        Self {
            map: UnsafeCell::new(map),
            in_use: Cell::new(false),
        }
    }
}

impl<K: Eq + Hash, V: StableDeref> Index<K> for FrozenIndexMap<K, V> {
    type Output = V::Target;
    fn index(&self, idx: K) -> &V::Target {
        self.get(&idx)
            .expect("attempted to index FrozenIndexMap with unknown key")
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for FrozenIndexMap<K, V> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (K, V)>,
    {
        let map: IndexMap<_, _> = iter.into_iter().collect();
        map.into()
    }
}

impl<K: Eq + Hash, V> Default for FrozenIndexMap<K, V> {
    fn default() -> Self {
        FrozenIndexMap::new()
    }
}
