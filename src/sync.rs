//! **This module is experimental**
//!
//! This module provides threadsafe versions of FrozenMap and FrozenVec,
//! ideal for use as a cache.
//!
//! These lock internally, however locks only last as long as the method calls
//!

use stable_deref_trait::StableDeref;
use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::hash::Hash;
use std::iter::{FromIterator, IntoIterator};
use std::ops::Index;

use std::sync::RwLock;

/// Append-only threadsafe version of `std::collections::HashMap` where
/// insertion does not require mutable access
pub struct FrozenMap<K, V> {
    map: RwLock<HashMap<K, V>>,
}

impl<K: Eq + Hash, V: StableDeref> FrozenMap<K, V> {
    // these should never return &K or &V
    // these should never delete any entries

    pub fn new() -> Self {
        Self {
            map: RwLock::new(Default::default()),
        }
    }

    pub fn insert(&self, k: K, v: V) -> &V::Target {
        let mut map = self.map.write().unwrap();
        let ret = unsafe {
            let inserted = &**map.entry(k).or_insert(v);
            &*(inserted as *const _)
        };
        ret
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenMap;
    ///
    /// let map = FrozenMap::new();
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V::Target>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let map = self.map.read().unwrap();
        let ret = unsafe { map.get(k).map(|x| &*(&**x as *const V::Target)) };
        ret
    }

    /// Applies a function to the owner of the value corresponding to the key (if any).
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenMap;
    ///
    /// let map = FrozenMap::new();
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.map_get(&1, Clone::clone), Some(Box::new("a")));
    /// assert_eq!(map.map_get(&2, Clone::clone), None);
    /// ```
    pub fn map_get<Q: ?Sized, T, F>(&self, k: &Q, f: F) -> Option<T>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
        F: FnOnce(&V) -> T,
    {
        let map = self.map.read().unwrap();
        let ret = map.get(k).map(f);
        ret
    }

    // TODO add more
}

/// Append-only threadsafe version of `std::vec::Vec` where
/// insertion does not require mutable access
pub struct FrozenVec<T> {
    vec: RwLock<Vec<T>>,
}

impl<T: StableDeref> FrozenVec<T> {
    pub fn new() -> Self {
        Self {
            vec: RwLock::new(Default::default()),
        }
    }

    // these should never return &T
    // these should never delete any entries

    pub fn push(&self, val: T) {
        let mut vec = self.vec.write().unwrap();
        vec.push(val);
    }

    /// Push, immediately getting a reference to the element
    pub fn push_get(&self, val: T) -> &T::Target {
        let mut vec = self.vec.write().unwrap();
        vec.push(val);
        unsafe { &*(&**vec.get_unchecked(vec.len() - 1) as *const T::Target) }
    }

    /// Push, immediately getting a an index of the element
    ///
    /// Index can then be used with the `get` method
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenVec;
    ///
    /// let map = FrozenVec::new();
    /// let idx = map.push_get_index(String::from("a"));
    /// assert_eq!(map.get(idx), Some("a"));
    /// assert_eq!(idx, 0);
    /// assert_eq!(map.push_get_index(String::from("b")), 1);
    /// ```
    pub fn push_get_index(&self, val: T) -> usize {
        let mut vec = self.vec.write().unwrap();
        let index = vec.len();
        vec.push(val);
        return index;
    }

    pub fn get(&self, index: usize) -> Option<&T::Target> {
        let vec = self.vec.read().unwrap();
        unsafe { vec.get(index).map(|x| &*(&**x as *const T::Target)) }
    }

    // TODO add more
}

/// Append-only threadsafe version of `std::collections::BTreeMap` where
/// insertion does not require mutable access
#[derive(Debug)]
pub struct FrozenBTreeMap<K, V>(RwLock<BTreeMap<K, V>>);

impl<K: Clone + Ord, V: StableDeref> FrozenBTreeMap<K, V> {
    pub fn new() -> Self {
        Self(RwLock::new(BTreeMap::new()))
    }

    // these should never return &K or &V
    // these should never delete any entries

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Ord`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenBTreeMap;
    ///
    /// let map = FrozenBTreeMap::new();
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V::Target>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        let map = self.0.read().unwrap();
        let ret = unsafe { map.get(k).map(|x| &*(&**x as *const V::Target)) };
        ret
    }

    pub fn insert(&self, k: K, v: V) -> &V::Target {
        let mut map = self.0.write().unwrap();
        let ret = unsafe {
            let inserted = &**map.entry(k).or_insert(v);
            &*(inserted as *const _)
        };
        ret
    }

    /// Gets the item for the given key, or, if it doesn't exist, uses
    /// the closure to create, insert, and return a reference to it.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Ord`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenBTreeMap;
    ///
    /// let map = FrozenBTreeMap::new();
    /// assert_eq!(map.get_or_insert(&1, || -> Result<String,()> { Ok(String::from("a")) }), Ok("a"));
    /// assert_eq!(map.get_or_insert(&1, || -> Result<String,()> { panic!() }), Ok("a"));
    /// ```
    pub fn get_or_insert<'a, E>(
        &'a self,
        k: &K,
        value_fn: impl FnOnce() -> Result<V, E>,
    ) -> Result<&'a V::Target, E> {
        // The RHS of an if-let statement doesn't get dropped before the else block, so we have
        // to do this manually
        let guard = self.0.read().unwrap();
        let ptr = if let Some(x) = guard.get(k) {
            &**x as *const V::Target
        } else {
            drop(guard);

            // We compute the value outside the or_insert_with because
            // * it can fail
            // * we don't want to hold the lock while computing it
            let value = value_fn()?;

            let mut guard = self.0.write().unwrap();
            // highly important for the closure to be called during the guard only
            &**guard.entry(k.clone()).or_insert_with(|| value) as *const V::Target
        };

        // Even though we've given up the lock on it, the value is still there
        // because V is a stable reference and we never drop anything.
        Ok(unsafe { &*ptr })
    }

    /// Applies a function to the owner of the value corresponding to the key (if any).
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Ord`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenBTreeMap;
    ///
    /// let map = FrozenBTreeMap::new();
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.map_get(&1, Clone::clone), Some(Box::new("a")));
    /// assert_eq!(map.map_get(&2, Clone::clone), None);
    /// ```
    pub fn map_get<Q: ?Sized, T, F>(&self, k: &Q, f: F) -> Option<T>
    where
        K: Borrow<Q>,
        Q: Ord,
        F: FnOnce(&V) -> T,
    {
        let map = self.0.read().unwrap();
        let ret = map.get(k).map(f);
        ret
    }
}

impl<K: Clone + Ord, V: StableDeref> From<BTreeMap<K, V>> for FrozenBTreeMap<K, V> {
    fn from(map: BTreeMap<K, V>) -> Self {
        Self(RwLock::new(map))
    }
}

impl<K: Clone + Ord, V: StableDeref> Index<K> for FrozenBTreeMap<K, V> {
    type Output = V::Target;
    fn index(&self, idx: K) -> &V::Target {
        self.get(&idx)
            .expect("attempted to index FrozenBTreeMap with unknown key")
    }
}

impl<K: Clone + Ord, V: StableDeref> FromIterator<(K, V)> for FrozenBTreeMap<K, V> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (K, V)>,
    {
        let map: BTreeMap<_, _> = iter.into_iter().collect();
        map.into()
    }
}

impl<K: Clone + Ord, V: StableDeref> Default for FrozenBTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}
