use std::borrow::Borrow;
use std::cell::{Cell, UnsafeCell};
use std::collections::hash_map::RandomState;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::hash::{BuildHasher, Hash};
use std::iter::FromIterator;
use std::ops::Index;

use stable_deref_trait::StableDeref;

/// Append-only version of `std::collections::HashMap` where
/// insertion does not require mutable access
pub struct FrozenMap<K, V, S = RandomState> {
    map: UnsafeCell<HashMap<K, V, S>>,
    /// Eq/Hash implementations can have side-effects, and using Rc it is possible
    /// for FrozenMap::insert to be called on a key that itself contains the same
    /// `FrozenMap`, whose `eq` implementation also calls FrozenMap::insert
    ///
    /// We use this `in_use` flag to guard against any reentrancy.
    in_use: Cell<bool>,
}

// safety: UnsafeCell implies !Sync

impl<K: Eq + Hash, V> FrozenMap<K, V> {
    pub fn new() -> Self {
        Self {
            map: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false),
        }
    }
}

impl<K: Eq + Hash, V: StableDeref, S: BuildHasher> FrozenMap<K, V, S> {
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

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenMap;
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
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let map = self.map.get();
            (*map).get(k).map(|x| &**x)
        };
        self.in_use.set(false);
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
    /// use elsa::FrozenMap;
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
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let map = self.map.get();
            (*map).get(k).map(f)
        };
        self.in_use.set(false);
        ret
    }

    pub fn into_map(self) -> HashMap<K, V, S> {
        self.map.into_inner()
    }

    /// Get mutable access to the underlying [`HashMap`].
    ///
    /// This is safe, as it requires a `&mut self`, ensuring nothing is using
    /// the 'frozen' contents.
    pub fn as_mut(&mut self) -> &mut HashMap<K, V, S> {
        unsafe { &mut *self.map.get() }
    }

    // TODO add more
}

impl<K, V, S> From<HashMap<K, V, S>> for FrozenMap<K, V, S> {
    fn from(map: HashMap<K, V, S>) -> Self {
        Self {
            map: UnsafeCell::new(map),
            in_use: Cell::new(false),
        }
    }
}

impl<K: Eq + Hash, V: StableDeref, S: BuildHasher> Index<K> for FrozenMap<K, V, S> {
    type Output = V::Target;
    fn index(&self, idx: K) -> &V::Target {
        self.get(&idx)
            .expect("attempted to index FrozenMap with unknown key")
    }
}

impl<K: Eq + Hash, V, S: BuildHasher + Default> FromIterator<(K, V)> for FrozenMap<K, V, S> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (K, V)>,
    {
        let map: HashMap<_, _, _> = iter.into_iter().collect();
        map.into()
    }
}

impl<K: Eq + Hash, V, S: Default> Default for FrozenMap<K, V, S> {
    fn default() -> Self {
        Self {
            map: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false),
        }
    }
}

/// Append-only version of `std::collections::BTreeMap` where
/// insertion does not require mutable access
pub struct FrozenBTreeMap<K, V> {
    map: UnsafeCell<BTreeMap<K, V>>,
    /// Eq/Hash implementations can have side-effects, and using Rc it is possible
    /// for FrozenBTreeMap::insert to be called on a key that itself contains the same
    /// `FrozenBTreeMap`, whose `eq` implementation also calls FrozenBTreeMap::insert
    ///
    /// We use this `in_use` flag to guard against any reentrancy.
    in_use: Cell<bool>,
}

// safety: UnsafeCell implies !Sync

impl<K: Clone + Ord, V: StableDeref> FrozenBTreeMap<K, V> {
    pub fn new() -> Self {
        Self {
            map: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false),
        }
    }
}

impl<K: Clone + Ord, V: StableDeref> FrozenBTreeMap<K, V> {
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

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenBTreeMap;
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
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let map = self.map.get();
            (*map).get(k).map(|x| &**x)
        };
        self.in_use.set(false);
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
    /// use elsa::FrozenBTreeMap;
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
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let map = self.map.get();
            (*map).get(k).map(f)
        };
        self.in_use.set(false);
        ret
    }

    pub fn into_map(self) -> BTreeMap<K, V> {
        self.map.into_inner()
    }

    /// Get mutable access to the underlying [`HashMap`].
    ///
    /// This is safe, as it requires a `&mut self`, ensuring nothing is using
    /// the 'frozen' contents.
    pub fn as_mut(&mut self) -> &mut BTreeMap<K, V> {
        unsafe { &mut *self.map.get() }
    }

    // TODO add more
}

impl<K: Clone + Ord, V: StableDeref> From<BTreeMap<K, V>> for FrozenBTreeMap<K, V> {
    fn from(map: BTreeMap<K, V>) -> Self {
        Self {
            map: UnsafeCell::new(map),
            in_use: Cell::new(false),
        }
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
        Self {
            map: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false),
        }
    }
}
