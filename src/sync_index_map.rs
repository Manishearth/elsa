use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::iter::FromIterator;
use std::ops::Index;

use indexmap::IndexMap;
use stable_deref_trait::StableDeref;
use std::sync::RwLock;

/// Append-only threadsafe version of `indexmap::IndexMap` where
/// insertion does not require mutable access
#[derive(Debug)]
pub struct FrozenIndexMap<K, V, S = RandomState> {
    map: RwLock<IndexMap<K, V, S>>,
}

// safety: UnsafeCell implies !Sync

impl<K: Eq + Hash, V> FrozenIndexMap<K, V> {
    pub fn new() -> Self {
        Self {
            map: RwLock::new(Default::default()),
        }
    }
}

impl<K: Eq + Hash, V: StableDeref, S: BuildHasher> FrozenIndexMap<K, V, S> {
    // these should never return &K or &V
    // these should never delete any entries
    //
    /// If the key exists in the map, returns a reference to the corresponding
    /// value, otherwise inserts a new entry in the map for that key
    /// and returns a reference to the generated value.
    ///
    /// Existing values are never overwritten.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Example
    /// ```
    /// use elsa::sync_index_map::FrozenIndexMap;
    /// let map = FrozenIndexMap::new();
    /// assert_eq!(map.insert(1, Box::new("a")), &"a");
    /// assert_eq!(map.insert(1, Box::new("b")), &"a");
    /// ```
    pub fn insert(&self, k: K, v: V) -> &V::Target {
        let mut map = self.map.write().unwrap();
        let ret = unsafe {
            let inserted = &**map.entry(k).or_insert(v);
            &*(inserted as *const _)
        };
        ret
    }

    // these should never return &K or &V
    // these should never delete any entries
    /// If the key exists in the map, returns a reference to the corresponding
    /// value and its index, otherwise inserts a new entry in the map for that key
    /// and returns a reference to the generated value and its index.
    ///
    /// Existing values are never overwritten.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Example
    /// ```
    /// use elsa::sync_index_map::FrozenIndexMap;
    /// let map = FrozenIndexMap::new();
    /// assert_eq!(map.insert_full(12, Box::new("a")), (0, &"a"));
    /// assert_eq!(map.insert_full(12, Box::new("b")), (0, &"a"));
    /// ```
    pub fn insert_full(&self, k: K, v: V) -> (usize, &V::Target) {
        let mut map = self.map.write().unwrap();
        let ret = unsafe {
            let entry = (*map).entry(k);
            let index = entry.index();
            let value = &**entry.or_insert(v);
            (index, &*(value as *const _))
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
    /// use elsa::sync_index_map::FrozenIndexMap;
    ///
    /// let map = FrozenIndexMap::new();
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

    /// Returns a reference to the key-value mapping corresponding to an index.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync_index_map::FrozenIndexMap;
    ///
    /// let map = FrozenIndexMap::new();
    /// let (idx, _ref) = map.insert_full(Box::new("foo"), Box::new("a"));
    /// assert_eq!(idx, 0);
    /// assert_eq!(map.get_index(idx), Some((&"foo", &"a")));
    /// assert_eq!(map.get_index(idx + 1), None);
    /// ```
    pub fn get_index(&self, index: usize) -> Option<(&K::Target, &V::Target)>
    where
        K: StableDeref,
    {
        let map = self.map.read().unwrap();
        let ret = unsafe {
            map.get_index(index)
                .map(|(k, v)| (&**k, &**v))
                .map(|(k, v)| (&*(k as *const K::Target), &*(v as *const V::Target)))
        };
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
    /// use elsa::sync_index_map::FrozenIndexMap;
    ///
    /// let map = FrozenIndexMap::new();
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
}

impl<K, V, S> FrozenIndexMap<K, V, S> {
    /// Collects the contents of this map into a vector of tuples.
    ///
    /// The order of the entries is as if iterating an [`IndexMap`].
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync_index_map::FrozenIndexMap;
    ///
    /// let map = FrozenIndexMap::new();
    /// map.insert(1, Box::new("a"));
    /// map.insert(2, Box::new("b"));
    /// let tuple_vec = map.into_tuple_vec();
    ///
    /// assert_eq!(tuple_vec, vec![(1, Box::new("a")), (2, Box::new("b"))]);
    /// ```
    pub fn into_tuple_vec(self) -> Vec<(K, V)> {
        self.map
            .into_inner()
            .unwrap()
            .into_iter()
            .collect::<Vec<_>>()
    }

    pub fn into_map(self) -> IndexMap<K, V, S> {
        self.map.into_inner().unwrap()
    }

    /// Get mutable access to the underlying [`IndexMap`].
    ///
    /// This is safe, as it requires a `&mut self`, ensuring nothing is using
    /// the 'frozen' contents.
    pub fn as_mut(&mut self) -> &mut IndexMap<K, V, S> {
        self.map.get_mut().unwrap()
    }

    /// # Examples
    ///
    /// ```
    /// use elsa::sync_index_map::FrozenIndexMap;
    ///
    /// let map = FrozenIndexMap::new();
    /// assert_eq!(map.is_empty(), true);
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        let map = self.map.read().unwrap();
        map.is_empty()
    }
}

impl<K, V, S> From<IndexMap<K, V, S>> for FrozenIndexMap<K, V, S> {
    fn from(map: IndexMap<K, V, S>) -> Self {
        Self {
            map: RwLock::new(map),
        }
    }
}

impl<Q: ?Sized, K: Eq + Hash, V: StableDeref, S: BuildHasher> Index<&Q> for FrozenIndexMap<K, V, S>
where
    Q: Eq + Hash,
    K: Eq + Hash + Borrow<Q>,
    V: StableDeref,
    S: BuildHasher,
{
    type Output = V::Target;

    /// # Examples
    ///
    /// ```
    /// use elsa::sync_index_map::FrozenIndexMap;
    ///
    /// let map = FrozenIndexMap::new();
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map[&1], "a");
    /// ```
    fn index(&self, idx: &Q) -> &V::Target {
        self.get(&idx)
            .expect("attempted to index FrozenIndexMap with unknown key")
    }
}

impl<K: Eq + Hash, V, S: BuildHasher + Default> FromIterator<(K, V)> for FrozenIndexMap<K, V, S> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (K, V)>,
    {
        let map: IndexMap<_, _, _> = iter.into_iter().collect();
        map.into()
    }
}

impl<K: Eq + Hash, V, S: Default> Default for FrozenIndexMap<K, V, S> {
    fn default() -> Self {
        Self {
            map: RwLock::new(Default::default()),
        }
    }
}
