use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::iter::FromIterator;
use std::ops::Index;

use indexmap::IndexMap;
#[cfg(all(feature = "shuttle", test))]
use shuttle::sync::RwLock;
use stable_deref_trait::StableDeref;
#[cfg(not(all(feature = "shuttle", test)))]
use std::sync::RwLock;
use std::sync::TryLockError;

/// Append-only threadsafe version of `indexmap::IndexMap` where
/// insertion does not require mutable access
pub struct FrozenIndexMap<K, V, S = RandomState> {
    map: RwLock<IndexMap<K, V, S>>,
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for FrozenIndexMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.map.try_read() {
            Ok(guard) => guard.fmt(f),
            Err(TryLockError::Poisoned(err)) => f
                .debug_tuple("FrozenIndexMap")
                .field(&&**err.get_ref())
                .finish(),
            Err(TryLockError::WouldBlock) => {
                struct LockedPlaceholder;
                impl fmt::Debug for LockedPlaceholder {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        f.write_str("<locked>")
                    }
                }
                f.debug_tuple("FrozenIndexMap")
                    .field(&LockedPlaceholder)
                    .finish()
            }
        }
    }
}

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
    /// use elsa::sync::index_map::FrozenIndexMap;
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
    /// use elsa::sync::index_map::FrozenIndexMap;
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
    /// use elsa::sync::index_map::FrozenIndexMap;
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
    /// use elsa::sync::index_map::FrozenIndexMap;
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
    /// use elsa::sync::index_map::FrozenIndexMap;
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
    /// use elsa::sync::index_map::FrozenIndexMap;
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
    #[cfg(not(feature = "shuttle"))]
    pub fn as_mut(&mut self) -> &mut IndexMap<K, V, S> {
        self.map.get_mut().unwrap()
    }

    /// # Examples
    ///
    /// ```
    /// use elsa::sync::index_map::FrozenIndexMap;
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
    /// use elsa::sync::index_map::FrozenIndexMap;
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

#[cfg(all(feature = "shuttle", test))]
mod tests {
    use shuttle::rand::{thread_rng, Rng};
    use shuttle::thread;
    use std::sync::Arc;

    #[test]
    fn test_insert_idempotent() {
        shuttle::check_random(
            || {
                let map = Arc::new(super::FrozenIndexMap::new());
                let map_clone = map.clone();
                let t1 = thread::spawn(move || {
                    let i1 = map.insert(1, Box::new("a"));
                    let i2 = map.insert(1, Box::new("dummy"));
                    assert_eq!(i1, i2);
                    *i1
                });
                let t2 = thread::spawn(move || {
                    let i1 = map_clone.insert(1, Box::new("b"));
                    let i2 = map_clone.insert(1, Box::new("dummy"));
                    assert_eq!(i1, i2);
                    *i1
                });
                let v1 = t1.join().unwrap();
                let v2 = t2.join().unwrap();
                assert_eq!(v1, v2);
            },
            100,
        )
    }

    #[test]
    fn test_insert_full_incremental() {
        shuttle::check_random(
            || {
                let map = Arc::new(super::FrozenIndexMap::new());
                let map_clone = map.clone();
                let t1 = thread::spawn(move || {
                    let (idx1, _) = map.insert_full(11, Box::new("a"));
                    idx1
                });
                let t2 = thread::spawn(move || {
                    let (idx2, _) = map_clone.insert_full(22, Box::new("b"));
                    idx2
                });
                let idx1 = t1.join().unwrap();
                let idx2 = t2.join().unwrap();
                assert_eq!(0, std::cmp::min(idx1, idx2));
                assert_eq!(1, std::cmp::max(idx2, idx1));
            },
            100,
        )
    }

    #[test]
    fn test_get_index() {
        shuttle::check_random(
            || {
                let map = Arc::new(super::FrozenIndexMap::new());
                let map_clone = map.clone();
                let map_clone2 = map.clone();
                let t1 = thread::spawn(move || {
                    let (idx1, v) = map.insert_full(Box::new("foo"), Box::new("a"));
                    ("a" == *v).then(|| idx1)
                });
                let t2 = thread::spawn(move || {
                    let (idx2, v) = map_clone.insert_full(Box::new("foo"), Box::new("b"));
                    ("b" == *v).then(|| idx2)
                });
                let idx1 = t1.join().unwrap();
                let idx2 = t2.join().unwrap();

                let idx = idx1.or(idx2).unwrap();
                assert_eq!(idx, 0);
                assert_eq!(*map_clone2.get_index(idx).unwrap().0, "foo");
            },
            100,
        )
    }

    #[test]
    fn test_len() {
        const ITEMS: usize = 100;
        shuttle::check_random(
            || {
                let map = Arc::new(super::FrozenIndexMap::new());
                let map_clone = map.clone();
                let map_clone2 = map.clone();
                let t1 = thread::spawn(move || {
                    for i in 0..ITEMS {
                        let v = thread_rng().gen::<u64>();
                        map.insert(i, Box::new(v));
                    }
                });
                let t2 = thread::spawn(move || {
                    for i in 0..ITEMS {
                        let v = thread_rng().gen::<u64>();
                        map_clone.insert(i, Box::new(v));
                    }
                });
                t1.join().unwrap();
                t2.join().unwrap();
                for i in 0..ITEMS {
                    assert!(map_clone2.get(&i).is_some());
                }
                assert_eq!(map_clone2.insert_full(ITEMS, Box::new(0)).0, ITEMS);
            },
            100,
        )
    }
}
