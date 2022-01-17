use std::borrow::Borrow;
use std::cell::{Cell, UnsafeCell};
use std::collections::HashMap;
use std::hash::Hash;
use std::iter::FromIterator;
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

impl<K: Eq + Hash, V> FrozenMap<K, V> {
    pub fn new() -> Self {
        Self {
            map: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false),
        }
    }
}

impl<K: Eq + Hash, V: StableDeref> FrozenMap<K, V> {
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

    pub fn into_map(self) -> HashMap<K, V> {
        self.map.into_inner()
    }

    /// Get mutable access to the underlying [`HashMap`].
    ///
    /// This is safe, as it requires a `&mut self`, ensuring nothing is using
    /// the 'frozen' contents.
    pub fn as_mut(&mut self) -> &mut HashMap<K, V> {
        unsafe { &mut *self.map.get() }
    }

    /// Create [`HashMap`] with copies of original keys and references to original values.
    /// So you can iterate over `FrozenMap` if you have shared reference to it
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenMap;
    ///
    /// let map = FrozenMap::new();
    /// map.insert(1, Box::new("a"));
    /// for i in map.map_of_refs() {
    ///     assert_eq!(i, (1, &"a"));
    /// }
    /// ```
    ///
    /// # Rationale
    ///
    /// Let's assume we have shared reference to our `FrozenMap` and we want to
    /// read somehow all its values. How to do this? We cannot return iterator to underlying
    /// [`HashMap`]: this will not work if we insert new values before dropping
    /// the iterator. Maybe we can create deep copy of underlying [`HashMap`]? No.
    /// First, this will require [`Clone`] for `V`, and so in particular this will not work if `V` is
    /// another `FrozenMap` (as of 2022-01-17 `FrozenMap` is not [`Clone`]). Second, this
    /// will not have much sense, because values may be self-referential.
    /// And so their copies will contain references to original values,
    /// this is not what we want. So, the only remaining way to read all the values is this:
    /// create shallow copy of underlying [`HashMap`]. Such copy will contain copies of the keys
    /// and references to the values. Once you got such [`HashMap`], you can iterate over it
    pub fn map_of_refs(&self) -> HashMap<K, &V::Target>
    where
        K: Clone,
    {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let mut result = HashMap::new();
        for (k, v) in unsafe { (*self.map.get()).iter() } {
            result.insert(K::clone(k), &**v);
        }
        self.in_use.set(false);
        result
    }

    // TODO add more
}

impl<K, V> From<HashMap<K, V>> for FrozenMap<K, V> {
    fn from(map: HashMap<K, V>) -> Self {
        Self {
            map: UnsafeCell::new(map),
            in_use: Cell::new(false),
        }
    }
}

impl<K: Eq + Hash, V: StableDeref> Index<K> for FrozenMap<K, V> {
    type Output = V::Target;
    fn index(&self, idx: K) -> &V::Target {
        self.get(&idx)
            .expect("attempted to index FrozenMap with unknown key")
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for FrozenMap<K, V> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (K, V)>,
    {
        let map: HashMap<_, _> = iter.into_iter().collect();
        map.into()
    }
}

impl<K: Eq + Hash, V> Default for FrozenMap<K, V> {
    fn default() -> Self {
        FrozenMap::new()
    }
}
