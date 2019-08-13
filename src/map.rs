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
            in_use: Cell::new(false)
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

    pub fn into_map(self) -> HashMap<K, V> {
        self.map.into_inner()
    }

    // TODO add more
}

impl<K: Eq + Hash + StableDeref, V: StableDeref> FrozenMap<K, V> {
    pub fn iter(&self) -> Iter<K, V> {
        self.into_iter()
    }
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

impl<K: Eq + Hash, V> FromIterator<(K, V)> for FrozenMap<K, V> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (K, V)> {
        let map: HashMap<_, _> = iter.into_iter().collect();
        map.into()
    }
}

impl<K: Eq + Hash, V:> Default for FrozenMap<K, V> {
    fn default() -> Self {
        FrozenMap::new()
    }
}

/// Iterator over FrozenHashMap, obtained via `.iter()`
///
/// Inserting elements to the map during iteration will panic
pub struct Iter<'a, K, V> {
    map: &'a FrozenMap<K, V>,
    iter: Option<std::collections::hash_map::Iter<'a, K, V>>,
}

impl<'a, K, V> Drop for Iter<'a, K, V> {
    fn drop(&mut self) {
        self.iter.take();
        self.map.in_use.set(false);
    }
}

impl<'a, K: StableDeref, V: StableDeref> Iterator for Iter<'a, K, V> {
    type Item = (&'a K::Target, &'a V::Target);
    fn next(&mut self) -> Option<(&'a K::Target, &'a V::Target)> {
        let val = self.iter.as_mut()?.next();
        if val.is_none() {
            self.iter.take();
            self.map.in_use.set(false);
        }
        val.map(|(k, v)| (&**k, &**v))
    }
}

impl<'a, K: StableDeref, V: StableDeref> IntoIterator for &'a FrozenMap<K, V> {
    type Item = (&'a K::Target, &'a V::Target);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Iter<'a, K, V> {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        Iter {
            map: self,
            iter: unsafe {
                let map = self.map.get();
                Some((&*map).iter())
            },
        }
    }
}
