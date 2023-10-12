use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::iter::FromIterator;
use std::ops::Index;
use std::sync::{RwLock, TryLockError};

use indexmap::IndexSet;
use stable_deref_trait::StableDeref;

/// Append-only threadsafeversion of `indexmap::IndexSet` where
/// insertion does not require mutable access
pub struct FrozenIndexSet<T, S = RandomState> {
    set: RwLock<IndexSet<T, S>>,
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for FrozenIndexSet<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.set.try_read() {
            Ok(guard) => guard.fmt(f),
            Err(TryLockError::Poisoned(err)) => {
                f.debug_tuple("FrozenIndexSet").field(&&**err.get_ref()).finish()
            }
            Err(TryLockError::WouldBlock) => {
                struct LockedPlaceholder;
                impl fmt::Debug for LockedPlaceholder {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        f.write_str("<locked>")
                    }
                }
                f.debug_tuple("FrozenIndexSet")
                    .field(&LockedPlaceholder)
                    .finish()
            }
        }
    }
}

impl<T: Eq + Hash> FrozenIndexSet<T> {
    pub fn new() -> Self {
        Self::from(IndexSet::new())
    }
}

impl<T: Eq + Hash + StableDeref, S: BuildHasher> FrozenIndexSet<T, S> {
    // these should never return &T
    // these should never delete any entries
    /// If the value exists in the set, returns a reference to the corresponding
    /// value, otherwise inserts a new entry in the set for that value
    /// and returns a reference to it.
    ///
    /// Existing values are never overwritten.
    ///
    /// # Example
    /// ```
    /// use elsa::sync::index_set::FrozenIndexSet;
    /// let set = FrozenIndexSet::new();
    /// let a_ref = set.insert(Box::new("a"));
    /// let aa = "a";
    /// let other_a_ref = unsafe { aa.as_ptr() as *const &str};
    /// let other_a = Box::new(aa);
    /// assert!(!std::ptr::eq(a_ref, other_a_ref));
    /// assert!(std::ptr::eq(a_ref, set.insert(other_a)));
    /// ```
    pub fn insert(&self, value: T) -> &T::Target {
        let mut set = self.set.write().unwrap();
        let ret = unsafe {
            let (index, _was_vacant) = (*set).insert_full(value);
            let val = &*(*set)[index];
            &*(val as *const _)
        };
        ret
    }

    // these should never return &T
    // these should never delete any entries
    /// If the key exists in the set, returns a reference to the corresponding
    /// value and its index, otherwise inserts a new entry in the set for that value
    /// and returns a reference to it and its index.
    ///
    /// Existing values are never overwritten.
    ///
    /// # Example
    /// ```
    /// use elsa::sync::index_set::FrozenIndexSet;
    /// let map = FrozenIndexSet::new();
    /// assert_eq!(map.insert_full(Box::new("a")), (0, &"a"));
    /// assert_eq!(map.insert_full(Box::new("b")), (1, &"b"));
    /// ```
    pub fn insert_full(&self, value: T) -> (usize, &T::Target) {
        let mut set = self.set.write().unwrap();
        let ret = unsafe {
            let (index, _was_vacant) = (*set).insert_full(value);
            let val = &*(*set)[index];
            (index, &*(val as *const _))
        };
        ret
    }

    /// If the key exists in the set, returns a reference to the index of the corresponding
    /// value and false, otherwise inserts a new entry in the set for that value
    /// and returns its index and true.
    ///
    /// Existing values are never overwritten.
    ///
    /// # Example
    /// ```
    /// use elsa::sync::index_set::FrozenIndexSet;
    /// let map = FrozenIndexSet::new();
    /// assert_eq!(map.insert_probe(Box::new("a")), (0, true));
    /// assert_eq!(map.insert_probe(Box::new("b")), (1, true));
    /// assert_eq!(map.insert_probe(Box::new("a")), (0, false));
    /// ```
    pub fn insert_probe(&self, value: T) -> (usize, bool) {
        let mut set = self.set.write().unwrap();
        (*set).insert_full(value)
    }

    /// Returns a reference to the value passed as argument if present in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::index_set::FrozenIndexSet;
    ///
    /// let set = FrozenIndexSet::new();
    /// set.insert(Box::new("a"));
    /// assert_eq!(set.get(&Box::new("a")), Some(&"a"));
    /// assert_eq!(set.get(&Box::new("b")), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&T::Target>
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        let set = self.set.read().unwrap();
        let ret = unsafe { (*set).get(k).map(|x| &**x).map(|val| &*(val as *const _)) };
        ret
    }

    /// Returns a reference to the value passed as argument if present in the set,
    /// along with its index
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::index_set::FrozenIndexSet;
    ///
    /// let set = FrozenIndexSet::new();
    /// set.insert(Box::new("a"));
    /// assert_eq!(set.get_full(&Box::new("a")), Some((0, &"a")));
    /// assert_eq!(set.get_full(&Box::new("b")), None);
    /// ```
    pub fn get_full<Q: ?Sized>(&self, k: &Q) -> Option<(usize, &T::Target)>
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        let set = self.set.read().unwrap();
        let ret = unsafe {
            (*set)
                .get_full(k)
                .map(|(i, x)| (i, &**x))
                .map(|(i, val)| (i, &*(val as *const _)))
        };
        ret
    }

    /// Returns a reference to value at the index passed as argument, if
    /// present in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::index_set::FrozenIndexSet;
    ///
    /// let set = FrozenIndexSet::new();
    /// set.insert(Box::new("a"));
    /// assert_eq!(set.get_index(0), Some(&"a"));
    /// assert_eq!(set.get_index(1), None);
    /// ```
    pub fn get_index(&self, index: usize) -> Option<&T::Target> {
        let set = self.set.read().unwrap();
        let ret = unsafe {
            (*set)
                .get_index(index)
                .map(|r| &**r)
                .map(|val| &*(val as *const _))
        };
        ret
    }
}

impl<T, S> FrozenIndexSet<T, S> {
    pub fn into_set(self) -> IndexSet<T, S> {
        self.set.into_inner().unwrap()
    }

    /// Get mutable access to the underlying [`IndexSet`].
    ///
    /// This is safe, as it requires a `&mut self`, ensuring nothing is using
    /// the 'frozen' contents.
    pub fn as_mut(&mut self) -> &mut IndexSet<T, S> {
        self.set.get_mut().unwrap()
    }
}

impl<T, S> From<IndexSet<T, S>> for FrozenIndexSet<T, S> {
    fn from(set: IndexSet<T, S>) -> Self {
        Self {
            set: RwLock::new(set),
        }
    }
}

impl<T: Eq + Hash + StableDeref, S> Index<usize> for FrozenIndexSet<T, S> {
    type Output = T::Target;
    fn index(&self, idx: usize) -> &T::Target {
        let set = self.set.read().unwrap();
        let ret = unsafe {
            let val = &*(*set)[idx];
            &*(val as *const _)
        };
        ret
    }
}

impl<T: Eq + Hash, S: Default + BuildHasher> FromIterator<T> for FrozenIndexSet<T, S> {
    fn from_iter<U>(iter: U) -> Self
    where
        U: IntoIterator<Item = T>,
    {
        let set: IndexSet<_, _> = iter.into_iter().collect();
        set.into()
    }
}

impl<T: Eq + Hash, S: Default> Default for FrozenIndexSet<T, S> {
    fn default() -> Self {
        Self::from(IndexSet::default())
    }
}
