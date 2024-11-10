use std::borrow::Borrow;
use std::cell::{Cell, UnsafeCell};
use std::collections::hash_map::RandomState;
use std::collections::BTreeSet;
use hashbrown::HashSet;
use std::hash::{BuildHasher, Hash};
use std::iter::FromIterator;
use std::ops::Index;

use stable_deref_trait::StableDeref;

/// Append-only version of `std::collections::HashSet` where
/// insertion does not require mutable access
pub struct FrozenSet<T, S = RandomState> {
    set: UnsafeCell<HashSet<T, S>>,
    /// Eq/Hash implementations can have side-effects, and using Rc it is possible
    /// for FrozenSet::insert to be called on a key that itself contains the same
    /// `FrozenSet`, whose `eq` implementation also calls FrozenSet::insert
    ///
    /// We use this `in_use` flag to guard against any reentrancy.
    in_use: Cell<bool>,
}

// safety: UnsafeCell implies !Sync

impl<T: Eq + Hash> FrozenSet<T> {
    pub fn new() -> Self {
        Self {
            set: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false),
        }
    }

    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenSet;
    ///
    /// let set = FrozenSet::new();
    /// assert_eq!(set.len(), 0);
    /// set.insert(1, Box::new("a"));
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let len = unsafe {
            let set = self.set.get();
            (*set).len()
        };
        self.in_use.set(false);
        len
    }

    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenSet;
    ///
    /// let set = FrozenSet::new();
    /// assert_eq!(set.is_empty(), true);
    /// set.insert(1, Box::new("a"));
    /// assert_eq!(set.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T: Eq + Hash + StableDeref, S: BuildHasher> FrozenSet<T, S> {
    // these should never return &T
    // these should never delete any entries
    pub fn insert(&self, value: T) -> &T::Target {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let set = self.set.get();
            &*(*set).get_or_insert(value)
        };
        self.in_use.set(false);
        ret
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the set's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenSet;
    ///
    /// let set = FrozenSet::new();
    /// set.insert(1, Box::new("a"));
    /// assert_eq!(set.get(&1), Some(&"a"));
    /// assert_eq!(set.get(&2), None);
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&T::Target>
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let set = self.set.get();
            (*set).get(value).map(|x| &**x)
        };
        self.in_use.set(false);
        ret
    }
}

impl<T, S> FrozenSet<T, S> {
    /// Collects the contents of this set into a vector of tuples.
    ///
    /// The order of the entries is as if iterating a [`HashSet`] (stochastic).
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenSet;
    ///
    /// let set = FrozenSet::new();
    /// set.insert(1, Box::new("a"));
    /// set.insert(2, Box::new("b"));
    /// let mut tuple_vec = set.into_tuple_vec();
    /// tuple_vec.sort();
    ///
    /// assert_eq!(tuple_vec, vec![(1, Box::new("a")), (2, Box::new("b"))]);
    /// ```
    pub fn into_tuple_vec(self) -> Vec<T> {
        self.set.into_inner().into_iter().collect::<Vec<_>>()
    }

    pub fn into_set(self) -> HashSet<T, S> {
        self.set.into_inner()
    }
}

impl<T, S> std::convert::AsMut<HashSet<T, S>> for FrozenSet<T, S> {
    /// Get mutable access to the underlying [`HashSet`].
    ///
    /// This is safe, as it requires a `&mut self`, ensuring nothing is using
    /// the 'frozen' contents.
    fn as_mut(&mut self) -> &mut HashSet<T, S> {
        unsafe { &mut *self.set.get() }
    }
}

impl<T, S> From<HashSet<T, S>> for FrozenSet<T, S> {
    fn from(set: HashSet<T, S>) -> Self {
        Self {
            set: UnsafeCell::new(set),
            in_use: Cell::new(false),
        }
    }
}

impl<Q: ?Sized, T, S> Index<&Q> for FrozenSet<T, S>
where
    Q: Eq + Hash,
    T: Eq + Hash + StableDeref + Borrow<Q>,
    S: BuildHasher,
{
    type Output = T::Target;

    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenSet;
    ///
    /// let set = FrozenSet::new();
    /// set.insert(1, Box::new("a"));
    /// assert_eq!(set[&1], "a");
    /// ```
    fn index(&self, idx: &Q) -> &T::Target {
        self.get(idx)
            .expect("attempted to index FrozenSet with unknown key")
    }
}

impl<T: Eq + Hash, S: BuildHasher + Default> FromIterator<T> for FrozenSet<T, S> {
    fn from_iter<U>(iter: U) -> Self
    where
        U: IntoIterator<Item = T>,
    {
        let set: HashSet<_, _> = iter.into_iter().collect();
        set.into()
    }
}

impl<T: Eq + Hash, S: Default> Default for FrozenSet<T, S> {
    fn default() -> Self {
        Self {
            set: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false),
        }
    }
}

impl<T: Clone, S: Clone> Clone for FrozenSet<T, S> {
    fn clone(&self) -> Self {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let self_clone = Self {
            set: unsafe { self.set.get().as_ref().unwrap() }.clone().into(),
            in_use: Cell::from(false),
        };
        self.in_use.set(false);
        self_clone
    }
}

impl<T: Eq + Hash + PartialEq + StableDeref> PartialEq for FrozenSet<T> {
    fn eq(&self, other: &Self) -> bool {
        assert!(!self.in_use.get());
        assert!(!other.in_use.get());
        self.in_use.set(true);
        other.in_use.set(true);
        let ret = unsafe { self.set.get().as_ref() == other.set.get().as_ref() };
        self.in_use.set(false);
        other.in_use.set(false);
        ret
    }
}

/// Append-only version of `std::collections::BTreeSet` where
/// insertion does not require mutable access
pub struct FrozenBTreeSet<T> {
    set: UnsafeCell<BTreeSet<T>>,
    /// Eq/Hash implementations can have side-effects, and using Rc it is possible
    /// for FrozenBTreeSet::insert to be called on a key that itself contains the same
    /// `FrozenBTreeSet`, whose `eq` implementation also calls FrozenBTreeSet::insert
    ///
    /// We use this `in_use` flag to guard against any reentrancy.
    in_use: Cell<bool>,
}

// safety: UnsafeCell implies !Sync

impl<T: Clone + Ord + StableDeref> FrozenBTreeSet<T> {
    pub fn new() -> Self {
        Self {
            set: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false),
        }
    }

    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenBTreeSet;
    ///
    /// let set = FrozenBTreeSet::new();
    /// assert_eq!(set.len(), 0);
    /// set.insert(1, Box::new("a"));
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let len = unsafe {
            let set = self.set.get();
            (*set).len()
        };
        self.in_use.set(false);
        len
    }

    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenBTreeSet;
    ///
    /// let set = FrozenBTreeSet::new();
    /// assert_eq!(set.is_empty(), true);
    /// set.insert(1, Box::new("a"));
    /// assert_eq!(set.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T: Clone + Ord + StableDeref> FrozenBTreeSet<T> {
    // these should never return &K or &V
    // these should never delete any entries
    pub fn insert(&self, value: T) -> &T::Target {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let set = self.set.get();
            if let Some(ret) = (*set).get(&value) {
                ret
            } else {
                let ptr = &value as *const T;
                (*set).insert(value);
                // Safe thanks to T being StableDeref
                &*ptr
            }
        };
        self.in_use.set(false);
        ret
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the set's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenBTreeSet;
    ///
    /// let set = FrozenBTreeSet::new();
    /// set.insert(1, Box::new("a"));
    /// assert_eq!(set.get(&1), Some(&"a"));
    /// assert_eq!(set.get(&2), None);
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&T::Target>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let set = self.set.get();
            (*set).get(value).map(|x| &**x)
        };
        self.in_use.set(false);
        ret
    }
}

impl<T> FrozenBTreeSet<T> {
    /// Collects the contents of this set into a vector of tuples.
    ///
    /// The order of the entries is as if iterating a [`BTreeSet`] (ordered by key).
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenBTreeSet;
    ///
    /// let set = FrozenBTreeSet::new();
    /// set.insert(1, Box::new("a"));
    /// set.insert(2, Box::new("b"));
    /// let mut tuple_vec = set.into_tuple_vec();
    /// tuple_vec.sort();
    ///
    /// assert_eq!(tuple_vec, vec![(1, Box::new("a")), (2, Box::new("b"))]);
    /// ```
    pub fn into_tuple_vec(self) -> Vec<T> {
        self.set.into_inner().into_iter().collect::<Vec<_>>()
    }

    pub fn into_set(self) -> BTreeSet<T> {
        self.set.into_inner()
    }

    // TODO add more
}

impl<T> std::convert::AsMut<BTreeSet<T>> for FrozenBTreeSet<T> {
    /// Get mutable access to the underlying [`HashSet`].
    ///
    /// This is safe, as it requires a `&mut self`, ensuring nothing is using
    /// the 'frozen' contents.
    fn as_mut(&mut self) -> &mut BTreeSet<T> {
        unsafe { &mut *self.set.get() }
    }
}

impl<T: Clone + Ord + StableDeref> From<BTreeSet<T>> for FrozenBTreeSet<T> {
    fn from(set: BTreeSet<T>) -> Self {
        Self {
            set: UnsafeCell::new(set),
            in_use: Cell::new(false),
        }
    }
}

impl<Q: ?Sized, T> Index<&Q> for FrozenBTreeSet<T>
where
    Q: Ord,
    T: Clone + Ord + StableDeref + Borrow<Q>,
{
    type Output = T::Target;

    /// # Examples
    ///
    /// ```
    /// use elsa::FrozenBTreeSet;
    ///
    /// let set = FrozenBTreeSet::new();
    /// set.insert(1, Box::new("a"));
    /// assert_eq!(set[&1], "a");
    /// ```
    fn index(&self, idx: &Q) -> &T::Target {
        self.get(idx)
            .expect("attempted to index FrozenBTreeSet with unknown key")
    }
}

impl<T: Clone + Ord + StableDeref> FromIterator<T> for FrozenBTreeSet<T> {
    fn from_iter<U>(iter: U) -> Self
    where
        U: IntoIterator<Item = T>,
    {
        let set: BTreeSet<_> = iter.into_iter().collect();
        set.into()
    }
}

impl<T: Clone + Ord + StableDeref> Default for FrozenBTreeSet<T> {
    fn default() -> Self {
        Self {
            set: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false),
        }
    }
}

impl<T: Clone> Clone for FrozenBTreeSet<T> {
    fn clone(&self) -> Self {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let self_clone = Self {
            set: unsafe { self.set.get().as_ref().unwrap() }.clone().into(),
            in_use: Cell::from(false),
        };
        self.in_use.set(false);
        self_clone
    }
}

impl<T: Eq + Hash + PartialEq + StableDeref> PartialEq for FrozenBTreeSet<T> {
    fn eq(&self, other: &Self) -> bool {
        assert!(!self.in_use.get());
        assert!(!other.in_use.get());
        self.in_use.set(true);
        other.in_use.set(true);
        let ret = unsafe { self.set.get().as_ref() == other.set.get().as_ref() };
        self.in_use.set(false);
        other.in_use.set(false);
        ret
    }
}
