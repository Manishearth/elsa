//! **This module is experimental**
//!
//! This module provides threadsafe versions of FrozenMap and FrozenVec,
//! ideal for use as a cache.
//!
//! These lock internally, however locks only last as long as the method calls
//!

use stable_deref_trait::StableDeref;
use std::alloc::Layout;
use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::hash::Hash;
use std::iter::{FromIterator, IntoIterator};
use std::mem::MaybeUninit;
use std::ops::Index;

use std::sync::atomic::AtomicPtr;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::RwLock;

/// Append-only threadsafe version of `std::collections::HashMap` where
/// insertion does not require mutable access
pub struct FrozenMap<K, V> {
    map: RwLock<HashMap<K, V>>,
}

impl<K, V> Default for FrozenMap<K, V> {
    fn default() -> Self {
        Self {
            map: Default::default(),
        }
    }
}

impl<K: Eq + Hash, V: StableDeref> FrozenMap<K, V> {
    // these should never return &K or &V
    // these should never delete any entries

    pub fn new() -> Self {
        Self::default()
    }

    /// If the key exists in the map, returns a reference
    /// to the corresponding value, otherwise inserts a
    /// new entry in the map for that key and returns a
    /// reference to the given value.
    ///
    /// Existing values are never overwritten.
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

    /// If the key exists in the map, returns a reference to the corresponding
    /// value, otherwise inserts a new entry in the map for that key and the
    /// value returned by the creation function, and returns a reference to the
    /// generated value.
    ///
    /// Existing values are never overwritten.
    ///
    /// The key may be any borrowed form of the map's key type, but [`Hash`] and
    /// [`Eq`] on the borrowed form *must* match those for the key type.
    ///
    /// **Note** that the write lock is held for the duration of this function’s
    /// execution, even while the value creation function is executing (if
    /// needed). This will block any concurrent `get` or `insert` calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenMap;
    ///
    /// let map = FrozenMap::new();
    /// assert_eq!(map.insert_with(1, || Box::new("a")), &"a");
    /// assert_eq!(map.insert_with(1, || unreachable!()), &"a");
    /// ```
    pub fn insert_with(&self, k: K, f: impl FnOnce() -> V) -> &V::Target {
        let mut map = self.map.write().unwrap();
        let ret = unsafe {
            let inserted = &**map.entry(k).or_insert_with(f);
            &*(inserted as *const _)
        };
        ret
    }

    /// If the key exists in the map, returns a reference to the corresponding
    /// value, otherwise inserts a new entry in the map for that key and the
    /// value returned by the creation function, and returns a reference to the
    /// generated value.
    ///
    /// Existing values are never overwritten.
    ///
    /// The key may be any borrowed form of the map's key type, but [`Hash`] and
    /// [`Eq`] on the borrowed form *must* match those for the key type.
    ///
    /// **Note** that the write lock is held for the duration of this function’s
    /// execution, even while the value creation function is executing (if
    /// needed). This will block any concurrent `get` or `insert` calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenMap;
    ///
    /// let map = FrozenMap::new();
    /// assert_eq!(map.insert_with_key(1, |_| Box::new("a")), &"a");
    /// assert_eq!(map.insert_with_key(1, |_| unreachable!()), &"a");
    /// ```
    pub fn insert_with_key(&self, k: K, f: impl FnOnce(&K) -> V) -> &V::Target {
        let mut map = self.map.write().unwrap();
        let ret = unsafe {
            let inserted = &**map.entry(k).or_insert_with_key(f);
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

    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenMap;
    ///
    /// let map = FrozenMap::new();
    /// assert_eq!(map.len(), 0);
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        let map = self.map.read().unwrap();
        map.len()
    }

    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenMap;
    ///
    /// let map = FrozenMap::new();
    /// assert_eq!(map.is_empty(), true);
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        let map = self.map.read().unwrap();
        map.is_empty()
    }

    // TODO add more
}

/// Append-only threadsafe version of `std::vec::Vec` where
/// insertion does not require mutable access
pub struct FrozenVec<T> {
    vec: RwLock<Vec<T>>,
}

impl<T> Default for FrozenVec<T> {
    fn default() -> Self {
        Self {
            vec: Default::default(),
        }
    }
}

impl<T: StableDeref> FrozenVec<T> {
    pub fn new() -> Self {
        Default::default()
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

/// Append-only threadsafe version of `std::vec::Vec` where
/// insertion does not require mutable access.
/// Does not have locks, only allows `Copy` types and will
/// spinlock on contention. The spinlocks are really rare as
/// they only happen on reallocation due to a push going over
/// the capacity.
pub struct LockFreeFrozenVec<T: Copy> {
    data: AtomicPtr<T>,
    len: AtomicUsize,
    cap: AtomicUsize,
}

impl<T: Copy> Drop for LockFreeFrozenVec<T> {
    fn drop(&mut self) {
        let ptr = self.aquire();
        let cap = self.cap.load(Ordering::Acquire);
        let num_bytes = std::mem::size_of::<T>() * cap;
        let align = std::mem::align_of::<T>();
        let layout = Layout::from_size_align(num_bytes, align).unwrap();
        unsafe {
            std::alloc::dealloc(ptr.cast(), layout);
        }
    }
}

impl<T: Copy> Default for LockFreeFrozenVec<T> {
    fn default() -> Self {
        Self {
            data: AtomicPtr::new(Box::into_raw(Box::new([Self::UNINIT; 128])).cast()),
            len: AtomicUsize::new(0),
            cap: AtomicUsize::new(128),
        }
    }
}

impl<T: Copy> LockFreeFrozenVec<T> {
    const UNINIT: MaybeUninit<T> = MaybeUninit::uninit();

    pub fn new() -> Self {
        Default::default()
    }

    fn aquire(&self) -> *mut T {
        loop {
            let ptr = self.data.swap(std::ptr::null_mut(), Ordering::Acquire);
            if !ptr.is_null() {
                // Wheeeee spinlock
                return ptr;
            }
        }
    }

    fn release(&self, ptr: *mut T) {
        self.data.store(ptr, Ordering::Release);
    }

    // these should never return &T
    // these should never delete any entries

    pub fn push(&self, val: T) -> usize {
        let mut ptr = self.aquire();
        // These values must be consistent with the pointer we got.
        let len = self.len.load(Ordering::Acquire);
        let cap = self.cap.load(Ordering::Acquire);
        if len >= cap {
            // Out of memory, realloc with double the capacity
            let num_bytes = std::mem::size_of::<T>() * cap;
            let align = std::mem::align_of::<T>();
            let layout = Layout::from_size_align(num_bytes, align).unwrap();
            unsafe {
                ptr = std::alloc::realloc(ptr.cast(), layout, num_bytes * 2).cast::<T>();
            }
            assert!(!ptr.is_null());
            self.cap.store(cap * 2, Ordering::Release);
        }
        unsafe {
            ptr.add(len).write(val);
        }
        self.len.store(len + 1, Ordering::Release);

        self.release(ptr);
        len
    }

    pub fn get(&self, index: usize) -> Option<T> {
        // The length can only grow, so just doing the length check
        // independently of the aquire and read is fine. Worst case we
        // read an old length value and end up returning `None` even if
        // another thread already inserted the value.
        let len = self.len.load(Ordering::Relaxed);
        if index >= len {
            return None;
        }
        let ptr = self.aquire();
        let val = unsafe { ptr.add(index).read() };
        self.release(ptr);
        Some(val)
    }
}

#[test]
fn test_non_lockfree() {
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    struct Moo(i32);
    let vec: LockFreeFrozenVec<Moo> = LockFreeFrozenVec::new();

    assert_eq!(vec.get(1), None);

    vec.push(Moo(1));
    let i = vec.push(Moo(2));
    vec.push(Moo(3));

    assert_eq!(vec.get(i), Some(Moo(2)));

    std::thread::scope(|s| {
        s.spawn(|| {
            for i in 0..1000 {
                vec.push(Moo(i));
            }
        });
        s.spawn(|| {
            for i in 0..1000 {
                vec.push(Moo(i));
            }
        });
        for i in 0..2000 {
            while vec.get(i).is_none() {}
        }
    });
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

    /// Insert a new value into the map. Does nothing if the key is already occupied.
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenBTreeMap;
    ///
    /// let map = FrozenBTreeMap::new();
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// ```
    pub fn insert(&self, k: K, v: V) -> &V::Target {
        let mut map = self.0.write().unwrap();
        let ret = unsafe {
            let inserted = &**map.entry(k).or_insert(v);
            &*(inserted as *const _)
        };
        ret
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

    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenBTreeMap;
    ///
    /// let map = FrozenBTreeMap::new();
    /// assert_eq!(map.len(), 0);
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        let map = self.0.read().unwrap();
        map.len()
    }

    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenBTreeMap;
    ///
    /// let map = FrozenBTreeMap::new();
    /// assert_eq!(map.is_empty(), true);
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        let map = self.0.read().unwrap();
        map.is_empty()
    }
}

impl<K: Clone + Ord, V: StableDeref> From<BTreeMap<K, V>> for FrozenBTreeMap<K, V> {
    fn from(map: BTreeMap<K, V>) -> Self {
        Self(RwLock::new(map))
    }
}

impl<Q: ?Sized, K, V> Index<&Q> for FrozenBTreeMap<K, V>
where
    Q: Ord,
    K: Clone + Ord + Borrow<Q>,
    V: StableDeref,
{
    type Output = V::Target;

    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenBTreeMap;
    ///
    /// let map = FrozenBTreeMap::new();
    /// map.insert(1, Box::new("a"));
    /// assert_eq!(map[&1], "a");
    /// ```
    fn index(&self, idx: &Q) -> &V::Target {
        self.get(idx)
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
