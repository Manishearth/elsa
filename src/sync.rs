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
use std::ops::Index;

use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicPtr;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::RwLock;

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Append-only threadsafe version of `std::collections::HashMap` where
/// insertion does not require mutable access
#[cfg_attr(feature = "serde", derive(Serialize))]
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

impl<K, V> FrozenMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: Eq + Hash, V: StableDeref> FrozenMap<K, V> {
    // these should never return &K or &V
    // these should never delete any entries

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
}

impl<K, V> FrozenMap<K, V> {
    /// Collects the contents of this map into a vector of tuples.
    ///
    /// The order of the entries is as if iterating a [`HashMap`] (stochastic).
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenMap;
    ///
    /// let map = FrozenMap::new();
    /// map.insert(1, Box::new("a"));
    /// map.insert(2, Box::new("b"));
    /// let mut tuple_vec = map.into_tuple_vec();
    /// tuple_vec.sort();
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

impl<K: Clone, V> FrozenMap<K, V> {
    pub fn keys_cloned(&self) -> Vec<K> {
        self.map.read().unwrap().keys().cloned().collect()
    }
}

impl<K: Eq + Hash, V: Copy> FrozenMap<K, V> {
    /// Returns a copy of the value corresponding to the key.
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
    /// map.get_copy_or_insert(1, 6);
    /// assert_eq!(map.get_copy(&1), Some(6));
    /// assert_eq!(map.get_copy(&2), None);
    /// ```
    pub fn get_copy<Q: ?Sized>(&self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let map = self.map.read().unwrap();
        map.get(k).cloned()
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
    /// assert_eq!(map.get_copy_or_insert(1, 6), 6);
    /// assert_eq!(map.get_copy_or_insert(1, 12), 6);
    /// ```
    pub fn get_copy_or_insert(&self, k: K, v: V) -> V {
        let mut map = self.map.write().unwrap();
        // This is safe because `or_insert` does not overwrite existing values
        let inserted = map.entry(k).or_insert(v);
        *inserted
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
    /// assert_eq!(map.get_copy_or_insert_with(1, || 6), 6);
    /// assert_eq!(map.get_copy_or_insert_with(1, || unreachable!()), 6);
    /// ```
    pub fn get_copy_or_insert_with(&self, k: K, f: impl FnOnce() -> V) -> V {
        let mut map = self.map.write().unwrap();
        // This is safe because `or_insert_with` does not overwrite existing values
        let inserted = map.entry(k).or_insert_with(f);
        *inserted
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
    /// assert_eq!(map.get_copy_or_insert_with_key(1, |_| 6), 6);
    /// assert_eq!(map.get_copy_or_insert_with_key(1, |_| unreachable!()), 6);
    /// ```
    pub fn get_copy_or_insert_with_key(&self, k: K, f: impl FnOnce(&K) -> V) -> V {
        let mut map = self.map.write().unwrap();
        // This is safe because `or_insert_with_key` does not overwrite existing values
        let inserted = map.entry(k).or_insert_with_key(f);
        *inserted
    }
}

impl<K, V> std::convert::AsMut<HashMap<K, V>> for FrozenMap<K, V> {
    /// Get mutable access to the underlying [`HashMap`].
    ///
    /// This is safe, as it requires a `&mut self`, ensuring nothing is using
    /// the 'frozen' contents.
    fn as_mut(&mut self) -> &mut HashMap<K, V> {
        self.map.get_mut().unwrap()
    }
}

#[cfg(feature = "serde")]
impl<'de, K, V> Deserialize<'de> for FrozenMap<K, V>
where
    K: Deserialize<'de> + Eq + Hash,
    V: Deserialize<'de>,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let map = HashMap::<K, V>::deserialize(deserializer)?;
        Ok(Self {
            map: RwLock::new(map),
        })
    }
}

/// Append-only threadsafe version of `std::vec::Vec` where
/// insertion does not require mutable access
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct FrozenVec<T> {
    vec: RwLock<Vec<T>>,
}

impl<T> FrozenVec<T> {
    /// Returns the number of elements in the vector.
    pub fn len(&self) -> usize {
        let vec = self.vec.read().unwrap();
        vec.len()
    }

    /// Returns `true` if the vector contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
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
}

impl<T> FrozenVec<T> {
    /// Returns the internal vector backing this structure
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenVec;
    ///
    /// let map = FrozenVec::new();
    /// map.push("a");
    /// map.push("b");
    /// let tuple_vec = map.into_vec();
    ///
    /// assert_eq!(tuple_vec, vec!["a", "b"]);
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.vec.into_inner().unwrap()
    }

    // TODO add more
}

impl<T> std::convert::AsMut<Vec<T>> for FrozenVec<T> {
    /// Get mutable access to the underlying vector.
    ///
    /// This is safe, as it requires a `&mut self`, ensuring nothing is using
    /// the 'frozen' contents.
    fn as_mut(&mut self) -> &mut Vec<T> {
        self.vec.get_mut().unwrap()
    }
}

impl<T> Default for FrozenVec<T> {
    fn default() -> Self {
        Self {
            vec: Default::default(),
        }
    }
}

// The context for these functions is that we want to have a
// series of exponentially increasing buffer sizes. We want
// to maximize the total size of the buffers (since this
// determines the maximum size of the container) whilst
// minimizing the number of buffers (since we pay an up-front
// cost in space proportional to the number of buffers)
// without increasing the buffer size too much each time as
// this determines how much space will be wasted on average
// in allocated buffers. Finally, we also want a sequence
// which will generate nice round numbers and is easy to
// work with.

/// we multiply the buffer size by 4 each time whilst sizing
/// the first buffer to 3, so the buffer sizes generated by
/// the function will be 3, 12, 48, 192, etc.
const fn buffer_size(idx: usize) -> usize {
    3 << (idx * 2)
}

/// This computes the sum of the sizes of buffers prior to a
/// particular buffer index, aka `4^idx - 1`. The choice of
/// sequence means that the total buffer size will always be
/// a sequence of `1`s in binary, since it's a power of 2 minus one.
const fn prior_total_buffer_size(idx: usize) -> usize {
    (1 << (idx * 2)) - 1
}

/// This determines which buffer contains the nth item
/// (assuming the items are arranged sequentially in the buffers).
/// Since the total buffer sizes are always sequences of 1s in binary,
/// we can just count the number of binary digits in `(i+1)` and
/// divide by `2` (rounding up).
/// (That's what the `(65 - (i + 1).leading_zeros()) >> 1` part does.)
/// We use 65 rather than `64` so that the division by `2` rounds
/// up instead of down. We divide by `2 (>> 1)` because we skip
/// every other power of `2` since we increase the buffer size by `4`
/// each time, and finally we subtract one because buffer indices are
/// zero-indexed.
const fn buffer_index(i: usize) -> usize {
    (((usize::BITS + 1 - (i + 1).leading_zeros()) >> 1) - 1) as usize
}

const NUM_BUFFERS: usize = (usize::BITS >> 2) as usize;

/// Append-only threadsafe version of `std::vec::Vec` where
/// insertion does not require mutable access.
/// Does not lock for reading, only allows `Copy` types and
/// will spinlock on pushes without affecting reads.
/// Note that this data structure is `64` pointers large on
/// 64 bit systems,
/// in contrast to `Vec` which is `3` pointers large.
pub struct LockFreeFrozenVec<T: Copy> {
    data: [AtomicPtr<T>; NUM_BUFFERS],
    len: AtomicUsize,
    locked: AtomicBool,
}

impl<T: Copy> Drop for LockFreeFrozenVec<T> {
    fn drop(&mut self) {
        // We need to drop the elements from all allocated buffers.
        for i in 0..NUM_BUFFERS {
            let layout = Self::layout(buffer_size(i));
            unsafe {
                let ptr = *self.data[i].get_mut();
                if ptr.is_null() {
                    // After the first null pointer there will only be more
                    // null pointers.
                    break;
                } else {
                    std::alloc::dealloc(ptr.cast(), layout);
                }
            }
        }
    }
}

impl<T: Copy> Default for LockFreeFrozenVec<T> {
    /// Creates an empty `LockFreeFrozenVec` that does not allocate
    /// any heap allocations until the first time data is pushed to it.
    fn default() -> Self {
        Self {
            data: [Self::NULL; NUM_BUFFERS],
            len: AtomicUsize::new(0),
            locked: AtomicBool::new(false),
        }
    }
}

impl<T: Copy> LockFreeFrozenVec<T> {
    const NULL: AtomicPtr<T> = AtomicPtr::new(std::ptr::null_mut());
    pub fn new() -> Self {
        Default::default()
    }

    /// Obtains a write lock that ensures other writing threads
    /// wait for us to finish. Reading threads are unaffected and
    /// can concurrently read while we push a new element.
    fn lock<U>(&self, f: impl FnOnce() -> U) -> U {
        while self.locked.swap(true, Ordering::Acquire) {
            // Wheeeee spinlock
            std::hint::spin_loop();
        }

        let ret = f();
        self.locked.store(false, Ordering::Release);
        ret
    }

    fn layout(cap: usize) -> Layout {
        Layout::array::<T>(cap).unwrap()
    }

    // these should never return &T
    // these should never delete any entries

    const NOT_ZST: () = if std::mem::size_of::<T>() == 0 {
        panic!("`LockFreeFrozenVec` cannot be used with ZSTs");
    };

    /// Pushes an element to the vector, potentially allocating new memory.
    /// Returns the index at which the element was inserted.
    pub fn push(&self, val: T) -> usize {
        // This statement actually does something: it evaluates a constant.
        #[allow(path_statements)]
        {
            Self::NOT_ZST
        }
        self.lock(|| {
            // These values must be consistent with the pointer we got.
            let len = self.len.load(Ordering::Acquire);
            let buffer_idx = buffer_index(len);
            let mut ptr = self.data[buffer_idx].load(Ordering::Acquire);
            if ptr.is_null() {
                // Out of memory, allocate more
                let layout = Self::layout(buffer_size(buffer_idx));
                // SAFETY: `LockFreeFrozenVec` statically rejects zsts and the input `ptr` has always been
                // allocated at the size stated in `cap`.
                unsafe {
                    ptr = std::alloc::alloc(layout).cast::<T>();
                }

                assert!(!ptr.is_null());

                self.data[buffer_idx].store(ptr, Ordering::Release);
            }
            let local_index = len - prior_total_buffer_size(buffer_idx);
            unsafe {
                ptr.add(local_index).write(val);
            }
            // This is written before updating the data pointer. Other `push` calls cannot observe this,
            // because they are blocked on aquiring the data pointer before they ever read the `len`.
            // `get` may read the length without synchronization, but that is fine,
            // as there will be actually the right number of elements stored, or less elements,
            // in which case you get a spurious `None`.
            self.len.store(len + 1, Ordering::Release);
            len
        })
    }

    /// Load an element (if it exists). This operation is lock-free and
    /// performs minimal synchronization.
    pub fn get(&self, index: usize) -> Option<T> {
        // The length can only grow, so just doing the length check
        // independently of the  read is fine. Worst case we
        // read an old length value and end up returning `None` even if
        // another thread already inserted the value.
        let len = self.len.load(Ordering::Acquire);
        if index >= len {
            return None;
        }
        let buffer_idx = buffer_index(index);
        let buffer_ptr = self.data[buffer_idx].load(Ordering::Acquire);
        let local_index = index - prior_total_buffer_size(buffer_idx);
        Some(unsafe { *buffer_ptr.add(local_index) })
    }

    pub fn is_empty(&self) -> bool {
        self.len.load(Ordering::Relaxed) == 0
    }

    /// Load an element (if it exists). This operation is lock-free and
    /// performs no synchronized atomic operations. This is a useful primitive to
    /// implement your own data structure with newtypes around the index.
    pub unsafe fn get_unchecked(&self, index: usize) -> T {
        let buffer_idx = buffer_index(index);
        let buffer_ptr = self.data[buffer_idx].load(Ordering::Relaxed);
        let local_index = index - prior_total_buffer_size(buffer_idx);
        unsafe { *buffer_ptr.add(local_index) }
    }
}

#[test]
fn test_non_lockfree_unchecked() {
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    struct Moo(i32);

    let vec = LockFreeFrozenVec::new();

    let idx_set = std::sync::Mutex::new(std::collections::HashSet::new());

    std::thread::scope(|s| {
        s.spawn(|| {
            for i in 0..1000 {
                idx_set.lock().unwrap().insert(vec.push(Moo(i)));
            }
        });
        s.spawn(|| {
            for i in 0..1000 {
                idx_set.lock().unwrap().insert(vec.push(Moo(i)));
            }
        });
        for _ in 0..2000 {
            let idxes = std::mem::take(&mut *idx_set.lock().unwrap());
            for idx in idxes {
                unsafe {
                    vec.get_unchecked(idx);
                }
            }
        }
    });

    // Test dropping empty vecs
    LockFreeFrozenVec::<()>::new();
}

#[cfg(feature = "serde")]
impl<T: Copy + Serialize> Serialize for LockFreeFrozenVec<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeSeq;

        let len = self.len.load(Ordering::Relaxed);
        let mut seq = serializer.serialize_seq(Some(len))?;
        for i in 0..len {
            seq.serialize_element(&self.get(i).unwrap())?;
        }
        seq.end()
    }
}

#[cfg(feature = "serde")]
impl<'de, T: Copy + Deserialize<'de>> Deserialize<'de> for LockFreeFrozenVec<T> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        use serde::de::{SeqAccess, Visitor};
        use std::marker::PhantomData;

        struct SeqVisitor<T>(PhantomData<T>);

        impl<'de, T: Copy + Deserialize<'de>> Visitor<'de> for SeqVisitor<T> {
            type Value = LockFreeFrozenVec<T>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("a sequence of elements")
            }

            fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
                let ret = LockFreeFrozenVec::new();
                while let Some(elem) = seq.next_element()? {
                    ret.push(elem);
                }
                Ok(ret)
            }
        }

        deserializer.deserialize_seq(SeqVisitor(PhantomData))
    }
}

#[test]
fn test_non_lockfree() {
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    #[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
    struct Moo(i32);

    let vec = LockFreeFrozenVec::new();

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

    // Test dropping empty vecs
    LockFreeFrozenVec::<()>::new();

    #[cfg(feature = "serde")]
    {
        let vec = LockFreeFrozenVec::new();
        vec.push(Moo(1));
        vec.push(Moo(2));
        vec.push(Moo(3));
        let json = serde_json::to_string(&vec).unwrap();
        let vec = serde_json::from_str::<LockFreeFrozenVec<Moo>>(&json).unwrap();
        assert_eq!(vec.get(0), Some(Moo(1)));
        assert_eq!(vec.get(1), Some(Moo(2)));
        assert_eq!(vec.get(2), Some(Moo(3)));
    }
}

// TODO: Implement IntoIterator for LockFreeFrozenVec

/// Append-only threadsafe version of `std::collections::BTreeMap` where
/// insertion does not require mutable access
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize))]
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
}

impl<K, V> FrozenBTreeMap<K, V> {
    /// Collects the contents of this map into a vector of tuples.
    ///
    /// The order of the entries is as if iterating a [`BTreeMap`] (ordered by key).
    ///
    /// # Examples
    ///
    /// ```
    /// use elsa::sync::FrozenBTreeMap;
    ///
    /// let map = FrozenBTreeMap::new();
    /// map.insert(1, Box::new("a"));
    /// map.insert(2, Box::new("b"));
    /// let tuple_vec = map.into_tuple_vec();
    ///
    /// assert_eq!(tuple_vec, vec![(1, Box::new("a")), (2, Box::new("b"))]);
    /// ```
    pub fn into_tuple_vec(self) -> Vec<(K, V)> {
        self.0.into_inner().unwrap().into_iter().collect::<Vec<_>>()
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

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for FrozenBTreeMap<String, String> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let map = BTreeMap::<String, String>::deserialize(deserializer)?;
        Ok(map.into())
    }
}
