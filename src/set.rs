use std::cell::{Cell, UnsafeCell};
use std::collections::hash_map::{Entry, HashMap};
use std::hash::Hash;
use std::iter::FromIterator;

use stable_deref_trait::StableDeref;

/// Append-only version of `std::collections::HashSet` where
/// insertion does not require mutable access
//  We don't use `FrozenMap<T, ()>`, as the `StableDeref` requirements are different
//  We don't use `HashSet<T>` to get access to the `entry` API
pub struct FrozenSet<T> {
    // FUTURE(rust-lang/rust#60896): use `set: UnsafeCell<HashSet<T>>` instead
    map: UnsafeCell<HashMap<T, ()>>,
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
            map: UnsafeCell::new(Default::default()),
            in_use: Cell::new(false),
        }
    }
}

unsafe fn strip_lt<'a, T: 'a + ?Sized>(t: &T) -> &'a T {
    &*(t as *const T)
}

impl<T: Eq + Hash + StableDeref> FrozenSet<T> {
    // these should never return &T
    // these should never delete any entries
    pub fn insert(&self, t: T) -> &T::Target {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let map = self.map.get();
            match (*map).entry(t) {
                Entry::Occupied(occupied) => strip_lt(&**occupied.key()),
                Entry::Vacant(vacant) => {
                    let ret = strip_lt(&**vacant.key());
                    vacant.insert(());
                    ret
                }
            }
            // &*(*map).raw_entry_mut().from_key(&t).or_insert(t, ()).0
            // &*set.get_or_insert(t)
        };
        self.in_use.set(false);
        ret
    }

    pub fn get(&self, t: T) -> Option<&T::Target>
    // <Q: ?Sized> (t: &Q) where
    //     T: Borrow<Q>,
    //     Q: Hash + Eq,
    {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        let ret = unsafe {
            let map = self.map.get();
            match (*map).entry(t) {
                Entry::Occupied(occupied) => Some(strip_lt(&**occupied.key())),
                Entry::Vacant(_) => None,
            }
            // (*map).raw_entry().from_key(t).map(|(k, _)| &**k)
            // (*map).get_key_value(t).map(|(k, _)| &**k)
            // (*set).get(t).map(|(t)| &*t)
        };
        self.in_use.set(false);
        ret
    }

    // This is unsound while we hold a map
    // pub fn into_set(self) -> HashSet<T> {
    //     self.set.into_inner()
    // }

    // TODO add more
}

// This is unsound while we hold a map
// impl<T> From<HashSet<T>> for FrozenSet<T> {
//     fn from(set: HashSet<T>) -> Self {
//         Self {
//             set: UnsafeCell::new(set),
//             in_use: Cell::new(false)
//         }
//     }
// }

impl<T: Eq + Hash> FromIterator<T> for FrozenSet<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let map: HashMap<_, _> = iter.into_iter().map(|t| (t, ())).collect();
        FrozenSet {
            map: UnsafeCell::new(map),
            in_use: Cell::new(false),
        }
    }
}

impl<T: Eq + Hash> Default for FrozenSet<T> {
    fn default() -> Self {
        FrozenSet::new()
    }
}
