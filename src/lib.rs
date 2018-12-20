use std::borrow::Borrow;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::hash::Hash;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::Arc;

pub unsafe trait FrozenDeref: Deref {}
unsafe impl FrozenDeref for String {}
unsafe impl<T> FrozenDeref for Box<T> {}
unsafe impl<T> FrozenDeref for Rc<T> {}
unsafe impl<T> FrozenDeref for Arc<T> {}
unsafe impl<T> FrozenDeref for Vec<T> {}

pub struct FrozenMap<K, V> {
    map: UnsafeCell<HashMap<K, V>>,
}

impl<K: FrozenDeref + Eq + Hash, V: FrozenDeref> FrozenMap<K, V> {
    // under no circumstances implement remove() on this
    // under no circumstances return an &K or an &V
    pub fn new() -> Self {
        Self {
            map: UnsafeCell::new(Default::default()),
        }
    }

    pub fn insert(&self, k: K, v: V) -> &V::Target {
        unsafe {
            let map = self.map.get();
            &*(*map).entry(k).or_insert(v)
        }
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&V::Target>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        unsafe {
            let map = self.map.get();
            (*map).get(k).map(|x| &**x)
        }
    }
}
