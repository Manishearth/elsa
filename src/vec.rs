use std::cell::UnsafeCell;
use std::iter::FromIterator;
use std::ops::Index;

use stable_deref_trait::StableDeref;

/// Append-only version of `std::vec::Vec` where
/// insertion does not require mutable access
pub struct FrozenVec<T> {
    vec: UnsafeCell<Vec<T>>,
    // XXXManishearth do we need a reentrancy guard here as well?
    // StableDeref may not guarantee that there are no side effects
}

// safety: UnsafeCell implies !Sync

impl<T: StableDeref> FrozenVec<T> {
    pub fn new() -> Self {
        Self {
            vec: UnsafeCell::new(Default::default()),
        }
    }

    // these should never return &T
    // these should never delete any entries

    pub fn push(&self, val: T) {
        unsafe {
            let vec = self.vec.get();
            (*vec).push(val)
        }
    }

    pub fn get(&self, index: usize) -> Option<&T::Target> {
        unsafe {
            let vec = self.vec.get();
            (*vec).get(index).map(|x| &**x)
        }
    }

    pub fn len(&self) -> usize {
        unsafe {
            let vec = self.vec.get();
            (*vec).len()
        }
    }

    pub fn iter(&self) -> Iter<T> {
        self.into_iter()
    }

    pub fn into_vec(self) -> Vec<T> {
        self.vec.into_inner()
    }
    // TODO add more
}


impl<T> From<Vec<T>> for FrozenVec<T> {
    fn from(vec: Vec<T>) -> Self {
        Self {
            vec: UnsafeCell::new(vec)
        }
    }
}


impl<T: StableDeref> Index<usize> for FrozenVec<T> {
    type Output = T::Target;
    fn index(&self, idx: usize) -> &T::Target {
        self.get(idx)
            .unwrap_or_else(|| panic!("index out of bounds: the len is {} but the index is {}", self.len(), idx))
    }
}

impl<A> FromIterator<A> for FrozenVec<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = A> {
        let vec: Vec<_> = iter.into_iter().collect();
        vec.into()
    }
}

/// Iterator over FrozenVec, obtained via `.iter()`
///
/// It is safe to push to the vector during iteration
pub struct Iter<'a, T> {
    vec: &'a FrozenVec<T>,
    idx: usize
}

impl<'a, T: StableDeref> Iterator for Iter<'a, T> {
    type Item = &'a T::Target;
    fn next(&mut self) -> Option<&'a T::Target> {
        if let Some(ret) = self.vec.get(self.idx) {
            self.idx += 1;
            Some(ret)
        } else {
            None
        }
    }
}

impl<'a, T: StableDeref> IntoIterator for &'a FrozenVec<T> {
    type Item = &'a T::Target;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Iter<'a, T> {
        Iter {
            vec: self,
            idx: 0
        }
    }
}

#[test]
fn test_iteration() {
    let vec = vec!["a", "b", "c", "d"];
    let frozen: FrozenVec<_> = vec.clone().into();

    assert_eq!(vec, frozen.iter().collect::<Vec<_>>());
    for (e1, e2) in vec.iter().zip(frozen.iter()) {
        assert_eq!(*e1, e2);
    }

    assert_eq!(vec.len(), frozen.iter().count())
}