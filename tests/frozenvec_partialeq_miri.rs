use std::ptr;
use std::cmp::PartialEq;
use elsa::FrozenVec;

#[derive(Clone)]
struct Yo<'a> {
    some_flag: bool,
    reference: &'a FrozenVec<Box<Yo<'a>>>,
}

impl PartialEq for Yo<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.reference.push(Box::new( Yo{
            some_flag: self.some_flag,
            reference: self.reference
        }));
        ptr::eq(self.reference, other.reference) && self.some_flag == other.some_flag
    }
}

#[test]
fn test_miri() {
    let vec:  FrozenVec<Box<Yo>> = FrozenVec::new();
    let other_vec = FrozenVec::new();
    let something = Box::new(Yo {
        some_flag: true,
        reference: &vec,
    });
    other_vec.push(something.clone());
    vec.push(something);
    let _ = vec == other_vec;
}