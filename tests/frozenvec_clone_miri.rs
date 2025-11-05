use elsa::FrozenVec;

struct Yo<'a> {
    some_flag: bool,
    reference: &'a FrozenVec<Box<Yo<'a>>>,
}
impl Clone for Yo<'_> {
    fn clone(&self) -> Self {
        self.reference.push(Box::new(Yo {
            some_flag: self.some_flag,
            reference: &self.reference,
        }));

        Self {
            some_flag: self.some_flag,
            reference: self.reference,
        }
    }
}

#[test]
fn test_miri() {
    let vec: FrozenVec<Box<Yo>> = FrozenVec::new();

    let something = Box::new(Yo {
        some_flag: true,
        reference: &vec,
    });

    vec.push(something);
    let _ = vec.clone();
}
