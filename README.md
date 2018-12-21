## elsa


### This crate is unfinished, please don't use it yet


This crate provides various "frozen" collections.

These are append-only collections where references to entries can be held on to even across insertions. This is safe because these collections only support storing data that's present behind some indirection -- i.e. `String`, `Vec<T>`, `Box<T>`, etc, and they only yield references to the data behind the allocation (`&str`, `&[T]`, and `&T` respectively)

The typical use case is having a global cache of strings or other data which the rest of the program borrows from.


I haven't completely thought out the safety aspects of this, use at your own risk.