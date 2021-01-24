# counting-pointer

`counting-pointer` provides structs `Sc` and `Asc` .
They behave like `std::rc::Rc` and `std::sync::Arc` except for the followings.

- `Sc` and `Asc` treats only strong reference but not weak reference.
- `Sc` and `Asc` takes `GlobalAlloc` type as a template parameter.

It is difficult for `Rc` and `Arc` to achieve both good performance and small memory usage at
the same time. This crate gives up supporting weak reference to do it.

License: LGPL-3.0-or-later OR Apache-2.0 OR BSD-2-Clause
