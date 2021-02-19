# counting-pointer

`counting-pointer` provides struct `Sc` and `Asc` .
They behave like `std::rc::Rc` and `std::sync::Arc` except for the followings.

- `Sc` and `Asc` treats only strong reference but not weak reference for the performance.
- `Sc` and `Asc` takes `GlobalAlloc` type as a template parameter.

License: LGPL-3.0-or-later OR Apache-2.0 OR BSD-2-Clause
