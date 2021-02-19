// Copyright 2020 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0 OR BSD-2-Clause"
//
// This is part of counting-pointer
//
//  counting-pointer is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  counting-pointer is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with counting-pointer.  If not, see <http://www.gnu.org/licenses/>.
//
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//
// Redistribution and use in source and binary forms, with or without modification, are permitted
// provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this list of
//    conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright notice, this
//    list of conditions and the following disclaimer in the documentation and/or other
//    materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
// IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
// INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
// NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
// WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.

use core::alloc::{GlobalAlloc, Layout};
use core::any::Any;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::mem::{self, align_of, size_of, MaybeUninit};
use core::ops::Deref;
use core::result::Result;
use std::alloc::{handle_alloc_error, System};
use std::borrow::Borrow;
use std::fmt;

/// Bucket of `Sc` to allocate/deallocate memory for reference count and value at once.
#[repr(C)]
struct Bucket<T: ?Sized> {
    count: usize,
    size: usize,
    val: T,
}

impl<T> From<T> for Bucket<T> {
    fn from(val: T) -> Self {
        debug_assert_eq!(align_of::<usize>(), align_of::<Self>());

        Self {
            count: 1,
            size: size_of::<Self>(),
            val,
        }
    }
}

impl<T: ?Sized> Bucket<T> {
    unsafe fn count(val: &mut T) -> &mut usize {
        let ptr: *mut T = val;
        let ptr: *mut usize = ptr.cast();
        let ptr = ptr.sub(2);
        &mut *ptr
    }

    unsafe fn size(ptr: *const T) -> usize {
        let ptr: *const usize = ptr.cast();
        let ptr = ptr.sub(1);
        *ptr
    }

    unsafe fn dealloc_ptr(ptr: *mut T) -> *mut u8 {
        let ptr: *mut usize = ptr.cast();
        let ptr = ptr.sub(2);
        ptr as *mut u8
    }
}

/// A single-threaded strong reference-counting pointer. 'Sc' stands for 'Strong Counted.'
///
/// It behaves like `std::rc::Rc` except for that this treats only strong pointer; i.e. `Sc` gives
/// up weak pointer for the performance.
///
/// The inherent methods of `Sc` are all associated funcitons, which means that you have to call
/// them as e.g., `Sc::get_mut(&mut value)` instead of `value.get_mut()` . This avoids conflicts
/// with methods of the inner type `T` .
pub struct Sc<T: ?Sized, A = System>
where
    A: GlobalAlloc,
{
    ptr: *mut T,
    alloc: A,
}

impl<T: ?Sized, A> Drop for Sc<T, A>
where
    A: GlobalAlloc,
{
    fn drop(&mut self) {
        unsafe {
            let count = Bucket::count(&mut *self.ptr);
            *count -= 1;

            if *count == 0 {
                let layout =
                    Layout::from_size_align(Bucket::size(self.ptr), align_of::<usize>()).unwrap();
                let ptr = Bucket::dealloc_ptr(self.ptr);

                self.ptr.drop_in_place();
                self.alloc.dealloc(ptr, layout);
            }
        }
    }
}

impl<T, A> Default for Sc<T, A>
where
    T: Default,
    A: Default + GlobalAlloc,
{
    fn default() -> Self {
        Self::new(T::default(), A::default())
    }
}

impl<T, A> From<T> for Sc<T, A>
where
    A: Default + GlobalAlloc,
{
    fn from(val: T) -> Self {
        Self::new(val, A::default())
    }
}

impl<T, A> From<&'_ [T]> for Sc<[T], A>
where
    T: Clone,
    A: Default + GlobalAlloc,
{
    fn from(vals: &'_ [T]) -> Self {
        Sc::<T, A>::from_slice_alloc(vals, A::default())
    }
}

impl<T: ?Sized, A> Clone for Sc<T, A>
where
    A: Clone + GlobalAlloc,
{
    fn clone(&self) -> Self {
        // increment the count.
        unsafe {
            let val = &mut *self.ptr;
            *Bucket::count(val) += 1;
        };

        Self {
            ptr: self.ptr,
            alloc: self.alloc.clone(),
        }
    }
}

impl<T, A> Sc<T, A>
where
    A: GlobalAlloc,
{
    /// Creates a new instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::alloc::System;
    /// use counting_pointer::Sc;
    ///
    /// let _five = Sc::new(5, System);
    /// ```
    pub fn new(val: T, alloc: A) -> Self {
        let bucket = unsafe {
            let layout = Layout::new::<Bucket<T>>();
            let ptr = alloc.alloc(layout) as *mut Bucket<T>;
            if ptr.is_null() {
                handle_alloc_error(layout);
            }

            ptr.write(Bucket::from(val));
            &mut *ptr
        };
        Self {
            ptr: &mut bucket.val,
            alloc,
        }
    }

    /// Creates a new instance of `Sc<[T], A>` .
    ///
    /// # Examples
    ///
    /// ```
    /// use std::alloc::System;
    /// use counting_pointer::Sc;
    ///
    /// let vals: [i32; 4] = [0, 1, 2, 3];
    /// let sc = Sc::from_slice_alloc(&vals, System);
    /// assert_eq!(&vals, &*sc);
    /// ```
    pub fn from_slice_alloc(vals: &[T], alloc: A) -> Sc<[T], A>
    where
        T: Clone,
    {
        unsafe {
            let layout = {
                let align = align_of::<Bucket<T>>();
                let size = size_of::<Bucket<T>>() - size_of::<Bucket<T>>()
                    + vals.len() * size_of::<Bucket<T>>();
                Layout::from_size_align_unchecked(size, align)
            };

            let ptr = alloc.alloc(layout) as *mut Bucket<T>;
            if ptr.is_null() {
                handle_alloc_error(layout);
            }

            let mut bucket = &mut *ptr;
            bucket.count = 1;
            bucket.size = layout.size();

            let ptr = &mut bucket.val as *mut T;
            for i in 0..vals.len() {
                let v = vals[i].clone();
                let ptr = ptr.add(i);
                ptr.write(v);
            }

            let slice_ref = core::slice::from_raw_parts_mut(ptr, vals.len());
            Sc::<[T], A> {
                ptr: &mut *slice_ref,
                alloc,
            }
        }
    }
}

impl<A> Sc<dyn Any, A>
where
    A: GlobalAlloc,
{
    /// Creates `Sc<dyn Any>` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::alloc::System;
    /// use counting_pointer::Sc;
    ///
    /// let _five = Sc::new_any(5, System);
    /// ```
    pub fn new_any<T>(val: T, alloc: A) -> Self
    where
        T: Any,
    {
        let bucket = unsafe {
            let layout = Layout::new::<Bucket<T>>();
            let ptr = alloc.alloc(layout) as *mut Bucket<T>;
            if ptr.is_null() {
                handle_alloc_error(layout);
            }

            ptr.write(Bucket::from(val));
            &mut *ptr
        };
        Self {
            ptr: &mut bucket.val,
            alloc,
        }
    }
}

impl<T: ?Sized, A> fmt::Debug for Sc<T, A>
where
    A: fmt::Debug + GlobalAlloc,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ptr = format!("{:p}", self.ptr);
        let alloc = format!("{:?}", self.alloc);

        f.debug_struct("Sc")
            .field("ptr", &ptr)
            .field("alloc", &alloc)
            .finish()
    }
}

impl<T: ?Sized, A> PartialEq for Sc<T, A>
where
    T: PartialEq,
    A: GlobalAlloc,
{
    fn eq(&self, other: &Self) -> bool {
        let this: &T = self.borrow();
        let other: &T = other.borrow();
        this.eq(other)
    }
}

impl<T: ?Sized, A> Eq for Sc<T, A>
where
    T: Eq,
    A: GlobalAlloc,
{
}

impl<T: ?Sized, A> PartialOrd for Sc<T, A>
where
    T: PartialOrd,
    A: GlobalAlloc,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let this: &T = self.borrow();
        let other: &T = other.borrow();
        this.partial_cmp(other)
    }
}

impl<T: ?Sized, A> Ord for Sc<T, A>
where
    T: Ord,
    A: GlobalAlloc,
{
    fn cmp(&self, other: &Self) -> Ordering {
        let this: &T = self.borrow();
        let other: &T = other.borrow();
        this.cmp(other)
    }
}

impl<T: ?Sized, A> Hash for Sc<T, A>
where
    T: Hash,
    A: GlobalAlloc,
{
    fn hash<H>(&self, hasher: &mut H)
    where
        H: Hasher,
    {
        let inner: &T = self.borrow();
        inner.hash(hasher);
    }
}

impl<T: ?Sized, A> fmt::Display for Sc<T, A>
where
    T: fmt::Display,
    A: GlobalAlloc,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner: &T = self.deref();
        fmt::Display::fmt(inner, f)
    }
}

impl<T: ?Sized, A> AsRef<T> for Sc<T, A>
where
    A: GlobalAlloc,
{
    fn as_ref(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized, A> Borrow<T> for Sc<T, A>
where
    A: GlobalAlloc,
{
    fn borrow(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized, A> Deref for Sc<T, A>
where
    A: GlobalAlloc,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr }
    }
}

impl<T, A> Sc<T, A>
where
    A: GlobalAlloc,
{
    /// Consumes `this`, returning `Sc<dyn Any, A>`
    ///
    /// # Examples
    ///
    /// ```
    /// use counting_pointer::Sc;
    ///
    /// let sc: Sc<i32> = Sc::from(6);
    /// let any = Sc::to_any(sc);
    /// ```
    pub fn to_any(this: Self) -> Sc<dyn Any, A>
    where
        T: Any,
    {
        let (ptr, alloc) = Self::decouple(this);
        Sc::<dyn Any, A> { ptr, alloc }
    }
}

impl<T: ?Sized, A> Sc<T, A>
where
    A: GlobalAlloc,
{
    /// Provides a raw pointer to the data.
    ///
    /// The counts are not affected in any way and the `Sc` is not consumed. The pointer is valid
    /// for as long as another `Sc` instance is pointing to the address.
    ///
    /// # Examples
    ///
    /// ```
    /// use counting_pointer::Sc;
    ///
    /// let x: Sc<String> = Sc::from(String::from("Hello"));
    /// let x_ptr = Sc::as_ptr(&x);
    /// assert_eq!("Hello", unsafe { &*x_ptr });
    /// ```
    pub fn as_ptr(this: &Self) -> *const T {
        this.ptr
    }

    /// Returns the number of `Sc` pointers pointing to the same address.
    ///
    /// # Examples
    ///
    /// ```
    /// use counting_pointer::Sc;
    ///
    /// let five: Sc<i32> = Sc::from(5);
    /// assert_eq!(1, Sc::count(&five));
    ///
    /// let _also_five = five.clone();
    /// assert_eq!(2, Sc::count(&five));
    /// assert_eq!(2, Sc::count(&_also_five));
    ///
    /// drop(five);
    /// assert_eq!(1, Sc::count(&_also_five));
    /// ```
    pub fn count(this: &Self) -> usize {
        unsafe {
            let val = &mut *this.ptr;
            *Bucket::count(val)
        }
    }

    /// Returns a mutable reference into the given `Sc` , if no other `Sc` instance is pointing to
    /// the same address; otherwise returns `None` .
    ///
    /// See also [`make_mut`] , which will `clone` the inner value when some other `Sc` instances
    /// are.
    ///
    /// [`make_mut`]: #method.make_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use counting_pointer::Sc;
    ///
    /// let mut x: Sc<i32> = Sc::from(3);
    /// assert_eq!(3, *x);
    ///
    /// *Sc::get_mut(&mut x).unwrap() = 4;
    /// assert_eq!(4, *x);
    ///
    /// let _y = x.clone();
    /// let n = Sc::get_mut(&mut x);
    /// assert!(n.is_none());
    /// ```
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        if Self::count(this) == 1 {
            Some(unsafe { &mut *this.ptr })
        } else {
            None
        }
    }

    /// Returns `true` if the two `Sc` instances point to the same address, or `false` .
    ///
    /// # Examples
    ///
    /// ```
    /// use counting_pointer::Sc;
    ///
    /// let five: Sc<i32> = Sc::from(5);
    /// let same_five = five.clone();
    /// let other_five: Sc<i32> = Sc::from(5);
    ///
    /// assert_eq!(true, Sc::ptr_eq(&five, &same_five));
    /// assert_eq!(false, Sc::ptr_eq(&five, &other_five));
    /// ```
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        Sc::as_ptr(this) == Sc::as_ptr(other)
    }

    /// Consumes `this` , returning the wrapped pointer and the allocator.
    ///
    /// To avoid memory leak, the returned pointer must be converted back to an `Sc` using
    /// [`from_raw_alloc`] .
    ///
    /// Using this function and [`from_raw_alloc`] , user can create an `Sc<T: ?Sized>` instance.
    ///
    /// [`from_raw_alloc`]: #method.from_raw_alloc
    ///
    /// # Examples
    ///
    /// ```
    /// use counting_pointer::Sc;
    ///
    /// let sc: Sc<String> = Sc::from("Foo".to_string());
    /// let (ptr, alloc) = Sc::into_raw_alloc(sc);
    /// let _sc: Sc<dyn AsRef<str>> = unsafe { Sc::from_raw_alloc(ptr, alloc) };
    /// ```
    pub fn into_raw_alloc(this: Self) -> (*const T, A) {
        let (ptr, alloc) = Self::decouple(this);
        (ptr, alloc)
    }

    /// Constructs a new instance from a raw pointer and allocator.
    ///
    /// The raw pointer must have been previously returned by a call to [`into_raw_alloc`] .
    ///
    /// Using this function and [`into_raw_alloc`] , user can create an `Sc<T: ?Sized>` instance.
    ///
    /// # Safety
    ///
    /// It may lead to memory unsafety to use improperly, even if the returned value will never be
    /// accessed.
    ///
    /// [`into_raw_alloc`]: #method.into_raw_alloc
    ///
    /// # Examples
    ///
    /// ```
    /// use counting_pointer::Sc;
    ///
    /// let sc: Sc<String> = Sc::from("Foo".to_string());
    /// let (ptr, alloc) = Sc::into_raw_alloc(sc);
    /// let _sc: Sc<dyn AsRef<str>> = unsafe { Sc::from_raw_alloc(ptr, alloc) };
    /// ```
    pub unsafe fn from_raw_alloc(ptr: *const T, alloc: A) -> Self {
        Self {
            ptr: ptr as *mut T,
            alloc,
        }
    }

    fn decouple(this: Self) -> (*mut T, A) {
        let alloc = unsafe {
            let mut alloc = MaybeUninit::<A>::uninit();
            let ptr = alloc.as_mut_ptr();
            ptr.copy_from_nonoverlapping(&this.alloc, 1);
            alloc.assume_init()
        };

        let ret = (this.ptr, alloc);
        mem::forget(this);
        ret
    }
}

impl<T: Clone, A: Clone> Sc<T, A>
where
    A: GlobalAlloc,
{
    /// Makes a mutable reference into the given `Sc` .
    ///
    /// If another `Sc` instance is pointing to the same address, `make_mut` will `clone` the inner
    /// value to a new allocation to ensure unique ownership.
    ///
    /// See also [`get_mut`] , which will fail rather than cloning.
    ///
    /// [`get_mut`]: #method.get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use counting_pointer::Sc;
    ///
    /// let mut data: Sc<i32> = Sc::from(5);
    /// assert_eq!(5, *data);
    ///
    /// *Sc::make_mut(&mut data) += 1; // Won't clone anything.
    /// assert_eq!(6, *data);
    ///
    /// let mut data2 = data.clone();  // Won't clone the inner data.
    /// *Sc::make_mut(&mut data) += 1; // Clones inner data.
    /// assert_eq!(7, *data);
    /// assert_eq!(6, *data2);
    /// ```
    pub fn make_mut(this: &mut Self) -> &mut T {
        if Self::count(this) != 1 {
            let val: &T = this.deref();
            *this = Sc::new(val.clone(), this.alloc.clone());
        }

        unsafe { &mut *this.ptr }
    }
}

impl<A> Sc<dyn Any, A>
where
    A: GlobalAlloc,
{
    /// Attempts to downcast the `Sc<dyn Any, A>` to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::alloc::System;
    /// use std::any::Any;
    /// use counting_pointer::Sc;
    ///
    /// let sc = Sc::new_any(8 as i32, System);
    ///
    /// let success = Sc::downcast::<i32>(sc.clone()).unwrap();
    /// assert_eq!(8, *success);
    ///
    /// let fail = Sc::downcast::<String>(sc.clone());
    /// assert_eq!(true, fail.is_err());
    /// ```
    pub fn downcast<T: Any>(self) -> Result<Sc<T, A>, Self> {
        let val: &mut dyn Any = unsafe { &mut *self.ptr };
        match val.downcast_mut() {
            None => Err(self),
            Some(t) => {
                let (_, alloc) = Self::decouple(self);
                Ok(Sc::<T, A> {
                    ptr: t as *mut T,
                    alloc,
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gharial::{GAlloc, GBox};

    #[test]
    fn new() {
        let five = GBox::from(5);
        let _five = Sc::new(five, GAlloc::default());
    }

    #[test]
    fn clone() {
        let five = GBox::from(5);

        let five = Sc::new(five, GAlloc::default());
        let _cloned = five.clone();
    }

    #[test]
    fn make_mut() {
        let inner = GBox::from(5);

        let mut data = Sc::new(inner, GAlloc::default());
        {
            let _mr = Sc::make_mut(&mut data);
        }

        let _data2 = data.clone();
        {
            let _mr = Sc::make_mut(&mut data);
        }
    }

    #[test]
    fn downcast() {
        let inner = GBox::from(8);

        let sc = Sc::new_any(inner, GAlloc::default());

        let ok = Sc::downcast::<GBox<i32>>(sc.clone());
        assert_eq!(true, ok.is_ok());

        let fail = Sc::downcast::<String>(sc.clone());
        assert_eq!(true, fail.is_err());
    }

    #[test]
    fn to_any() {
        let inner = GBox::from(6);

        let sc = Sc::new(inner, GAlloc::default());
        let _any = Sc::to_any(sc);
    }

    #[test]
    fn from_slice_alloc() {
        let inners: [GBox<i32>; 2] = [GBox::from(6), GBox::from(4)];

        let _sc = Sc::from_slice_alloc(&inners, GAlloc::default());
    }

    #[test]
    fn raw_alloc() {
        let sc: Sc<GBox<i32>> = Sc::from(GBox::from(0));
        let (ptr, alloc) = Sc::into_raw_alloc(sc);
        let _sc = unsafe { Sc::from_raw_alloc(ptr, alloc) };
    }
}
