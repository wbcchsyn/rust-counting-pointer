// Copyright 2020 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0 OR BSD-2-Clause"
//
// This is part of strong-counting-pointer
//
//  strong-counting-pointer is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  strong-counting-pointer is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with strong-counting-pointer.  If not, see <http://www.gnu.org/licenses/>.
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
use core::mem::{align_of, size_of};
use core::ops::Deref;
use std::alloc::{handle_alloc_error, System};

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
/// It behaves like `std::rc::Rc` , except for this treats only strong pointer, but not weak
/// pointer. The performance of `Sc` is better than `std::rc::Rc` to give up weak pointer.
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
    /// use strong_counting_pointer::Sc;
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
    /// use strong_counting_pointer::Sc;
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
    /// use strong_counting_pointer::Sc;
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
    /// use strong_counting_pointer::Sc;
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
}
