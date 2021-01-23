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
use std::alloc::System;

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
