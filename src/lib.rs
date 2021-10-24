//! ***Please note that the safety of this code has not been battle-tested yet. Use at your
//! own risk! Most of the functionality of this crate can also be acheived using [`smallvec`],
//! so please consider using that before considering to use this crate.***
//!
//! This crate allows you to create a "temporary" Vec of references which persists its
//! allocated memory and which can be stored as a member variable.
//!
//! For example, say that you want to prepare a Vec of buffer references to send to another
//! piece of your code. However, the issue here is that this will allocate memory, which can
//! cause issues with performance (or in the case of realtime code, allocation of any kind
//! is unacceptable).
//! ```rust
//! # let my_buffer_1: [f32; 256] = [0.0; 256];
//! # let my_buffer_2: [f32; 256] = [0.0; 256];
//! # fn i_want_a_slice_of_references(_slice: &[&[f32; 256]]) {}
//! let mut buffers: Vec<&[f32; 256]> = Vec::new();
//!
//! // "Push" allocates memory here
//! buffers.push(&my_buffer_1);
//! buffers.push(&my_buffer_2);
//!
//! i_want_a_slice_of_references(&buffers[..]);
//! ```
//!
//! The usual solution here is to use [`smallvec`] which allocates the memory on the stack.
//! In fact, if this solves your use case, please use that instead of this crate.
//! ```rust
//! # use smallvec::SmallVec;
//! # let my_buffer_1: [f32; 256] = [0.0; 256];
//! # let my_buffer_2: [f32; 256] = [0.0; 256];
//! # fn i_want_a_slice_of_references(_slice: &[&[f32; 256]]) {}
//! let mut buffers: SmallVec<[&[f32; 256]; 8]> = SmallVec::new();
//!
//! // Does not allocated memory anymore!
//! buffers.push(&my_buffer_1);
//! buffers.push(&my_buffer_2);
//!
//! i_want_a_slice_of_references(&buffers[..]);
//! ```
//!
//! However, note that if we push more than the 8 slots we defined in this SmallVec, then it
//! will allocate memory again. If the maximum number of slots is not known at compile-time,
//! you have 2 options:
//!
//! Option 1 is to just allocate a large number of slots and hope that it never exceeds
//! capacity. However, this can potentially overflow your stack if it gets too large, and if
//! the majority of the time only a few slots are being used, there can be a performance
//! penalty of having a function with an unusually large stack size.
//!
//! Option 2 is to use this crate. It works by creating a struct that contains a Vec of
//! static references that can be stored in a member variable. Because Rust does not like
//! self-referencing structs very well, this Vec must have the type `Vec<&'static T>`.
//! However, it's more than likely that your data does not have a static lifetime. The key
//! trick here is that in order to use this struct, it must be borrowed and used inside a
//! closure. This function converts this `Vec<&'static T>` into a `Vec<&'a T>` that is then
//! sent to your closure. This operation remains safe because the function ensures that the
//! Vec it sends you is always empty, meaning no uninitialized data can be ever be read from
//! it and cause undefined behavior. It also automatically clears the Vec at the end of the
//! closure's scope so as to avoid self-referential structs.
//! ```rust
//! # let my_buffer_1: [f32; 256] = [0.0; 256];
//! # let my_buffer_2: [f32; 256] = [0.0; 256];
//! # fn i_want_a_slice_of_references(_slice: &[&[f32; 256]]) {}
//! use member_ref_vec::MemberRefVec;
//!
//! // Pre-allocate some capacity in a non-performance critical part
//! // of your code. Also, please note the lack of the `&` symbol in
//! // the turbofish operator here. This is *not* allocating 1024
//! // buffers with 256 f32s, This is still just allocating 1024
//! // references to buffers.
//! let mut buffer_refs: MemberRefVec<[f32; 256]> = MemberRefVec::with_capacity(1024);
//!
//! // -- In the performance-critical part of your code: ---------
//!
//! buffer_refs.as_empty_vec_of_refs(|buffers| {
//!   // Does not allocated memory! (as long as you don't push more
//!   // elements than what was allocated in the non-realtime thread)
//!   buffers.push(&my_buffer_1);
//!   buffers.push(&my_buffer_2);
//!
//!   i_want_a_slice_of_references(&buffers[..]);
//! });
//! ```
//!
//! ## Safety Notes
//! This crate currently assumes that a `Vec<&'static T>` always has the exact same layout in
//! memory as a `Vec<&'a T>` (and that a `Vec<&'static mut T>` always has the exact same
//! layout in memory as a `Vec<&'a mut T>`) where `T: 'static + Sized`. If you happen to know
//! if this assumption is correct or not, please contact me.
//!
//! [`smallvec`]: https://crates.io/crates/smallvec

use std::{ffi::c_void, mem::ManuallyDrop};

/// This struct allows you to create a "temporary" Vec of immutable references which persists
/// its allocated memory and which can be stored as a member variable.
///
/// For example, say that you want to prepare a Vec of buffer references to send to another
/// piece of your code. However, the issue here is that this will allocate memory, which can
/// cause issues with performance (or in the case of realtime code, allocation of any kind
/// is unacceptable).
/// ```rust
/// # let my_buffer_1: [f32; 256] = [0.0; 256];
/// # let my_buffer_2: [f32; 256] = [0.0; 256];
/// # fn i_want_a_slice_of_references(_slice: &[&[f32; 256]]) {}
/// let mut buffers: Vec<&[f32; 256]> = Vec::new();
///
/// // "Push" allocates memory here
/// buffers.push(&my_buffer_1);
/// buffers.push(&my_buffer_2);
///
/// i_want_a_slice_of_references(&buffers[..]);
/// ```
///
/// The usual solution here is to use [`smallvec`] which allocates the memory on the stack.
/// In fact, if this solves your use case, please use that instead of this crate.
/// ```rust
/// # use smallvec::SmallVec;
/// # let my_buffer_1: [f32; 256] = [0.0; 256];
/// # let my_buffer_2: [f32; 256] = [0.0; 256];
/// # fn i_want_a_slice_of_references(_slice: &[&[f32; 256]]) {}
/// let mut buffers: SmallVec<[&[f32; 256]; 8]> = SmallVec::new();
///
/// // Does not allocated memory anymore!
/// buffers.push(&my_buffer_1);
/// buffers.push(&my_buffer_2);
///
/// i_want_a_slice_of_references(&buffers[..]);
/// ```
///
/// However, note that if we push more than the 8 slots we defined in this SmallVec, then it
/// will allocate memory again. If the maximum number of slots is not known at compile-time,
/// you have 2 options:
///
/// Option 1 is to just allocate a large number of slots and hope that it never exceeds
/// capacity. However, this can potentially overflow your stack if it gets too large, and if
/// the majority of the time only a few slots are being used, there can be a performance
/// penalty of having a function with an unusually large stack size.
///
/// Option 2 is to use this crate. It works by creating a struct that contains a Vec of
/// static references that can be stored in a member variable. Because Rust does not like
/// self-referencing structs very well, this Vec must have the type `Vec<&'static T>`.
/// However, it's more than likely that your data does not have a static lifetime. The key
/// trick here is that in order to use this struct, it must be borrowed and used inside a
/// closure. This function converts this `Vec<&'static T>` into a `Vec<&'a T>` that is then
/// sent to your closure. This operation remains safe because the function ensures that the
/// Vec it sends you is always empty, meaning no uninitialized data can be ever be read from
/// it and cause undefined behavior. It also automatically clears the Vec at the end of the
/// closure's scope so as to avoid self-referential structs.
/// ```rust
/// # let my_buffer_1: [f32; 256] = [0.0; 256];
/// # let my_buffer_2: [f32; 256] = [0.0; 256];
/// # fn i_want_a_slice_of_references(_slice: &[&[f32; 256]]) {}
/// use member_ref_vec::MemberRefVec;
///
/// // Pre-allocate some capacity in a non-performance critical part
/// // of your code. Also, please note the lack of the `&` symbol in
/// // the turbofish operator here. This is *not* allocating 1024
/// // buffers with 256 f32s, This is still just allocating 1024
/// // references to buffers.
/// let mut buffer_refs: MemberRefVec<[f32; 256]> = MemberRefVec::with_capacity(1024);
///
/// // -- In the performance-critical part of your code: ---------
///
/// buffer_refs.as_empty_vec_of_refs(|buffers| {
///   // Does not allocated memory! (as long as you don't push more
///   // elements than what was allocated in the non-realtime thread)
///   buffers.push(&my_buffer_1);
///   buffers.push(&my_buffer_2);
///
///   i_want_a_slice_of_references(&buffers[..]);
/// });
/// ```
///
/// ## Safety Notes
/// This crate currently assumes that a `Vec<&'static T>` always has the exact same layout in
/// memory as a `Vec<&'a T>` (and that a `Vec<&'static mut T>` always has the exact same
/// layout in memory as a `Vec<&'a mut T>`) where `T: 'static + Sized`. If you happen to know
/// if this assumption is correct or not, please contact me.
///
/// [`smallvec`]: https://crates.io/crates/smallvec
pub struct MemberRefVec<T: 'static + Sized> {
    v: Option<ManuallyDrop<Vec<&'static T>>>,
}

impl<T: 'static + Sized> Default for MemberRefVec<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: 'static + Sized> MemberRefVec<T> {
    /// Creates a new `MemberRefVec` with an empty capacity.
    pub fn new() -> Self {
        Self {
            v: Some(ManuallyDrop::new(Vec::new())),
        }
    }

    /// Creates a new `MemberRefVec` with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            v: Some(ManuallyDrop::new(Vec::with_capacity(capacity))),
        }
    }

    /// Borrow this vector as an `&mut Vec<&'a T>`.
    ///
    /// This borrowed vector will **always** be cleared to a length of 0
    /// before being sent to the given closure, and all elements will be cleared
    /// once the closure exits.
    ///
    /// However, the reserved capacity of this vector *will* be retained across
    /// consecutive calls to `as_empty_vec_of_refs()`.
    pub fn as_empty_vec_of_refs<'a, F: FnOnce(&mut ManuallyDrop<Vec<&'a T>>)>(&mut self, f: F) {
        let mut v = self.v.take().unwrap();

        v.clear();

        let capacity = v.capacity();
        let ptr = Vec::as_mut_ptr(&mut v);

        // This is safe because:
        //
        // * We cleared the vector to a length of 0, so no uninitialized data
        // can be read by the user.
        //
        // * We use the same capacity, so all memory here points to valid
        // owned Memberated data.
        //
        // TODO: Check that `Vec<&'static T>` and `Vec<&'a T>` do indeed
        // always have the exact same layout in memory.
        let mut borrowed_v: ManuallyDrop<Vec<&'a T>> = ManuallyDrop::new(unsafe {
            Vec::from_raw_parts(ptr as *mut c_void as *mut &'a T, 0, capacity)
        });

        (f)(&mut borrowed_v);

        // Make sure that any items that were pushed by the user are
        // deMemberated correctly.
        borrowed_v.clear();

        // Make sure that the pointer and capacity are still correct in case
        // the user caused the vector to reMemberate and/or move.
        let capacity = borrowed_v.capacity();
        let ptr = Vec::as_mut_ptr(&mut borrowed_v);

        // This is safe because:
        //
        // * We cleared the vector to a length of 0, so no uninitialized data
        // can be read by the user.
        //
        // * We use the same capacity, so all memory here points to valid
        // owned Memberated data.
        //
        // TODO: Check that `Vec<&'static T>` and `Vec<&'a T>` do indeed
        // always have the exact same layout in memory.
        self.v = Some(ManuallyDrop::new(unsafe {
            Vec::from_raw_parts(ptr as *mut c_void as *mut &'static T, 0, capacity)
        }));
    }

    /// Attempts to set the capacity of this vector.
    ///
    /// * When the given `capacity` is equal to this vector's capacity,
    /// then this is a no-op.
    /// * When the given `capacity` is greater than this vector's capacity,
    /// then this is equivalent to `Vec::reserve(capacity - vec.capacity())`.
    /// The Memberator may still reserve a larger capacity than requested.
    /// * When the given `capacity` is less than this vector's capacity.
    /// this is equivalent to calling `Vec::shrink_to_fit()` and then
    /// reserving the space needed using `Vec::reserve(capacity)`. The
    /// Memberator may still reserve a larger capacity than requested.
    pub fn set_capacity(&mut self, capacity: usize) {
        let v = self.v.as_mut().unwrap();

        if capacity > v.capacity() {
            let additional = capacity - v.capacity();
            v.reserve(additional);
        } else if capacity < v.capacity() {
            v.shrink_to_fit();
            if capacity > v.capacity() {
                let additional = capacity - v.capacity();
                v.reserve(additional);
            }
        }
    }

    /// Attempts to set the capacity of this vector.
    ///
    /// * When the given `capacity` is equal to this vector's capacity,
    /// then this is a no-op.
    /// * When the given `capacity` is greater than this vector's capacity,
    /// then this is equivalent to `Vec::reserve_exact(capacity - vec.capacity())`.
    /// The Memberator may still reserve a larger capacity than requested.
    /// * When the given `capacity` is less than this vector's capacity.
    /// this is equivalent to calling `Vec::shrink_to_fit()` and then
    /// reserving the space needed using `Vec::reserve_exact(capacity)`. The
    /// Memberator may still reserve a larger capacity than requested.
    pub fn set_capacity_exact(&mut self, capacity: usize) {
        let v = self.v.as_mut().unwrap();

        if capacity > v.capacity() {
            let additional = capacity - v.capacity();
            v.reserve_exact(additional);
        } else if capacity < v.capacity() {
            v.shrink_to_fit();
            if capacity > v.capacity() {
                let additional = capacity - v.capacity();
                v.reserve_exact(additional);
            }
        }
    }

    /// The current capacity of this vector.
    pub fn capacity(&self) -> usize {
        self.v.as_ref().unwrap().capacity()
    }
}

impl<T: 'static + Sized> Drop for MemberRefVec<T> {
    fn drop(&mut self) {
        if let Some(v) = self.v.take() {
            let _ = ManuallyDrop::into_inner(v);
        }
    }
}

/// This struct allows you to create a "temporary" Vec of mutable references which persists
/// its allocated memory and which can be stored as a member variable.
///
/// For example, say that you want to prepare a Vec of buffer references to send to another
/// piece of your code. However, the issue here is that this will allocate memory, which can
/// cause issues with performance (or in the case of realtime code, allocation of any kind
/// is unacceptable).
/// ```rust
/// # let mut my_buffer_1: [f32; 256] = [0.0; 256];
/// # let mut my_buffer_2: [f32; 256] = [0.0; 256];
/// # fn i_want_a_slice_of_mut_references(_slice: &mut [&mut [f32; 256]]) {}
/// let mut buffers: Vec<&mut [f32; 256]> = Vec::new();
///
/// // "Push" allocates memory here
/// buffers.push(&mut my_buffer_1);
/// buffers.push(&mut my_buffer_2);
///
/// i_want_a_slice_of_mut_references(&mut buffers[..]);
/// ```
///
/// The usual solution here is to use [`smallvec`] which allocates the memory on the stack.
/// In fact, if this solves your use case, please use that instead of this crate.
/// ```rust
/// # use smallvec::SmallVec;
/// # let mut my_buffer_1: [f32; 256] = [0.0; 256];
/// # let mut my_buffer_2: [f32; 256] = [0.0; 256];
/// # fn i_want_a_slice_of_mut_references(_slice: &mut [&mut [f32; 256]]) {}
/// let mut buffers: SmallVec<[&mut [f32; 256]; 8]> = SmallVec::new();
///
/// // Does not allocated memory anymore!
/// buffers.push(&mut my_buffer_1);
/// buffers.push(&mut my_buffer_2);
///
/// i_want_a_slice_of_mut_references(&mut buffers[..]);
/// ```
///
/// However, note that if we push more than the 8 slots we defined in this SmallVec, then it
/// will allocate memory again. If the maximum number of slots is not known at compile-time,
/// you have 2 options:
///
/// Option 1 is to just allocate a large number of slots and hope that it never exceeds
/// capacity. However, this can potentially overflow your stack if it gets too large, and if
/// the majority of the time only a few slots are being used, there can be a performance
/// penalty of having a function with an unusually large stack size.
///
/// Option 2 is to use this crate. It works by creating a struct that contains a Vec of
/// static references that can be stored in a member variable. Because Rust does not like
/// self-referencing structs very well, this Vec must have the type `Vec<&'static mut T>`.
/// However, it's more than likely that your data does not have a static lifetime. The key
/// trick here is that in order to use this struct, it must be borrowed and used inside a
/// closure. This function converts this `Vec<&'static mut T>` into a `Vec<&'a mut T>` that
/// is then sent to your closure. This operation remains safe because the function ensures
/// that the Vec it sends you is always empty, meaning no uninitialized data can be ever be
/// read from it and cause undefined behavior. It also automatically clears the Vec at the
/// end of the closure's scope so as to avoid self-referential structs.
/// ```rust
/// # let mut my_buffer_1: [f32; 256] = [0.0; 256];
/// # let mut my_buffer_2: [f32; 256] = [0.0; 256];
/// # fn i_want_a_slice_of_mut_references(_slice: &mut [&mut [f32; 256]]) {}
/// use member_ref_vec::MemberRefVecMut;
///
/// // Pre-allocate some capacity in a non-performance critical part
/// // of your code. Also, please note the lack of the `&mut` symbol in
/// // the turbofish operator here. This is *not* allocating 1024
/// // buffers with 256 f32s, This is still just allocating 1024
/// // references to buffers.
/// let mut buffer_refs: MemberRefVecMut<[f32; 256]> = MemberRefVecMut::with_capacity(1024);
///
/// // -- In the performance-critical part of your code: ---------
///
/// buffer_refs.as_empty_vec_of_refs(|buffers| {
///   // Does not allocated memory! (as long as you don't push more
///   // elements than what was allocated in the non-realtime thread)
///   buffers.push(&mut my_buffer_1);
///   buffers.push(&mut my_buffer_2);
///
///   i_want_a_slice_of_mut_references(&mut buffers[..]);
/// });
/// ```
///
/// ## Safety Notes
/// This crate currently assumes that a `Vec<&'static T>` always has the exact same layout in
/// memory as a `Vec<&'a T>` (and that a `Vec<&'static mut T>` always has the exact same
/// layout in memory as a `Vec<&'a mut T>`) where `T: 'static + Sized`. If you happen to know
/// if this assumption is correct or not, please contact me.
///
/// [`smallvec`]: https://crates.io/crates/smallvec
pub struct MemberRefVecMut<T: 'static + Sized> {
    v: Option<ManuallyDrop<Vec<&'static mut T>>>,
}

impl<T: 'static + Sized> Default for MemberRefVecMut<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: 'static + Sized> MemberRefVecMut<T> {
    /// Creates a new `MemberRefVec` with an empty capacity.
    pub fn new() -> Self {
        Self {
            v: Some(ManuallyDrop::new(Vec::new())),
        }
    }

    /// Creates a new `MemberRefVec` with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            v: Some(ManuallyDrop::new(Vec::with_capacity(capacity))),
        }
    }

    /// Borrow this vector as an `&mut Vec<&'a mut T>`.
    ///
    /// This borrowed vector will **always** be cleared to a length of 0
    /// before being sent to the given closure, and all elements will be cleared
    /// once the closure exits.
    ///
    /// However, the reserved capacity of this vector *will* be retained across
    /// consecutive calls to `as_empty_vec_of_refs()`.
    pub fn as_empty_vec_of_refs<'a, F: FnOnce(&mut ManuallyDrop<Vec<&'a mut T>>)>(&mut self, f: F) {
        let mut v = self.v.take().unwrap();

        v.clear();

        let capacity = v.capacity();
        let ptr = Vec::as_mut_ptr(&mut v);

        // This is safe because:
        //
        // * We cleared the vector to a length of 0, so no uninitialized data
        // can be read by the user.
        //
        // * We use the same capacity, so all memory here points to valid
        // owned Memberated data.
        //
        // TODO: Check that `Vec<&'static mut T>` and `Vec<&'a mut T>` do indeed
        // always have the exact same layout in memory.
        let mut borrowed_v: ManuallyDrop<Vec<&'a mut T>> = ManuallyDrop::new(unsafe {
            Vec::from_raw_parts(ptr as *mut c_void as *mut &'a mut T, 0, capacity)
        });

        (f)(&mut borrowed_v);

        // Make sure that any items that were pushed by the user are
        // deMemberated correctly.
        borrowed_v.clear();

        // Make sure that the pointer and capacity are still correct in case
        // the user caused the vector to reMemberate and/or move.
        let capacity = borrowed_v.capacity();
        let ptr = Vec::as_mut_ptr(&mut borrowed_v);

        // This is safe because:
        //
        // * We cleared the vector to a length of 0, so no uninitialized data
        // can be read by the user.
        //
        // * We use the same capacity, so all memory here points to valid
        // owned Memberated data.
        //
        // TODO: Check that `Vec<&'static mut T>` and `Vec<&'a mut T>` do indeed
        // always have the exact same layout in memory.
        self.v = Some(ManuallyDrop::new(unsafe {
            Vec::from_raw_parts(ptr as *mut c_void as *mut &'static mut T, 0, capacity)
        }));
    }

    /// Attempts to set the capacity of this vector.
    ///
    /// * When the given `capacity` is equal to this vector's capacity,
    /// then this is a no-op.
    /// * When the given `capacity` is greater than this vector's capacity,
    /// then this is equivalent to `Vec::reserve(capacity - vec.capacity())`.
    /// The Memberator may still reserve a larger capacity than requested.
    /// * When the given `capacity` is less than this vector's capacity.
    /// this is equivalent to calling `Vec::shrink_to_fit()` and then
    /// reserving the space needed using `Vec::reserve(capacity)`. The
    /// Memberator may still reserve a larger capacity than requested.
    pub fn set_capacity(&mut self, capacity: usize) {
        let v = self.v.as_mut().unwrap();

        if capacity > v.capacity() {
            let additional = capacity - v.capacity();
            v.reserve(additional);
        } else if capacity < v.capacity() {
            v.shrink_to_fit();
            if capacity > v.capacity() {
                let additional = capacity - v.capacity();
                v.reserve(additional);
            }
        }
    }

    /// Attempts to set the capacity of this vector.
    ///
    /// * When the given `capacity` is equal to this vector's capacity,
    /// then this is a no-op.
    /// * When the given `capacity` is greater than this vector's capacity,
    /// then this is equivalent to `Vec::reserve_exact(capacity - vec.capacity())`.
    /// The Memberator may still reserve a larger capacity than requested.
    /// * When the given `capacity` is less than this vector's capacity.
    /// this is equivalent to calling `Vec::shrink_to_fit()` and then
    /// reserving the space needed using `Vec::reserve_exact(capacity)`. The
    /// Memberator may still reserve a larger capacity than requested.
    pub fn set_capacity_exact(&mut self, capacity: usize) {
        let v = self.v.as_mut().unwrap();

        if capacity > v.capacity() {
            let additional = capacity - v.capacity();
            v.reserve_exact(additional);
        } else if capacity < v.capacity() {
            v.shrink_to_fit();
            if capacity > v.capacity() {
                let additional = capacity - v.capacity();
                v.reserve_exact(additional);
            }
        }
    }

    /// The current capacity of this vector.
    pub fn capacity(&self) -> usize {
        self.v.as_ref().unwrap().capacity()
    }
}

impl<T: 'static + Sized> Drop for MemberRefVecMut<T> {
    fn drop(&mut self) {
        if let Some(v) = self.v.take() {
            let _ = ManuallyDrop::into_inner(v);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let test_data_1: Vec<u64> = vec![0, 1, 2];
        let test_data_2: Vec<u64> = vec![3, 4, 5, 6];

        let mut mrv = MemberRefVec::<Vec<u64>>::with_capacity(10);
        let capacity = mrv.capacity();

        mrv.as_empty_vec_of_refs(|borrowed_vec| {
            assert_eq!(borrowed_vec.len(), 0);
            assert_eq!(borrowed_vec.capacity(), capacity);

            borrowed_vec.push(&test_data_1);
            borrowed_vec.push(&test_data_2);

            i_expect_a_slice_of_refs(borrowed_vec.as_slice());
        });

        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), capacity);

        assert_eq!(&test_data_1, &[0, 1, 2]);
        assert_eq!(&test_data_2, &[3, 4, 5, 6]);

        // -- Test setting capacity from struct ---------------------

        mrv.set_capacity(capacity + 10);
        let capacity = mrv.capacity();

        mrv.as_empty_vec_of_refs(|borrowed_vec| {
            assert_eq!(borrowed_vec.len(), 0);
            assert_eq!(borrowed_vec.capacity(), capacity);

            borrowed_vec.push(&test_data_2);
            borrowed_vec.push(&test_data_1);

            i_expect_a_slice_of_refs(borrowed_vec.as_slice());
        });

        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), capacity);

        assert_eq!(&test_data_1, &[0, 1, 2]);
        assert_eq!(&test_data_2, &[3, 4, 5, 6]);

        // -- Test setting capacity from borrowed struct ------------

        let mut borrow_capacity = capacity + 100;

        mrv.as_empty_vec_of_refs(|borrowed_vec| {
            assert_eq!(borrowed_vec.len(), 0);
            assert_eq!(borrowed_vec.capacity(), capacity);

            borrowed_vec.reserve(borrow_capacity - capacity);
            borrow_capacity = borrowed_vec.capacity();

            borrowed_vec.push(&test_data_1);
            borrowed_vec.push(&test_data_2);

            i_expect_a_slice_of_refs(borrowed_vec.as_slice());
        });

        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), borrow_capacity);

        assert_eq!(&test_data_1, &[0, 1, 2]);
        assert_eq!(&test_data_2, &[3, 4, 5, 6]);

        // -- Test moving value inside closure ---------------------

        mrv.as_empty_vec_of_refs(|mut borrowed_vec| {
            let mut new_vec = Vec::new();

            assert_eq!(borrowed_vec.len(), 0);
            assert_eq!(borrowed_vec.capacity(), borrow_capacity);

            std::mem::swap(&mut new_vec, &mut borrowed_vec);

            borrowed_vec.push(&test_data_2);
            borrowed_vec.push(&test_data_1);

            borrow_capacity = borrowed_vec.capacity();

            i_expect_a_slice_of_refs(borrowed_vec.as_slice());
        });

        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), borrow_capacity);

        assert_eq!(&test_data_1, &[0, 1, 2]);
        assert_eq!(&test_data_2, &[3, 4, 5, 6]);
    }

    fn i_expect_a_slice_of_refs(s: &[&Vec<u64>]) {
        for v in s.iter() {
            for item in v.iter() {
                println!("{}", *item);
            }
        }
    }

    #[test]
    fn test_mut() {
        let mut test_data_1: Vec<u64> = vec![0, 1, 2];
        let mut test_data_2: Vec<u64> = vec![3, 4, 5, 6];

        let mut mrv = MemberRefVecMut::<Vec<u64>>::with_capacity(10);
        let capacity = mrv.capacity();

        mrv.as_empty_vec_of_refs(|borrowed_vec| {
            assert_eq!(borrowed_vec.len(), 0);
            assert_eq!(borrowed_vec.capacity(), capacity);

            borrowed_vec.push(&mut test_data_1);
            borrowed_vec.push(&mut test_data_2);

            i_expect_a_slice_of_mut_refs(borrowed_vec.as_mut_slice());
        });

        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), capacity);

        assert_eq!(&test_data_1, &[100, 101, 102]);
        assert_eq!(&test_data_2, &[203, 204, 205, 206]);

        // -- Test setting capacity from struct ---------------------

        mrv.set_capacity(capacity + 10);
        let capacity = mrv.capacity();

        mrv.as_empty_vec_of_refs(|borrowed_vec| {
            assert_eq!(borrowed_vec.len(), 0);
            assert_eq!(borrowed_vec.capacity(), capacity);

            borrowed_vec.push(&mut test_data_2);
            borrowed_vec.push(&mut test_data_1);

            i_expect_a_slice_of_mut_refs(borrowed_vec.as_mut_slice());
        });

        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), capacity);

        assert_eq!(&test_data_1, &[300, 301, 302]);
        assert_eq!(&test_data_2, &[303, 304, 305, 306]);

        // -- Test setting capacity from borrowed struct ------------

        let mut borrow_capacity = capacity + 100;

        mrv.as_empty_vec_of_refs(|borrowed_vec| {
            assert_eq!(borrowed_vec.len(), 0);
            assert_eq!(borrowed_vec.capacity(), capacity);

            borrowed_vec.reserve(borrow_capacity - capacity);
            borrow_capacity = borrowed_vec.capacity();

            borrowed_vec.push(&mut test_data_1);
            borrowed_vec.push(&mut test_data_2);

            i_expect_a_slice_of_mut_refs(borrowed_vec.as_mut_slice());
        });

        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), borrow_capacity);

        assert_eq!(&test_data_1, &[400, 401, 402]);
        assert_eq!(&test_data_2, &[503, 504, 505, 506]);

        // -- Test moving value inside closure ---------------------

        mrv.as_empty_vec_of_refs(|mut borrowed_vec| {
            let mut new_vec = Vec::new();

            assert_eq!(borrowed_vec.len(), 0);
            assert_eq!(borrowed_vec.capacity(), borrow_capacity);

            std::mem::swap(&mut new_vec, &mut borrowed_vec);

            borrowed_vec.push(&mut test_data_2);
            borrowed_vec.push(&mut test_data_1);

            borrow_capacity = borrowed_vec.capacity();

            i_expect_a_slice_of_mut_refs(borrowed_vec.as_mut_slice());
        });

        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), borrow_capacity);

        assert_eq!(&test_data_1, &[600, 601, 602]);
        assert_eq!(&test_data_2, &[603, 604, 605, 606]);
    }

    fn i_expect_a_slice_of_mut_refs(s: &mut [&mut Vec<u64>]) {
        for (i, v) in s.iter_mut().enumerate() {
            for item in v.iter_mut() {
                *item += 100 * (i + 1) as u64;
            }
        }
    }
}
