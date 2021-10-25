use std::mem::size_of;

pub struct MemberRefVec<T: 'static + Sized> {
    v: Option<Vec<&'static mut T>>,
}

impl<T: 'static + Sized> MemberRefVec<T> {
    /// Creates a new `MemberRefVec` with an empty capacity.
    pub fn new() -> Self {
        Self {
            v: Some(Vec::new()),
        }
    }

    /// Creates a new `MemberRefVec` with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            v: Some(Vec::with_capacity(capacity)),
        }
    }

    /// Creates a new `MemberRefVec` from the given vector `v`.
    pub fn from_vec(mut v: Vec<&'static mut T>) -> Self {
        v.clear();

        Self { v: Some(v) }
    }

    pub fn take_empty_vec<'a>(&mut self) -> Vec<&'a T> {
        // Not for safety, only to ensure the expected performance characteristic.
        debug_assert!(size_of::<&'static mut T>() == size_of::<&'a T>());

        let v = self.v.take().expect("Vec already taken from MemberRefVec. Remember to call MemberRefVec::put() once the taken Vec is finished being used.");
        Self::convert_to(v)
    }

    pub fn try_take_empty_vec<'a>(&mut self) -> Result<Vec<&'a T>, ()> {
        // Not for safety, only to ensure the expected performance characteristic.
        debug_assert!(size_of::<&'static mut T>() == size_of::<&'a T>());

        if let Some(v) = self.v.take() {
            Ok(Self::convert_to(v))
        } else {
            Err(())
        }
    }

    pub fn take_empty_vec_mut<'a>(&mut self) -> Vec<&'a mut T> {
        // Not for safety, only to ensure the expected performance characteristic.
        debug_assert!(size_of::<&'static mut T>() == size_of::<&'a mut T>());

        let v = self.v.take().expect("Vec already taken from MemberRefVec. Remember to call MemberRefVec::put() once the taken Vec is finished being used.");
        Self::convert_to_mut(v)
    }

    pub fn try_take_empty_vec_mut<'a>(&mut self) -> Result<Vec<&'a mut T>, ()> {
        // Not for safety, only to ensure the expected performance characteristic.
        debug_assert!(size_of::<&'static mut T>() == size_of::<&'a T>());

        if let Some(v) = self.v.take() {
            Ok(Self::convert_to_mut(v))
        } else {
            Err(())
        }
    }

    pub fn put(&mut self, returned: Vec<&T>) {
        // Not for safety, only to ensure the expected performance characteristic.
        debug_assert!(size_of::<&'static mut T>() == size_of::<&T>());

        self.v = Some(Self::convert_from(returned));
    }

    pub fn try_put<'a>(&mut self, returned: Vec<&'a T>) -> Result<(), Vec<&'a T>> {
        // Not for safety, only to ensure the expected performance characteristic.
        debug_assert!(size_of::<&'static mut T>() == size_of::<&'a T>());

        if self.v.is_none() {
            self.v = Some(Self::convert_from(returned));
            Ok(())
        } else {
            Err(returned)
        }
    }

    pub fn put_mut(&mut self, returned: Vec<&mut T>) {
        // Not for safety, only to ensure the expected performance characteristic.
        debug_assert!(size_of::<&'static mut T>() == size_of::<&mut T>());

        self.v = Some(Self::convert_from_mut(returned));
    }

    pub fn try_put_mut<'a>(&mut self, returned: Vec<&'a mut T>) -> Result<(), Vec<&'a mut T>> {
        // Not for safety, only to ensure the expected performance characteristic.
        debug_assert!(size_of::<&'static mut T>() == size_of::<&'a mut T>());

        if self.v.is_none() {
            self.v = Some(Self::convert_from_mut(returned));

            Ok(())
        } else {
            Err(returned)
        }
    }

    pub fn use_as_empty_vec<'a, F: FnOnce(&mut Vec<&'a T>)>(&mut self, f: F) {
        // Not for safety, only to ensure the expected performance characteristic.
        debug_assert!(size_of::<&'static mut T>() == size_of::<&'a T>());

        let v = self.v.take().expect("Vec already taken from MemberRefVec. Remember to call MemberRefVec::put() once the taken Vec is finished being used.");
        let mut borrowed_v: Vec<&'a T> = Self::convert_to(v);

        (f)(&mut borrowed_v);

        self.v = Some(Self::convert_from(borrowed_v));
    }

    pub fn use_as_empty_vec_mut<'a, F: FnOnce(&mut Vec<&'a mut T>)>(&mut self, f: F) {
        // Not for safety, only to ensure the expected performance characteristic.
        debug_assert!(size_of::<&'static mut T>() == size_of::<&'a mut T>());

        let v = self.v.take().expect("Vec already taken from MemberRefVec. Remember to call MemberRefVec::put() once the taken Vec is finished being used.");
        let mut borrowed_v: Vec<&'a mut T> = Self::convert_to_mut(v);

        (f)(&mut borrowed_v);

        self.v = Some(Self::convert_from_mut(borrowed_v));
    }

    /// Attempts to set the capacity of this vector.
    ///
    /// * When the given `capacity` is equal to this vector's capacity,
    /// then this is a no-op.
    /// * When the given `capacity` is greater than this vector's capacity,
    /// then this is equivalent to `Vec::reserve(capacity - vec.capacity())`.
    /// The allocator may still reserve a larger capacity than requested.
    /// * When the given `capacity` is less than this vector's capacity.
    /// this is equivalent to calling `Vec::shrink_to_fit()` and then
    /// reserving the space needed using `Vec::reserve(capacity)`. The
    /// allocator may still reserve a larger capacity than requested.
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
    /// The allocator may still reserve a larger capacity than requested.
    /// * When the given `capacity` is less than this vector's capacity.
    /// this is equivalent to calling `Vec::shrink_to_fit()` and then
    /// reserving the space needed using `Vec::reserve_exact(capacity)`. The
    /// allocator may still reserve a larger capacity than requested.
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

    /// Consumes this `MemberRefVec` and returns the underlying `Vec<&'static T>`.
    pub fn into_inner(mut self) -> Vec<&'static mut T> {
        let v = self.v.take().unwrap();
        v
    }

    #[inline]
    fn convert_to<'a>(mut v: Vec<&'static mut T>) -> Vec<&'a T> {
        v.clear();
        let converted_v: Vec<&'a T> = v.into_iter().map(|_| unreachable!()).collect();
        converted_v
    }

    #[inline]
    fn convert_to_mut<'a>(mut v: Vec<&'static mut T>) -> Vec<&'a mut T> {
        v.clear();
        let converted_v: Vec<&'a mut T> = v.into_iter().map(|_| unreachable!()).collect();
        converted_v
    }

    #[inline]
    fn convert_from<'a>(mut v: Vec<&'a T>) -> Vec<&'static mut T> {
        v.clear();
        let converted_v: Vec<&'static mut T> = v.into_iter().map(|_| unreachable!()).collect();
        converted_v
    }

    #[inline]
    fn convert_from_mut<'a>(mut v: Vec<&'a mut T>) -> Vec<&'static mut T> {
        v.clear();
        let converted_v: Vec<&'static mut T> = v.into_iter().map(|_| unreachable!()).collect();
        converted_v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_take_put() {
        let test_data_1: Vec<u64> = vec![0, 1, 2];
        let test_data_2: Vec<u64> = vec![3, 4, 5, 6];

        let mut mrv = MemberRefVec::<Vec<u64>>::with_capacity(2);
        let capacity = mrv.capacity();

        let mut borrowed_vec = mrv.take_empty_vec();
        assert_eq!(borrowed_vec.len(), 0);
        assert_eq!(borrowed_vec.capacity(), capacity);
        borrowed_vec.push(&test_data_1);
        borrowed_vec.push(&test_data_2);
        i_expect_a_slice_of_refs(borrowed_vec.as_slice());

        mrv.put(borrowed_vec);
        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), capacity);
        assert_eq!(&test_data_1, &[0, 1, 2]);
        assert_eq!(&test_data_2, &[3, 4, 5, 6]);

        // -- Test setting capacity from struct ---------------------

        mrv.set_capacity(capacity + 10);
        let capacity = mrv.capacity();

        let mut borrowed_vec = mrv.take_empty_vec();
        assert_eq!(borrowed_vec.len(), 0);
        assert_eq!(borrowed_vec.capacity(), capacity);
        borrowed_vec.push(&test_data_1);
        borrowed_vec.push(&test_data_2);
        i_expect_a_slice_of_refs(borrowed_vec.as_slice());

        mrv.put(borrowed_vec);
        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), capacity);
        assert_eq!(&test_data_1, &[0, 1, 2]);
        assert_eq!(&test_data_2, &[3, 4, 5, 6]);

        // -- Test setting capacity from borrowed struct ------------

        let mut borrow_capacity = capacity + 100;

        let mut borrowed_vec = mrv.take_empty_vec();
        assert_eq!(borrowed_vec.len(), 0);
        assert_eq!(borrowed_vec.capacity(), capacity);
        borrowed_vec.reserve(borrow_capacity - capacity);
        borrow_capacity = borrowed_vec.capacity();
        borrowed_vec.push(&test_data_1);
        borrowed_vec.push(&test_data_2);
        i_expect_a_slice_of_refs(borrowed_vec.as_slice());

        mrv.put(borrowed_vec);
        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), borrow_capacity);
        assert_eq!(&test_data_1, &[0, 1, 2]);
        assert_eq!(&test_data_2, &[3, 4, 5, 6]);

        // -- Test moving value -------------------------------------

        let mut new_vec = Vec::new();

        let mut borrowed_vec = mrv.take_empty_vec();
        assert_eq!(borrowed_vec.len(), 0);
        assert_eq!(borrowed_vec.capacity(), borrow_capacity);
        std::mem::swap(&mut new_vec, &mut borrowed_vec);
        borrowed_vec.push(&test_data_1);
        borrowed_vec.push(&test_data_2);
        borrow_capacity = borrowed_vec.capacity();
        i_expect_a_slice_of_refs(borrowed_vec.as_slice());

        mrv.put(borrowed_vec);
        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), borrow_capacity);
        assert_eq!(&test_data_1, &[0, 1, 2]);
        assert_eq!(&test_data_2, &[3, 4, 5, 6]);
    }

    #[test]
    fn test_take_put_mut() {
        let mut test_data_1: Vec<u64> = vec![0, 1, 2];
        let mut test_data_2: Vec<u64> = vec![3, 4, 5, 6];

        let mut mrv = MemberRefVec::<Vec<u64>>::with_capacity(2);
        let capacity = mrv.capacity();

        let mut borrowed_vec = mrv.take_empty_vec_mut();
        assert_eq!(borrowed_vec.len(), 0);
        assert_eq!(borrowed_vec.capacity(), capacity);
        borrowed_vec.push(&mut test_data_1);
        borrowed_vec.push(&mut test_data_2);
        i_expect_a_slice_of_mut_refs(borrowed_vec.as_mut_slice());

        mrv.put_mut(borrowed_vec);
        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), capacity);
        assert_eq!(&test_data_1, &[100, 101, 102]);
        assert_eq!(&test_data_2, &[203, 204, 205, 206]);

        // -- Test setting capacity from struct ---------------------

        mrv.set_capacity(capacity + 10);
        let capacity = mrv.capacity();

        let mut borrowed_vec = mrv.take_empty_vec_mut();
        assert_eq!(borrowed_vec.len(), 0);
        assert_eq!(borrowed_vec.capacity(), capacity);
        borrowed_vec.push(&mut test_data_2);
        borrowed_vec.push(&mut test_data_1);
        i_expect_a_slice_of_mut_refs(borrowed_vec.as_mut_slice());

        mrv.put_mut(borrowed_vec);
        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), capacity);
        assert_eq!(&test_data_1, &[300, 301, 302]);
        assert_eq!(&test_data_2, &[303, 304, 305, 306]);

        // -- Test setting capacity from borrowed struct ------------

        let mut borrow_capacity = capacity + 100;

        let mut borrowed_vec = mrv.take_empty_vec_mut();
        assert_eq!(borrowed_vec.len(), 0);
        assert_eq!(borrowed_vec.capacity(), capacity);
        borrowed_vec.reserve(borrow_capacity - capacity);
        borrow_capacity = borrowed_vec.capacity();
        borrowed_vec.push(&mut test_data_1);
        borrowed_vec.push(&mut test_data_2);
        i_expect_a_slice_of_mut_refs(borrowed_vec.as_mut_slice());

        mrv.put_mut(borrowed_vec);
        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), borrow_capacity);
        assert_eq!(&test_data_1, &[400, 401, 402]);
        assert_eq!(&test_data_2, &[503, 504, 505, 506]);

        // -- Test moving value -------------------------------------

        let mut new_vec = Vec::new();

        let mut borrowed_vec = mrv.take_empty_vec_mut();
        assert_eq!(borrowed_vec.len(), 0);
        assert_eq!(borrowed_vec.capacity(), borrow_capacity);
        std::mem::swap(&mut new_vec, &mut borrowed_vec);
        borrowed_vec.push(&mut test_data_2);
        borrowed_vec.push(&mut test_data_1);
        borrow_capacity = borrowed_vec.capacity();
        i_expect_a_slice_of_mut_refs(borrowed_vec.as_mut_slice());

        mrv.put_mut(borrowed_vec);
        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), borrow_capacity);
        assert_eq!(&test_data_1, &[600, 601, 602]);
        assert_eq!(&test_data_2, &[603, 604, 605, 606]);
    }

    #[test]
    #[should_panic]
    fn test_take_assert() {
        let mut mrv = MemberRefVec::<Vec<u64>>::with_capacity(2);
        let _borrowed_vec = mrv.take_empty_vec();
        let _borrowed_vec_2 = mrv.take_empty_vec();
    }

    #[test]
    #[should_panic]
    fn test_take_mut_assert() {
        let mut mrv = MemberRefVec::<Vec<u64>>::with_capacity(2);
        let _borrowed_vec = mrv.take_empty_vec_mut();
        let _borrowed_vec_2 = mrv.take_empty_vec_mut();
    }

    #[test]
    fn test_use_as_empty_vec() {
        let test_data_1: Vec<u64> = vec![0, 1, 2];
        let test_data_2: Vec<u64> = vec![3, 4, 5, 6];

        let mut mrv = MemberRefVec::<Vec<u64>>::with_capacity(2);
        let capacity = mrv.capacity();

        mrv.use_as_empty_vec(|borrowed_vec| {
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

        mrv.use_as_empty_vec(|borrowed_vec| {
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

        // -- Test setting capacity from borrowed struct ------------

        let mut borrow_capacity = capacity + 100;

        mrv.use_as_empty_vec(|borrowed_vec| {
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

        mrv.use_as_empty_vec(|mut borrowed_vec| {
            let mut new_vec = Vec::new();
            assert_eq!(borrowed_vec.len(), 0);
            assert_eq!(borrowed_vec.capacity(), borrow_capacity);
            std::mem::swap(&mut new_vec, &mut borrowed_vec);
            borrowed_vec.push(&test_data_1);
            borrowed_vec.push(&test_data_2);
            borrow_capacity = borrowed_vec.capacity();
            i_expect_a_slice_of_refs(borrowed_vec.as_slice());
        });

        assert_eq!(mrv.v.as_ref().unwrap().len(), 0);
        assert_eq!(mrv.capacity(), borrow_capacity);
        assert_eq!(&test_data_1, &[0, 1, 2]);
        assert_eq!(&test_data_2, &[3, 4, 5, 6]);
    }

    #[test]
    fn test_use_as_empty_vec_mut() {
        let mut test_data_1: Vec<u64> = vec![0, 1, 2];
        let mut test_data_2: Vec<u64> = vec![3, 4, 5, 6];

        let mut mrv = MemberRefVec::<Vec<u64>>::with_capacity(2);
        let capacity = mrv.capacity();

        mrv.use_as_empty_vec_mut(|borrowed_vec| {
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

        mrv.use_as_empty_vec_mut(|borrowed_vec| {
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

        mrv.use_as_empty_vec_mut(|borrowed_vec| {
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

        mrv.use_as_empty_vec_mut(|mut borrowed_vec| {
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

    fn i_expect_a_slice_of_refs(s: &[&Vec<u64>]) {
        for (i, v) in s.iter().enumerate() {
            if i == 0 {
                assert_eq!(&v[..], &[0, 1, 2]);
            } else if i == 1 {
                assert_eq!(&v[..], &[3, 4, 5, 6]);
            }
        }
    }

    fn i_expect_a_slice_of_mut_refs(s: &mut [&mut Vec<u64>]) {
        for (i, v) in s.iter_mut().enumerate() {
            for item in v.iter_mut() {
                *item += 100 * (i + 1) as u64;
            }
        }
    }
}
