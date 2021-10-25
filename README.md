# Member Reference Vector
![Stable](https://github.com/BillyDM/member-ref-vec/workflows/stable/badge.svg)
![Nightly](https://github.com/BillyDM/member-ref-vec/workflows/nightly/badge.svg)
[![Documentation](https://docs.rs/member-ref-vec/badge.svg)](https://docs.rs/member-ref-vec)
[![Crates.io](https://img.shields.io/crates/v/member-ref-vec.svg)](https://crates.io/crates/member-ref-vec)
[![License](https://img.shields.io/crates/l/member-ref-vec.svg)](https://github.com/BillyDM/member-ref-vec/blob/main/LICENSE)

This crate allows you to create a "temporary" Vec of references which persists its allocated memory and which can be stored as a member variable.

For example, say that you want to prepare a Vec of buffer references to send to another piece of your code. But the issue is that this will allocate memory, which can lead to issues with performance (or in the case of realtime code, allocation of any kind is unacceptable).
```rust
let mut buffers: Vec<&[f32; 256]> = Vec::new();

// "Push" allocates memory here
buffers.push(&my_buffer_1);
buffers.push(&my_buffer_2);

i_want_a_slice_of_references(&buffers[..]);
```

The usual solution here is to use [`smallvec`] which allocates the memory on the stack. In fact, if this solves your use case, please use that instead of this crate.
```rust
let mut buffers: SmallVec<[&[f32; 256]; 8]> = SmallVec::new();

// Does not allocated memory anymore!
buffers.push(&my_buffer_1);
buffers.push(&my_buffer_2);

i_want_a_slice_of_references(&buffers[..]);
```

However, if we happen to push more than the 8 slots we defined in this SmallVec, then it will allocate memory again. If the maximum number of slots is not known at compile-time, you have 2 options:

Option 1 is to just allocate a large number of slots and hope that it never exceeds capacity. However, this can potentially overflow your stack if it gets too large, and if the majority of the time only a few slots are being used, there can be a performance penalty in having a function with an unusually large stack size.

Option 2 is to use this crate. Here's how it works:

Because Rust does not like self-referencing structs, the `MemberRefVec` must contain the type `Vec<&'static T>`. But it is more than likely your data does not have a static lifetime.

The key trick here is that this struct converts this `Vec<&'static T>` into a `Vec<&'a T>` when you acess one of its methods. This operation is safe because this Vec is always cleared before being sent to the closure, meaning no uninitialized data can be ever be read from it and cause undefined behavior. It also avoids self-referential structs by automatically clearing the Vec at the end of the closure's scope.
```rust
use member_ref_vec::MemberRefVec;

// Pre-allocate some capacity in a non-performance critical part
// of your code. Also please note the lack of the `&` symbol in
// the type parameter here. This is *not* allocating 1024
// buffers with 256 f32s, This is still just allocating 1024
// references to buffers.
let mut buffer_refs: MemberRefVec<[f32; 256]> = MemberRefVec::with_capacity(1024);

// (You may also use `MemberRefVecMut` for mutable references.)

// -- In the performance-critical part of your code: ---------

buffer_refs.as_empty_vec_of_refs(|buffers| {
  // Does not allocated memory! (as long as you don't push more
  // elements than what was allocated in the non-performance
  // critical part of your code)
  buffers.push(&my_buffer_1);
  buffers.push(&my_buffer_2);

  i_want_a_slice_of_references(&buffers[..]);
});
```

## Safety Notes
*Please note that the safety of this code has not been battle-tested yet. It appears to be safe through my brief testing, but use at your own risk. Most of the functionality of this crate can also be acheived using [`smallvec`], so please consider using that before considering to use this crate.*

This crate currently assumes that a `Vec<&'static T>` always has the exact same layout in memory as a `Vec<&'a T>` (and that a `Vec<&'static mut T>` always has the exact same layout in memory as a `Vec<&'a mut T>`) where `T: 'static + Sized`. If you happen to know if this assumption is correct or not, please contact me.

[`smallvec`]: https://crates.io/crates/smallvec
