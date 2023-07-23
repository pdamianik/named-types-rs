// ==== std ====

#[cfg(all(feature = "std", feature = "rust-1-65-0"))]
pub use std::backtrace;
#[cfg(feature = "std")]
pub use std::{
    alloc, any, array, ascii, borrow, boxed, cell, char, cmp, collections, convert, env, error,
    ffi, fmt, fs, future, hash, io, iter, marker, mem, net, num, ops, option, os, panic, path, pin,
    process, ptr, rc, result, slice, str, string, sync, task, thread, time, vec,
};

// ==== alloc ====

#[cfg(all(not(feature = "std"), feature = "alloc"))]
mod import {
    pub extern crate alloc;
}
#[cfg(all(not(feature = "std"), feature = "alloc"))]
pub use import::alloc::{alloc, borrow, boxed, collections, fmt, rc, slice, str, string, vec};

// ==== core ====

#[cfg(not(any(feature = "std", feature = "alloc")))]
pub use core::{alloc, borrow, ffi, fmt, slice, str, sync};
#[cfg(not(feature = "std"))]
pub use core::{
    any, array, ascii, cell, char, cmp, convert, future, hash, iter, marker, mem, num, ops, option, panic, pin,
    ptr, result, task, time,
};

#[cfg(all(not(feature = "std"), feature = "alloc"))]
pub mod ffi {
    extern crate alloc;

    pub use alloc::ffi::*;
    pub use core::ffi::*;
}

#[cfg(all(not(feature = "std"), feature = "alloc"))]
pub mod sync {
    extern crate alloc;

    pub use alloc::sync::*;
    pub use core::sync::*;
}
