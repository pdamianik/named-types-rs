//! This crate provides [`Named`], a trait that provides a nice [`core::fmt::Display`]able way to
//! get a types Name. It is similar to [`core::any::type_name`] without paths, but should
//! provide a more sensical name for something like `std::io::Error`, which would show up
//! as `Error` with something like [pretty-type-name](https://crates.io/crates/pretty-type-name),
//! whereas this crate provides the name `IoError`.
//!
//! The names for `std` are given based on the [Duck
//! Test](https://en.wikipedia.org/wiki/Duck_test), e.g. [`core::slice::Iter`] stays `Iter`
//! conflicting with something like [`core::option::Iter`] because it behaves like a generic iterator, whereas
//! `std::io::Error` does not behave like a generic Error but rather is a specific Error type
//! for io operations.
//!
//! Additionally a [`Named`](derive.Named.html) derive macro is provided for deriving the [`Named`] trait. This macro
//! can be configured by attributing a derived type with `#[named(...)]`. The following options can
//! be passed to the attribute:
//!
//!  * `rename = "..."` to change the types name.
//!  * `format = "..."` to use a custom format string that accepts all non-ignored generic.
//!  Overrides `rename = "..."`
//!  parameters to format the types name.
//!  * `ignore_all` to ignore all generic parameters.
//!  * `ignore = ...` to ignore a generic parameter.
//!  * `passthrough = ...` to use the [`Named`] implementation of a generic parameter. Takes
//!  priority over other options.
//! 
//! To configure multiple options repeat the `#[named(...)]` attribute.
//!
//! ## Feature flags
#![doc = document_features::document_features!()]

#![cfg_attr(not(feature = "std"), no_std)]

mod stdlib;
use crate::stdlib::*;

/// Like [`core::fmt::Display`] or [`Debug`] but for type names and generic type names.
pub trait Named {
    /// A constant way to [`core::fmt::Display`] the Nameds type name.
    const NAME: Name = Name(Self::format_name);

    /// Formats the name of the Self type.
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

/// The name of a type
#[derive(Copy, Clone)]
pub struct Name(pub fn(&mut stdlib::fmt::Formatter<'_>) -> stdlib::fmt::Result);

impl stdlib::fmt::Debug for Name {
    #[inline]
    fn fmt(&self, f: &mut stdlib::fmt::Formatter<'_>) -> stdlib::fmt::Result {
        stdlib::fmt::Display::fmt(self, f)
    }
}

impl stdlib::fmt::Display for Name {
    #[inline]
    fn fmt(&self, f: &mut stdlib::fmt::Formatter<'_>) -> stdlib::fmt::Result {
        self.0(f)
    }
}

macro_rules! simple_impl {
    ($simple:ty => $name:expr) => {
        impl $crate::Named for $simple {
            #[inline]
            fn format_name(
                f: &mut $crate::stdlib::fmt::Formatter<'_>,
            ) -> $crate::stdlib::fmt::Result {
                write!(f, $name)
            }
        }
    };
}

macro_rules! simple_trait_impl {
    ($simple:ty => $name:expr) => {
        impl $crate::Named for $simple {
            #[inline]
            fn format_name(
                f: &mut $crate::stdlib::fmt::Formatter<'_>,
            ) -> $crate::stdlib::fmt::Result {
                write!(f, concat!("dyn ", $name))
            }
        }
    };
}

macro_rules! simple_container_impl {
    (impl<$ig:ident$(: $first_gd:ident$( + $gd:ident)*)?> $type:ty => $name:expr) => {
        impl<$ig$(: $first_gd$( + $gd)*)?> $crate::Named for $type where $ig: $crate::Named {
            #[inline]
            fn format_name(f: &mut $crate::stdlib::fmt::Formatter<'_>) -> $crate::stdlib::fmt::Result {
                write!(f, concat!($name, "<{}>"), $ig::NAME)
            }
        }
    };
}

macro_rules! simple_map_impl {
    (impl<$key_generic:ident$(: $first_key_gd:ident$( + $key_gd:ident)*)?, $value_generic:ident$(: $first_value_gd:ident$( + $value_gd:ident)*)?> $type:ty => $name:expr) => {
        impl<$key_generic$(: $first_key_gd$( + $key_gd)*)?, $value_generic$(: $first_value_gd$( + $value_gd)*)?> $crate::Named for $type where $key_generic: $crate::Named, $value_generic: $crate::Named {
            #[inline]
            fn format_name(f: &mut $crate::stdlib::fmt::Formatter<'_>) -> $crate::stdlib::fmt::Result {
                write!(f, concat!($name, "<{}, {}>"), $key_generic::NAME, $value_generic::NAME)
            }
        }
    };
}

macro_rules! tuple_impl {
    ($(($leading_name:ident$(, $name:ident)*))*$(,)?) => {
        $(
            impl<$leading_name: $crate::Named, $($name: $crate::Named), *> $crate::Named for ($leading_name, $($name), *) {
                #[inline]
                fn format_name(f: &mut $crate::stdlib::fmt::Formatter<'_>) -> $crate::stdlib::fmt::Result {
                    write!(f, "({}", $leading_name::NAME)?;
                    $(write!(f, ", {}", $name::NAME)?;)*
                    write!(f, ")")
                }
            }
        )+
    };
}

macro_rules! deref_impl {
    (impl <$($desc:tt)+) => {
        impl <$($desc)+ where T: $crate::Named {
            const NAME: $crate::Name = T::NAME;

            #[inline]
            fn format_name(f: &mut $crate::stdlib::fmt::Formatter<'_>) -> $crate::stdlib::fmt::Result {
                T::format_name(f)
            }
        }
    };
}

macro_rules! simple_op_trait_impl {
    ($type:ty = $type_assign:ty => $name:expr, $op:expr) => {
        impl<Rhs, Output> Named for $type
        where
            Rhs: Named,
            Output: Named,
        {
            #[inline]
            fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(
                    f,
                    concat!("dyn ", $name, " ", $op, " {} = {}"),
                    Rhs::NAME,
                    Output::NAME
                )
            }
        }

        impl<Rhs> Named for $type_assign
        where
            Rhs: Named,
        {
            #[inline]
            fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!("dyn ", $name, "Assign ", $op, "= {}"), Rhs::NAME)
            }
        }
    };
}

// ==== Primitive Types ====

// ---- array ----

impl<T: Named, const N: usize> Named for [T; N] {
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}; {}]", T::NAME, N)
    }
}

simple_impl!(bool => "bool");
simple_impl!(char => "char");
simple_impl!(f32 => "f32");
simple_impl!(f64 => "f64");
simple_impl!(i8 => "i8");
simple_impl!(i16 => "i16");
simple_impl!(i32 => "i32");
simple_impl!(i64 => "i64");
simple_impl!(i128 => "i128");
simple_impl!(isize => "isize");

// ---- pointer ----

deref_impl!(impl<T: ?Sized> Named for *const T);
deref_impl!(impl<T: ?Sized> Named for *mut T);

// ---- reference ----

deref_impl!(impl<'a, T: ?Sized> Named for &'a T);
deref_impl!(impl<'a, T: ?Sized> Named for &'a mut T);

// ---- slice ----

impl<T: Named> Named for [T] {
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}]", T::NAME)
    }
}

simple_impl!(str => "str");

tuple_impl!(
    (T0)(T0, T1)(T0, T1, T2)(T0, T1, T2, T3)(T0, T1, T2, T3, T4)(T0, T1, T2, T3, T4, T5)(
        T0, T1, T2, T3, T4, T5, T6
    )(T0, T1, T2, T3, T4, T5, T6, T7)(T0, T1, T2, T3, T4, T5, T6, T7, T8)(
        T0, T1, T2, T3, T4, T5, T6, T7, T8, T9
    )(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)(
        T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11
    )(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)(
        T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13
    )(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14)(
        T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15
    )
);

simple_impl!(u8 => "u8");
simple_impl!(u16 => "u16");
simple_impl!(u32 => "u32");
simple_impl!(u64 => "u64");
simple_impl!(u128 => "u128");
simple_impl!(() => "()");
simple_impl!(usize => "usize");

// ==== {std, alloc, core}::alloc ====

// ---- structs ----

simple_impl!(alloc::Layout => "AllocLayout");
simple_impl!(alloc::LayoutError => "AllocLayoutError");
#[cfg(feature = "std")]
simple_impl!(alloc::System => "SystemAlloc");

// ---- traits ----
simple_trait_impl!(dyn alloc::GlobalAlloc => "GlobalAlloc");

// ==== {std, core}::any ====

// ---- structs ----

simple_impl!(any::TypeId => "TypeId");

// ---- traits ----

simple_trait_impl!(dyn any::Any => "Any");

// ==== {std, core}::any ====

// ---- structs ----

impl<T, const N: usize> Named for array::IntoIter<T, N>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IntoIter<{}, {}>", T::NAME, N)
    }
}

// ==== {std, core}::ascii ====

// ---- structs ----

simple_impl!(ascii::EscapeDefault => "EscapeDefault");

// ==== std::backtrace ====

// ---- structs ----

#[cfg(all(feature = "std", feature = "rust-1-65-0"))]
simple_impl!(backtrace::Backtrace => "Backtrace");

// ---- enums ----

#[cfg(all(feature = "std", feature = "rust-1-65-0"))]
simple_impl!(backtrace::BacktraceStatus => "BacktraceStatus");

// ==== {std, alloc, core}::borrow ====

// ---- enums ----

#[cfg(any(feature = "std", feature = "alloc"))]
impl<B: borrow::ToOwned + ?Sized> Named for borrow::Cow<'_, B>
where
    B: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", B::NAME)
    }
}

// ---- traits ----

impl<Borrowed: ?Sized> Named for dyn borrow::Borrow<Borrowed>
where
    Borrowed: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Borrowed::NAME)
    }
}

impl<Borrowed: ?Sized> Named for dyn borrow::BorrowMut<Borrowed>
where
    Borrowed: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Borrowed::NAME)
    }
}

// ==== {std, alloc}::boxed ====

// ---- structs ----

#[cfg(any(feature = "std", feature = "alloc"))]
deref_impl!(impl<T: ?Sized> Named for boxed::Box<T>);

// ==== {std, core}::cell ====

// ---- structs ----

simple_impl!(cell::BorrowError => "BorrowError");
simple_impl!(cell::BorrowMutError => "BorrowMutError");
deref_impl!(impl<T: ?Sized> Named for cell::Cell<T>);
#[cfg(feature = "rust-1-70-0")]
deref_impl!(impl<T> Named for cell::OnceCell<T>);
deref_impl!(impl<'b, T: ?Sized> Named for cell::Ref<'b, T>);
deref_impl!(impl<T: ?Sized> Named for cell::RefCell<T>);
deref_impl!(impl<'b, T: ?Sized> Named for cell::RefMut<'b, T>);
deref_impl!(impl<T: ?Sized> Named for cell::UnsafeCell<T>);

// ==== {std, core}::char ====

// ---- structs ----

simple_impl!(char::CharTryFromError => "CharTryFromError");

impl<I: Iterator<Item = u16>> Named for char::DecodeUtf16<I>
where
    I: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DecodeUtf16<from {}>", I::NAME)
    }
}

simple_impl!(char::DecodeUtf16Error => "DecodeUtf16Error");
simple_impl!(char::EscapeDebug => "EscapeDebug");
simple_impl!(char::EscapeDefault => "EscapeDefault");
simple_impl!(char::EscapeUnicode => "EscapeUnicode");
simple_impl!(char::ParseCharError => "ParseCharError");
simple_impl!(char::ToLowercase => "ToLowercase");
simple_impl!(char::ToUppercase => "ToUppercase");
#[cfg(feature = "rust-1-59-0")]
simple_impl!(char::TryFromCharError => "TryFromCharError");

// ==== {std, core}::cmp ====

// ---- structs ----

simple_container_impl!(impl<T> cmp::Reverse<T> => "Reverse");

// ---- enums ----

simple_impl!(cmp::Ordering => "Ordering");

// ---- traits ----

impl<Rhs: ?Sized> Named for dyn cmp::PartialEq<Rhs>
where
    Rhs: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "dyn PartialEq<{}>", Rhs::NAME)
    }
}

impl<Rhs: ?Sized> Named for dyn PartialOrd<Rhs>
where
    Rhs: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "dyn PartialOrd<{}>", Rhs::NAME)
    }
}

// ==== {std, alloc}::collections ====

// ---- structs ----

#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T: Ord> collections::binary_heap::BinaryHeap<T> => "BinaryHeap");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::binary_heap::Drain<'_, T> => "Drain");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::binary_heap::IntoIter<T> => "IntoIter");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::binary_heap::Iter<'_, T> => "Iter");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T: Ord> collections::binary_heap::PeekMut<'_, T> => "PeekMut");

#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::BTreeMap<K, V> => "BTreeMap");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::IntoIter<K, V> => "IntoIter");
#[cfg(all(any(feature = "std", feature = "alloc"), feature = "rust-1-54-0"))]
simple_map_impl!(impl<K, V> collections::btree_map::IntoKeys<K, V> => "IntoKeys");
#[cfg(all(any(feature = "std", feature = "alloc"), feature = "rust-1-54-0"))]
simple_map_impl!(impl<K, V> collections::btree_map::IntoValues<K, V> => "IntoValues");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::Iter<'_, K, V> => "Iter");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::IterMut<'_, K, V> => "IterMut");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::Keys<'_, K, V> => "Keys");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::OccupiedEntry<'_, K, V> => "OccupiedEntry");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::Range<'_, K, V> => "Range");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::RangeMut<'_, K, V> => "RangeMut");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::VacantEntry<'_, K, V> => "VacantEntry");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::Values<'_, K, V> => "Values");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::ValuesMut<'_, K, V> => "ValuesMut");

#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::btree_set::BTreeSet<T> => "BTreeSet");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::btree_set::Difference<'_, T> => "Difference");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::btree_set::Intersection<'_, T> => "Intersection");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::btree_set::IntoIter<T> => "IntoIter");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::btree_set::Iter<'_, T> => "Iter");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::btree_set::Range<'_, T> => "Range");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::btree_set::SymmetricDifference<'_, T> => "SymmetricDifference");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::btree_set::Union<'_, T> => "Union");

#[cfg(feature = "std")]
simple_map_impl!(impl<K, V> collections::hash_map::HashMap<K, V> => "HashMap");
#[cfg(feature = "std")]
simple_impl!(collections::hash_map::DefaultHasher => "DefaultHasher");
#[cfg(feature = "std")]
simple_map_impl!(impl<K, V> collections::hash_map::Drain<'_, K, V> => "Drain");
#[cfg(feature = "std")]
simple_map_impl!(impl<K, V> collections::hash_map::IntoIter<K, V> => "IntoIter");
#[cfg(all(feature = "std", feature = "rust-1-54-0"))]
simple_map_impl!(impl<K, V> collections::hash_map::IntoKeys<K, V> => "IntoKeys");
#[cfg(all(feature = "std", feature = "rust-1-54-0"))]
simple_map_impl!(impl<K, V> collections::hash_map::IntoValues<K, V> => "IntoValues");
#[cfg(feature = "std")]
simple_map_impl!(impl<K, V> collections::hash_map::Iter<'_, K, V> => "Iter");
#[cfg(feature = "std")]
simple_map_impl!(impl<K, V> collections::hash_map::IterMut<'_, K, V> => "IterMut");
#[cfg(feature = "std")]
simple_map_impl!(impl<K, V> collections::hash_map::Keys<'_, K, V> => "Keys");
#[cfg(feature = "std")]
simple_map_impl!(impl<K, V> collections::hash_map::OccupiedEntry<'_, K, V> => "OccupiedEntry");
#[cfg(feature = "std")]
simple_impl!(collections::hash_map::RandomState => "RandomState");
#[cfg(feature = "std")]
simple_map_impl!(impl<K, V> collections::hash_map::VacantEntry<'_, K, V> => "VacantEntry");
#[cfg(feature = "std")]
simple_map_impl!(impl<K, V> collections::hash_map::Values<'_, K, V> => "Values");
#[cfg(feature = "std")]
simple_map_impl!(impl<K, V> collections::hash_map::ValuesMut<'_, K, V> => "ValuesMut");

#[cfg(feature = "std")]
simple_container_impl!(impl<T> collections::hash_set::HashSet<T> => "HashSet");
#[cfg(feature = "std")]
simple_map_impl!(impl<T, S> collections::hash_set::Difference<'_, T, S> => "Difference");
#[cfg(feature = "std")]
simple_container_impl!(impl<K> collections::hash_set::Drain<'_, K> => "Drain");
#[cfg(feature = "std")]
simple_map_impl!(impl<T, S> collections::hash_set::Intersection<'_, T, S> => "Intersection");
#[cfg(feature = "std")]
simple_container_impl!(impl<K> collections::hash_set::IntoIter<K> => "IntoIter");
#[cfg(feature = "std")]
simple_container_impl!(impl<K> collections::hash_set::Iter<'_, K> => "Iter");
#[cfg(feature = "std")]
simple_map_impl!(impl<T, S> collections::hash_set::SymmetricDifference<'_, T, S> => "SymmetricDifference");
#[cfg(feature = "std")]
simple_map_impl!(impl<T, S> collections::hash_set::Union<'_, T, S> => "Union");

#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::linked_list::LinkedList<T> => "LinkedList");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::linked_list::IntoIter<T> => "IntoIter");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::linked_list::Iter<'_, T> => "Iter");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::linked_list::IterMut<'_, T> => "IterMut");

#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::vec_deque::VecDeque<T> => "VecDeque");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::vec_deque::Drain<'_, T> => "Drain");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::vec_deque::IntoIter<T> => "IntoIter");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::vec_deque::Iter<'_, T> => "Iter");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> collections::vec_deque::IterMut<'_, T> => "IterMut");

#[cfg(any(feature = "std", feature = "alloc"))]
#[cfg(feature = "rust-1-57-0")]
simple_impl!(collections::TryReserveError => "TryReserveError");

// ---- enums ----

#[cfg(any(feature = "std", feature = "alloc"))]
simple_map_impl!(impl<K, V> collections::btree_map::Entry<'_, K, V> => "Entry");
#[cfg(feature = "std")]
simple_map_impl!(impl<K, V> collections::hash_map::Entry<'_, K, V> => "Entry");

// ==== {std,core}::convert ====

// ---- enums ----

simple_impl!(convert::Infallible => "Infallible");

// ---- traits ----

deref_impl!(impl<T: ?Sized> Named for dyn convert::AsMut<T>);
deref_impl!(impl<T: ?Sized> Named for dyn convert::AsRef<T>);

// ==== std::env ====

// ---- structs ----

#[cfg(feature = "std")]
simple_impl!(env::Args => "MainArgs");
#[cfg(feature = "std")]
simple_impl!(env::ArgsOs => "MainArgsOs");
#[cfg(feature = "std")]
simple_impl!(env::JoinPathsError => "JoinPathsError");

#[cfg(feature = "std")]
simple_impl!(env::SplitPaths<'_> => "SplitPaths");

#[cfg(feature = "std")]
simple_impl!(env::Vars => "EnvVars");
#[cfg(feature = "std")]
simple_impl!(env::VarsOs => "EnvVarsOs");

// ---- enums ----

#[cfg(feature = "std")]
simple_impl!(env::VarError => "EnvVarError");

// ==== error ====

// ---- traits ----

#[cfg(feature = "std")]
simple_trait_impl!(dyn error::Error => "Error");

// ==== {std,alloc,core}::ffi ====

// ---- structs ----

simple_impl!(ffi::CStr => "CStr");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_impl!(ffi::CString => "CString");
#[cfg(not(feature = "std"))]
simple_impl!(ffi::FromBytesUntilNulError => "FromBytesUntilNullError");
simple_impl!(ffi::FromBytesWithNulError => "FromBytesWithNulError");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_impl!(ffi::FromVecWithNulError => "FromVecWithNulError");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_impl!(ffi::IntoStringError => "IntoStringError");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_impl!(ffi::NulError => "NulError");
#[cfg(feature = "std")]
simple_impl!(ffi::OsStr => "OsStr");
#[cfg(feature = "std")]
simple_impl!(ffi::OsString => "OsString");

// ---- enums ----

simple_impl!(ffi::c_void => "c_void");

// ==== {std,alloc,core}::fmt ====

// ---- structs ----

simple_impl!(fmt::Arguments<'_> => "FormatArguments");
simple_impl!(fmt::DebugList<'_, '_> => "FormatDebugList");
simple_impl!(fmt::DebugMap<'_, '_> => "FormatDebugMap");
simple_impl!(fmt::DebugSet<'_, '_> => "FormatDebugSet");
simple_impl!(fmt::DebugStruct<'_, '_> => "FormatDebugStruct");
simple_impl!(fmt::DebugTuple<'_, '_> => "FormatDebugTuple");
simple_impl!(fmt::Error => "FormatError");
simple_impl!(fmt::Formatter<'_> => "FormatFormatter");

// ---- enums ----

simple_impl!(fmt::Alignment => "FormatAlignment");

// ---- traits ----

simple_trait_impl!(dyn fmt::Binary => "FormatAsBinary");
simple_trait_impl!(dyn fmt::Debug => "Debug");
simple_trait_impl!(dyn fmt::Display => "Display");
simple_trait_impl!(dyn fmt::LowerExp => "FormatAsLowerExp");
simple_trait_impl!(dyn fmt::LowerHex => "FormatAsLowerHex");
simple_trait_impl!(dyn fmt::Octal => "FormatAsOctal");
simple_trait_impl!(dyn fmt::Pointer => "FormatAsPointer");
simple_trait_impl!(dyn fmt::UpperExp => "FormatAsUpperExp");
simple_trait_impl!(dyn fmt::UpperHex => "FormatAsUpperHex");
simple_trait_impl!(dyn fmt::Write => "FormatWrite");

// ==== std::fs ====

// ---- structs ----

#[cfg(feature = "std")]
simple_impl!(fs::DirBuilder => "DirBuilder");
#[cfg(feature = "std")]
simple_impl!(fs::DirEntry => "DirEntry");
#[cfg(feature = "std")]
simple_impl!(fs::File => "File");
#[cfg(feature = "std")]
simple_impl!(fs::FileType => "FileType");
#[cfg(feature = "std")]
simple_impl!(fs::Metadata => "FileMetadata");
#[cfg(feature = "std")]
simple_impl!(fs::OpenOptions => "FileOpenOptions");
#[cfg(feature = "std")]
simple_impl!(fs::Permissions => "FilePermissions");
#[cfg(feature = "std")]
simple_impl!(fs::ReadDir => "ReadDir");

// ==== {std,core}::future ====

// ---- structs ----

simple_container_impl!(impl<T> future::Pending<T> => "Pending");
#[cfg(feature = "rust-1-64-0")]
simple_container_impl!(impl<T> future::PollFn<T> => "PollFn");
simple_container_impl!(impl<T> future::Ready<T> => "Ready");

// ---- traits ----

impl<Output> Named for dyn future::Future<Output = Output>
where
    Output: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "dyn Future<Output = {}>", Output::NAME)
    }
}

#[cfg(feature = "rust-1-64-0")]
impl<Output, IntoFuture: future::Future<Output = Output>> Named
    for dyn future::IntoFuture<Output = Output, IntoFuture = IntoFuture>
where
    Output: Named,
    IntoFuture: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "dyn IntoFuture<Output = {}, IntoFuture = {}>",
            Output::NAME,
            IntoFuture::NAME
        )
    }
}

// ==== {std,core}::hash ====

// ---- structs ----

simple_container_impl!(impl<H> hash::BuildHasherDefault<H> => "BuildHasherDefault");

// ---- traits ----

impl<H: hash::Hasher> Named for dyn hash::BuildHasher<Hasher = H>
where
    H: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "dyn BuildHasher<Hasher = {}>", H::NAME)
    }
}

simple_trait_impl!(dyn hash::Hasher => "Hasher");

// ==== std::io ====

// ---- structs ----

#[cfg(feature = "std")]
simple_container_impl!(impl<R> io::BufReader<R> => "BufReader");

#[cfg(feature = "std")]
impl<R: io::Write> Named for io::BufWriter<R>
where
    R: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, concat!("BufWriter", "<{}>"), R::NAME)
    }
}

#[cfg(feature = "std")]
simple_container_impl!(impl<R> io::Bytes<R> => "Bytes");

#[cfg(feature = "std")]
simple_map_impl!(impl<T, U> io::Chain<T, U> => "Chain");

#[cfg(feature = "std")]
simple_container_impl!(impl<R> io::Cursor<R> => "Cursor");
#[cfg(feature = "std")]
simple_impl!(io::Empty => "Empty");
#[cfg(feature = "std")]
simple_impl!(io::Error => "IoError");
#[cfg(feature = "std")]
simple_container_impl!(impl<W> io::IntoInnerError<W> => "IntoInnerError");
#[cfg(feature = "std")]
simple_impl!(io::IoSlice<'_> => "IoSlice");
#[cfg(feature = "std")]
simple_impl!(io::IoSliceMut<'_> => "IoSliceMut");

#[cfg(feature = "std")]
impl<W: io::Write> Named for io::LineWriter<W>
where
    W: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LineWriter<{}>", W::NAME)
    }
}

#[cfg(feature = "std")]
simple_container_impl!(impl<B> io::Lines<B> => "Lines");
#[cfg(feature = "std")]
simple_impl!(io::Repeat => "Repeat");
#[cfg(feature = "std")]
simple_impl!(io::Sink => "Sink");
#[cfg(feature = "std")]
simple_container_impl!(impl<B> io::Split<B> => "Split");
#[cfg(feature = "std")]
simple_impl!(io::Stderr => "Stderr");
#[cfg(feature = "std")]
simple_impl!(io::StderrLock<'_> => "StderrLock");
#[cfg(feature = "std")]
simple_impl!(io::Stdin => "Stdin");
#[cfg(feature = "std")]
simple_impl!(io::StdinLock<'_> => "StdinLock");
#[cfg(feature = "std")]
simple_impl!(io::Stdout => "Stdout");
#[cfg(feature = "std")]
simple_impl!(io::StdoutLock<'_> => "StdoutLock");
#[cfg(feature = "std")]
simple_container_impl!(impl<T> io::Take<T> => "Take");
#[cfg(all(feature = "std", feature = "rust-1-56-0"))]
simple_impl!(io::WriterPanicked => "WriterPanicked");

// ---- enums ----

#[cfg(feature = "std")]
simple_impl!(io::ErrorKind => "IoErrorKind");
#[cfg(feature = "std")]
simple_impl!(io::SeekFrom => "SeekFrom");

// ---- traits ----

#[cfg(feature = "std")]
simple_trait_impl!(dyn io::BufRead => "BufRead");
#[cfg(feature = "std")]
simple_trait_impl!(dyn io::IsTerminal => "IsTerminal");
#[cfg(feature = "std")]
simple_trait_impl!(dyn io::Read => "Read");
#[cfg(feature = "std")]
simple_trait_impl!(dyn io::Seek => "Seek");
#[cfg(feature = "std")]
simple_trait_impl!(dyn io::Write => "Write");

// ==== {std,core}::iter ====

simple_map_impl!(impl<A, B> iter::Chain<A, B> => "Chain");
simple_container_impl!(impl<I> iter::Cloned<I> => "Cloned");
simple_container_impl!(impl<I> iter::Copied<I> => "Copied");
simple_container_impl!(impl<I> iter::Cycle<I> => "Cycle");
simple_container_impl!(impl<T> iter::Empty<T> => "Empty");
simple_container_impl!(impl<I> iter::Enumerate<I> => "Enumerate");
simple_map_impl!(impl<I, P> iter::Filter<I, P> => "Filter");
simple_map_impl!(impl<I, P> iter::FilterMap<I, P> => "FilterMap");

impl<I, U: IntoIterator, P> Named for iter::FlatMap<I, U, P>
where
    I: Named,
    U: Named,
    P: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FilterMap<{}, {}, {}>", I::NAME, U::NAME, P::NAME)
    }
}

impl<Item: Iterator, I: Iterator<Item = Item>> Named for iter::Flatten<I>
where
    I: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Flatten<{}>", I::NAME)
    }
}

simple_container_impl!(impl<F> iter::FromFn<F> => "iter::FromFn");
simple_container_impl!(impl<I> iter::Fuse<I> => "iter::Fuse");

impl<I, F> Named for iter::Inspect<I, F>
where
    I: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Inspect<{}>", I::NAME)
    }
}

impl<I, F> Named for iter::Map<I, F>
where
    I: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Map<{}>", I::NAME)
    }
}

#[cfg(feature = "rust-1-57-0")]
impl<I, F> Named for iter::MapWhile<I, F>
where
    I: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MapWhile<{}>", I::NAME)
    }
}

simple_container_impl!(impl<T> iter::Once<T> => "Once");
simple_container_impl!(impl<T> iter::OnceWith<T> => "OnceWith");
simple_container_impl!(impl<I: Iterator> iter::Peekable<I> => "Peekable");
simple_container_impl!(impl<A> iter::Repeat<A> => "Repeat");

impl<F> Named for iter::RepeatWith<F> {
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RepeatWith")
    }
}

simple_container_impl!(impl<T> iter::Rev<T> => "Rev");

impl<I, St, F> Named for iter::Scan<I, St, F>
where
    I: Named,
    St: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Scan<{}, {}>", I::NAME, St::NAME)
    }
}

simple_container_impl!(impl<I> iter::Skip<I> => "Skip");

impl<I, P> Named for iter::SkipWhile<I, P>
where
    I: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SkipWhile<{}>", I::NAME)
    }
}

simple_container_impl!(impl<I> iter::StepBy<I> => "StepBy");

impl<T, F> Named for iter::Successors<T, F>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Successors<{}>", T::NAME)
    }
}

simple_container_impl!(impl<I> iter::Take<I> => "Take");

impl<I, P> Named for iter::TakeWhile<I, P>
where
    I: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TakeWhile<{}>", I::NAME)
    }
}

simple_map_impl!(impl<A, B> iter::Zip<A, B> => "Zip");

// ---- traits ----

impl<Item> Named for dyn iter::DoubleEndedIterator<Item = Item>
where
    Item: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "dyn DoubleEndedIterator<Item = {}>", Item::NAME)
    }
}

impl<Item> Named for dyn iter::ExactSizeIterator<Item = Item>
where
    Item: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "dyn ExactSizeIterator<Item = {}>", Item::NAME)
    }
}

impl<Item> Named for dyn iter::FusedIterator<Item = Item>
where
    Item: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FusedIterator<Item = {}>", Item::NAME)
    }
}

impl<Item, IntoIter: Iterator<Item = Item>> Named
    for dyn iter::IntoIterator<Item = Item, IntoIter = IntoIter>
where
    Item: Named,
    IntoIter: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "dyn IntoIterator<Item = {}, IntoIter = {}>",
            Item::NAME,
            IntoIter::NAME
        )
    }
}

impl<Item> Named for dyn iter::Iterator<Item = Item>
where
    Item: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Iterator<Item = {}>", Item::NAME)
    }
}

// ==== {std,core}::marker

// ---- structs ----

deref_impl!(impl<T> Named for marker::PhantomData<T>);
simple_impl!(marker::PhantomPinned => "PhantomPinned");

// ---- traits ----

simple_trait_impl!(dyn marker::Send => "Send");
simple_trait_impl!(dyn marker::Sync => "Sync");
simple_trait_impl!(dyn marker::Unpin => "Unpin");

// ==== {std,core}::mem

// ---- structs ----

simple_container_impl!(impl<T> mem::Discriminant<T> => "Discriminant");

impl<T: ?Sized> Named for mem::ManuallyDrop<T>
where
    T: Named,
{
    const NAME: Name = Name(T::format_name);

    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::format_name(f)
    }
}

// ==== std::net ====

// ---- structs ----

#[cfg(feature = "std")]
simple_impl!(net::AddrParseError => "AddrParseError");
#[cfg(feature = "std")]
simple_impl!(net::Incoming<'_> => "IncomingConnection");
#[cfg(feature = "std")]
simple_impl!(net::Ipv4Addr => "Ipv4Addr");
#[cfg(feature = "std")]
simple_impl!(net::Ipv6Addr => "Ipv6Addr");
#[cfg(feature = "std")]
simple_impl!(net::SocketAddrV4 => "SocketAddrV4");
#[cfg(feature = "std")]
simple_impl!(net::SocketAddrV6 => "SocketAddrV6");
#[cfg(feature = "std")]
simple_impl!(net::TcpListener => "TcpListener");
#[cfg(feature = "std")]
simple_impl!(net::TcpStream => "TcpStream");
#[cfg(feature = "std")]
simple_impl!(net::UdpSocket => "UdpSocket");

// ---- enums ----

#[cfg(feature = "std")]
simple_impl!(net::IpAddr => "IpAddr");
#[cfg(feature = "std")]
simple_impl!(net::Shutdown => "ShutdownConnectionDirection");
#[cfg(feature = "std")]
simple_impl!(net::SocketAddr => "SocketAddr");

// ---- traits ----

#[cfg(feature = "std")]
impl<Item, Iter: Iterator<Item = Item>> Named for dyn net::ToSocketAddrs<Iter = Iter>
where
    Iter: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "dyn ToSocketAddrs<Iter = {}>", Iter::NAME)
    }
}

// ==== {std,core}::num ====

// ---- structs ----

simple_impl!(num::NonZeroI8 => "i8!=0");
simple_impl!(num::NonZeroI16 => "i16!=0");
simple_impl!(num::NonZeroI32 => "i32!=0");
simple_impl!(num::NonZeroI64 => "i64!=0");
simple_impl!(num::NonZeroI128 => "i128!=0");
simple_impl!(num::NonZeroIsize => "isize!=0");
simple_impl!(num::NonZeroU8 => "u8!=0");
simple_impl!(num::NonZeroU16 => "u16!=0");
simple_impl!(num::NonZeroU32 => "u32!=0");
simple_impl!(num::NonZeroU64 => "u64!=0");
simple_impl!(num::NonZeroU128 => "u128!=0");
simple_impl!(num::NonZeroUsize => "usize!=0");
simple_impl!(num::ParseFloatError => "ParseFloatError");
simple_impl!(num::ParseIntError => "ParseIntError");
simple_impl!(num::TryFromIntError => "TryFromIntError");
simple_container_impl!(impl<T> num::Wrapping<T> => "Wrapping");

// ---- enums ----

simple_impl!(num::FpCategory => "FloatingPointCategory");
simple_impl!(num::IntErrorKind => "IntErrorKind");

// ==== {std,core}::ops ====

// ---- structs ----

impl<Idx> Named for ops::Range<Idx>
where
    Idx: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{0}..{0}", Idx::NAME)
    }
}

impl<Idx> Named for ops::RangeFrom<Idx>
where
    Idx: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..", Idx::NAME)
    }
}

simple_impl!(ops::RangeFull => "..");

impl<Idx> Named for ops::RangeInclusive<Idx>
where
    Idx: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{0}..={0}", Idx::NAME)
    }
}

impl<Idx> Named for ops::RangeTo<Idx>
where
    Idx: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "..{}", Idx::NAME)
    }
}

impl<Idx> Named for ops::RangeToInclusive<Idx>
where
    Idx: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "..={}", Idx::NAME)
    }
}

// ---- enums ----

simple_container_impl!(impl<T> ops::Bound<T> => "Bound");

#[cfg(feature = "rust-1-55-0")]
impl<B, C> Named for ops::ControlFlow<B, C>
where
    B: Named,
    C: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ControlFlow<{}, {}>", B::NAME, C::NAME)
    }
}

// ---- traits ----

simple_op_trait_impl!(dyn ops::Add<Rhs, Output = Output> = dyn ops::AddAssign<Rhs> => "Add", "+");
simple_op_trait_impl!(dyn ops::BitAnd<Rhs, Output = Output> = dyn ops::BitAndAssign<Rhs> => "BitAnd", "&");
simple_op_trait_impl!(dyn ops::BitOr<Rhs, Output = Output> = dyn ops::BitOrAssign<Rhs> => "BitOr", "|");
simple_op_trait_impl!(dyn ops::BitXor<Rhs, Output = Output> = dyn ops::BitXorAssign<Rhs> => "BitXor", "^");

impl<Target: ?Sized> Named for dyn ops::Deref<Target = Target>
where
    Target: Named,
{
    const NAME: Name = Name(Target::format_name);

    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Target::format_name(f)
    }
}

impl<Target: ?Sized> Named for dyn ops::DerefMut<Target = Target>
where
    Target: Named,
{
    const NAME: Name = Name(Target::format_name);

    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Target::format_name(f)
    }
}

simple_op_trait_impl!(dyn ops::Div<Rhs, Output = Output> = dyn ops::DivAssign<Rhs> => "Div", "/");

#[allow(dyn_drop)]
impl Named for dyn ops::Drop {
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "dyn Drop")
    }
}

impl<Idx, Output> Named for dyn ops::Index<Idx, Output = Output>
where
    Idx: Named,
    Output: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "dyn Index[{}] = {}", Idx::NAME, Output::NAME)
    }
}

impl<Idx, Output> Named for dyn ops::IndexMut<Idx, Output = Output>
where
    Idx: Named,
    Output: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "dyn Index[{}] = {}", Idx::NAME, Output::NAME)
    }
}

simple_op_trait_impl!(dyn ops::Mul<Rhs, Output = Output> = dyn ops::MulAssign<Rhs> => "Mul", "*");

impl<Output> Named for dyn ops::Neg<Output = Output>
where
    Output: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "-dyn Neg = {}", Output::NAME)
    }
}

impl<Output> Named for dyn ops::Not<Output = Output>
where
    Output: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "!dyn Neg = {}", Output::NAME)
    }
}

simple_op_trait_impl!(dyn ops::Rem<Rhs, Output = Output> = dyn ops::RemAssign<Rhs> => "Rem", "%");
simple_op_trait_impl!(dyn ops::Shl<Rhs, Output = Output> = dyn ops::ShlAssign<Rhs> => "Shl", "<<");
simple_op_trait_impl!(dyn ops::Shr<Rhs, Output = Output> = dyn ops::ShrAssign<Rhs> => "Shr", ">>");
simple_op_trait_impl!(dyn ops::Sub<Rhs, Output = Output> = dyn ops::SubAssign<Rhs> => "Sub", "-");

// ==== {std,core}::options ====

// ---- structs ----

simple_container_impl!(impl<A> option::IntoIter<A> => "option::IntoIter");
simple_container_impl!(impl<A> option::Iter<'_, A> => "option::Iter");
simple_container_impl!(impl<A> option::IterMut<'_, A> => "option::IterMut");

// ---- enums ----

simple_container_impl!(impl<T> option::Option<T> => "Option");

// ==== std::os ====

// ---- structs ----

#[cfg(all(feeature = "std", feature = "rust-1-66-0", any(unix, target_os = "wasi")))]
simple_impl!(os::fd::BorrowedFd<'_> => "BorrowedFd");
#[cfg(all(feature = "std", feature = "rust-1-66-0", any(unix, target_os = "wasi")))]
simple_impl!(os::fd::OwnedFd => "OwnedFd");

#[cfg(all(feature = "std", unix))]
simple_impl!(os::unix::net::Incoming<'_> => "ConnectionIncoming");
#[cfg(all(feature = "std", unix))]
simple_impl!(os::unix::net::SocketAddr => "SocketAddr");
#[cfg(all(feature = "std", unix))]
simple_impl!(os::unix::net::UnixDatagram => "Datagram");
#[cfg(all(feature = "std", unix))]
simple_impl!(os::unix::net::UnixListener => "Listener");
#[cfg(all(feature = "std", unix))]
simple_impl!(os::unix::net::UnixStream => "Stream");

#[cfg(all(feature = "std", windows))]
simple_impl!(os::windows::ffi::EncodeWide<'_> => "EncodeWide");

#[cfg(all(feature = "std", windows, feature = "rust-1-63-0"))]
simple_impl!(os::windows::io::BorrowedHandle<'_> => "BorrowedHandle");
#[cfg(all(feature = "std", windows, feature = "rust-1-63-0"))]
simple_impl!(os::windows::io::BorrowedSocket<'_> => "BorrowedSocket");
#[cfg(all(feature = "std", windows, feature = "rust-1-63-0"))]
simple_impl!(os::windows::io::HandleOrInvalid => "HandleOrInvalid");
#[cfg(all(feature = "std", windows, feature = "rust-1-63-0"))]
simple_impl!(os::windows::io::HandleOrNull => "HandleOrNull");
#[cfg(all(feature = "std", windows, feature = "rust-1-63-0"))]
simple_impl!(os::windows::io::InvalidHandleError => "InvalidHandleError");
#[cfg(all(feature = "std", windows, feature = "rust-1-63-0"))]
simple_impl!(os::windows::io::NullHandleError => "NullHandleError");
#[cfg(all(feature = "std", windows, feature = "rust-1-63-0"))]
simple_impl!(os::windows::io::OwnedHandle => "OwnedHandle");
#[cfg(all(feature = "std", windows, feature = "rust-1-63-0"))]
simple_impl!(os::windows::io::OwnedSocket => "OwnedSocket");

// ---- traits ----

#[cfg(all(feature = "std", any(unix, target_os = "wasi")))]
simple_trait_impl!(dyn os::fd::AsFd => "AsFd");
#[cfg(all(feature = "std", any(unix, target_os = "wasi")))]
simple_trait_impl!(dyn os::fd::AsRawFd => "AsRawFd");
#[cfg(all(feature = "std", any(unix, target_os = "wasi")))]
simple_trait_impl!(dyn os::fd::IntoRawFd => "IntoRawFd");

#[cfg(all(feature = "std", target_os = "linux"))]
simple_trait_impl!(dyn os::linux::fs::MetadataExt => "FileMetadata");

#[cfg(all(feature = "std", unix))]
simple_trait_impl!(dyn os::unix::fs::DirEntryExt => "DirEntry");
#[cfg(all(feature = "std", unix))]
simple_trait_impl!(dyn os::unix::fs::FileExt => "File");
#[cfg(all(feature = "std", unix))]
simple_trait_impl!(dyn os::unix::fs::FileTypeExt => "FileType");
#[cfg(all(feature = "std", unix))]
simple_trait_impl!(dyn os::unix::fs::MetadataExt => "FileMetadata");

#[cfg(all(feature = "std", unix))]
simple_trait_impl!(dyn os::unix::thread::JoinHandleExt => "JoinHandle");

#[cfg(all(feature = "std", windows))]
simple_trait_impl!(dyn os::windows::ffi::OsStrExt => "OsStr");

#[cfg(all(feature = "std", windows))]
simple_trait_impl!(dyn os::windows::fs::FileExt => "File");
#[cfg(all(feature = "std", windows, feature = "rust-1-64-0"))]
simple_trait_impl!(dyn os::windows::fs::FileTypeExt => "FileType");
#[cfg(all(feature = "std", windows))]
simple_trait_impl!(dyn os::windows::fs::MetadataExt => "FileMetadata");

#[cfg(all(feature = "std", windows, feature = "rust-1-63-0"))]
simple_trait_impl!(dyn os::windows::io::AsHandle => "AsHandle");
#[cfg(all(feature = "std", windows))]
simple_trait_impl!(dyn os::windows::io::AsRawHandle => "AsRawHandle");
#[cfg(all(feature = "std", windows))]
simple_trait_impl!(dyn os::windows::io::AsRawSocket => "AsRawSocket");
#[cfg(all(feature = "std", windows, feature = "rust-1-63-0"))]
simple_trait_impl!(dyn os::windows::io::AsSocket => "AsSocket");
#[cfg(all(feature = "std", windows))]
simple_trait_impl!(dyn os::windows::io::IntoRawHandle => "IntoRawHandle");
#[cfg(all(feature = "std", windows))]
simple_trait_impl!(dyn os::windows::io::IntoRawSocket => "IntoRawSocket");

// ==== {std,core}::panic ====

// ---- structs ----

deref_impl!(impl<T> Named for panic::AssertUnwindSafe<T>);
simple_impl!(panic::Location<'_> => "PanicLocation");
simple_impl!(panic::PanicInfo<'_> => "PanicInfo");

// ---- traits ----

simple_trait_impl!(dyn panic::RefUnwindSafe => "RefUnwindSafe");
simple_trait_impl!(dyn panic::UnwindSafe => "UnwindSafe");

// ==== std::path ====

// ---- structs ----

#[cfg(feature = "std")]
simple_impl!(path::Ancestors<'_> => "PathAncestors");
#[cfg(feature = "std")]
simple_impl!(path::Components<'_> => "PathComponents");
#[cfg(feature = "std")]
simple_impl!(path::Display<'_> => "DisplayPath");
#[cfg(feature = "std")]
simple_impl!(path::Iter<'_> => "Iter");
#[cfg(feature = "std")]
simple_impl!(path::Path => "Path");
#[cfg(feature = "std")]
simple_impl!(path::PathBuf => "PathBuf");
#[cfg(feature = "std")]
simple_impl!(path::PrefixComponent<'_> => "PathPrefixComponent");
#[cfg(feature = "std")]
simple_impl!(path::StripPrefixError => "StripPrefixError");

// ---- enums ----

#[cfg(feature = "std")]
simple_impl!(path::Component<'_> => "PathComponent");
#[cfg(feature = "std")]
simple_impl!(path::Prefix<'_> => "PathPrefix");

// ==== {std,core}::pin ====

// ---- structs ----

deref_impl!(impl<T> Named for pin::Pin<T>);

// ==== std::process ====

// ---- structs ----

#[cfg(feature = "std")]
simple_impl!(process::Child => "ProcessChild");
#[cfg(feature = "std")]
simple_impl!(process::ChildStderr => "ChildStderr");
#[cfg(feature = "std")]
simple_impl!(process::ChildStdin => "ChildStdin");
#[cfg(feature = "std")]
simple_impl!(process::ChildStdout => "ChildStdout");
#[cfg(feature = "std")]
simple_impl!(process::Command => "Command");
#[cfg(all(feature = "std", feature = "rust-1-57-0"))]
simple_impl!(process::CommandArgs<'_> => "CommandArgs");
#[cfg(all(feature = "std", feature = "rust-1-57-0"))]
simple_impl!(process::CommandEnvs<'_> => "CommandEnvs");
#[cfg(all(feature = "std", feature = "rust-1-61-0"))]
simple_impl!(process::ExitCode => "ExitCode");
#[cfg(feature = "std")]
simple_impl!(process::ExitStatus => "ExitStatus");
#[cfg(feature = "std")]
simple_impl!(process::Output => "ProcessOutput");
#[cfg(feature = "std")]
simple_impl!(process::Stdio => "Stdio");

// --- traits ----

#[cfg(feature = "std")]
simple_trait_impl!(dyn process::Termination => "Termination");

// ==== {std,core}::ptr ====

// ---- structs ----

deref_impl!(impl<T> Named for ptr::NonNull<T>);

// ==== {std,alloc}::rc ====

// ---- stucts ----

#[cfg(any(feature = "std", feature = "alloc"))]
impl<T: ?Sized> Named for rc::Rc<T>
where
    T: Named,
{
    const NAME: Name = Name(T::format_name);

    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::format_name(f)
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
impl<T: ?Sized> Named for rc::Weak<T>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RcWeak<{}>", T::NAME)
    }
}

// ==== {std,core}::result ====

// ---- structs ----

simple_container_impl!(impl<T> result::IntoIter<T> => "IntoIter");
simple_container_impl!(impl<T> result::Iter<'_, T> => "Iter");
simple_container_impl!(impl<T> result::IterMut<'_, T> => "IterMut");

// ---- enums ----

simple_map_impl!(impl<T, E> result::Result<T, E> => "Result");

// ==== {std,alloc,core}::slice ====

// ---- stucts ----

simple_container_impl!(impl<T> slice::Chunks<'_, T> => "Chunks");
simple_container_impl!(impl<T> slice::ChunksExact<'_, T> => "ChunksExact");
simple_container_impl!(impl<T> slice::ChunksExactMut<'_, T> => "ChunksExactMut");
simple_container_impl!(impl<T> slice::ChunksMut<'_, T> => "ChunksMut");
#[cfg(feature = "rust-1-60-0")]
simple_impl!(slice::EscapeAscii<'_> => "EscapeAscii");
simple_container_impl!(impl<T> slice::Iter<'_, T> => "Iter");
simple_container_impl!(impl<T> slice::IterMut<'_, T> => "IterMut");
simple_container_impl!(impl<T> slice::RChunks<'_, T> => "RChunks");
simple_container_impl!(impl<T> slice::RChunksExact<'_, T> => "RChunksExact");
simple_container_impl!(impl<T> slice::RChunksExactMut<'_, T> => "RChunksExactMut");
simple_container_impl!(impl<T> slice::RChunksMut<'_, T> => "RChunksMut");

impl<T, P: FnMut(&T) -> bool> Named for slice::RSplit<'_, T, P>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RSplit<{}>", T::NAME)
    }
}

impl<T, P: FnMut(&T) -> bool> Named for slice::RSplitMut<'_, T, P>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RSplitMut<{}>", T::NAME)
    }
}

impl<T, P: FnMut(&T) -> bool> Named for slice::RSplitN<'_, T, P>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RSplitN<{}>", T::NAME)
    }
}

impl<T, P: FnMut(&T) -> bool> Named for slice::RSplitNMut<'_, T, P>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RSplitNMut<{}>", T::NAME)
    }
}

impl<T, P: FnMut(&T) -> bool> Named for slice::Split<'_, T, P>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Split<{}>", T::NAME)
    }
}

impl<T, P: FnMut(&T) -> bool> Named for slice::SplitInclusive<'_, T, P>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SplitInclusive<{}>", T::NAME)
    }
}

impl<T, P: FnMut(&T) -> bool> Named for slice::SplitInclusiveMut<'_, T, P>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SplitInclusiveMut<{}>", T::NAME)
    }
}

impl<T, P: FnMut(&T) -> bool> Named for slice::SplitMut<'_, T, P>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SplitMut<{}>", T::NAME)
    }
}

impl<T, P: FnMut(&T) -> bool> Named for slice::SplitN<'_, T, P>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SplitN<{}>", T::NAME)
    }
}

impl<T, P: FnMut(&T) -> bool> Named for slice::SplitNMut<'_, T, P>
where
    T: Named,
{
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SplitNMut<{}>", T::NAME)
    }
}

simple_container_impl!(impl<T> slice::Windows<'_, T> => "Windows");

// ---- traits ----

impl<T: ?Sized, Output: ?Sized> Named for dyn slice::SliceIndex<T, Output = Output> where T: Named, Output: Named {
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}[dyn SliceIndex] = {}", T::NAME, Output::NAME)
    }
}

// ==== {std,alloc,core}::str ====

// ---- structs ----

simple_impl!(str::Bytes<'_> => "StrBytes");
simple_impl!(str::CharIndices<'_> => "CharIndices");
simple_impl!(str::Chars<'_> => "Chars");
simple_impl!(str::EncodeUtf16<'_> => "EncodeUtf16");
simple_impl!(str::EscapeDebug<'_> => "EscapeDebug");
simple_impl!(str::EscapeDefault<'_> => "EscapeDefault");
simple_impl!(str::EscapeUnicode<'_> => "EscapeUnicode");
simple_impl!(str::Lines<'_> => "StrLines");
simple_impl!(str::ParseBoolError => "ParseBoolError");
simple_impl!(str::SplitAsciiWhitespace<'_> => "SplitAsciiWhiteSpace");
simple_impl!(str::SplitWhitespace<'_> => "SplitWhiteSpace");
simple_impl!(str::Utf8Error => "Utf8Error");

// ==== {std,alloc}::string ====

// ---- structs ----

#[cfg(any(feature = "std", feature = "alloc"))]
simple_impl!(string::Drain<'_> => "Drain");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_impl!(string::FromUtf8Error => "FromUtf8Error");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_impl!(string::FromUtf16Error => "FromUtf16Error");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_impl!(string::String => "String");

// ---- traits ----

#[cfg(any(feature = "std", feature = "alloc"))]
simple_trait_impl!(dyn string::ToString => "ToString");

// ==== {std,alloc,core}::sync ====

// ---- structs ----

simple_impl!(sync::atomic::AtomicBool => "bool");
simple_impl!(sync::atomic::AtomicI8 => "i8");
simple_impl!(sync::atomic::AtomicI16 => "i16");
simple_impl!(sync::atomic::AtomicI32 => "i32");
simple_impl!(sync::atomic::AtomicI64 => "i64");
simple_impl!(sync::atomic::AtomicIsize => "isize");
deref_impl!(impl<T> Named for sync::atomic::AtomicPtr<T>);
simple_impl!(sync::atomic::AtomicU8 => "u8");
simple_impl!(sync::atomic::AtomicU16 => "u16");
simple_impl!(sync::atomic::AtomicU32 => "u32");
simple_impl!(sync::atomic::AtomicU64 => "u64");
simple_impl!(sync::atomic::AtomicUsize => "usize");

#[cfg(feature = "std")]
simple_container_impl!(impl<T> sync::mpsc::IntoIter<T> => "IntoIter");
#[cfg(feature = "std")]
simple_container_impl!(impl<T> sync::mpsc::Iter<'_, T> => "Iter");
#[cfg(feature = "std")]
simple_container_impl!(impl<T> sync::mpsc::Receiver<T> => "Receiver");
#[cfg(feature = "std")]
simple_impl!(sync::mpsc::RecvError => "ReceiveError");
#[cfg(feature = "std")]
simple_container_impl!(impl<T> sync::mpsc::SendError<T> => "SendError");
#[cfg(feature = "std")]
simple_container_impl!(impl<T> sync::mpsc::Sender<T> => "Sender");
#[cfg(feature = "std")]
simple_container_impl!(impl<T> sync::mpsc::SyncSender<T> => "SyncSender");
#[cfg(feature = "std")]
simple_container_impl!(impl<T> sync::mpsc::TryIter<'_, T> => "TryIter");

#[cfg(any(feature = "std", feature = "alloc"))]
impl<T: ?Sized> Named for sync::Arc<T> where T: Named {
    const NAME: Name = Name(T::format_name);

    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::format_name(f)
    }
}

#[cfg(feature = "std")]
simple_impl!(sync::Barrier => "Barrier");
#[cfg(feature = "std")]
simple_impl!(sync::BarrierWaitResult => "BarrierWaitResult");
#[cfg(feature = "std")]
simple_impl!(sync::Condvar => "Condvar");
#[cfg(feature = "std")]
deref_impl!(impl<T: ?Sized> Named for sync::Mutex<T>);

#[cfg(feature = "std")]
impl<T: ?Sized> Named for sync::MutexGuard<'_, T> where T: Named {
    const NAME: Name = Name(T::format_name);

    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::format_name(f)
    }
}

#[cfg(feature = "std")]
simple_impl!(sync::Once => "Once");
#[cfg(all(feature = "std", feature = "rust-1-70-0"))]
deref_impl!(impl<T> Named for sync::OnceLock<T>);
#[cfg(feature = "std")]
simple_impl!(sync::OnceState => "OnceState");
#[cfg(feature = "std")]
simple_container_impl!(impl<T> sync::PoisonError<T> => "LockPoisonError");
#[cfg(feature = "std")]
deref_impl!(impl<T: ?Sized> Named for sync::RwLock<T>);

#[cfg(feature = "std")]
impl<T: ?Sized> Named for sync::RwLockReadGuard<'_, T> where T: Named {
    const NAME: Name = Name(T::format_name);

    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::format_name(f)
    }
}

#[cfg(feature = "std")]
impl<T: ?Sized> Named for sync::RwLockWriteGuard<'_, T> where T: Named {
    const NAME: Name = Name(T::format_name);

    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::format_name(f)
    }
}

#[cfg(feature = "std")]
simple_impl!(sync::WaitTimeoutResult => "WaitTimeoutResult");
#[cfg(any(feature = "std", feature = "alloc"))]
impl<T: ?Sized> Named for sync::Weak<T> where T: Named {
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ArcWeak<{}>", T::NAME)
    }
}

// ---- enums ----

simple_impl!(sync::atomic::Ordering => "AtomicOrdering");

#[cfg(feature = "std")]
simple_impl!(sync::mpsc::RecvTimeoutError => "ReceiveTimeoutError");
#[cfg(feature = "std")]
simple_impl!(sync::mpsc::TryRecvError => "TryReceiveError");
#[cfg(feature = "std")]
simple_container_impl!(impl<T> sync::mpsc::TrySendError<T> => "TrySendError");

#[cfg(feature = "std")]
simple_container_impl!(impl<T> sync::TryLockError<T> => "TryLockError");

// ==== {std,core}::task ====

// ---- structs ----

simple_impl!(task::Context<'_> => "TaskContext");
simple_impl!(task::RawWaker => "RawWaker");
simple_impl!(task::RawWakerVTable => "RawWakerVTable");
simple_impl!(task::Waker => "Waker");

// ---- enums ----

simple_container_impl!(impl<T> task::Poll<T> => "Poll");

// ==== std::thread ====

// ---- structs ----

#[cfg(feature = "std")]
simple_impl!(thread::AccessError => "ThreadAccessError");
#[cfg(feature = "std")]
simple_impl!(thread::Builder => "ThreadBuilder");
#[cfg(feature = "std")]
simple_container_impl!(impl<T> thread::JoinHandle<T> => "JoinHandle");

#[cfg(feature = "std")]
impl<T: 'static> Named for thread::LocalKey<T> where T: Named {
    const NAME: Name = Name(T::format_name);

    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::format_name(f)
    }
}

#[cfg(all(feature = "std", feature = "rust-1-63-0"))]
impl<'scope, 'env: 'scope> Named for thread::Scope<'scope, 'env> {
    #[inline]
    fn format_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ThreadScope")
    }
}

#[cfg(all(feature = "std", feature = "rust-1-63-0"))]
simple_container_impl!(impl<T> thread::ScopedJoinHandle<'_, T> => "ScopedJoinHandle");
#[cfg(feature = "std")]
simple_impl!(thread::Thread => "Thread");
#[cfg(feature = "std")]
simple_impl!(thread::ThreadId => "ThreadId");

// ==== std::time ====

// ---- structs ----

simple_impl!(time::Duration => "Duration");
#[cfg(feature = "std")]
simple_impl!(time::Instant => "Instant");
#[cfg(feature = "std")]
simple_impl!(time::SystemTime => "SystemTime");
#[cfg(feature = "std")]
simple_impl!(time::SystemTimeError => "SystemTimeError");
simple_impl!(time::TryFromFloatSecsError => "TryFromFloatSecsError");

// ==== {std,alloc}::vec ====

// ---- structs ----

#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> vec::Drain<'_, T> => "Drain");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> vec::IntoIter<T> => "IntoIter");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<I: Iterator> vec::Splice<'_, I> => "Drain");
#[cfg(any(feature = "std", feature = "alloc"))]
simple_container_impl!(impl<T> vec::Vec<T> => "Vec");
