# named-types-rs

Like Display or Debug but for type names.

This crate provides `Named`, a trait that provides a `core::fmt::Display`able way to get a types Name.
It is similar to `core::any::type_name` without paths, but should provide a more sensical name for
something like `std::io::Error`, which would show up as `Error` with something like [pretty-type-name](https://crates.io/crates/pretty-type-name),
whereas this crate provides the name `IoError`.

The names for std are given based on the [Duck Test](https://en.wikipedia.org/wiki/Duck_test), e.g. 
`core::slice::Iter` stays `Iter` conflicting with something like `core::option::Iter` because they behave 
like generic iterators, whereas `std::io::Error` does not behave like a generic Error but rather is a 
specific Error type for io operations.

Additionally a Named derive macro is provided for deriving the Named trait. 
This macro can be configured by attributing a derived type with #[named(...)]. 
The following options can be passed to the attribute:

 * rename = "..." to change the types name.
 * format = "..." to use a custom format string that accepts all non-ignored generic. Overrides rename = "..." parameters to format the types name.
 * ignore_all to ignore all generic parameters.
 * ignore = ... to ignore a generic parameter.
 * passthrough = ... to use the Named implementation of a generic parameter. Takes priority over other options.

To configure multiple options repeat the #[named(...)] attribute.
