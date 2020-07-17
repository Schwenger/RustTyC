//! This crate provides an interface to perform lattice-based type checking on arbitrary structures structures.
//!
//! The `TypeChecker` struct constitutes the main struct.  It provides functions to create new `TcKey`s.  
//! These keys represent typed entities such as terms or variables in programming languages.
//! `TcKey` provides a set of functions generating constraints such as 'the type behind key a is more concrete than the type behind key b'
//! or 'type X is an upper bound of the type behind key a'.
//!
//! The user needs to supply a type lattice by implementing the `Abstract` trait.
//!
//! Then, iterate over your data structure, e.g. your abstract syntax tree, generate keys for terms and variables, and impose constraints
//! on the keys.
//! Lastly, generate a type table mapping keys to their resolved types.  The type table itself can be `Reifiable` if the abstract type can
//! be transformed into a concrete type.  
//!
//! # Example
//! Consider a type lattice consisting of a boolean type and an integer type, where the integer type is a variable bit length.
//! ```
//! enum MyType {
//!     Integer(usize),
//!     Boolean,
//!     Unknown,
//!     Error,
//! }
//! ```
//!
//! Implement the `Abstract` type for the enum.  This requires two additional types: an error type and a variant tag.
//! The latter indicates what kind of variant a certain type has.  This is a minor inconvenience required for constructing and destructing incomplete types.
//! The tag provides information about its arity, i.e., the number of subtypes relevant for this type.  As an example consider an `Option`-like type.
//! As a monad, it has arity 1.  Scalar types have arity 0.
//! Note that non-leaf types, i.e., types that are not resolved yet such as `MyVariant::Unknown`, do not provide a tag.
//! ```
//! #enum MyType {
//! #    Integer(usize),
//! #    Boolean,
//! #    Unknown,
//! #}
//! type MyTypeErr = String;
//! enum MyVariant { Integer, Boolean }
//! impl Abstract for MyType {
//!     type Err = MyTypeErr;
//!     type VariantTag = MyVariant;
//!     fn variant(&self) -> Option<Self::VariantTag> {
//!         match self {
//!             MyType::Integer(_) => Some(MyVariant::Integer),
//!             MyType::Boolean => Some(MyVariant::Boolean),
//!             MyType::Unknown => None,
//!         }
//!     }
//!     fn unconstrained() -> Self { MyType::Unknown }
//!     fn meet(&self, other: &Self) -> Result<Self, Self::Err> {
//!         match (self, other) {
//!             (MyType::Unknown, x) | (x, MyType::Unknown) => Ok(x),
//!             (MyType::Boolean, MyType::Boolean) => Ok(MyType::Boolean),
//!             (MyType::Integer(a), MyType::Integer(b)) => Ok(MyType::Integer(usize::max(a, b))),
//!             _ => Err(String::from("Cannot combine Boolean and Integer")),
//!         }
//!     }
//!     fn variant_arity(tag: Self::VariantTag) -> usize { 0 }
//!     fn from_tag(tag: Self::VariantTag, children: Vec<Self>) -> Self {
//!         match tag {
//!             MyVariant::Integer => MyType::Integer(0),
//!             MyVariant::Boolean => MyType::Boolean,
//!         }
//!     }
//! }
//! type Variable = u8;
//! let tc = TypeChecker::new();
//! let t1 = tc.get_term_key();
//! tc.impose(t1.more_concrete_than_explicit(MyType::Integer(3)))?; // The term is an int with at least a width of 3 bits.
//! let t2 = tc.get_term_key();
//! tc.impose(t2.more_concrete_than_explicit(MyType::Integer(5)))?; // The term is an int with at least a width of 5 bits.
//! let t3 = tc.get_term_key(); // t3 is the combination of t1 and t2, e.g. addition.
//! tc.impose(t1.is_meet_of(t1, t2))?; // Addition is the meet of both types.
//! let type_table = tc.type_check()?;
//! assert_eq!(type_table[t3], MyType::Integer(5));
//! # Ok(())
//!     

#![deny(
    missing_docs,
    missing_debug_implementations,
    missing_copy_implementations,
    trivial_casts,
    trivial_numeric_casts,
    unsafe_code,
    unstable_features,
    unused_import_braces,
    unused_qualifications,
    intra_doc_link_resolution_failure
)]

pub(crate) mod constraint_graph;
mod keys;
#[cfg(test)]
mod tests;
mod type_checker;
pub mod types;

pub use keys::TcKey;
pub use type_checker::{TcErr, TcVar, TypeChecker};
