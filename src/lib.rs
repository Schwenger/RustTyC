//! This crate provides an interface to perform lattice-based type checking on arbitrary structures.
//!
//! The [`TypeChecker`](struct.TypeChecker.html) struct constitutes the main struct.  It provides functions to create new [`TcKey`](struct.TcKey.html)s.  
//! These keys represent typed entities such as terms or variables in programming languages.
//! [`TcKey`](struct.TcKey.html) provides a set of functions generating constraints such as 'the type behind key a is more concrete than the type behind key b'
//! or 'type X is an upper bound of the type behind key a'.
//!
//! The user needs to supply a type lattice by implementing the [`Abstract`](trait.Abstract.html) trait.
//!
//! Then, iterate over your data structure, e.g. your abstract syntax tree, generate keys for terms and variables, and impose constraints
//! on the keys.
//! Lastly, generate a type table mapping keys to their resolved types.  The type table itself can be [`Reifiable`](trait.Reifiable.html) if the abstract type can
//! be transformed into a concrete type.  
//!
//! # Example
//! Consider a type lattice consisting of a boolean type and an integer type, where the integer type is a variable bit length.
//! ```
//! #[derive(PartialEq, Eq, Clone, Debug)]
//! enum MyType {
//!     Integer(usize),
//!     Boolean,
//!     Unknown,
//!     Error,
//! }
//! ```
//!
//! Implement the [`Abstract`](trait.Abstract.html) type for the enum.  This requires two additional types: an error type and a variant tag.
//! The latter indicates what kind of variant a certain type has.  This is a minor inconvenience required for constructing and destructing incomplete types.
//! The tag provides information about its arity, i.e., the number of subtypes relevant for this type.  As an example consider an `Option`-like type.
//! As a monad, it has arity 1.  Scalar types have arity 0.
//! Note that non-leaf types, i.e., types that are not resolved yet such as `MyVariant::Unknown`, do not provide a tag.
//! ```
//! # #[derive(PartialEq, Eq, Clone, Debug)]
//! # enum MyType {
//! #     Integer(usize),
//! #     Boolean,
//! #     Unknown,
//! # }
//! # use rusttyc::{TcVar, TypeChecker, types::Abstract, TcErr};
//! type MyTypeErr = String;
//! impl Abstract for MyType {
//!     type Err = MyTypeErr;
//!     fn arity(&self) -> Option<usize> {
//!         match self {
//!             MyType::Integer(_) | MyType::Boolean => Some(0),
//!             MyType::Unknown => None,
//!         }
//!     }
//!     fn unconstrained() -> Self { MyType::Unknown }
//!     fn meet(&self, other: &Self) -> Result<Self, Self::Err> {
//!         match (self, other) {
//!             (MyType::Unknown, x) | (x, MyType::Unknown) => Ok(x.clone()),
//!             (MyType::Boolean, MyType::Boolean) => Ok(MyType::Boolean),
//!             (MyType::Integer(a), MyType::Integer(b)) => Ok(MyType::Integer(usize::max(*a, *b))),
//!             _ => Err(String::from("Cannot combine Boolean and Integer")),
//!         }
//!     }
//!     fn with_children<I>(&self, children: I) -> Self
//!     where
//!         I: IntoIterator<Item = Self>,
//!     {
//!         assert!(children.into_iter().collect::<Vec<Self>>().is_empty());
//!         self.clone()
//!     }
//!     fn nth_child(&self, _: usize) -> &Self {
//!         panic!("will not be called")
//!     }
//! }
//! #[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
//! struct MyVariable(u8);
//! impl TcVar for MyVariable {}
//!
//! # fn main() -> Result<(), TcErr<MyType>> {
//! let mut tc: TypeChecker<MyType, MyVariable> = TypeChecker::new();
//! // We type check `x = 0b111 ^ 0b11010`, so x needs 5 bits.
//! let t1 = tc.new_term_key();
//! // The term is an int with at least a width of 3 bits.
//! tc.impose(t1.concretizes_explicit(MyType::Integer(3)))?;
//! let t2 = tc.new_term_key();
//! // The term is an int with at least a width of 5 bits.
//! tc.impose(t2.concretizes_explicit(MyType::Integer(5)))?;
//! let tx = tc.new_term_key(); // t3 is the combination of t1 and t2, e.g. addition.
//! tc.impose(tx.is_meet_of(t1, t2))?; // Addition is the meet of both types.
//! let type_table = tc.type_check()?;
//! assert_eq!(type_table[tx], MyType::Integer(5));
//! # Ok(())
//! }
//! ```
//!
//! ## Additional Examples
//! Check the documentation of [`TcKey`](struct.TcKey.html) for all possible constraints imposable on keys and their effects.
//! Check the RustTyC examples on github for more elaborate examples.
//!     

#![deny(
    // missing_docs,
    missing_debug_implementations,
    missing_copy_implementations,
    trivial_casts,
    trivial_numeric_casts,
    unsafe_code,
    unstable_features,
    unused_import_braces,
    unused_qualifications,
    broken_intra_doc_links,
)]

pub(crate) mod constraint_graph;
mod keys;
#[cfg(test)]
mod tests;
mod type_checker;
pub mod types;

pub use keys::TcKey;
pub use type_checker::{TcErr, TcVar, TypeChecker, VarlessTypeChecker};
pub use types::{Constructable, Partial, Preliminary, PreliminaryTypeTable, TypeTable, Variant};
