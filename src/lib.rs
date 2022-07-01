//! This crate provides an interface to perform lattice-based type checking on arbitrary structures.
//!
//! The [TypeChecker] struct constitutes the main struct.  It provides functions to create new [TcKey]s.  
//! These keys represent typed entities such as terms or variables in programming languages.
//! [TcKey] provides a set of functions generating constraints such as 'the type behind key a is more concrete than the type behind key b'
//! or 'type X is an upper bound of the type behind key a'.
//!
//! The user needs to supply a type lattice by implementing the [Variant] or [ContextSensitiveVariant] trait.  The following documentation
//! uses both traits interchangeably whenever possible without ambiguity.
//!
//! Then, iterate over your data structure, e.g. your abstract syntax tree, generate keys for terms and variables, and impose constraints
//! on the keys.
//! Lastly, generate a type table mapping keys to their resolved types.  These can either be [Variant]s with the keys representing their children, or
//! _constructed_ types if [Variant] implements [Constructable].
//!
//! # Example
//! Consider a type lattice consisting of a boolean type and an integer type, where the integer type is a variable bit length.
//! ```
//! #[derive(PartialEq, Eq, Clone, Debug)]
//! enum MyVariant {
//!     Integer(usize),
//!     Boolean,
//!     Top,
//! }
//! ```
//!
//! Implement the [Variant] type for the enum.  This requires an additional error type, access to a [Variant::top()] element, and information whether
//! or not the variant has a fixed or variable arity, i.e., the number of subtypes relevant for this type.  As an example consider an `Option`-like type.
//! As a monad, it has arity 1.  Scalar types have arity 0, tuples of undetermined length have variable arity.
//! ```
//! # #[derive(PartialEq, Eq, Clone, Debug)]
//! # enum MyVariant {
//! #     Integer(usize),
//! #     Boolean,
//! #     Top,
//! # }
//! # use rusttyc::{TcVar, TypeChecker, Variant, TcErr, Partial, Arity};
//! type MyTypeErr = String;
//! impl Variant for MyVariant {
//!     type Err = MyTypeErr;
//!     fn arity(&self) -> Arity<String> { Arity::FixedIndexed(0) }
//!     fn top() -> Self { MyVariant::Top }
//!     fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err> {
//!         use rusttyc::types::ChildConstraint;
//! assert_eq!(lhs.children.len(), 0);
//!         assert_eq!(lhs.children.len(), 0);
//!         let variant = match (lhs.variant, rhs.variant) {
//!             (MyVariant::Top, x) | (x, MyVariant::Top) => Ok(x),
//!             (MyVariant::Boolean, MyVariant::Boolean) => Ok(MyVariant::Boolean),
//!             (MyVariant::Integer(a), MyVariant::Integer(b)) => Ok(MyVariant::Integer(usize::max(a, b))),
//!             (MyVariant::Boolean, MyVariant::Integer(_)) | (MyVariant::Integer(_), MyVariant::Boolean) => Err(String::from("Cannot combine Boolean and Integer")),
//!         }?;
//!         Ok(Partial { variant, children: ChildConstraint::Indexed(0) })
//!     }
//! }
//! #[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
//! struct MyVariable(u8);
//! impl TcVar for MyVariable {}
//!
//! # fn main() -> Result<(), TcErr<MyVariant>> {
//! let mut tc: TypeChecker<MyVariant, MyVariable> = TypeChecker::new();
//! // We type check `x = 0b111 ^ 0b11010`, so x needs 5 bits.
//! let t1 = tc.new_term_key();
//! // The first term is an int with at least a width of 3 bits.
//! tc.impose(t1.concretizes_explicit(MyVariant::Integer(3)))?;
//! let t2 = tc.new_term_key();
//! // The second term is an int with at least a width of 5 bits.
//! tc.impose(t2.concretizes_explicit(MyVariant::Integer(5)))?;
//! let tx = tc.new_term_key(); // tx is the combination of t1 and t2, e.g. xor or addition.
//! tc.impose(tx.is_meet_of(t1, t2))?; // The result is the meet of both types.
//! let type_table = tc.type_check_preliminary()?;
//! assert_eq!(type_table[&tx].variant, MyVariant::Integer(5));
//! # Ok(())
//! }
//! ```
//!
//! ## Additional Examples
//! Check the documentation of [TcKey] for all possible constraints imposable on keys and their effects.
//! Check the RustTyC examples on github for more elaborate examples.
//!     

#![deny(
    missing_debug_implementations,
    missing_copy_implementations,
    // missing_docs,
    trivial_casts,
    trivial_numeric_casts,
    unsafe_code,
    unstable_features,
    unused_import_braces,
    unused_qualifications,
    rustdoc::broken_intra_doc_links,
    unused_results
)]

pub(crate) mod constraint_graph;
mod keys;
#[cfg(test)]
mod tests;
mod type_checker;
mod type_table;
mod children;
pub mod types;

pub use keys::Key;
pub use type_checker::{TcErr, VarId, TypeChecker, VarlessTypeChecker};
pub use types::{
    ContextType, Infered, Type,
};
