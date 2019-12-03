//! This create provides an interface for type checking some arbitrary structure.
//! It is based on an abstract type lattice that uses a union-find implementation (https://crates.io/crates/ena)
//! internally to successively constrain types.
//!
//! The main component is the `TypeChecker` struct, which is parametrized by a `Key` that implements the `ena::UnifyKey`
//! trait.  This trait in-turn requires an implementation of `ena::UnifyValue` and `type_checker::AbstractValue.
//! The
//!

mod constraints;
mod reification;
#[cfg(test)]
mod tests;
mod type_checker;

pub use constraints::TypeConstraint;
pub use reification::{Generalizable, Reifiable, ReificationError, TryReifiable};
pub use type_checker::{AbstractType, TypeCheckKey, TypeChecker};
