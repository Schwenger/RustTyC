//! This create provides an interface for type checking some arbitrary structure.
//! It is based on an abstract type lattice that uses a union-find implementation (https://crates.io/crates/ena)
//! internally to successively constrain types.
//!
//! The main component is the `TypeChecker` struct, which is parametrized by a `Key` that implements the `ena::UnifyKey`
//! trait.  This trait in-turn requires an implementation of `ena::UnifyValue` and `type_checker::AbstractValue.
//! The
//!

mod type_checker;
mod constraints;
mod reification;
#[cfg(test)]
mod tests;

pub use type_checker::{AbstractType, TypeCheckKey, TypeChecker};
pub use constraints::TypeConstraint;
pub use reification::{ReificationError, Generalizable, TryReifiable, Reifiable};
