//! This create provides an interface for type checking some arbitrary structure.
//! It is based on an abstract type lattice that uses a union-find implementation (https://crates.io/crates/ena)
//! internally to successively constrain types.
//!
//! The main component is the `TypeChecker` struct, which is parametrized by a `Key` that implements the `ena::UnifyKey`
//! trait.  This trait in-turn requires an implementation of `EnaValue` and `type_checker::AbstractValue`.
//! The `TypeChecker` manages a set of abstract types in a lattice-like structure and perform a union-find procedure to
//! derive the least concrete abstract type that satisfies a defined set of constraints.
//! Each abstract type is referred to with a key assigned by the `TypeChecker` (refer to
//! `TypeChecker::new_key(&mut self)`).
//!
//! # Usage
//! The `TypeChecker` requires two types: `Key` and `AbstractType`.
//! `Key` needs to implement `EnaKey`, which has an associated type `EnaKey::Value` that is the `AbstractType`.
//! Most of the time, the key is simply a `u32` in disguise.
//! The abstract type needs to implement `EnaValue` providing an abstract "meet" or "unification" function, and
//! `type_check::AbstractType`.
//! ```
//! use rusttyc::{ TypeCheckKey, TypeChecker, EnaValue, EnaKey };
//! use ena::unify::UnifyValue;
//! #[derive(Debug, PartialEq, Eq, Clone, Copy)]
//! struct Key(u32);
//! #[derive(Debug, PartialEq, Eq, Clone)]
//! enum AbstractType {
//!     Variant1,
//!     Unconstrained,
//!     /* ... */
//! }
//! impl rusttyc::AbstractType for AbstractType {
//!     fn unconstrained() -> Self {
//!         Self::Unconstrained
//!     }
//! }
//! impl EnaValue for AbstractType {
//!     type Error = ();
//!
//!     fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
//!         /* Do something meaningful. */
//!         return Ok(value1.clone())
//!     }
//! }
//! impl EnaKey for Key {
//!     type Value = AbstractType;
//!
//!     fn index(&self) -> u32 { self.0 }
//!
//!     fn from_index(u: u32) -> Self { Key(u) }
//!
//!     fn tag() -> &'static str { "key" }
//! }
//!
//! let mut tc: TypeChecker<Key> = TypeChecker::new();
//!
//! let first = tc.new_key();
//! let second = tc.new_key();
//!
//! assert!(tc.impose(second.bound_by_abstract(AbstractType::Variant1)).is_ok());
//! assert!(tc.impose(first.more_concrete_than(second)).is_ok());
//!
//! assert_eq!(tc.get_type(first), tc.get_type(second));
//! ```
//!
//! For a full example, refer to the example directory.

mod constraints;
mod reification;
#[cfg(test)]
mod tests;
mod type_checker;

pub use constraints::TypeConstraint;
pub use ena::unify::{UnifyKey as EnaKey, UnifyValue as EnaValue};
pub use reification::{Generalizable, Reifiable, ReificationError, TryReifiable};
pub use type_checker::{AbstractType, TypeCheckKey, TypeChecker};
