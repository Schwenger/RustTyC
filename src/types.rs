//! This mod contains everything related to types and collections of types (type tables).
//!
//! # Content
//! * [`Abstract`](trait.Abstract.html) is a trait representing abstract types that will
//! be inferred during the type checking procedure.
//! * Reification is the process of transforming an abstract type into a concrete one.  
//! This process can be fallible or infallible, represented by [`Reifiable`](trait.Reifiable.html),
//! [`TryReifiable`](trait.TryReifiable.html), and [`ReificationErr`](enum.ReificationErr.html).
//! * Generalization is the infallible process of transforming a concrete type into an abstract one represented by [`Generalizable`](trait.Generalizable.html)
//! * [`TypeTable`](trait.TypeTable.html) contains a mapping from a [`TcKey`](../struct.TcKey.html) to an [`Abstract`](trait.Abstract.html) or reified type.

use std::{collections::HashMap, fmt::Debug};

use crate::TcKey;

// /// An abstract type that will be inferred during the type checking procedure.
// ///
// /// This trait that needs to be implemented by all (rust-) types that represent a type in the type checking procedure.
// ///
// /// # Requirements
// /// The abstract types need to follow a [lattice structure](https://en.wikipedia.org/wiki/Lattice_(order)) where the top element is the least constrained, most abstract type
// /// possible.
// /// ## Refinement
// /// This value needs to be provided by the `Abstract::unconstrained` function.  Types will be refined
// /// successively using the fallible meet function.  If the types are incompatible, i.e., would result in a contradictory
// /// type, the meet needs to return a `Result::Err`.  Otherwise, it returns a `Result::Ok` containing the resulting type.
// /// The function needs to follow the rules for abstract meets.  Intuitively, these are:
// /// * The result of a meet needs to be more or equally concrete than either argument.
// /// * Meeting two types returns the greatest upper bound, i.e., the type that is more or equally concrete to either argument _and_ there is no other, less concrete type meeting this requirement.
// /// This especially entails that meeting any type `T` with an unconstrained type returns `T`.
// ///
// /// ## Arity
// /// Type can be recursive, i.e., they have a number of subtypes, their "children".
// /// An integer, for example, has no children and is thus 0-ary.  An optional type on the other hand is 1-ary, i.e., it has one sub-type.
// /// During the inference process, the arity might be undetermined:  the unconstrained type will resolve to something with an arity, but the value is not clear, yet.
// ///
// /// The type checking procedure keeps track of types and their potential children.
// /// For this, it requires some guarantees when it comes to the arity:
// ///
// /// ### Arity Stability
// /// * If a type has a defined arity, it may not change when turning more concrete.  Thus, abstract types with ambiguous arity must not return an arity.
// /// * A leaf type, i.e., a fully resolved non-contradictory type must provide an arity.
// /// A consequence is that the meet of two types with different, defined arity will result in an error.
// ///
// /// # Example
// /// For a full example of an abstract type system, refer to the [crate documentation](../index.html) and the examples. TODO: link!
// ///
// pub trait Abstract: Eq + Sized + Clone + Debug {
//     /// Result of a meet of two incompatible type, i.e., it represents a type contradiction.
//     /// May contain information regarding why the meet failed.
//     type Err: Debug;

//     /// Returns the unconstrained, most abstract type.
//     fn unconstrained() -> Self;

//     /// Determines whether or not `self` is the unconstrained type.
//     fn is_unconstrained(&self) -> bool {
//         self == &Self::unconstrained()
//     }

//     /// Attempts to meet two abstract types.
//     /// Refer to the documentation of [Abstract](trait.Abstract.html) for the responsibilities of this function.
//     fn meet(&self, other: &Self) -> Result<Self, Self::Err>;

//     /// Provides the arity of the `self` if the type is sufficiently resolved to determine it.
//     fn arity(&self) -> Option<usize>;

//     /// Provide access to the nth child.
//     /// # Guarantee
//     /// The arity of `self` is defined and greater or equal to `n`: `assert!(self.arity.map(|a| *a >= n).unwrap_or(false)`
//     fn nth_child(&self, n: usize) -> &Self;

//     /// Generate an instance of Self that is equivalent to `self` except that the children of the newly generated type will be
//     /// `children`.
//     /// # Guarantee
//     /// The arity of `self` is defined and corresponds to the number of element in `children`: assert!(self.arity.map(|a| a == children.collect::<Vec<Self>>().len()).unwrap_or(false))`
//     fn with_children<I>(&self, children: I) -> Self
//     where
//         I: IntoIterator<Item = Self>;
// }

#[derive(Debug, Clone)]
pub struct Partial<V: Variant> {
    pub variant: V,
    pub least_arity: usize,
}

pub trait Variant: Sized + Clone + Debug + Eq {
    // type Type: Debug + Clone; // Concrete type
    type Err: Debug;
    fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err>;
    fn fixed_arity(&self) -> bool;
    // fn try_construct(&self, children: &[Self::Type]) -> Result<Self::Type, Self::Err>;
    fn top() -> Self;
}

#[derive(Debug, Clone)]
pub struct Preliminary<V: Variant> {
    pub variant: V,
    pub children: Vec<Option<TcKey>>,
}

pub type PreliminaryTypeTable<V> = HashMap<TcKey, Preliminary<V>>;
pub type TypeTable<V> = HashMap<TcKey, <V as Constructable>::Type>;

/// A type implementing this trait can potentially be `reified` into a concrete representation.
/// This transformation can fail.  If it is infallible, refer to [`Reifiable`](trait.Reifiable.html).
pub trait Constructable: Variant {
    /// The result type of the attempted reification.
    type Type: Clone + Debug;
    /// Attempts to transform `self` into an more concrete `Self::Reified` type.
    /// Returns a [`ReificationErr`](enum.ReificationErr.html) if the transformation fails.
    fn construct(&self, children: &[Self::Type]) -> Result<Self::Type, <Self as Variant>::Err>;
}
