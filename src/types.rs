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

use std::fmt::Debug;

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
    pub(crate) variant: V,
    pub(crate) least_arity: usize,
}

pub trait Variant: Sized + Clone + Debug + Eq {
    type Type: Debug + Clone; // Concrete type
    type Err: Debug;
    fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err>;
    fn fixed_arity(&self) -> bool;
    fn try_construct(&self, children: &[Self::Type]) -> Result<Self::Type, Self::Err>;
    fn top() -> Self;
}

// /// Indicates that an abstract type could not be reified because it is too general or too restrictive.
// ///
// /// # Example
// /// 1. A numeric type cannot be reified into any concrete value because the concrete counterpart could be a natural
// /// number, integer, floating point number, .... -> `ReificationErr::TooGeneral`
// /// 2. An integer type cannot be reified into a concrete type with fixed memory layout except a default size is
// /// defined, e.g. an Int will be reified into an Int32. -> `ReificationErr::TooGeneral`
// /// 3. An unbounded integer might not have a concrete counterpart because the system requires a concrete bit size.
// /// -> `ReificationErr::Conflicting`
// ///
// /// Note the subtle difference between `ReificationErr::TooGeneral` and `ReificationErr::Conflicting`:
// ///     + In the `Conflicting` case there is no concrete counterpart
// ///     + In the `TooGeneral` case the concrete counterpart is not defined or not unique but could exist.
// #[derive(Debug, Clone)]
// pub enum ReificationErr {
//     /// Attempting to reify an abstract type with either no unique concrete counterpart or with no defined default
//     /// reification value results in this error.
//     TooGeneral(String),
//     /// Attempting to reify an abstract type for which no concrete counterpart does exist results in this error.
//     Conflicting(String),
// }

// /// A type implementing this trait can be `reified` into a concrete representation.
// /// This transformation cannot fail.  If it is fallible, refer to [`TryReifiable`](trait.TryReifiable.html).
// pub trait Reifiable {
//     /// The result type of the reification.
//     type Reified;
//     /// Transforms `self` into the more concrete `Self::Reified` type.
//     fn reify(&self) -> Self::Reified;
// }

// /// A type implementing this trait can potentially be `reified` into a concrete representation.
// /// This transformation can fail.  If it is infallible, refer to [`Reifiable`](trait.Reifiable.html).
// pub trait TryReifiable {
//     /// The result type of the attempted reification.
//     type Reified;
//     /// Attempts to transform `self` into an more concrete `Self::Reified` type.
//     /// Returns a [`ReificationErr`](enum.ReificationErr.html) if the transformation fails.
//     fn try_reify(&self) -> Result<Self::Reified, ReificationErr>;
// }

// /// A type implementing this trait can be `generalized` into an abstract representation infallibly.
// pub trait Generalizable {
//     /// The result type of the generalization.
//     type Generalized;
//     /// Generalizes the given concrete type.
//     fn generalize(&self) -> Self::Generalized;
// }

// /// A trait representing a type table.
// ///
// /// It maps [`TcKey`](../struct.TcKey.html) to `Self::Type` and allows for an automatic transformation into a hashmap.
// pub trait TypeTable: Index<TcKey> {
//     /// The (rust-) type of the (external-) type stored in this type table.
//     type Type;

//     /// Transforms itself into a hashmap.
//     fn as_hashmap(self) -> HashMap<TcKey, Self::Type>;
// }

// /// An implementation of [`TypeTable`](trait.TypeTable.html) for type implementing [`Abstract`](trait.Abstract.html).
// /// See [`ReifiedTypeTable`](struct.ReifiedTypeTable.html) for an implementation specializing on
// /// concrete types.
// ///
// /// Can automatically be generated from a `HashMap<TcKey, AbsTy>` for `AbsTy: Abstract`.
// #[derive(Debug, Clone)]
// pub struct AbstractTypeTable<AbsTy: Abstract> {
//     table: HashMap<TcKey, AbsTy>,
// }

// impl<AbsTy: Abstract> Index<TcKey> for AbstractTypeTable<AbsTy> {
//     type Output = AbsTy;
//     fn index(&self, index: TcKey) -> &Self::Output {
//         &self.table[&index]
//     }
// }

// impl<AbsTy: Abstract> From<HashMap<TcKey, AbsTy>> for AbstractTypeTable<AbsTy> {
//     fn from(map: HashMap<TcKey, AbsTy>) -> Self {
//         AbstractTypeTable { table: map }
//     }
// }

// /// An implementation of [`TypeTable`](trait.TypeTable.html) for concrete types.
// /// See [`AbstractTypeTable`](struct.AbstractTypeTable.html) for an implementation specializing on
// /// abstract types.
// ///
// /// Can automatically be generated from a `HashMap<TcKey, Concrete>`.
// #[derive(Debug, Clone)]
// pub struct ReifiedTypeTable<Concrete> {
//     table: HashMap<TcKey, Concrete>,
// }

// impl<Concrete> Index<TcKey> for ReifiedTypeTable<Concrete> {
//     type Output = Concrete;
//     fn index(&self, index: TcKey) -> &Self::Output {
//         &self.table[&index]
//     }
// }

// impl<Concrete> From<HashMap<TcKey, Concrete>> for ReifiedTypeTable<Concrete> {
//     fn from(map: HashMap<TcKey, Concrete>) -> Self {
//         ReifiedTypeTable { table: map }
//     }
// }

// impl<AbsTy: Abstract> TypeTable for AbstractTypeTable<AbsTy> {
//     type Type = AbsTy;

//     fn as_hashmap(self) -> HashMap<TcKey, Self::Type> {
//         self.table
//     }
// }

// impl<Concrete> TypeTable for ReifiedTypeTable<Concrete> {
//     type Type = Concrete;

//     fn as_hashmap(self) -> HashMap<TcKey, Self::Type> {
//         self.table
//     }
// }

// impl<AbsTy> AbstractTypeTable<AbsTy>
// where
//     AbsTy: Abstract + Reifiable,
// {
//     /// Transforms an [`AbstractTypeTable`](struct.AbstractTypeTable.html) into a [`ReifiedTypeTable`](struct.ReifiedTypeTable.html)
//     /// by reifying all abstract types.
//     pub fn reified(self) -> ReifiedTypeTable<AbsTy::Reified> {
//         ReifiedTypeTable { table: self.table.into_iter().map(|(key, ty)| (key, ty.reify())).collect() }
//     }
// }

// impl<AbsTy> AbstractTypeTable<AbsTy>
// where
//     AbsTy: Abstract + TryReifiable,
// {
//     /// Attempts to transform an [`AbstractTypeTable`](struct.AbstractTypeTable.html) into a [`ReifiedTypeTable`](struct.ReifiedTypeTable.html)
//     /// by reifying all abstract types.
//     pub fn try_reified(self) -> Result<ReifiedTypeTable<AbsTy::Reified>, ReificationErr> {
//         self.table
//             .into_iter()
//             .map(|(key, ty)| ty.try_reify().map(|re| (key, re)))
//             .collect::<Result<HashMap<TcKey, AbsTy::Reified>, ReificationErr>>()
//             .map(|table| ReifiedTypeTable { table })
//     }
// }
