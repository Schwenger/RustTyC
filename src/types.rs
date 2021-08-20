//! This mod contains everything related to types and collections of types (type tables).
//!
//! # Content
//! * [Variant] is a trait representing the variant of an abstract type that will be inferred during the type checking procedure.
//! * [Constructable]: A variant is constructable if it can be transformed into a concrete type, i.e., [Constructable::Type].
//! * [TypeTable] and [PreliminaryTypeTable] are mappings from a [TcKey] to a concrete [Constructable::Type] or [Preliminary] type.

use std::{collections::HashMap, fmt::Debug};

use crate::TcKey;

/// A variant that will be inferred during the type checking procedure.
///
/// # Requirements
/// The variant needs to follow a [lattice structure](https://en.wikipedia.org/wiki/Lattice_(order)) where the top element is the least constrained, most abstract type variant
/// possible.
/// ## Refinement
/// The top value needs to be provided by the [Variant::top()] function.  Types will be refined
/// successively using the fallible [Variant::meet()] function.  If the types are incompatible, i.e., would result in a contradictory
/// type, the meet needs to return a [Variant::Err]. Note that [Variant::meet()] needs to follow the rules of abstract meets.
/// Intuitively, these are:
/// * The result of a meet needs to be more or equally concrete than either argument.
/// * Meeting two variants returns the greatest upper bound, i.e., the type variant that is more or equally concrete to either argument _and_ there is no other, less concrete type meeting this requirement.
/// This especially entails that meeting any type `T` with an unconstrained type returns `T`.
/// The arguments of the meet functions are [Partial], i.e., the combination of a variant and the least number of children the respective type has.
/// This is of particular interest for types that are not fully resolved and thus do not have a fixed arity, yet.  An unconstained type variant could have
/// a sub-type because it will be later determined to be an "Option" or "Tuple" type.  More details in the next section.
///
/// ## Arity
/// Type can be recursive, i.e., they have a number of subtypes, their "children".
/// An integer, for example, has no children and is thus 0-ary.  An optional type on the other hand is 1-ary, tuples might have an arbitrary arity.
/// During the inference process, the arity might be undetermined:  the unconstrained type will resolve to something with an arity, but the value is not clear, yet.
/// Hence, its least arity is initially 0 and potentially increases when more information was collected.
///
/// The type checking procedure keeps track of types and their potential children.
/// For this, it requires some guarantees when it comes to the arity:
///
/// ### Arity Stability
/// The meet of two variants must not _reduce_ its arity.  For example, meeting a pair with fixed arity 2 and a triple with fixed arity 3 may not result in a variant with fixed arity 1.
/// It may, however, result in a variant with variable arity.
///
/// # Example
/// For a full example of an abstract type system, refer to the [crate documentation](../index.html) and the examples.
///
pub trait Variant: Sized + Clone + Debug + Eq {
    /// Result of a meet of two incompatible type, i.e., it represents a type contradiction.
    /// May contain information regarding why the meet failed.  The error will be wrapped into a [crate::TcErr] providing contextual information.
    type Err: Debug;

    /// Returns the unconstrained, most abstract type.
    fn top() -> Self;

    /// Attempts to meet two variants respecting their currently-determined potentially variable arity.
    /// Refer to [Variant] for the responsibilities of this function.
    /// In particular: `usize::max(lhs.least_arity, rhs.least_arity) <= result.least_arity`
    /// In the successful case, the variant and arity of the partial have to match, i.e., if the [Arity]
    /// is fixed with value `n`, then [Partial::least_arity] needs to be `n` as well.
    fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err>;

    /// Indicates whether the variant has a fixed arity.  Note that this values does not have to be constant over all instances of the variant.
    /// A tuple, for example, might have a variable arity until the inferrence reaches a point where it is determined to be a pair or a triple.
    /// The pair and triple are both represented by the same type variant and have a fixed, non-specific arity.  Before obtaining this information,
    /// the tuple has a variable arity and potentially a different variant.
    fn arity(&self) -> Arity;
}

/// TODO
pub trait ContextSensitiveVariant: Sized + Clone + Debug {
    /// Result of a meet of two incompatible type, i.e., it represents a type contradiction.
    /// May contain information regarding why the meet failed.  The error will be wrapped into a [crate::TcErr] providing contextual information.
    type Err: Debug;
    /// TODO
    type Context: Debug + Clone;

    /// Returns the unconstrained, most abstract type.
    fn top() -> Self;

    /// Attempts to meet two variants respecting their currently-determined potentially variable arity.
    /// Refer to [Variant] for the responsibilities of this function.
    /// In particular: `usize::max(lhs.least_arity, rhs.least_arity) <= result.least_arity`
    /// In the successful case, the variant and arity of the partial have to match, i.e., if the [Arity]
    /// is fixed with value `n`, then [Partial::least_arity] needs to be `n` as well.
    fn meet(lhs: Partial<Self>, rhs: Partial<Self>, ctx: &Self::Context) -> Result<Partial<Self>, Self::Err>;

    /// Indicates whether the variant has a fixed arity.  Note that this values does not have to be constant over all instances of the variant.
    /// A tuple, for example, might have a variable arity until the inferrence reaches a point where it is determined to be a pair or a triple.
    /// The pair and triple are both represented by the same type variant and have a fixed, non-specific arity.  Before obtaining this information,
    /// the tuple has a variable arity and potentially a different variant.
    fn arity(&self, ctx: &Self::Context) -> Arity;

    /// TODO
    fn equal(this: &Self, that: &Self, ctx: &Self::Context) -> bool;
}

impl<V: Variant> ContextSensitiveVariant for V {
    type Err = V::Err;

    type Context = ();

    fn top() -> Self {
        V::top()
    }

    fn meet(lhs: Partial<Self>, rhs: Partial<Self>, _ctx: &Self::Context) -> Result<Partial<Self>, Self::Err> {
        V::meet(lhs, rhs)
    }

    fn arity(&self, _ctx: &Self::Context) -> Arity {
        self.arity()
    }

    fn equal(this: &Self, that: &Self, _ctx: &Self::Context) -> bool {
        this == that
    }
}

/// Represents the arity of a [ContextSensitiveVariant].
#[derive(Debug, Clone, Copy)]
pub enum Arity {
    /// The arity is variable, i.e., it does not have a specific value.
    Variable,
    /// The arity has a fixed value.
    Fixed(usize),
}

impl Arity {
    pub(crate) fn to_opt(self) -> Option<usize> {
        match self {
            Arity::Variable => None,
            Arity::Fixed(n) => Some(n),
        }
    }
}

/// Partial is a container for a [ContextSensitiveVariant] and the least arity a particular instance of this variant currently has. Only used for [ContextSensitiveVariant::meet()].
///
/// The `least_arity` indicates how many children this instance of the variance has according to the current state of the type checker.
/// The value might increase in the future but never decrease.
#[derive(Debug, Clone)]
pub struct Partial<V: Sized> {
    /// The variant represented by this `Partial`.
    pub variant: V,
    ///The least number of children the variant will have after completing the type check.
    pub least_arity: usize,
}

/// Represents a preliminary output of the type check.  Mainly used if [Variant] does not implement [Constructable].
#[derive(Debug, Clone)]
pub struct Preliminary<V: ContextSensitiveVariant> {
    /// The type variant of the entity represented by this `Preliminary`.
    pub variant: V,
    /// The [TcKey]s of the children of this variant.
    pub children: Vec<Option<TcKey>>,
}

/// A type table containing a [Preliminary] type for each [TcKey].  Mainly used if [ContextSensitiveVariant] does not implement [Constructable].
pub type PreliminaryTypeTable<V> = HashMap<TcKey, Preliminary<V>>;
/// A type table containing the constructed type of the inferred [ContextSensitiveVariant] for each [TcKey].  Requires [ContextSensitiveVariant] to implement [Constructable].
pub type TypeTable<V> = HashMap<TcKey, <V as Constructable>::Type>;

/// A type implementing this trait can potentially be transformed into a concrete representation. This transformation can fail.
pub trait Constructable: ContextSensitiveVariant {
    /// The result type of the attempted construction.
    type Type: Clone + Debug;
    /// Attempts to transform `self` into an more concrete `Self::Type`.
    /// Returns a [ContextSensitiveVariant::Err] if the transformation fails.  This error will be wrapped into a [crate::TcErr] to enrich it with contextual information.
    fn construct(&self, children: &[Self::Type]) -> Result<Self::Type, <Self as ContextSensitiveVariant>::Err>;
}
