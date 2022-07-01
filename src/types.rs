//! This mod contains everything related to types and collections of types (type tables).
//!
//! # Content
//! * [Variant] is a trait representing the variant of an abstract type that will be inferred during the type checking procedure.
//! * [Constructable]: A variant is constructable if it can be transformed into a concrete type, i.e., [Constructable::Type].
//! * [TypeTable] and [PreliminaryTypeTable] are mappings from a [TcKey] to a concrete [Constructable::Type] or [Preliminary] type.

use std::fmt::Debug;

use crate::children::Arity;

/// A [Variant] which requires a context for meet operations and equality checks.
///
/// See [Variant] for general information and requirements on the implementation.
/// The context will ever only be borrowed without further requirements on it, in particular,
/// it does not have to implement [Clone].
pub trait ContextType: Sized + Clone + Debug + UpperBoundedType {
    /// Result of a meet of two incompatible type, i.e., it represents a type contradiction.
    /// May contain information regarding why the meet failed.  The error will be wrapped into a [crate::TcErr] providing contextual information.
    type Err: Debug;

    /// Represents the meet- and equality context.
    type Context: Debug;

    /// Attempts to meet two variants respecting their currently-determined potentially variable arity.
    /// Refer to [Variant] for the responsibilities of this function.
    /// In particular: `usize::max(lhs.children, rhs.children) <= result.children` in the indexed case and
    /// `lhs.children ∪ rhs.children ⊆ result.children` in the named case.
    /// If successful, the variant and arity of the resulting partial have to match, i.e., if the [Arity] fo the variant
    /// is fixed as `n` then [Partial::children] needs to be `n` as well.
    /// See [Arity] for a more detailed description of this relation.
    fn meet(lhs: Self, rhs: Self, ctx: &Self::Context) -> Result<Self, Self::Err>;

    /// Indicates whether the variant has a fixed arity.  Note that this values does not have to be constant over all instances of the variant.
    /// A tuple, for example, might have a variable arity until the inferrence reaches a point where it is determined to be a pair or a triple.
    /// The pair and triple are both represented by the same type variant and have a fixed, non-specific arity.  Before obtaining this information,
    /// the tuple has a variable arity and potentially a different variant.
    fn arity(&self, ctx: &Self::Context) -> Arity;

    /// Context-sensitive version of [Eq].  All rules apply.
    fn equal(this: &Self, that: &Self, ctx: &Self::Context) -> bool;
}

pub trait UpperBoundedType {
    /// Returns the unconstrained, most abstract type.
    fn top() -> Self;
}

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
/// The arguments of the meet functions are [Partial], i.e., the combination of a variant and the information about the children of the respective type.
/// This is of particular interest for types that are not fully resolved and thus do not have a fixed arity, yet.  An unconstained type variant could have
/// a sub-type because it will be later determined to be an "Option" or "Tuple" type.  More details in the next section.
///
/// ## Arity
/// Type can be recursive, i.e., they have a number of subtypes, their "children".
/// An integer, for example, has no children and is thus 0-ary.  An optional type on the other hand is 1-ary, tuples might have an arbitrary arity.
/// During the inference process, the arity might be undetermined: the unconstrained type will resolve to something with an arity, but the value is not clear, yet.
/// Hence, its arity is initially variable and potentially refines when more information was collected.
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
/// # Context
/// If the variant requires a context for the meet and/or equality operation, refer to [ContextSensitiveVariant].
/// Each [Variant] automatically implements [ContextSensitiveVariant].
///
pub trait Type: Sized + Clone + Debug + Eq + UpperBoundedType {
    /// Result of a meet of two incompatible type, i.e., it represents a type contradiction.
    /// May contain information regarding why the meet failed.  The error will be wrapped into a [crate::TcErr] providing contextual information.
    type Err: Debug;

    /// Attempts to meet two variants respecting their currently-determined potentially variable arity.
    /// Refer to [Variant] for the responsibilities of this function.
    /// In particular: `usize::max(lhs.children, rhs.children) <= result.children` in the indexed case and
    /// `lhs.children ∪ rhs.children ⊆ result.children` in the named case.
    /// If successful, the variant and arity of the resulting partial have to match, i.e., if the [Arity] fo the variant
    /// is fixed as `n` then [Partial::children] needs to be `n` as well.
    /// See [Arity] for a more detailed description of this relation.
    fn meet(lhs: Self, rhs: Self) -> Result<Self, Self::Err>;

    /// Indicates whether the variant has a fixed arity.  Note that this values does not have to be constant over all instances of the variant.
    /// A tuple, for example, might have a variable arity until the inferrence reaches a point where it is determined to be a pair or a triple.
    /// The pair and triple are both represented by the same type variant and have a fixed, non-specific arity.  Before obtaining this information,
    /// the tuple has a variable arity and potentially a different variant.
    fn arity(&self) -> Arity;
}

impl<T: Type> ContextType for T {
    type Err = T::Err;

    type Context = ();

    fn meet(lhs: Self, rhs: Self, _ctx: &Self::Context) -> Result<Self, Self::Err> {
        T::meet(lhs, rhs)
    }

    fn arity(&self, _ctx: &Self::Context) -> Arity {
        self.arity()
    }

    fn equal(this: &Self, that: &Self, _ctx: &Self::Context) -> bool {
        this == that
    }
}

/// Partial is a container for a [ContextSensitiveVariant] and the least arity a particular instance of this variant currently has. Only used for [ContextSensitiveVariant::meet()].
///
/// The `children` represent the current knowledge of the type checker about the children of the type.
/// See [ChildConstraint] for further information.
#[derive(Debug, Clone)]
pub struct Infered<T: Sized> {
    /// The variant represented by this `Partial`.
    pub ty: T,
    /// The least requirement for children.
    pub arity: Arity,
}





