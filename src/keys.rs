//! The type checker uses `TcKeys` to refer to entities like variables or terms.  `Constraints` related different keys and abstract/concrete types.
//!
//! `TcKey`s are an inexpensive and simple indexing mechanism that can be copied, checked for equality, and hashed.  
//! A `TcKey` offers functions for relating them to other keys or types, symmetrically or asymmetrically.

use crate::types::{Abstract, Generalizable};
use std::hash::Hash;

/// Represents a constraint on one or several `TcKey`s and/or types.
///
/// Rather than creating these constraints directly, `TcKey` provides several convenient functions for this
/// purpose.
#[must_use = "the creation of a `TypeConstraint` has no effect, it should be passed to a `TypeChecker`"]
#[derive(Debug, Clone)]
#[doc(hidden)]
pub enum Constraint<AbsTy: Abstract> {
    /// Equates two keys, i.e., they refer to the same type and are thus symmetrically connected.  Refining one will refine the other as well.
    Equal(TcKey, TcKey),

    /// Connects two keys asymmetrically.  Refining `bound` refines `target` whereas refining `target` leaves `bound` unaffected.
    MoreConc {
        /// The more concrete key that is bound and thus affected by changes to `bound`.
        target: TcKey,
        /// The less concrete key that constitutes a bound for `target`.
        bound: TcKey,
    },
    /// An asymmetric relation between a key and a type.  Note that the type cannot change over time.
    MoreConcExplicit(TcKey, AbsTy),

    /// A conjunction of several constraints.
    Conjunction(Vec<Self>),

    /// Declares that the key needs to resolve to a type with the given variant.
    Variant(TcKey, AbsTy::VariantTag),
}

/// An inexpensive and simple indexing mechanism using during the type checking procedure.
///
/// It can that can be copied, checked for equality, and hashed, however, it is not ordered.
/// A `TcKey` offers functions for relating them to other keys or types, symmetrically or asymmetrically, by creating constraints.
/// These constraints only serve one purpose: They can be passed to the type checker's `TypeChecker::impose` function.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TcKey {
    pub(crate) ix: usize,
}

impl TcKey {
    pub(crate) fn new(ix: usize) -> TcKey {
        TcKey { ix }
    }
}

impl TcKey {
    /// Connects two keys asymmetrically.  Refining `bound` refines `self` whereas refining `self` leaves `bound` unaffected.
    pub fn more_concrete_than<AbsTy: Abstract>(self, bound: Self) -> Constraint<AbsTy> {
        Constraint::MoreConc { target: self, bound }
    }
    /// Equates two keys, i.e., they refer to the same type and are thus symmetrically connected.  Refining one will refine the other as well.
    pub fn equate<AbsTy: Abstract>(self, other: Self) -> Constraint<AbsTy> {
        Constraint::Equal(self, other)
    }
    /// Declares that `self` is at least as concrete as `bound`.
    pub fn more_concrete_than_explicit<AbsTy: Abstract>(self, bound: AbsTy) -> Constraint<AbsTy> {
        Constraint::MoreConcExplicit(self, bound)
    }
    /// Declares that `self` is the meet of `left` and `right`.  
    /// This binds `self` to both `left` and `right` asymmetrically.
    pub fn is_meet_of<AbsTy: Abstract>(self, left: Self, right: Self) -> Constraint<AbsTy> {
        self.is_meet_of_all(&[left, right])
    }
    /// Declares that `self` is the meet of all elements contained in `elems`.  
    /// This binds `self` to all of these keys asymmetrically.
    pub fn is_meet_of_all<AbsTy: Abstract>(self, elems: &[Self]) -> Constraint<AbsTy> {
        Constraint::Conjunction(elems.iter().map(|e| self.more_concrete_than(*e)).collect())
    }
    /// Declares that `self` is at least as concrete as the abstracted version of `conc`.
    pub fn captures_concrete<AbsTy: Abstract, CT>(self, conc: CT) -> Constraint<AbsTy>
    where
        CT: Generalizable<Generalized = AbsTy>,
    {
        self.more_concrete_than_explicit(conc.generalize())
    }
}
