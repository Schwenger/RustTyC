//! The type checker uses [TcKey] to refer to entities like variables or terms.  [Constraint] related different keys and abstract/concrete types.
//!
//! [TcKey]s are an inexpensive and simple indexing mechanism that can be copied, checked for equality, and hashed.  
//! A [TcKey] offers functions for relating them to other keys or types, symmetrically or asymmetrically.

use crate::types::Variant;
use std::hash::Hash;

/// Represents a constraint on one or several [TcKey]s and/or types.
///
/// Rather than creating these constraints directly, [TcKey] provides several convenient functions for this
/// purpose.  They can then be passed to the [TypeChecker] via the [Typechecker::impose()] function.
#[must_use = "the creation of a `TypeConstraint` has no effect, it should be passed to a `TypeChecker`"]
#[derive(Debug, Clone)]
pub enum Constraint<V: Variant> {
    /// equate_withs two keys, i.e., they refer to the same type and are thus symmetrically connected.  Refining one will refine the other as well.
    #[doc(hidden)]
    Equal(TcKey, TcKey),

    /// Connects two keys asymmetrically.  Refining `bound` refines `target` whereas refining `target` leaves `bound` unaffected.
    #[doc(hidden)]
    MoreConc {
        /// The more concrete key that is bound and thus affected by changes to `bound`.
        #[doc(hidden)]
        target: TcKey,
        /// The less concrete key that constitutes a bound for `target`.
        #[doc(hidden)]
        bound: TcKey,
    },
    /// An asymmetric relation between a key and a type.  Note that the type cannot change over time.
    #[doc(hidden)]
    MoreConcExplicit(TcKey, V),

    /// A conjunction of several constraints.
    #[doc(hidden)]
    Conjunction(Vec<Self>),
}

/// An inexpensive and simple indexing mechanism using during the type checking procedure.
///
/// It can that can be copied, checked for equality, and hashed, however, it is not ordered.
/// A [TcKey] offers functions for relating them to other keys or types, symmetrically or asymmetrically, by creating constraints.
/// These constraints only serve one purpose: They can be passed to the type checker's [crate::TypeChecker::impose()] function.
///
/// # Example
/// There are several kinds of constraints that can be generated for a key.
/// Assume the following data structures exist:
/// ```
/// use rusttyc::{Variant, TcKey, TypeChecker, TcVar, TcErr, Partial, Arity};
///
/// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// enum MyVariant {
///     Top,
///     Numeric,
///     UInt,
///     U8,
///     String,
/// }
///
/// impl Variant for MyVariant {
///     type Err = String;
///     fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err> {
///         use MyVariant::*;
///         let variant = match (lhs.variant, rhs.variant) {
///             (Top, x) | (x, Top) => Ok(x),
///             (String, String) => Ok(String),
///             (String, _) | (_, String) => Err("string can only be met with string.".to_string()),
///             (Numeric, x) | (x, Numeric) => Ok(x), // x can only be Numeric, UInt, or U8.
///             (UInt, x) | (x, UInt) => Ok(x),       // x can only be UInt or U8.
///             (U8, U8) => Ok(U8),
///         }?;
///         Ok(Partial { variant, least_arity: 0 })
///     }
///     fn top() -> Self {
///         Self::Top
///     }
///     fn arity(&self) -> Arity {
///         Arity::Fixed(0)
///     }
/// }
/// #[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
/// struct MyVar(u8);
/// impl TcVar for MyVar {}
/// ```
///
/// The type checking procedure can then proceed as follows.
/// ```
/// # use rusttyc::{Variant, TcKey, TypeChecker, TcVar, TcErr, Partial, Arity};
/// #
/// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// enum MyVariant {
///     Top,
///     Numeric,
///     UInt,
///     U8,
///     String,
/// }
///
/// impl Variant for MyVariant {
///     type Err = String;
///     fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err> {
///         use MyVariant::*;
///         let variant = match (lhs.variant, rhs.variant) {
///             (Top, x) | (x, Top) => Ok(x),
///             (String, String) => Ok(String),
///             (String, _) | (_, String) => Err("string can only be met with string.".to_string()),
///             (Numeric, x) | (x, Numeric) => Ok(x), // x can only be Numeric, UInt, or U8.
///             (UInt, x) | (x, UInt) => Ok(x),       // x can only be UInt or U8.
///             (U8, U8) => Ok(U8),
///         }?;
///         Ok(Partial { variant, least_arity: 0 })
///     }
///     fn top() -> Self {
///         Self::Top
///     }
///     fn arity(&self) -> Arity {
///         Arity::Fixed(0)
///     }
/// }
/// #[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
/// struct MyVar(u8);
/// impl TcVar for MyVar {}
///
/// # fn main() -> Result<(), TcErr<MyVariant>> {
/// let mut tc: TypeChecker<MyVariant, MyVar> = TypeChecker::new();
/// let key1 = tc.new_term_key();
/// let key2 = tc.new_term_key();
/// let key3 = tc.new_term_key();
/// let key4 = tc.new_term_key();
///
/// tc.impose(key1.concretizes_explicit(MyVariant::Numeric))?;  // key1 is numeric.
/// // key2 is at least as concrete as k1, i.e. it will also be numeric.
/// tc.impose(key2.concretizes(key1))?;
/// tc.impose(key3.equate_with(key2))?; // key3 is the same type as key2, i.e., numeric
///
/// let tt = tc.clone().type_check_preliminary()?;
/// assert_eq!(tt[&key1].variant, MyVariant::Numeric);
/// assert_eq!(tt[&key2].variant, MyVariant::Numeric);
/// assert_eq!(tt[&key3].variant, MyVariant::Numeric);
/// // we did not impose a constraint on it, yet, so its the top element.
/// assert_eq!(tt[&key4].variant, MyVariant::Top);
///
/// // Concretize key3 to be a UInt.  Also affects key2 due to unification.  
/// // key1 is unaffected because of the asymmetric relation between key1 and key2,
/// // which translates to an asymmetric relation between key1 and key3 as well.
/// tc.impose(key3.concretizes_explicit(MyVariant::UInt))?;
///
/// let tt = tc.clone().type_check_preliminary()?;
/// assert_eq!(tt[&key1].variant, MyVariant::Numeric);
/// assert_eq!(tt[&key2].variant, MyVariant::UInt);
/// assert_eq!(tt[&key3].variant, MyVariant::UInt);
/// assert_eq!(tt[&key4].variant, MyVariant::Top);
///
/// // key4 is more concrete than both key2 (and transitively key3), and key1, so it becomes a UInt.
/// tc.impose(key4.is_meet_of(key2, key1))?;
/// // Make key2 and key3 U8.  key4 depends on them, so it becomes U8 as well.  key1 is unaffected.
/// tc.impose(key2.concretizes_explicit(MyVariant::U8))?;
/// let key5 = tc.new_term_key();
/// tc.impose(key5.concretizes_explicit(MyVariant::String))?; // key5 is a string.
///
/// let tt = tc.clone().type_check_preliminary()?;
/// assert_eq!(tt[&key1].variant, MyVariant::Numeric);
/// assert_eq!(tt[&key2].variant, MyVariant::U8);
/// assert_eq!(tt[&key3].variant, MyVariant::U8);
/// assert_eq!(tt[&key4].variant, MyVariant::U8);
/// assert_eq!(tt[&key5].variant, MyVariant::String);
///
/// let key6 = tc.new_term_key();
/// // key6 is the meet of all other keys.
/// tc.impose(key6.is_meet_of_all(&[key1, key2, key3, key4, key5]))?;
///
/// let res = tc.type_check_preliminary();
/// // The meet of numeric types and strings will fail, so key6 cannot be resolved.
/// assert!(res.is_err());  
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
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
    pub fn concretizes<V: Variant>(self, bound: Self) -> Constraint<V> {
        Constraint::MoreConc { target: self, bound }
    }
    /// Equates two keys, i.e., they refer to the same type and are thus symmetrically connected.  Refining one will refine the other as well.
    pub fn equate_with<V: Variant>(self, other: Self) -> Constraint<V> {
        assert_ne!(self, other, "Cannot equate equal keys.");
        Constraint::Equal(self, other)
    }
    /// Declares that `self` is at least as concrete as `bound`.
    pub fn concretizes_explicit<V: Variant>(self, bound: V) -> Constraint<V> {
        Constraint::MoreConcExplicit(self, bound)
    }
    /// Declares that `self` is the meet of `left` and `right`.  
    /// This binds `self` to both `left` and `right` asymmetrically.
    pub fn is_meet_of<V: Variant>(self, left: Self, right: Self) -> Constraint<V> {
        self.is_meet_of_all(&[left, right])
    }
    /// Declares that `self` is the meet of all elements contained in `elems`.  
    /// This binds `self` to all of these keys asymmetrically.
    pub fn is_meet_of_all<V: Variant>(self, elems: &[Self]) -> Constraint<V> {
        Constraint::Conjunction(elems.iter().map(|e| self.concretizes(*e)).collect())
    }
    /// Declares that `self` is the symmetric meet of `left` and `right`.  
    /// This binds `self` to both `left` and `right` symmetrically.
    pub fn is_sym_meet_of<V: Variant>(self, left: Self, right: Self) -> Constraint<V> {
        self.is_sym_meet_of_all(&[left, right])
    }
    /// Declares that `self` is the symmetric meet of all elements contained in `elems`.  
    /// This binds `self` to all of these keys symmetrically.
    pub fn is_sym_meet_of_all<V: Variant>(self, elems: &[Self]) -> Constraint<V> {
        Constraint::Conjunction(elems.iter().map(|e| self.equate_with(*e)).collect())
    }
}
