use crate::type_checker::{Abstract, TcKey};
use crate::Generalizable;
use ena::unify::UnifyKey;

/// Represents a constraint on one or several abstract types referred to by `TcKey`s.
/// Rather than creating these constraints directly, `TcKey` provides several convenient functions for this
/// purpose.
#[must_use = "the creation of a `TypeConstraint` has no effect, it should be passed to a `TypeChecker`"]
#[derive(Debug, Clone)]
pub enum Constraint<Key: UnifyKey>
where
    Key::Value: Abstract,
{
    /// Represents the restriction that `target` is more concrete than the meet of all abstract types belonging to the
    /// keys in `args`.
    MoreConcreteThanAll {
        /// The key that is supposed to be more concrete than the meet of all abstract types behind `args`.
        target: TcKey<Key>,
        /// Collection of keys where `target` is supposed to be more concrete than the abstract types behind elements
        /// of this collection.
        args: Vec<TcKey<Key>>,
    },

    /// Represents the restriction that `target` is more concrete than the meet of all abstract types in `args`.
    MoreConcreteThanType {
        /// The key that is supposed to be more concrete than the concrete types in `args`.
        target: TcKey<Key>,
        /// Collection of types where `target` is supposed to be more concrete than elements of this collection.
        args: Vec<Key::Value>,
    },
}

impl<Key: UnifyKey> TcKey<Key>
where
    Key::Value: Abstract,
{
    /// States that the left operand needs to be at least as concrete as the right one.
    /// Imposing these constraints lets the abstract type of `self` become the meet of the current
    /// abstract type of `self` and `other`.
    pub fn more_concrete_than(self, other: Self) -> Constraint<Key> {
        Constraint::MoreConcreteThanAll { target: self, args: vec![other] }
    }

    /// States that `target` needs to be more concrete than all `args` combined.
    /// Imposing this constraint computes the meet of all args and enforces that `self` is more
    /// concrete than the result.
    pub fn is_the_meet_of(self, args: &[Self]) -> Constraint<Key> {
        Constraint::MoreConcreteThanAll { target: self, args: args.to_vec() }
    }

    /// Bounds `self` by `other` where `other` is an abstract type.
    pub fn bound_by_abstract(self, other: Key::Value) -> Constraint<Key> {
        Constraint::MoreConcreteThanType { target: self, args: vec![other] }
    }
}

impl<Key: UnifyKey> TcKey<Key>
where
    Key::Value: Abstract,
{
    /// Bounds `self` by the generalization of the concrete type `conc`.
    pub fn bound_by_concrete<CT>(&self, conc: CT) -> Constraint<Key>
    where
        CT: Generalizable<Generalized = Key::Value>,
    {
        self.bound_by_abstract(conc.generalize())
    }
}
