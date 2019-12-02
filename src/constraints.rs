use crate::lattice::{AbstractType, TypeCheckKey};
use ena::unify::UnifyKey;
use crate::Generalizable;

/// Represents a constraint on one or several abstract types referred to by `TypeCheckKey`s.
/// Rather than creating these constraints directly, `TypeCheckKey` provides several convenient functions for this
/// purpose.
#[must_use = "the creation of a `TypeConstraint` has no effect, it should be passed to a `TypeChecker`"]
pub enum TypeConstraint<Key: UnifyKey>
where
    Key::Value: AbstractType,
{
    MoreConcreteThanAll { target: TypeCheckKey<Key>, args: Vec<TypeCheckKey<Key>> },
    MoreConcreteThanType { target: TypeCheckKey<Key>, args: Vec<Key::Value> },
}

impl<Key: UnifyKey> TypeCheckKey<Key>
where
    Key::Value: AbstractType,
{
    /// States that the left operand needs to be at least as concrete as the right one.
    /// Imposing this constraints let the abstract type of `self` become be the meet of the current
    /// abstract type of `self` and `other`.
    pub fn more_concrete_than(self, other: Self) -> TypeConstraint<Key> {
        TypeConstraint::MoreConcreteThanAll { target: self, args: vec![other] }
    }

    /// States that `target` needs to be more concrete than all `args` combined.
    /// Imposing this constraint computes the meet of all args and enforces that `self` is more
    /// concrete than the result.
    pub fn is_the_meet_of(self, args: &[Self]) -> TypeConstraint<Key> {
        TypeConstraint::MoreConcreteThanAll { target: self, args: args.to_vec() }
    }

    /// Bounds `self` by `other` where `other` is an abstract type.
    pub fn bound_by_abstract(self, other: Key::Value) -> TypeConstraint<Key> {
        TypeConstraint::MoreConcreteThanType { target: self, args: vec![other] }
    }
}

impl<Key: UnifyKey> TypeCheckKey<Key>
where
    Key::Value: AbstractType,
{
    /// Bounds `self` by the generalization of the concrete type `conc`.
    pub fn bound_by_concrete<CT>(&self, conc: CT) -> TypeConstraint<Key>
    where
        CT: Generalizable<Generalized = Key::Value>,
    {
        self.bound_by_abstract(conc.generalize())
    }
}
