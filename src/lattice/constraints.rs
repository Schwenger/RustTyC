use crate::lattice::reification::Generalizable;
use crate::lattice::{AbstractType, TypeCheckKey};
use ena::unify::UnifyKey;

pub enum TypeConstraint<Key: UnifyKey>
where
    Key::Value: AbstractType,
{
    MoreConcreteThanAll { target: TypeCheckKey<Key>, args: Vec<TypeCheckKey<Key>> },
    BoundByValue { target: TypeCheckKey<Key>, bound: Key::Value },
}

impl<Key: UnifyKey> TypeCheckKey<Key>
where
    Key::Value: AbstractType,
{
    /// States that the left operand needs to be at least as concrete as the right one.
    /// Imposing this constraints let the abstract type of `self` become be the meet of the current
    /// abstract type of `self` and `other`.
    pub fn more_concrete_than(&self, other: Self) -> TypeConstraint<Key> {
        TypeConstraint::MoreConcreteThanAll { target: *self, args: vec![other] }
    }

    /// States that `target` needs to be more concrete than all `args` combined.
    /// Imposing this constraint computes the meet of all args and enforces that `self` is more
    /// concrete than the result.
    pub fn is_the_meet_of(&self, args: &[Self]) -> TypeConstraint<Key> {
        TypeConstraint::MoreConcreteThanAll { target: *self, args: args.to_vec() }
    }
}

impl<Key: UnifyKey> TypeCheckKey<Key>
where
    Key::Value: AbstractType,
{
    pub fn bound_by_concrete<CT>(&self, conc: CT) -> TypeConstraint<Key>
    where
        CT: Generalizable<Generalized = Key::Value>,
    {
        let bound: Key::Value = conc.generalize();
        TypeConstraint::BoundByValue { target: *self, bound }
    }
}
