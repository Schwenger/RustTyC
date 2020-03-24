use crate::{Abstract, Generalizable, TcKey};

/// Represents a constraint on one or several abstract types referred to by `TcKey`s.
/// Rather than creating these constraints directly, `TcKey` provides several convenient functions for this
/// purpose.
#[must_use = "the creation of a `TypeConstraint` has no effect, it should be passed to a `TypeChecker`"]
#[derive(Debug, Clone)]
pub enum Constraint<AbsTy: Abstract> {
    EqKey(TcKey<AbsTy>, TcKey<AbsTy>),
    EqAbs(TcKey<AbsTy>, AbsTy),
    // Conjunction(Vec<Constraint<AbsTy>>),
}

impl<AbsTy: Abstract> TcKey<AbsTy> {
    pub fn unify_with(self, other: Self) -> Constraint<AbsTy> {
        Constraint::EqKey(self, other)
    }
    pub fn captures(self, other: AbsTy) -> Constraint<AbsTy> {
        Constraint::EqAbs(self, other)
    }
}

impl<Var: Abstract> TcKey<Var> {
    /// Bounds `self` by the generalization of the concrete type `conc`.
    pub fn captures_concrete<CT>(self, conc: CT) -> Constraint<Var>
    where
        CT: Generalizable<Generalized = Var>,
    {
        // TODO: This should not be a symmetric relation.  Change when asym relations are in the game again.
        self.captures(conc.generalize())
    }
}
