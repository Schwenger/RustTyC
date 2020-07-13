use crate::{Abstract, Generalizable, TcKey};

/// Represents a constraint on one or several abstract types referred to by `TcKey`s.
/// Rather than creating these constraints directly, `TcKey` provides several convenient functions for this
/// purpose.
#[must_use = "the creation of a `TypeConstraint` has no effect, it should be passed to a `TypeChecker`"]
#[derive(Debug, Clone)]
pub enum Constraint<AbsTy: Abstract> {
    // Symmetric
    Equal(TcKey, TcKey),

    // Asymmetric
    MoreConc { target: TcKey, bound: TcKey },
    MoreConcExplicit(TcKey, AbsTy),

    // Utility
    Conjunction(Vec<Self>),

    // Variants
    Variant(TcKey, AbsTy::VariantTag),
}

impl TcKey {
    pub fn more_concrete_than<AbsTy: Abstract>(self, bound: Self) -> Constraint<AbsTy> {
        Constraint::MoreConc { target: self, bound }
    }
    pub fn equate<AbsTy: Abstract>(self, other: Self) -> Constraint<AbsTy> {
        Constraint::Equal(self, other)
    }
    pub fn more_concrete_than_explicit<AbsTy: Abstract>(self, bound: AbsTy) -> Constraint<AbsTy> {
        Constraint::MoreConcExplicit(self, bound)
    }
    pub fn is_meet_of<AbsTy: Abstract>(self, left: Self, right: Self) -> Constraint<AbsTy> {
        self.is_meet_of_all(&[left, right])
    }
    pub fn is_meet_of_all<AbsTy: Abstract>(self, elems: &[Self]) -> Constraint<AbsTy> {
        Constraint::Conjunction(elems.iter().map(|e| self.more_concrete_than(*e)).collect())
    }
    pub fn captures_concrete<AbsTy: Abstract, CT>(self, conc: CT) -> Constraint<AbsTy>
    where
        CT: Generalizable<Generalized = AbsTy>,
    {
        self.more_concrete_than_explicit(conc.generalize())
    }
}
