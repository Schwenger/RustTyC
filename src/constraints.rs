use crate::{Abstract, Generalizable, TcKey};

/// Represents a constraint on one or several abstract types referred to by `TcKey`s.
/// Rather than creating these constraints directly, `TcKey` provides several convenient functions for this
/// purpose.
#[must_use = "the creation of a `TypeConstraint` has no effect, it should be passed to a `TypeChecker`"]
#[derive(Debug, Clone)]
pub enum Constraint<AbsTy: Abstract> {
    // Unification related
    SymLink(TcKey<AbsTy>, TcKey<AbsTy>),
    EqAbs(TcKey<AbsTy>, AbsTy),

    // Concreteness related
    MoreConc(TcKey<AbsTy>, TcKey<AbsTy>),

    // Pure checks
    Equal(TcKey<AbsTy>, TcKey<AbsTy>),
}

impl<AbsTy: Abstract> TcKey<AbsTy> {
    pub fn resolves_to_same_type(self, other: Self) -> Constraint<AbsTy> {
        Constraint::Equal(self, other)
    }
    pub fn is_linked_symmetrically(self, other: Self) -> Constraint<AbsTy> {
        Constraint::SymLink(self, other)
    }
    pub fn captures_abstract(self, other: AbsTy) -> Constraint<AbsTy> {
        Constraint::EqAbs(self, other)
    }
    pub fn is_more_conc_than(self, other: Self) -> Constraint<AbsTy> {
        Constraint::MoreConc(self, other)
    }
    pub fn captures_concrete<CT>(self, conc: CT) -> Constraint<AbsTy>
    where
        CT: Generalizable<Generalized = AbsTy>,
    {
        self.captures_abstract(conc.generalize())
    }
}
