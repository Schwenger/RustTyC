use crate::type_checker::TcValue;
use crate::types::Abstract;
use ena::unify::UnifyKey as EnaKey;
use std::hash::Hash;
use std::marker::PhantomData;

/// A `TcKey` references an abstract type object during the type checking procedure.
/// It can be created via `TypeChecker::new_{term/var}_ key` and provides functions creating `Constraint`s that
/// impose rules on type variables, e.g. by constraining single types are relating others.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TcKey<Val: Abstract> {
    pub(crate) ix: u32,
    phantom: PhantomData<Val>,
}

impl<Val: Abstract> TcKey<Val> {
    pub(crate) fn new(ix: u32) -> TcKey<Val> {
        TcKey { ix, phantom: PhantomData }
    }
}

impl<Val: Abstract> Copy for TcKey<Val> {}
impl<Val: Abstract> Hash for TcKey<Val> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ix.hash(state)
    }
}

impl<Val: Abstract> EnaKey for TcKey<Val> {
    type Value = TcValue<Val>;

    fn index(&self) -> u32 {
        self.ix
    }

    fn from_index(u: u32) -> Self {
        TcKey::new(u)
    }

    fn tag() -> &'static str {
        "TypeCheckKey"
    }
}
