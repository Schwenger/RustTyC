use crate::keys::TcKey;
use std::fmt::Debug;

/// The main trait representing types throughout the type checking procedure.
/// It is bound to the type checker as the `Value` for the `Key` parameter.  As such, it needs to implement
/// `EnaValue`.
pub trait Abstract: Eq + Sized + Clone + Debug {
    /// Represents an error during the meet of two abstract types.
    type Error;

    type Variant: TypeVariant;

    /// Returns an unconstrained abstract type.
    fn unconstrained() -> Self;

    /// Determines if an element is unconstrained.
    fn is_unconstrained(&self) -> bool {
        self == &Self::unconstrained()
    }

    /// Computes the meet of two abstract values.
    fn meet(self, other: Self) -> Result<Self, Self::Error>;
}

pub trait TypeVariant: Clone + Copy + PartialEq + Eq {
    fn arity(self) -> u8;
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TcMonad<AbsTy: Abstract> {
    _this: TcKey<AbsTy>,
    _child: TcKey<AbsTy>,
    _variant: AbsTy::Variant,
}

impl<AbsTy: Abstract> TcMonad<AbsTy> {
    pub fn new(this: TcKey<AbsTy>, child: TcKey<AbsTy>, variant: AbsTy::Variant) -> Self {
        TcMonad { _this: this, _child: child, _variant: variant }
    }

    pub fn key(&self) -> TcKey<AbsTy> {
        self._this
    }

    pub fn child(&self) -> TcKey<AbsTy> {
        self._child
    }
}
