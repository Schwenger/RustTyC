use std::fmt::Debug;

/// The main trait representing types throughout the type checking procedure.
/// It is bound to the type checker as the `Value` for the `Key` parameter.  As such, it needs to implement
/// `EnaValue`.
pub trait Abstract: Eq + Sized + Clone + Debug {
    /// Represents an error during the meet of two abstract types.
    type Err: Debug;

    type VariantTag: Debug + Clone + Copy + PartialEq + Eq;

    fn variant(&self) -> Option<Self::VariantTag>;

    /// Returns an unconstrained abstract type.
    fn unconstrained() -> Self;

    /// Determines if an element is unconstrained.
    fn is_unconstrained(&self) -> bool {
        self == &Self::unconstrained()
    }

    /// Computes the meet of two abstract values.
    fn meet(self, other: Self) -> Result<Self, Self::Err>;

    fn variant_arity(tag: Self::VariantTag) -> usize;

    fn nth_child(&self, n: usize) -> &Self;

    fn arity(&self) -> Option<usize> {
        self.variant().map(Self::variant_arity)
    }

    fn from_tag(tag: Self::VariantTag, children: Vec<Self>) -> Self;
}
