use crate::type_checker::TypeChecker;
use crate::type_checker::{Abstract, TcKey, TcVar};

/// Indicates that an abstract type could not be reified because it is too general or too restrictive.
/// # Example
/// 1. A numeric type cannot be reified into any concrete value because the concrete counterpart could be a natural
/// number, integer, floating point number, .... -> `ReificationError::TooGeneral`
/// 2. An integer type cannot be reified into a concrete type with fixed memory layout except a default size is
/// defined, e.g. an Int will be reified into an Int32. -> `ReificationError::TooGeneral`
/// 3. An unbounded integer might not have a concrete counterpart because the system requires a concrete bit size.
/// -> `ReificationError::Conflicting`
///
/// Note the subtle difference between `ReificationError::TooGeneral` and `ReificationError::Conflicting`:
///     + In the `Conflicting` case there is no valid counterpart
///     + In the `TooGeneral` case the counterpart is not defined or not unique but could exist.
#[derive(Debug)]
pub enum ReificationError {
    /// Attempting to reify an abstract type with either no unique concrete counterpart or with no defined default
    /// reification value results in this error.
    TooGeneral(String),
    /// Attempting to reify an abstract type for which no concrete counterpart does exist results in this error.
    Conflicting(String),
}

/// A type implementing this trait can be `reified` into a concrete representation.
/// This transformation cannot fail.  If it is fallible, refer to `TryReifiable`.
pub trait Reifiable {
    /// The result type of the reification.
    type Reified;
    /// Transforms an instance of `Reifiable` into an more concrete `Reifiable::Reified` type.
    fn reify(&self) -> Self::Reified;
}

/// A type implementing this trait can potentially be `reified` into a concrete representation.
/// This transformation can fail.  If it is infallible, refer to `Reifiable`.
pub trait TryReifiable {
    /// The result type of the attempted reification.
    type Reified;
    /// Attempts to transform an instance of `TryReifiable` into an more concrete
    /// `TryReifiable::Reified` type.  Returns a `ReificationError` if the transformation fails.
    fn try_reify(&self) -> Result<Self::Reified, ReificationError>;
}

/// A type implementing this trait can be `generalized` into an abstract representation.
/// This transformation cannot fail.
pub trait Generalizable {
    /// The result type of the generalization.
    type Generalized;
    /// Generalizes the given concrete type.
    fn generalize(&self) -> Self::Generalized;
}

impl<AbsTy: Abstract + TryReifiable, Var: TcVar> TypeChecker<AbsTy, Var> {
    /// Returns a mapping of all registered abstract type nodes to their reification.
    pub fn try_get_reified_type_table(
        &mut self,
    ) -> Vec<(TcKey<AbsTy>, Result<<AbsTy as TryReifiable>::Reified, ReificationError>)> {
        self.get_type_table().into_iter().map(|(key, value)| (key, value.try_reify())).collect()
    }
}

impl<AbsTy: Abstract + Reifiable, Var: TcVar> TypeChecker<AbsTy, Var> {
    /// Returns a mapping of all registered abstract type nodes to their reification.
    pub fn get_reified_type_table(&mut self) -> Vec<(TcKey<AbsTy>, <AbsTy as Reifiable>::Reified)> {
        self.get_type_table().into_iter().map(|(key, value)| (key, value.reify())).collect()
    }
}
