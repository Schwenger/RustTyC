use crate::type_checker::TypeChecker;
use crate::type_checker::{AbstractType, TypeCheckKey};
use ena::unify::UnifyKey;

/// Indicates that an abstract type could not be reified.
pub enum ReificationError {
    TooGeneral(String),
    Conflicting(String),
}

/// A type implementing this trait can be `reified` into a concrete representation.
/// This transformation cannot fail.  If it is fallible, refer to `TryReifiable`.
pub trait Reifiable {
    type Reified;
    /// Transforms an instance of `Reifiable` into an more concrete `Reifiable::Reified` type.
    fn reify(&self) -> Self::Reified;
}

/// A type implementing this trait can potentially be `reified` into a concrete representation.
/// This transformation can fail.  If it is infallible, refer to `Reifiable`.
pub trait TryReifiable {
    type Reified;
    /// Attempts to transform an instance of `TryReifiable` into an more concrete
    /// `TryReifiable::Reified` type.  Returns a `ReificationError` if the transformation fails.
    fn try_reify(&self) -> Result<Self::Reified, ReificationError>;
}

/// A type implementing this trait can be `generalized` into an abstract representation.
/// This transformation cannot fail.
pub trait Generalizable {
    type Generalized;
    fn generalize(&self) -> Self::Generalized;
}

impl<Key: UnifyKey> TypeChecker<Key>
where
    Key::Value: AbstractType + TryReifiable,
{
    /// Returns a mapping of all registered abstract type nodes to their reification.
    pub fn try_get_reified_type_table(&mut self) -> Vec<(TypeCheckKey<Key>, Result<<Key::Value as TryReifiable>::Reified, ReificationError>)> {
        self.get_type_table()
            .into_iter()
            .map(|(key, value)| (key, value.try_reify()))
            .collect()
    }
}

impl<Key: UnifyKey> TypeChecker<Key>
where
    Key::Value: AbstractType + Reifiable,
{
    /// Returns a mapping of all registered abstract type nodes to their reification.
    pub fn get_reified_type_table(&mut self) -> Vec<(TypeCheckKey<Key>, <Key::Value as Reifiable>::Reified)> {
        self.get_type_table().into_iter().map(|(key, value)| (key, value.reify())).collect()
    }
}
