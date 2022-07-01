use std::{iter::FromIterator, collections::HashMap, fmt::Debug};

use crate::{ContextType, children::Children, Key, types::UpperBoundedType};

/// Represents a preliminary output of the type check.  Mainly used if [Variant] does not implement [Constructable].
#[derive(Debug, Clone)]
pub struct Preliminary<T: ContextType> {
    /// The type variant of the entity represented by this `Preliminary`.
    pub ty: T,
    /// The [TcKey]s of the children of this variant.
    pub children: Children,
}

/// Represents the final resolved children of a type.
#[derive(Debug, Clone)]
pub enum ResolvedChildren<T: Clone + Debug> {
    /// The type doesn't have any children.
    None,
    /// The type has children accessed by index, given by the collection.
    Indexed(Vec<T>),
    /// The type has children accessed by name, given by the collection.
    Named(HashMap<String, T>),
}

impl<T: Clone + Debug> FromIterator<T> for ResolvedChildren<T> {
    fn from_iter<IT: IntoIterator<Item = T>>(iter: IT) -> Self {
        let mut iter = iter.into_iter().peekable();
        if iter.peek().is_some() {
            ResolvedChildren::Indexed(Vec::from_iter(iter))
        } else {
            ResolvedChildren::None
        }
    }
}

impl<T: Clone + Debug> FromIterator<(String, T)> for ResolvedChildren<T> {
    fn from_iter<IT: IntoIterator<Item = (String, T)>>(iter: IT) -> Self {
        let mut iter = iter.into_iter().peekable();
        if iter.peek().is_some() {
            ResolvedChildren::Named(HashMap::from_iter(iter))
        } else {
            ResolvedChildren::None
        }
    }
}

impl<T: Clone + Debug> ResolvedChildren<T> {
    /// Expects the children to be indexed and returns the inner collection.
    /// Panics, if the children are not indexed.
    pub fn into_indexed(self) -> Vec<T> {
        match self {
            ResolvedChildren::Indexed(res) => res,
            ResolvedChildren::Named(_) | ResolvedChildren::None => panic!("Children did not resolve as indexed."),
        }
    }

    /// Expects the children to be named and returns the inner collection.
    /// Panics, if the children are not named.
    pub fn into_named(self) -> HashMap<String, T> {
        match self {
            ResolvedChildren::Named(res) => res,
            ResolvedChildren::Indexed(_) | ResolvedChildren::None => panic!("Children did not resolve as named."),
        }
    }
}

/// A type implementing this trait can potentially be transformed into a concrete representation. This transformation can fail.
pub trait Constructable: ContextType {
    /// The result type of the attempted construction.
    type Type: Clone + Debug + UpperBoundedType;
    /// Attempts to transform `self` into an more concrete `Self::Type`.
    /// Returns a [ContextSensitiveVariant::Err] if the transformation fails.  This error will be wrapped into a [crate::TcErr] to enrich it with contextual information.
    fn construct(
        &self,
        children: ResolvedChildren<Self::Type>,
    ) -> Result<Self::Type, <Self as ContextType>::Err>;
}


/// A type table containing a [Preliminary] type for each [TcKey].  Mainly used if [ContextSensitiveVariant] does not implement [Constructable].
pub type PreliminaryTypeTable<T> = HashMap<Key, Preliminary<T>>;
/// A type table containing the constructed type of the inferred [ContextSensitiveVariant] for each [TcKey].  Requires [ContextSensitiveVariant] to implement [Constructable].
pub type TypeTable<T> = HashMap<Key, <T as Constructable>::Type>;