use std::{collections::HashMap, fmt::Debug, iter::FromIterator};

use crate::{
    subtys::SubTys,
    types::{SubTyId, UpperBoundedType},
    ContextType, Key,
};

/// Represents a preliminary output of the type check.  Mainly used if [Variant] does not implement [Constructable].
#[derive(Debug, Clone)]
pub struct Preliminary<T: ContextType> {
    /// The type variant of the entity represented by this `Preliminary`.
    pub ty: T,
    /// The [TcKey]s of the children of this variant.
    pub subtys: SubTys<T::SubTyId>,
}

/// Represents the final resolved children of a type.
#[derive(Debug, Clone)]
pub enum ResolvedSubTys<Id: SubTyId, Resolved: Debug + Clone> {
    /// The type doesn't have any children.
    None,
    /// The type has children accessed by index, given by the collection.
    Numeric(Vec<Resolved>),
    /// The type has children accessed by name, given by the collection.
    Fields(HashMap<Id, Resolved>),
}

impl<Id: SubTyId, Resolved: Debug + Clone> FromIterator<Resolved> for ResolvedSubTys<Id, Resolved> {
    fn from_iter<IT: IntoIterator<Item = Resolved>>(iter: IT) -> Self {
        let mut iter = iter.into_iter().peekable();
        if iter.peek().is_some() {
            ResolvedSubTys::Numeric(Vec::from_iter(iter))
        } else {
            ResolvedSubTys::None
        }
    }
}

impl<Id: SubTyId, Resolved: Debug + Clone> FromIterator<(Id, Resolved)> for ResolvedSubTys<Id, Resolved> {
    fn from_iter<IT: IntoIterator<Item = (Id, Resolved)>>(iter: IT) -> Self {
        let mut iter = iter.into_iter().peekable();
        if iter.peek().is_some() {
            ResolvedSubTys::Fields(HashMap::from_iter(iter))
        } else {
            ResolvedSubTys::None
        }
    }
}

impl<Id: SubTyId, Resolved: Debug + Clone> ResolvedSubTys<Id, Resolved> {
    /// Expects the children to be indexed and returns the inner collection.
    /// Panics, if the children are not indexed.
    pub fn into_numerically_indexed(self) -> Vec<Resolved> {
        match self {
            ResolvedSubTys::Numeric(res) => res,
            ResolvedSubTys::Fields(_) | ResolvedSubTys::None => panic!("Children did not resolve as indexed."),
        }
    }

    /// Expects the children to be named and returns the inner collection.
    /// Panics, if the children are not named.
    pub fn into_field_map(self) -> HashMap<Id, Resolved> {
        match self {
            ResolvedSubTys::Fields(res) => res,
            ResolvedSubTys::Numeric(_) | ResolvedSubTys::None => panic!("Children did not resolve as named."),
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
        children: ResolvedSubTys<Self::SubTyId, Self::Type>,
    ) -> Result<Self::Type, <Self as ContextType>::Err>;
}

/// A type table containing a [Preliminary] type for each [TcKey].  Mainly used if [ContextSensitiveVariant] does not implement [Constructable].
pub type PreliminaryTypeTable<T> = HashMap<Key, Preliminary<T>>;
/// A type table containing the constructed type of the inferred [ContextSensitiveVariant] for each [TcKey].  Requires [ContextSensitiveVariant] to implement [Constructable].
pub type TypeTable<T> = HashMap<Key, <T as Constructable>::Type>;
