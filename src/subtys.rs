use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use crate::Key;

/// Represents the current children of a type.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum SubTys {
    /// There are no known children yet.
    Variable(InferredSubTyMap),
    /// The type doesn't have any children.
    None,
}

impl SubTys {
    pub(crate) fn top() -> Self {
        Self::Variable(HashMap::new())
    }

    pub(crate) fn empty() -> Self {
        Self::Variable(HashMap::new())
    }

    pub(crate) fn all_numeric(&self) -> bool {
        self.all(SubTyAccess::is_numeric)
    }

    pub(crate) fn all_field(&self) -> bool {
        self.all(SubTyAccess::is_field)
    }

    #[allow(unused)]
    pub(crate) fn is_variable(&self) -> bool {
        match self {
            Self::Variable(inner) => inner.is_empty(),
            Self::None => false,
        }
    }

    pub(crate) fn is_none(&self) -> bool {
        matches!(self, SubTys::None)
    }

    pub(crate) fn subty(&self, access: &SubTyAccess) -> Result<Option<Key>, SubTyAccessErr> {
        Ok(self._valid_subty_access(access)?.get(access).cloned().flatten())
    }

    pub(crate) fn all<F>(&self, f: F) -> bool
    where
        F: FnMut(&SubTyAccess) -> bool,
    {
        match self {
            Self::None => true,
            Self::Variable(inner) => inner.keys().all(f),
        }
    }

    fn _valid_subty_access_mut(&mut self, access: &SubTyAccess) -> Result<&mut InferredSubTyMap, SubTyAccessErr> {
        let all_field = self.all_field();
        let all_numeric = self.all_numeric();
        debug_assert!(all_field || all_numeric);
        let access_matches = access.is_field() == all_field;
        if !access_matches || self.is_none() {
            return Err(SubTyAccessErr { subtys: self.clone(), accessor: access.clone() });
        }
        if let SubTys::Variable(inner) = self {
            return Ok(inner);
        }
        unreachable!("Rework this function.")
    }

    fn _valid_subty_access(&self, access: &SubTyAccess) -> Result<&InferredSubTyMap, SubTyAccessErr> {
        let all_field = self.all_field();
        let all_numeric = self.all_numeric();
        debug_assert!(all_field || all_numeric);
        let access_matches = access.is_field() == all_field;
        if let SubTys::Variable(inner) = self {
            if access_matches {
                return Ok(inner);
            }
        }
        Err(SubTyAccessErr { subtys: self.clone(), accessor: access.clone() })
    }

    pub(crate) fn add_potential_subty(
        &mut self,
        access: &SubTyAccess,
        subty_key: Option<Key>,
    ) -> Result<ReqsMerge, SubTyAccessErr> {
        let inner = self._valid_subty_access_mut(access)?;
        let res = match inner.get(access).cloned().flatten() {
            Some(old) => Ok(ReqsMerge::Yes(old)),
            None => Ok(ReqsMerge::No),
        };
        let _ = inner.insert(access.clone(), subty_key);
        res
    }

    pub(crate) fn add_subty(&mut self, access: &SubTyAccess, subty_key: Key) -> Result<ReqsMerge, SubTyAccessErr> {
        self.add_potential_subty(access, Some(subty_key))
    }

    pub(crate) fn to_vec(&self) -> Vec<(&SubTyAccess, &Option<Key>)> {
        match self {
            SubTys::None => vec![],
            SubTys::Variable(inner) => inner.iter().collect(),
        }
    }

    pub(crate) fn from_arity(arity: Arity) -> Self {
        match arity {
            Arity::None => SubTys::None,
            Arity::Variable => SubTys::Variable(HashMap::new()),
            Arity::Fields(fields) => {
                SubTys::Variable(fields.into_iter().map(SubTyAccess::Field).map(|acc| (acc, None)).collect())
            }
            Arity::Numeric { greatest } => SubTys::Variable(
                (0..=greatest).into_iter().map(SubTyAccess::Numeric).map(|acc| (acc, None)).collect(),
            ),
        }
    }
}

impl From<Arity> for SubTys {
    fn from(arity: Arity) -> Self {
        Self::from_arity(arity)
    }
}

pub(crate) type InferredSubTyMap = HashMap<SubTyAccess, Option<Key>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ReqsMerge {
    Yes(Key),
    No,
}

impl ReqsMerge {
    pub(crate) fn as_opt(&self) -> Option<Key> {
        match self {
            Self::Yes(key) => Some(*key),
            Self::No => None,
        }
    }

    pub(crate) fn zip(&self, other: Option<Key>) -> Option<(Key, Key)> {
        self.as_opt().zip(other)
    }
}

pub(crate) type Equates = Vec<Equate>;
pub(crate) type Equate = (Key, Key);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SubTyAccessErr {
    pub(crate) subtys: SubTys,
    pub(crate) accessor: SubTyAccess,
}

// /// Represents the arity of a [Variant] or [ContextSensitiveVariant].
// /// The arity of a variant corresponds directly to the [ChildConstraint] of a type in the following manner:
// /// * `Arity::Variable <=> ChildConstraint::Unconstrained`
// /// * `Arity::None <=> ChildConstraint::NoChildren`
// /// * `Arity::FixedIndexed(idx) <=> ChildConstraint::Indexed(idx)`
// /// * `Arity::FixedNamed(names) <=> ChildConstraint::Named(names)`
#[derive(Debug, Clone)]
pub enum Arity {
    /// The Type should have no children at all.
    None,
    /// The arity is variable, i.e., it does not have a specific value.
    Variable,
    /// The arity is fixed and the children are accessed by name.
    Fields(HashSet<String>),
    Numeric {
        greatest: usize,
    },
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum SubTyAccess {
    Numeric(usize),
    Field(String), // todo
}

impl SubTyAccess {
    pub fn is_field(&self) -> bool {
        matches!(self, Self::Field(_))
    }
    pub fn is_numeric(&self) -> bool {
        matches!(self, Self::Numeric(_))
    }
    pub fn numeric(&self) -> Option<usize> {
        match self {
            Self::Numeric(idx) => Some(*idx),
            Self::Field(_) => None,
        }
    }
    pub fn field(&self) -> Option<String> {
        match self {
            Self::Numeric(_) => None,
            Self::Field(field) => Some(field.clone()),
        }
    }
}

impl Arity {
    pub fn for_tuple(of_size: usize) -> Self {
        Arity::Numeric { greatest: of_size }
    }

    pub fn for_struct(with_fields: HashSet<String>) -> Self {
        Arity::Fields(with_fields)
    }
}
