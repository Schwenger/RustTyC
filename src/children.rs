use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use crate::Key;

/// Represents the current children of a type.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Children {
    /// There are no known children yet.
    Variable(InferedChildMap),
    /// The type doesn't have any children.
    None,
}

impl Children {
    pub(crate) fn top() -> Self {
        Self::Variable(HashMap::new())
    }

    pub(crate) fn empty() -> Self {
        Self::Variable(HashMap::new())
    }

    pub(crate) fn all_indexed(&self) -> bool {
        self.all(ChildAccessor::is_index)
    }

    pub(crate) fn all_field(&self) -> bool {
        self.all(ChildAccessor::is_field)
    }

    #[allow(unused)]
    pub(crate) fn is_variable(&self) -> bool {
        match self {
            Self::Variable(inner) => inner.is_empty(),
            Self::None => false,
        }
    }

    pub(crate) fn is_none(&self) -> bool {
        matches!(self, Children::None)
    }

    pub(crate) fn child(&self, child: &ChildAccessor) -> Result<Option<Key>, ChildAccessErr> {
        Ok(self._valid_child_access(child)?.get(child).cloned().flatten())
    }

    pub(crate) fn all<F>(&self, f: F) -> bool
    where
        F: FnMut(&ChildAccessor) -> bool,
    {
        match self {
            Self::None => true,
            Self::Variable(inner) => inner.keys().all(f),
        }
    }

    fn _valid_child_access_mut(&mut self, child: &ChildAccessor) -> Result<&mut InferedChildMap, ChildAccessErr> {
        let all_field = self.all_field();
        let all_indexed = self.all_indexed();
        debug_assert!(all_field || all_indexed);
        let access_matches = child.is_field() == all_field;
        if !access_matches || self.is_none() {
            return Err(ChildAccessErr { children: self.clone(), accessor: child.clone() });
        }
        if let Children::Variable(inner) = self {
            return Ok(inner);
        }
        unreachable!("Rework this function.")
    }

    fn _valid_child_access(&self, child: &ChildAccessor) -> Result<&InferedChildMap, ChildAccessErr> {
        let all_field = self.all_field();
        let all_indexed = self.all_indexed();
        debug_assert!(all_field || all_indexed);
        let access_matches = child.is_field() == all_field;
        if let Children::Variable(inner) = self {
            if access_matches {
                return Ok(inner);
            }
        }
        Err(ChildAccessErr { children: self.clone(), accessor: child.clone() })
    }

    pub(crate) fn add_potential_child(
        &mut self,
        child: &ChildAccessor,
        child_key: Option<Key>,
    ) -> Result<ReqsMerge, ChildAccessErr> {
        let inner = self._valid_child_access_mut(child)?;
        let res = match inner.get(child).cloned().flatten() {
            Some(old) => Ok(ReqsMerge::Yes(old)),
            None => Ok(ReqsMerge::No),
        };
        let _ = inner.insert(child.clone(), child_key);
        res
    }

    pub(crate) fn add_child(&mut self, child: &ChildAccessor, child_key: Key) -> Result<ReqsMerge, ChildAccessErr> {
        self.add_potential_child(child, Some(child_key))
    }

    pub(crate) fn to_vec(&self) -> Vec<(&ChildAccessor, &Option<Key>)> {
        match self {
            Children::None => vec![],
            Children::Variable(inner) => inner.iter().collect(),
        }
    }

    pub(crate) fn from_arity(arity: Arity) -> Self {
        match arity {
            Arity::None => Children::None,
            Arity::Variable => Children::Variable(HashMap::new()),
            Arity::Fields(fields) => {
                Children::Variable(fields.into_iter().map(ChildAccessor::Field).map(|acc| (acc, None)).collect())
            }
            Arity::Indices { greatest } => Children::Variable(
                (0..=greatest).into_iter().map(ChildAccessor::Index).map(|acc| (acc, None)).collect(),
            ),
        }
    }
}

impl From<Arity> for Children {
    fn from(arity: Arity) -> Self {
        Self::from_arity(arity)
    }
}

pub(crate) type InferedChildMap = HashMap<ChildAccessor, Option<Key>>;

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
pub(crate) struct ChildAccessErr {
    pub(crate) children: Children,
    pub(crate) accessor: ChildAccessor,
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
    Indices {
        greatest: usize,
    },
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ChildAccessor {
    Index(usize),
    Field(String), // TODO!
}

impl ChildAccessor {
    pub fn is_field(&self) -> bool {
        matches!(self, Self::Field(_))
    }
    pub fn is_index(&self) -> bool {
        matches!(self, Self::Index(_))
    }
    pub fn index(&self) -> Option<usize> {
        match self {
            Self::Index(idx) => Some(*idx),
            Self::Field(_) => None,
        }
    }
    pub fn field(&self) -> Option<String> {
        match self {
            Self::Index(_) => None,
            Self::Field(field) => Some(field.clone()),
        }
    }
}

impl Arity {
    pub fn for_tuple(of_size: usize) -> Self {
        Arity::Indices { greatest: of_size }
    }

    pub fn for_struct(with_fields: HashSet<String>) -> Self {
        Arity::Fields(with_fields)
    }
}
