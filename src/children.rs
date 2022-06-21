use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use crate::TcKey;

/// Represents the current children of a type.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Children {
    /// There are no known children yet.
    Unknown,
    /// The type doesn't have any children.
    None,
    /// The type has indexed children represented by the collection within.
    Indexed(Vec<Option<TcKey>>),
    /// The type has named children represented by the collection within.
    Named(HashMap<usize, Option<TcKey>>),
}

impl Children {
    pub(crate) fn len(&self) -> Option<usize> {
        match self {
            Children::Unknown => None,
            Children::None => Some(0),
            Children::Indexed(c) => Some(c.len()),
            Children::Named(c) => Some(c.len()),
        }
    }

    pub(crate) fn is_indexed(&self) -> bool {
        matches!(self, Children::Indexed(_))
    }

    pub(crate) fn is_named(&self) -> bool {
        matches!(self, Children::Named(_))
    }

    pub(crate) fn indexed(&self) -> Option<&Vec<Option<TcKey>>> {
        match self {
            Children::Indexed(res) => Some(res),
            Children::Unknown | Children::Named(_) | Children::None => None,
        }
    }

    pub(crate) fn indexed_mut(&mut self) -> Option<&mut Vec<Option<TcKey>>> {
        match self {
            Children::Indexed(res) => Some(res),
            Children::Unknown => {
                *self = Children::Indexed(vec![]);
                self.indexed_mut()
            }
            Children::Named(_) | Children::None => None,
        }
    }

    pub(crate) fn named(&self) -> Option<&HashMap<usize, Option<TcKey>>> {
        match self {
            Children::Named(res) => Some(res),
            Children::Unknown | Children::Indexed(_) | Children::None => None,
        }
    }

    pub(crate) fn named_mut(&mut self) -> Option<&mut HashMap<usize, Option<TcKey>>> {
        match self {
            Children::Named(res) => Some(res),
            Children::Unknown => {
                *self = Children::Named(HashMap::new());
                self.named_mut()
            }
            Children::Indexed(_) | Children::None => None,
        }
    }

    pub(crate) fn to_constraint(&self) -> ChildConstraint {
        match self {
            Children::Unknown => ChildConstraint::Unconstrained,
            Children::None => ChildConstraint::NoChildren,
            Children::Indexed(c) => ChildConstraint::Indexed(c.len()),
            Children::Named(c) => ChildConstraint::Named(c.keys().copied().collect()),
        }
    }
}


#[derive(Debug, Clone)]
/// Represents the current (incomplete) information the type checker has about the children of a type.
pub enum ChildConstraint {
    /// The type should not have any children.
    NoChildren,
    /// There is no information about the children yet. They can be either `NoChildren`, `Indexed` or `Named`
    Unconstrained,
    /// Children are expected to be accessed through indices.
    /// The number represents the least amount of children the type will have.
    Indexed(usize),
    /// Children are expected to be accessed by names.
    /// The HashSet represents the minimum set of fields required.
    Named(HashSet<usize>),
}

impl ChildConstraint {
    /// The least number of children there are.
    pub fn len(&self) -> usize {
        match self {
            ChildConstraint::Unconstrained => 0,
            ChildConstraint::NoChildren => 0,
            ChildConstraint::Indexed(size) => *size,
            ChildConstraint::Named(set) => set.len(),
        }
    }

    /// Expects the children to be accessed by name and returns the HashSet representing the minimum set of fields the type will have.
    /// Panics if th children are not accessed by name.
    pub fn names(&self) -> &HashSet<usize> {
        match self {
            ChildConstraint::Named(set) => set,
            ChildConstraint::Indexed(_) | ChildConstraint::Unconstrained | ChildConstraint::NoChildren => {
                panic!("Child constraint is not named")
            }
        }
    }

    /// Expects the children to be accessed through indices and returns least amount of children the type will have.
    /// Panics if th children are not accessed through indices.
    pub fn index(&self) -> usize {
        match self {
            ChildConstraint::Indexed(idx) => *idx,
            ChildConstraint::Named(_) | ChildConstraint::Unconstrained | ChildConstraint::NoChildren => {
                panic!("Child constraint is not named")
            }
        }
    }
}

/// Represents the arity of a [Variant] or [ContextSensitiveVariant].
/// The arity of a variant corresponds directly to the [ChildConstraint] of a type in the following manner:
/// * `Arity::Variable <=> ChildConstraint::Unconstrained`
/// * `Arity::None <=> ChildConstraint::NoChildren`
/// * `Arity::FixedIndexed(idx) <=> ChildConstraint::Indexed(idx)`
/// * `Arity::FixedNamed(names) <=> ChildConstraint::Named(names)`
#[derive(Debug, Clone)]
pub enum Arity<R: Debug + Clone + Hash> {
    /// The Type should have no children at all.
    None,
    /// The arity is variable, i.e., it does not have a specific value.
    Variable,
    /// The arity is fixed and the children are accessed by index.
    FixedIndexed(usize),
    /// The arity is fixed and the children are accessed by name.
    FixedNamed(HashSet<R>),
}

impl<R: Debug + Clone + Hash> Arity<R> {
    /// Transform `self` into an option, i.e., it will yield a `Some` with its arity if defined and `None` otherwise.
    pub(crate) fn to_opt(&self) -> Option<usize> {
        match self {
            Arity::Variable => None,
            Arity::None => Some(0),
            Arity::FixedIndexed(n) => Some(*n),
            Arity::FixedNamed(s) => Some(s.len()),
        }
    }
}

impl Arity<String> {
    /// Substitutes the strings in case of `FixedNamed` with usizes according to the given map.
    pub(crate) fn substitute(&self, child_ids: &HashMap<String, usize>) -> Arity<usize> {
        match self {
            Arity::Variable => Arity::Variable,
            Arity::None => Arity::None,
            Arity::FixedIndexed(idx) => Arity::FixedIndexed(*idx),
            Arity::FixedNamed(names) => Arity::FixedNamed(names.iter().map(|k| child_ids[k]).collect()),
        }
    }
}
impl From<Arity<usize>> for ChildConstraint {
    fn from(a: Arity<usize>) -> Self {
        match a {
            Arity::Variable => ChildConstraint::Unconstrained,
            Arity::None => ChildConstraint::NoChildren,
            Arity::FixedIndexed(idx) => ChildConstraint::Indexed(idx),
            Arity::FixedNamed(names) => ChildConstraint::Named(names),
        }
    }
}