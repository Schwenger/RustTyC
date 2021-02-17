use crate::types::{Constructable, PreliminaryTypeTable, TypeTable, Variant};
use crate::{constraint_graph::ConstraintGraph, types::ConstructionErr};
use crate::{
    keys::{Constraint, TcKey},
    types::Preliminary,
};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

/// Represents a re-usable variable in the type checking procedure.  
///
/// [`TcKey`](struct.TcKey.html)s for variables will be managed by the `TypeChecker`.
pub trait TcVar: Debug + Eq + Hash + Clone {}

/// The `TypeChecker` is the main interaction point for the type checking procedure.
///
/// The `TypeChecker` is the main interaction point for the type checking procedure.
/// It provides functionality to obtain `TcKeys`, manage variables, impose constraints, and generate a type table.
///
/// # Related Data Structures
/// * [`TcKey`](struct.TcKey.html) represent different entities during the type checking procedure such as variables or terms.
/// * [`TcVar`](trait.TcVar.html) represent variables in the external structure, e.g. in the AST that is type checked.
/// A variable has exactly one associated key, even if it occurs several times in the external data structure.
/// The type checker manages keys for variables.
/// * `Constraint`s represent dependencies between keys and types.  They can only be created using [`TcKey`](struct.TcKey.html).
/// * [`Variant`](trait.Variant.html) is an external data type that constitutes a potentially unresolved type.
/// * [`TcErr`](enum.TcErr.html) is a wrapper for `Variant::Err` that contains additional information on what went wrong.
/// * [`VariantTypeTable`](struct.VariantTypeTable.html) maps keys to Variant types.
///
/// # Process
/// In the first step after creation, the `TypeChecker` generates keys and collects information.  It may already resolve some constraints
/// and reveal contradictions.  This prompts it to return a negative result with a [`TcErr`](enum.TcErr.html).
/// When all information is collected, it resolves them and generates a type table that contains the least restrictive Variant type for
/// each registered key.
///
/// ## Note:
/// The absence of errors does not entail that a constraint can be satisfied.  Only the successful generation of a
/// type table indicates that all constraints can be satisfied.
///
/// # Example
/// See [`crate documentation`](index.html).
#[derive(Debug, Clone)]
pub struct TypeChecker<V: Variant, Var: TcVar> {
    variables: HashMap<Var, TcKey>,
    graph: ConstraintGraph<V>,
}

impl<V: Variant, Var: TcVar> Default for TypeChecker<V, Var> {
    fn default() -> Self {
        TypeChecker::new()
    }
}

// %%%%%%%%%%% PUBLIC INTERFACE %%%%%%%%%%%
impl<V: Variant, Var: TcVar> TypeChecker<V, Var> {
    /// Creates a new, empty `TypeChecker`.  
    pub fn new() -> Self {
        TypeChecker { variables: HashMap::new(), graph: ConstraintGraph::new() }
    }

    /// Generates a new key representing a term.  
    pub fn new_term_key(&mut self) -> TcKey {
        self.graph.create_vertex()
    }

    /// Manages keys for variables.  It checks if `var` already has an associated key.
    /// If so, it returns the key.  Otherwise, it generates a new one.
    pub fn get_var_key(&mut self, var: &Var) -> TcKey {
        // Avoid cloning `var` by forgoing the `entry` function if possible.
        if let Some(tck) = self.variables.get(var) {
            *tck
        } else {
            let key = self.new_term_key();
            self.variables.insert(var.clone(), key);
            key
        }
    }

    /// Provides a key to the `nth` child of the type behind `parent`.
    /// This imposes the restriction that `parent` resolves to a type that has at least `nth` dependent sub-types.
    /// If this imposition immediately leads to a contradiction, an [`TcErr`](enum.TcErr.html) is returned.
    /// Contradictions due to this constraint may only occur later when resolving further constraints.
    /// Calling this function several times on a parent with the same `nth` results in the same key.
    pub fn get_child_key(&mut self, parent: TcKey, nth: usize) -> Result<TcKey, TcErr<V>> {
        self.graph.nth_child(parent, nth)
    }

    /// Imposes a constraint on keys.  They can be obtained by using the associated functions of [`TcKey`](struct.TcKey.html).
    /// Returns a [`TcErr`](enum.TcErr.html) if the constraint immediately reveals a contradiction.
    pub fn impose(&mut self, constr: Constraint<V>) -> Result<(), TcErr<V>> {
        match constr {
            Constraint::Conjunction(cs) => cs.into_iter().try_for_each(|c| self.impose(c))?,
            Constraint::Equal(a, b) => self.graph.equate(a, b)?,
            Constraint::MoreConc { target, bound } => self.graph.add_upper_bound(target, bound),
            Constraint::MoreConcExplicit(target, bound) => self.graph.explicit_bound(target, bound)?,
        }
        Ok(())
    }

    /// Lifts a collection of keys as children into a certain recursive variant.
    pub fn lift_into(&mut self, variant: V, mut sub_types: Vec<TcKey>) -> TcKey {
        self.lift_partially(variant, sub_types.drain(..).map(Some).collect())
    }
    /// Lifts a collection of keys as subset of children into a certain recursive variant.
    pub fn lift_partially(&mut self, variant: V, sub_types: Vec<Option<TcKey>>) -> TcKey {
        self.graph.lift(variant, sub_types)
    }

    /// Returns an iterator over all keys currently present in the type checking procedure.
    pub fn all_keys(&self) -> impl Iterator<Item = TcKey> + '_ {
        self.graph.all_keys()
    }

    /// Finalizes the type check procedure.
    /// Calling this function indicates that all relevant information was passed on to the type checker.
    /// It will attempt to resolve all constraints and return a type table mapping each registered key to its
    /// minimally constrained Variant type.
    /// If any constrained caused a contradiction, it will return a [`TcErr`]: ./TcErr.html containing information about it.
    pub fn type_check_preliminary(self) -> Result<PreliminaryTypeTable<V>, TcErr<V>> {
        self.graph.solve_preliminary()
    }
}

impl<V, Var: TcVar> TypeChecker<V, Var>
where
    V: Variant + Constructable,
{
    /// Finalizes the type check procedure.
    /// Calling this function indicates that all relevant information was passed on to the type checker.
    /// It will attempt to resolve all constraints and return a type table mapping each registered key to its
    /// minimally constrained Variant type.
    /// If any constrained caused a contradiction, it will return a [`TcErr`]: ./TcErr.html containing information about it.
    pub fn type_check(self) -> Result<TypeTable<V>, TcErr<V>> {
        self.graph.solve()
    }
}

/// Represents an error during the type check procedure.
#[derive(Debug, Clone)]
pub enum TcErr<V: Variant> {
    /// Two keys were attempted to be equated and their underlying types turned out to be incompatible.
    /// Contains the two keys and the error that occurred when attempting to meet their Variant types.
    KeyEquation(TcKey, TcKey, V::Err),
    /// An explicit type bound imposed on a key turned out to be incompatible with the type inferred based on
    /// remaining information on the key.  Contains the key and the error that occurred when meeting the explicit
    /// bound with the inferred type.
    Bound(TcKey, Option<TcKey>, V::Err),
    /// This error occurs when a constraint accesses the `n`th child of a type and its variant turns out to only
    /// have `k < n` sub-types.
    /// Contains the affected key, its inferred or explicitly assigned variant, and the index of the child that
    /// was attempted to be accessed.
    ChildAccessOutOfBound(TcKey, V, usize),
    ArityMismatch {
        key: TcKey,
        variant: V,
        inferred_arity: usize,
        reported_arity: usize,
    },
    Construction(Preliminary<V>, ConstructionErr),
}
