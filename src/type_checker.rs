use crate::constraint_graph::ConstraintGraph;
use crate::keys::{Constraint, TcKey};
use crate::types::{Abstract, AbstractTypeTable};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

/// Represents a re-usable variable in the type checking procedure.  
///
/// TcKeys for variables will be managed by the `TypeChecker`.
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
/// * [`Abstract`](trait.Abstract.html) is an external data type that constitutes a potentially unresolved type.
/// * [`TcErr`](struct.TcErr.html) is a wrapper for `Abstract::Err` that contains additional information on what went wrong.
/// * `[`AbstractTypeTable`](struct.AbstractTypeTable.html) maps keys to abstract types.
///
/// # Process
/// In the first step after creation, the `TypeChecker` generates keys and collects information.  It may already resolve some constraints
/// and reveal contradictions.  This prompts it to return a negative result with a [`TcErr`](struct.TcErr.html).
/// When all information is collected, it resolves them and generates a type table that contains the least restrictive abstract type for
/// each registered key.
///
/// ## Note:
/// The absence of errors does not entail that a constraint can be satisfied.  Only the successful generation of a
/// type table indicates that all constraints can be satisfied.
///
/// # Example
/// TODO: Example
#[derive(Debug, Clone)]
pub struct TypeChecker<AbsTy: Abstract, Var: TcVar> {
    variables: HashMap<Var, TcKey>,
    graph: ConstraintGraph<AbsTy>,
    keys: Vec<TcKey>,
}

impl<AbsTy: Abstract, Var: TcVar> Default for TypeChecker<AbsTy, Var> {
    fn default() -> Self {
        TypeChecker::new()
    }
}

// %%%%%%%%%%% PUBLIC INTERFACE %%%%%%%%%%%
impl<AbsTy: Abstract, Var: TcVar> TypeChecker<AbsTy, Var> {
    /// Creates a new, empty `TypeChecker`.  
    pub fn new() -> Self {
        TypeChecker { keys: Vec::new(), variables: HashMap::new(), graph: ConstraintGraph::new() }
    }

    #[cfg(test)]
    pub fn test_peek(&self, key: TcKey) -> &AbsTy {
        self.peek(key)
    }

    /// Not necessarily the final result, use with caution!
    #[allow(dead_code)]
    fn peek(&self, key: TcKey) -> &AbsTy {
        self.graph.peek(key)
    }

    fn next_key(&self) -> TcKey {
        TcKey::new(self.keys.len())
    }

    /// Generates a new key representing a term.  
    pub fn new_term_key(&mut self) -> TcKey {
        let key = self.next_key();
        self.graph.add(key);
        self.keys.push(key); // TODO: probably unnecessary.
        key
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
    /// If this imposition immediately leads to a contradiction, an [`TcErr`]: ./TcErr.html is returned.
    /// Contradictions due to this constraint may only occur later when resolving further constraints.
    /// Calling this function several times on a parent with the same `nth` results in the same key.
    pub fn get_child_key(&mut self, parent: TcKey, nth: usize) -> Result<TcKey, TcErr<AbsTy>> {
        let next_key = self.next_key(); // Cannot mutate the state!
        let child = self.graph.nth_child(parent, nth, || next_key)?;
        if child != next_key {
            self.keys.push(child);
        }
        Ok(child)
    }

    /// Imposes a constraint on keys.  They can be obtained by using the associated functions of `[`TcKey`]: ../keys/TcKey.html.
    /// Returns a [`TcErr`]: ./TcErr.html if the constraint immediately reveals a contradiction.
    pub fn impose(&mut self, constr: Constraint<AbsTy>) -> Result<(), TcErr<AbsTy>> {
        match constr {
            Constraint::Conjunction(cs) => {
                cs.into_iter().map(|c| self.impose(c)).collect::<Result<(), TcErr<AbsTy>>>()?
            }
            Constraint::Equal(a, b) => self.graph.equate(a, b),
            Constraint::MoreConc { target, bound } => self.graph.add_upper_bound(target, bound),
            Constraint::MoreConcExplicit(target, bound) => self.graph.explicit_bound(target, bound)?,
            Constraint::Variant(target, variant) => self.graph.register_variant(target, variant)?,
        }
        Ok(())
    }

    /// Returns an iterator over all keys currently present in the type checking procedure.
    pub fn all_keys(&self) -> impl Iterator<Item = &TcKey> {
        self.keys.iter()
    }

    /// Finalizes the type check procedure.
    /// Calling this function indicates that all relevant information was passed on to the type checker.
    /// It will attempt to resolve all constraints and return a type table mapping each registered key to its
    /// minimally constrained abstract type.  
    /// If any constrained caused a contradiction, it will return a [`TcErr`]: ./TcErr.html containing information about it.
    pub fn type_check(self) -> Result<AbstractTypeTable<AbsTy>, TcErr<AbsTy>> {
        self.graph.solve().map(AbstractTypeTable::from)
    }
}

/// Represents an error during the type check procedure.
#[derive(Debug, Clone)]
pub enum TcErr<AbsTy: Abstract> {
    /// Two keys were attempted to be equated and their underlying types turned out to be incompatible.
    /// Contains the two keys and the error that occurred when attempting to meet their abstract types.
    KeyEquation(TcKey, TcKey, AbsTy::Err),
    /// An explicit type bound imposed on a key turned out to be incompatible with the type inferred based on
    /// remaining information on the key.  Contains the key and the error that occurred when meeting the explicit
    /// bound with the inferred type.
    TypeBound(TcKey, AbsTy::Err),
    /// A type can ever only have at most one specific variant.  This error indicates that the constraints
    /// imply that the type needs to possess two variants at once.
    /// Contains the key and both variants.  These can be inferred or explicitly assigned variants.
    DoubleVariantAssignment(TcKey, AbsTy::VariantTag, AbsTy::VariantTag),
    /// This error occurs when a constraint accesses the `n`th child of a type and its variant turns out to only
    /// have `k < n` sub-types.
    /// Contains the affected key, its inferred or explicitly assigned variant, and the index of the child that
    /// was attempted to be accessed.
    ChildAccessOutOfBound(TcKey, AbsTy::VariantTag, usize),
}
