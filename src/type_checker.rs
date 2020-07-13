use crate::constraint_graph::ConstraintGraph;
use crate::keys::TcKey;
use crate::types::Abstract;
use crate::AbstractTypeTable;
use crate::Constraint;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

/// Represents a re-usable variable in the type checking procedure.  TcKeys for variables will be managed by the
/// `TypeChecker` to avoid duplication.
pub trait TcVar: Debug + Eq + Hash + Clone {}

/// Represents a type checker.
/// The main struct for the type checking procedure.
/// It manages a set of abstract types in a lattice-like structure and perform a union-find procedure to derive
/// the least concrete abstract type that satisfies a defined set of constraints.
/// Each abstract type is referred to with a key assigned by the `TypeChecker`
///
/// The `TypeChecker` allows for the creation of keys and imposition of constraints on them,
/// refer to `TypeChecker::new_{term/var}_key(&mut self)` and
/// `TypeChecker::impose(&mut self, constr: Constraint<Key>)`, respectively.
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
    pub fn test_peek(&mut self, key: TcKey) -> &AbsTy {
        self.peek(key)
    }

    /// Not necessarily the final result, use with caution!
    #[allow(dead_code)]
    fn peek(&mut self, key: TcKey) -> &AbsTy {
        self.graph.peek(key)
    }

    fn next_key(&self) -> TcKey {
        TcKey::new(self.keys.len())
    }

    pub fn new_term_key(&mut self) -> TcKey {
        let key = self.next_key();
        self.graph.add(key);
        self.keys.push(key); // probably unnecessary.
        key
    }

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

    pub fn get_child_key(&mut self, parent: TcKey, nth: usize) -> Result<TcKey, TcErr<AbsTy>> {
        let next_key = self.next_key(); // Cannot mutate the state!
        let child = self.graph.nth_child(parent, nth, || next_key)?;
        if child != next_key {
            self.keys.push(child);
        }
        Ok(child)
    }

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
    pub fn all_keys(&self) -> &[TcKey] {
        &self.keys
    }

    pub fn type_check(self) -> Result<AbstractTypeTable<AbsTy>, TcErr<AbsTy>> {
        self.graph.solve().map(AbstractTypeTable::from)
    }
}

#[derive(Debug, Clone)]
pub enum TcErr<AbsTy: Abstract> {
    KeyUnification(TcKey, TcKey, AbsTy::Err),
    TypeBound(TcKey, AbsTy::Err),
    TypeComparison(TcKey, TcKey, &'static str), // TODO: &str is insufficient
    DoubleVariantAssignment(TcKey, AbsTy::VariantTag, AbsTy::VariantTag),
    ChildAccessOutOfBound(AbsTy::VariantTag, usize),
}
