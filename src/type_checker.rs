use crate::constraint_graph::ConstraintGraph;
use crate::types::{Constructable, ContextSensitiveVariant, PreliminaryTypeTable, TypeTable, Variant};
use crate::{
    keys::{Constraint, TcKey},
    types::Preliminary,
};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

/// Represents a re-usable variable in the type checking procedure.
///
/// [TcKey]s for variables will be managed by the [TypeChecker].
pub trait TcVar: Debug + Eq + Hash + Clone {}

/// The [TypeChecker] is the main interaction point for the type checking procedure.
///
/// The [TypeChecker] is the main interaction point for the type checking procedure.
/// It provides functionality to obtain [TcKey]s, manage variables, impose constraints, and generate a type table.
///
/// # Related Data Structures
/// * [TcKey] represent different entities during the type checking procedure such as variables or terms.
/// * [TcVar] represent variables in the external structure, e.g. in the AST that is type checked.
/// A variable has exactly one associated key, even if it occurs several times in the external data structure.
/// The type checker manages keys for variables.
/// * `Constraint`s represent dependencies between keys and types.  They can only be created using [TcKey]s.
/// * [Variant] is an external data type that constitutes a potentially unresolved type.
/// * [TcErr] is a wrapper for [Variant::Err] that contains additional information on what went wrong.
/// * [TypeTable] maps keys to [Constructable::Type] if [Variant] implements [Constructable].
/// * [PreliminaryTypeTable] maps keys to [Preliminary].  This is only useful if [Variant] does not implement [Constructable]
///
/// # Process
/// In the first step after creation, the [TypeChecker] generates keys and collects information.  It may already resolve some constraints
/// and reveal contradictions.  This prompts it to return a negative result with a [TcErr].
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
pub struct TypeChecker<V: ContextSensitiveVariant, Var: TcVar> {
    variables: HashMap<Var, TcKey>,
    graph: ConstraintGraph<V>,
    context: V::Context,
}

impl<V: Variant, Var: TcVar> Default for TypeChecker<V, Var> {
    fn default() -> Self {
        TypeChecker::new()
    }
}

/// A convenience struct representing non-existant variables during a type check precedure.  Can and should not be accessed, modified, or created.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct NoVars {
    unit: (), // Prevents external creation.
}
impl TcVar for NoVars {}

/// A [TypeChecker] instance in case no variables are required.
pub type VarlessTypeChecker<V> = TypeChecker<V, NoVars>;
impl<V: Variant> TypeChecker<V, NoVars> {
    /// Instantiates a new, empty type checker that does not require variables.
    pub fn without_vars() -> VarlessTypeChecker<V> {
        TypeChecker::new()
    }
}

// %%%%%%%%%%% PUBLIC INTERFACE %%%%%%%%%%%
impl<V: Variant, Var: TcVar> TypeChecker<V, Var> {
    /// Creates a new, empty type checker.
    pub fn new() -> Self {
        Self::with_context(())
    }
}
impl<V: ContextSensitiveVariant, Var: TcVar> TypeChecker<V, Var> {
    /// Creates a new, empty type checker with the given context.
    pub fn with_context(context: V::Context) -> Self {
        TypeChecker { variables: HashMap::new(), graph: ConstraintGraph::new(), context }
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
            let _ = self.variables.insert(var.clone(), key);
            key
        }
    }

    /// Provides a key to the `nth` child of the type behind `parent`.
    /// This imposes the restriction that `parent` resolves to a type that has at least an arity of `nth`.
    /// If this imposition immediately leads to a contradiction, a [TcErr] is returned.
    /// Contradictions due to this constraint may only occur later when resolving further constraints.
    /// Calling this function several times on a parent with the same `nth` results in the same key.
    pub fn get_child_key(&mut self, parent: TcKey, nth: usize) -> Result<TcKey, TcErr<V>> {
        let TypeChecker { graph, variables: _, context } = self;
        let key = graph.nth_child(parent, nth, context)?;
        Ok(key)
    }

    /// Imposes a constraint on keys.  They can be obtained by using the associated functions of [TcKey].
    /// Returns a [TcErr] if the constraint immediately reveals a contradiction.
    pub fn impose(&mut self, constr: Constraint<V>) -> Result<(), TcErr<V>> {
        match constr {
            Constraint::Conjunction(cs) => cs.into_iter().try_for_each(|c| self.impose(c))?,
            Constraint::Equal(a, b) => {
                let TypeChecker { graph, variables: _, context } = self;
                graph.equate(a, b, context)?;
            }
            Constraint::MoreConc { target, bound } => self.graph.add_upper_bound(target, bound),
            Constraint::MoreConcExplicit(target, bound) => {
                let TypeChecker { graph, variables: _, context } = self;
                graph.explicit_bound(target, bound, context)?;
            }
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

    /// Updates the current context.
    ///
    /// Applies the `update` function to the context of the current typechecker.
    /// The function may mutate the context.
    ///
    /// # Warning
    /// This will not change any call retroactively, i.e. it only applies to future
    /// meet and equate calls.  Proceed with caution.
    pub fn update_context<F>(&mut self, update: F)
    where
        F: FnOnce(&mut V::Context),
    {
        update(&mut self.context);
    }

    /// Finalizes the type check procedure without constructing a full type table.  Refer to [TypeChecker::type_check] if [Variant] implements [Constructable].
    /// Calling this function indicates that all relevant information was passed on to the type checker.
    /// It will attempt to resolve all constraints and return a type table mapping each registered key to its minimally constrained [Variant]s.
    /// For recursive types, the respective [Preliminary] provides access to [crate::TcKey]s refering to their children.
    /// If any constrained caused a contradiction, it will return a [TcErr] containing information about it.
    pub fn type_check_preliminary(self) -> Result<PreliminaryTypeTable<V>, TcErr<V>> {
        let TypeChecker { graph, variables: _, context } = self;
        graph.solve_preliminary(context)
    }
}

impl<V, Var: TcVar> TypeChecker<V, Var>
where
    V: Constructable,
{
    /// Finalizes the type check procedure.
    /// Calling this function indicates that all relevant information was passed on to the type checker.
    /// It will attempt to resolve all constraints and return a type table mapping each registered key to its
    /// minimally constrained, constructed type, i.e. [Constructable::Type].  Refer to [TypeChecker::type_check_preliminary()] if [Variant] does not implement [Constructable].
    /// If any constrained caused a contradiction, it will return a [TcErr] containing information about it.
    pub fn type_check(self) -> Result<TypeTable<V>, TcErr<V>> {
        let TypeChecker { graph, variables: _, context } = self;
        graph.solve(context)
    }
}

/// Represents an error during the type check procedure.
#[derive(Debug, Clone)]
pub enum TcErr<V: ContextSensitiveVariant> {
    /// Two keys were attempted to be equated and their underlying types turned out to be incompatible.
    /// Contains the two keys and the error that occurred when attempting to meet their [ContextSensitiveVariant] types.
    KeyEquation(TcKey, TcKey, V::Err),
    /// An explicit type bound imposed on a key turned out to be incompatible with the type inferred based on
    /// remaining information on the key.  Contains the key and the error that occurred when meeting the explicit
    /// bound with the inferred type variant.
    Bound(TcKey, Option<TcKey>, V::Err),
    /// This error occurs when a constraint accesses the `n`th child of a type and its variant turns out to only
    /// have `k < n` sub-types.
    /// Contains the affected key, its inferred or explicitly assigned variant, and the index of the child that
    /// was attempted to be accessed.
    ChildAccessOutOfBound(TcKey, V, usize),
    /// This error occurs if the type checker inferred a specific arity but the variant reports a fixed arity that is lower than the inferred one.
    ArityMismatch {
        /// The key for which the mismatch was detected.
        key: TcKey,
        /// The variant with fixed arity.
        variant: V,
        /// The least required arity according to the type check procedure.
        inferred_arity: usize,
        /// The arity required according to the meet operation that created the variant.
        reported_arity: usize,
    },
    /// An error reporting a failed type construction.  Contains the affected key, the preliminary result for which the construction failed, and the
    /// error reported by the construction.
    Construction(TcKey, Preliminary<V>, V::Err),
    /// This error indicates that a variant requires children, for one of which the construction failed.
    /// Note that this can occur seemingly-spuriously, e.g., if a child needs to be present but there were no restrictions on said child.
    /// In this case, the construction attempts and might fail to construct a child out of a [ContextSensitiveVariant::top()].
    /// The error contains the affected key, the index of the child, the preliminary result of which a child construction failed, and the error
    /// reported by the construction of the child.
    ChildConstruction(TcKey, usize, Preliminary<V>, V::Err),
    /// This error reports cyclic non-equality dependencies in the constraint graph.
    /// Example: Key 1 is more concrete than Key 2, which is more concrete than Key 3, which is more concrete than Key 1.
    CyclicGraph,
}
