use crate::keys::TcKey;
use crate::types::{Abstract, TcMonad};
use crate::Constraint;
use ena::unify::{InPlace, InPlaceUnificationTable, Snapshot, UnificationTable, UnifyValue as EnaValue};
use std::collections::HashMap;
use std::fmt::{Debug, Error, Formatter};
use std::hash::Hash;
use std::slice::Iter;

/// Represents a type checker.
/// The main struct for the type checking procedure.
/// It manages a set of abstract types in a lattice-like structure and perform a union-find procedure to derive
/// the least concrete abstract type that satisfies a defined set of constraints.
/// Each abstract type is referred to with a key assigned by the `TypeChecker`
///
/// The `TypeChecker` allows for the creation of keys and imposition of constraints on them,
/// refer to `TypeChecker::new_{term/var}_key(&mut self)` and
/// `TypeChecker::impose(&mut self, constr: Constraint<Key>)`, respectively.
pub struct TypeChecker<AbsTy: Abstract, Var: TcVar> {
    store: InPlaceUnificationTable<TcKey<AbsTy>>,
    keys: Vec<TcKey<AbsTy>>,
    snapshots: Vec<Snapshot<InPlace<TcKey<AbsTy>>>>,
    variables: HashMap<Var, TcKey<AbsTy>>,
    monads: Vec<TcMonad<AbsTy>>,
}

impl<AbsTy: Abstract, Var: TcVar> Debug for TypeChecker<AbsTy, Var> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(
            f,
            "TypeChecker: [\n\tstore: {:?}, \n\tkeys: {:?}, \n\tsnapshots: {}\n]",
            self.store,
            self.keys,
            self.snapshots.len()
        )
    }
}

impl<AbsTy: Abstract, Var: TcVar> Default for TypeChecker<AbsTy, Var> {
    fn default() -> Self {
        TypeChecker::new()
    }
}

/// Represents a re-usable variable in the type checking procedure.  TcKeys for variables will be managed by the
/// `TypeChecker` to avoid duplication.
pub trait TcVar: Eq + Hash + Clone {}

impl<A: Abstract> From<A> for TcValue<A> {
    fn from(a: A) -> Self {
        TcValue(a)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TcValue<A: Abstract>(A);

impl<A: Abstract> Abstract for TcValue<A> {
    type Error = A::Error;
    type Variant = A::Variant;

    fn unconstrained() -> Self {
        TcValue(A::unconstrained())
    }

    fn meet(self, other: Self) -> Result<Self, Self::Error> {
        self.0.meet(other.0).map(TcValue)
    }
}

impl<A: Abstract> EnaValue for TcValue<A> {
    type Error = A::Error;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
        value1.clone().meet(value2.clone())
    }
}

// %%%%%%%%%%% PUBLIC INTERFACE %%%%%%%%%%%
impl<AbsTy: Abstract, Var: TcVar> TypeChecker<AbsTy, Var> {
    /// Creates a new, empty `TypeChecker`.  
    pub fn new() -> Self {
        TypeChecker {
            store: UnificationTable::new(),
            keys: Vec::new(),
            snapshots: Vec::new(),
            variables: HashMap::new(),
            monads: Vec::new(),
        }
    }
    //
    // /// Returns a view on the current state of `self`.  Returns a mapping of all keys known to
    // /// `self` to the `Key::Value` associated with it.
    // pub fn get_type_table(&mut self) -> Vec<(TcKey<AbsTy>, AbsTy)> {
    //     let keys = self.keys.clone();
    //     keys.into_iter().map(|key| (key, self.get_type(key))).collect()
    // }

    /// Creates a new unconstrained variable that can be referred to using the returned
    /// `TcKey`.  The current state of it can be accessed using
    /// `TypeChecker::get_type(TcKey)` and constraints can be imposed using
    /// `TypeChecker::impose(Constraint)`.
    /// `TcKey` provides means to create such `Constraints`.
    /// This key ought to represent a non-reusable term rather than a variable; refer to
    /// `TypeChecker::new_var_key(Var)`.
    pub fn new_term_key(&mut self) -> TcKey<AbsTy> {
        let new = TcKey::new(self.store.new_key(TcValue::unconstrained()).ix);
        self.keys.push(new);
        new
    }

    /// Returns a key that is associated with the passed variable.  If no such key exists, an
    /// unconstrained key is created and returned.  Otherwise, the respective associated key
    /// will be returned.
    /// Constraints on the key can be imposed using `TypeChecker::impose(Constraint)`.
    /// `TcKey` provides means to create such `Constraints`.
    /// This key ought to represent a reusable variable rather than a term; refer to
    /// `TypeChecker::new_term_key()`.
    pub fn get_var_key(&mut self, var: &Var) -> TcKey<AbsTy> {
        // Avoid cloning `var` by forgoing the `entry` function if possible.
        if let Some(tck) = self.variables.get(var) {
            *tck
        } else {
            let key = self.new_term_key();
            *self.variables.entry(var.clone()).or_insert(key)
        }
    }

    pub fn new_monad_key(&mut self, variant: AbsTy::Variant) -> TcMonad<AbsTy> {
        let res = TcMonad::new(self.new_term_key(), self.new_term_key(), variant);
        self.monads.push(res);
        res
    }

    /// Imposes `constr` on the current state of the type checking procedure. This may or may not change the abstract
    /// types of some keys.
    /// This process might entail that several values need to be met.  The evaluation is lazy, i.e. it stops the
    /// entire process as soon as a single meet fails, leaving all other meet operations unattempted.  This potentially
    /// shadows additional type errors!
    pub fn impose(&mut self, constr: Constraint<AbsTy>) -> Result<(), AbsTy::Error> {
        match constr {
            Constraint::EqKey(key1, key2) => self.store.unify_var_var(key1, key2),
            Constraint::EqAbs(key, ty) => self.store.unify_var_value(key, TcValue(ty)),
        }
    }

    /// Returns an iterator over all keys currently present in the type checking procedure.
    pub fn keys(&self) -> Iter<TcKey<AbsTy>> {
        self.keys.iter()
    }

    // /// Commits to the last snapshot taken with `TypeChecker::snapshot(&mut self)`.
    // /// For committing to a specific snapshot, refer to `TypeChecker::commit_to(&mut self, Snapshot<...>)`.
    // pub fn commit_last_ss(&mut self) {
    //     let latest = self.snapshots.pop().expect("Cannot commit to a snapshot without taking one.");
    //     self.store.commit(latest);
    // }
    //
    // /// Commits to `snapshot`.
    // /// For committing to the last snapshot taken, refer to `TypeChecker::commit_last_ss(&mut self)`.
    // pub fn commit_to(&mut self, snapshot: Snapshot<InPlace<TcKey<AbsTy>>>) {
    //     self.store.commit(snapshot);
    // }
    //
    // /// Rolls back to the last snapshot taken with `TypeChecker::snapshot(&mut self)`.
    // /// For rolling back to a specific snapshot, refer to `TypeChecker::rollback_to(&mut self, Snapshot<...>).`
    // pub fn rollback_to_last_ss(&mut self) {
    //     let latest = self.snapshots.pop().expect("Cannot roll back to a snapshot without taking one.");
    //     self.store.rollback_to(latest)
    // }
    //
    // /// Rolls back to `snapshot`.
    // /// For rolling back to the last snapshot taken, refer to `TypeChecker::rollback_to(&mut self, Snapshot<...>).`
    // pub fn rollback_to(&mut self, snapshot: Snapshot<InPlace<TcKey<AbsTy>>>) {
    //     self.store.rollback_to(snapshot)
    // }
}
