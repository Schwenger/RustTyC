use crate::Constraint;
use ena::unify::{
    InPlace, InPlaceUnificationTable, Snapshot, UnificationTable, UnifyKey as EnaKey, UnifyValue as EnaValue,
};
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
pub struct TypeChecker<Key: EnaKey, Var: TcVar>
where
    Key::Value: Abstract,
{
    store: InPlaceUnificationTable<Key>,
    keys: Vec<TcKey<Key>>,
    snapshots: Vec<Snapshot<InPlace<Key>>>,
    variables: HashMap<Var, TcKey<Key>>,
}

impl<Key: EnaKey, Var: TcVar> Debug for TypeChecker<Key, Var>
where
    Key::Value: Abstract,
{
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

/// Represents a re-usable variable in the type checking procedure.  TcKeys for variables will be managed by the
/// `TypeChecker` to avoid duplication.
pub trait TcVar: Eq + Hash + Clone {}

/// A `TcKey` references an abstract type object during the type checking procedure.
/// It can be created via `TypeChecker::new_{term/var}_ key` and provides functions creating `Constraint`s that
/// impose rules on type variables, e.g. by constraining single types are relating others.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TcKey<Key: EnaKey>(Key)
where
    Key::Value: Abstract;

/// The main trait representing types throughout the type checking procedure.
/// It is bound to the type checker as the `Value` for the `Key` parameter.  As such, it needs to implement
/// `EnaValue`.
pub trait Abstract: Eq + Sized {
    /// Returns an unconstrained abstract type.
    fn unconstrained() -> Self;

    /// Determines if an element is unconstrained.
    fn is_unconstrained(&self) -> bool {
        self == &Self::unconstrained()
    }
}

impl<Key: EnaKey, Var: TcVar> Default for TypeChecker<Key, Var>
where
    Key::Value: Abstract,
{
    fn default() -> Self {
        TypeChecker::new()
    }
}

// %%%%%%%%%%% PUBLIC INTERFACE %%%%%%%%%%%
impl<Key: EnaKey, Var: TcVar> TypeChecker<Key, Var>
where
    Key::Value: Abstract,
{
    /// Creates a new, empty `TypeChecker`.  
    pub fn new() -> Self {
        TypeChecker {
            store: UnificationTable::new(),
            keys: Vec::new(),
            snapshots: Vec::new(),
            variables: HashMap::new(),
        }
    }

    /// Returns a view on the current state of `self`.  Returns a mapping of all keys known to
    /// `self` to the `Key::Value` associated with it.
    pub fn get_type_table(&mut self) -> Vec<(TcKey<Key>, Key::Value)> {
        let keys = self.keys.clone();
        keys.into_iter().map(|key| key).map(|key| (key, self.get_type(key))).collect()
    }

    /// Creates a new unconstrained variable that can be referred to using the returned
    /// `TcKey`.  The current state of it can be accessed using
    /// `TypeChecker::get_type(TcKey)` and constraints can be imposed using
    /// `TypeChecker::impose(Constraint)`.
    /// `TcKey` provides means to create such `Constraints`.
    /// This key ought to represent a non-reusable term rather than a variable; refer to
    /// `TypeChecker::new_var_key(Var)`.
    pub fn new_term_key(&mut self) -> TcKey<Key> {
        let new = TcKey(self.store.new_key(<Key::Value as Abstract>::unconstrained()));
        self.keys.push(new);
        new
    }

    /// Creates a new unconstrained variable that can be referred to using the returned
    /// `TcKey`.  The current state of it can be accessed using
    /// `TypeChecker::get_type(TcKey)` and constraints can be imposed using
    /// `TypeChecker::impose(Constraint)`.
    /// `TcKey` provides means to create such `Constraints`.
    /// This key ought to represent a reusable variable rather than a term; refer to
    /// `TypeChecker::new_term_key()`.
    pub fn new_var_key(&mut self, var: &Var) -> TcKey<Key> {
        // Avoid cloning `var` by forgoing the `entry` function if possible.
        if let Some(tck) = self.variables.get(var) {
            *tck
        } else {
            let key = self.new_term_key();
            *self.variables.entry(var.clone()).or_insert(key)
        }
    }

    /// Imposes `constr` on the current state of the type checking procedure. This may or may not change the abstract
    /// types of some keys.
    /// This process might entail that several values need to be met.  The evaluation is lazy, i.e. it stops the
    /// entire process as soon as a single meet fails, leaving all other meet operations unattempted.  This potentially
    /// shadows additional type errors!
    pub fn impose(&mut self, constr: Constraint<Key>) -> Result<(), <Key::Value as EnaValue>::Error> {
        use Constraint::*;
        match constr {
            MoreConcreteThanAll { target, args } => {
                // Look-up all constrains of args, bound `target` by each.
                for arg in args {
                    self.store.unify_var_var(target.0, arg.0)?;
                }
            }
            MoreConcreteThanType { target, args } => {
                for bound in args {
                    dbg!(self.get_type(target));
                    dbg!(&bound);
                    self.store.unify_var_value(target.0, bound)?;
                }
            }
        }
        Ok(())
    }

    /// Returns the abstract type associated with `key`.
    pub fn get_type(&mut self, key: TcKey<Key>) -> Key::Value {
        self.store.probe_value(key.0)
    }

    /// Returns an iterator over all keys currently present in the type checking procedure.
    pub fn keys(&self) -> Iter<TcKey<Key>> {
        self.keys.iter()
    }

    /// Takes a snapshot and stores it internally.  Can be rolled back via `TypeChecker::rollback(&mut self)` and committed via
    /// `TypeChecker::commit_last_ss(&mut self)`.
    /// When external access to the snapshot is desired or necessary, refer to
    /// `TypeChecker::take_snapshot(&mut self) -> Snapshot<...>`.
    pub fn snapshot(&mut self) {
        self.snapshots.push(self.store.snapshot());
    }

    /// Takes and returns a snapshot that needs to be managed externally.  Can be rolled back via
    /// `TypeChecker::rollback_to(&mut self, Snapshot<...>)` and committed via
    /// `TypeChecker::commit_to(&mut self, Snapshot<...>)`.
    /// When external management is undesired or unnecessary, refer to `TypeChecker::snapshot(&mut self)`.
    pub fn take_snapshot(&mut self) -> Snapshot<InPlace<Key>> {
        self.store.snapshot()
    }

    /// Commits to the last snapshot taken with `TypeChecker::snapshot(&mut self)`.
    /// For committing to a specific snapshot, refer to `TypeChecker::commit_to(&mut self, Snapshot<...>)`.
    pub fn commit_last_ss(&mut self) {
        let latest = self.snapshots.pop().expect("Cannot commit to a snapshot without taking one.");
        self.store.commit(latest);
    }

    /// Commits to `snapshot`.
    /// For committing to the last snapshot taken, refer to `TypeChecker::commit_last_ss(&mut self)`.
    pub fn commit_to(&mut self, snapshot: Snapshot<InPlace<Key>>) {
        self.store.commit(snapshot);
    }

    /// Rolls back to the last snapshot taken with `TypeChecker::snapshot(&mut self)`.
    /// For rolling back to a specific snapshot, refer to `TypeChecker::rollback_to(&mut self, Snapshot<...>).`
    pub fn rollback_to_last_ss(&mut self) {
        let latest = self.snapshots.pop().expect("Cannot roll back to a snapshot without taking one.");
        self.store.rollback_to(latest)
    }

    /// Rolls back to `snapshot`.
    /// For rolling back to the last snapshot taken, refer to `TypeChecker::rollback_to(&mut self, Snapshot<...>).`
    pub fn rollback_to(&mut self, snapshot: Snapshot<InPlace<Key>>) {
        self.store.rollback_to(snapshot)
    }
}
