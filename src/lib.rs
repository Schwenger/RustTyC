mod lattice;
mod constraints;
mod reification;
#[cfg(test)]
mod tests;

pub use lattice::{AbstractType, TypeCheckKey, TypeChecker, UpperBounded};
pub use constraints::TypeConstraint;
pub use reification::{ReificationError, Generalizable, TryReifiable, Reifiable};
