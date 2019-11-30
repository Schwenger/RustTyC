mod lattice;
#[cfg(test)]
mod tests;

pub use lattice::{TypeChecker, TypeCheckKey, AbstractType, LowerBounded, constraints::TypeConstraint, reification::*};
