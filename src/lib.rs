mod lattice;
#[cfg(test)]
mod tests;

pub use lattice::{constraints::TypeConstraint, reification::*, AbstractType, TypeCheckKey, TypeChecker};
