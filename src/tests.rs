use crate::lattice::reification::{Generalizable, ReificationError, TryReifiable};
use crate::lattice::{TypeChecker, UpperBounded};
use ena::unify::{UnifyKey, UnifyValue};
use std::cmp::max;

#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Ord, Eq, Hash)]
struct Key(u32);

#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Ord, Eq, Hash)]
enum AbstractType {
    Any,
    Fixed(u8, u8),
    Integer(u8),
    Error,
}

enum ConcreteType {
    Int128,
    FixedPointI64F64,
}

impl TryReifiable for AbstractType {
    type Reified = ConcreteType;

    fn try_reify(&self) -> Result<Self::Reified, ReificationError> {
        match self {
            AbstractType::Error => Err(ReificationError::Conflicting),
            AbstractType::Any => Err(ReificationError::TooGeneral),
            AbstractType::Integer(w) if *w <= 128 => Ok(ConcreteType::Int128),
            AbstractType::Integer(_) => Err(ReificationError::Conflicting),
            AbstractType::Fixed(i, f) if *i <= 64 && *f <= 64 => Ok(ConcreteType::FixedPointI64F64),
            AbstractType::Fixed(_, _) => Err(ReificationError::Conflicting),
        }
    }
}

impl Generalizable for ConcreteType {
    type Generalized = AbstractType;

    fn generalize(&self) -> Self::Generalized {
        match self {
            ConcreteType::FixedPointI64F64 => AbstractType::Fixed(64, 64),
            ConcreteType::Int128 => AbstractType::Integer(128),
        }
    }
}

impl UpperBounded for AbstractType {
    fn top() -> Self {
        AbstractType::Any
    }
}

impl crate::lattice::AbstractType for AbstractType {}

impl UnifyKey for Key {
    type Value = AbstractType;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Key(u)
    }

    fn tag() -> &'static str {
        "Key"
    }
}

impl UnifyValue for AbstractType {
    type Error = ();

    fn unify_values(left: &Self, right: &Self) -> Result<Self, <AbstractType as UnifyValue>::Error> {
        use crate::tests::AbstractType::*;
        match (left, right) {
            (Integer(l), Integer(r)) => Ok(Integer(max(*r, *l))),
            (Fixed(li, lf), Fixed(ri, rf)) => Ok(Fixed(max(*li, *ri), max(*lf, *rf))),
            (Fixed(i, f), Integer(u)) | (Integer(u), Fixed(i, f)) if *f == 0 => Ok(Integer(max(*i, *u))),
            (Fixed(i, f), Integer(u)) | (Integer(u), Fixed(i, f)) => Ok(Fixed(max(*i, *u), *f)),
            (Any, other) | (other, Any) => Ok(other.clone()),
            (Error, _) | (_, Error) => Err(()),
        }
    }
}

#[test]
fn create_different_types() {
    let mut tc: TypeChecker<Key> = TypeChecker::new();
    let first = tc.new_key();
    let second = tc.new_key();
    assert_ne!(first, second);
}

#[test]
fn bound_by_concrete_transitive() {
    let mut tc: TypeChecker<Key> = TypeChecker::new();
    let first = tc.new_key();
    let second = tc.new_key();
    tc.impose(second.bound_by_concrete(ConcreteType::Int128));
    tc.impose(first.more_concrete_than(second));
    assert_eq!(tc.get_type(first), tc.get_type(second));
}

#[test]
fn bound_then_refine() {
    let mut tc: TypeChecker<Key> = TypeChecker::new();
    let a = tc.new_key();
    let b = tc.new_key();
    let first_bound = AbstractType::Integer(3);
    let second_bound = AbstractType::Integer(8);
    tc.impose(b.bound_by_abstract(first_bound));
    tc.impose(a.more_concrete_than(b));
    tc.impose(b.bound_by_abstract(second_bound));
    assert_ne!(tc.get_type(a), tc.get_type(b));
    assert_eq!(tc.get_type(a), first_bound);
    assert_eq!(tc.get_type(b), second_bound);
}
