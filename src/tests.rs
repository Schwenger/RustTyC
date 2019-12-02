use crate::lattice::{TypeChecker, UpperBounded};
use crate::{Generalizable, ReificationError, TryReifiable, TypeCheckKey};
use ena::unify::{UnifyKey, UnifyValue};
use std::cmp::max;
use std::convert::TryInto;

/// The key used for referencing objects with types.  Needs to implement `ena::UnifyKey`.
#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Ord, Eq, Hash)]
struct Key(u32);

/// Represents abstract types.  Needs to implement `ena::UnifyValue`.
#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Ord, Eq, Hash)]
enum AbstractType {
    Any,
    Fixed(u8, u8),
    Integer(u8),
    Numeric,
    Bool,
}

/// Concrete version of the abstract type.  Not strictly required, unlocks convenient type table extraction when
/// combined with `Generalizable` and `(Try)Reifiable`.
#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Ord, Eq, Hash)]
enum ConcreteType {
    Int128,
    FixedPointI64F64,
    Bool,
}

// ************ IMPLEMENTATION OF REQUIRED TRAITS ************ //

impl UpperBounded for AbstractType {
    fn top() -> Self {
        AbstractType::Any
    }
}

// Merely requires `UpperBounded`.
impl crate::lattice::AbstractType for AbstractType {}

impl UnifyKey for Key {
    type Value = AbstractType;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Key(u)
    }

    /// Doesn't really matter.
    fn tag() -> &'static str {
        "Key"
    }
}

/// Represents a type in a parametrized function; either refers to a type parameter or is an abstract type.
#[derive(Clone, Copy, Debug)]
enum ParamType {
    ParamId(usize),
    Abstract(AbstractType),
}

#[derive(Clone, Debug)]
enum Expression {
    /// Conditional expression.
    /// Requirement: `cond` more concrete than bool, `cons` and `alt` compatible.
    /// Returns: meet of `cons` and `alt`.
    Conditional {
        cond: Box<Expression>,
        cons: Box<Expression>,
        alt: Box<Expression>,
    },
    /// Polymorphic function f<T_1: C_1, ..., T_n: C_n>(p_1: C_{n+1}, ..., p_m: C_{n+m}) -> T
    /// Arguments:
    ///     `name` for illustration,
    ///     `param_constraints`: vector of parameters and their constraints if any, in this example vec![C_1, ..., C_n].
    ///     `arg_types`: vector of type constraints on the arguments, in this example vec![C_{n+1}, ..., C_{n+m}]. May refer to parameters.
    ///     `args`: vector containing all argument expressions.
    ///     `returns`: return type. May refer to a parameter.
    /// Requirement: each argument needs to comply with its constraint. If several arguments refer to the same parametric type, they need to be compliant.
    /// Returns: `returns`.
    PolyFn {
        name: &'static str,
        param_constraints: Vec<Option<AbstractType>>,
        args: Vec<(ParamType, Expression)>,
        returns: ParamType,
    },
    ConstInt(i128),
    ConstBool(bool),
    ConstFixed(i64, u64),
}

impl UnifyValue for AbstractType {
    type Error = ();

    /// Returns the meet of two abstract types.  Returns `Err` if they are incompatible.
    fn unify_values(left: &Self, right: &Self) -> Result<Self, <AbstractType as UnifyValue>::Error> {
        use crate::tests::AbstractType::*;
        match (left, right) {
            (Any, other) | (other, Any) => Ok(other.clone()),
            (Integer(l), Integer(r)) => Ok(Integer(max(*r, *l))),
            (Fixed(li, lf), Fixed(ri, rf)) => Ok(Fixed(max(*li, *ri), max(*lf, *rf))),
            (Fixed(i, f), Integer(u)) | (Integer(u), Fixed(i, f)) if *f == 0 => Ok(Integer(max(*i, *u))),
            (Fixed(i, f), Integer(u)) | (Integer(u), Fixed(i, f)) => Ok(Fixed(max(*i, *u), *f)),
            (Bool, Bool) => Ok(Bool),
            (Bool, _) | (_, Bool) => Err(()),
            (Numeric, Integer(w)) | (Integer(w), Numeric) => Ok(Integer(*w)),
            (Numeric, Fixed(i, f)) | (Fixed(i, f), Numeric) => Ok(Fixed(*i, *f)),
            (Numeric, Numeric) => Ok(Numeric),
        }
    }
}


impl TryReifiable for AbstractType {
    type Reified = ConcreteType;

    fn try_reify(&self) -> Result<Self::Reified, ReificationError> {
        match self {
            AbstractType::Any => Err(ReificationError::TooGeneral),
            AbstractType::Integer(w) if *w <= 128 => Ok(ConcreteType::Int128),
            AbstractType::Integer(_) => Err(ReificationError::Conflicting),
            AbstractType::Fixed(i, f) if *i <= 64 && *f <= 64 => Ok(ConcreteType::FixedPointI64F64),
            AbstractType::Fixed(_, _) => Err(ReificationError::Conflicting),
            AbstractType::Numeric => Err(ReificationError::TooGeneral), // Note: it would also make sense e.g. to default to an integer here.
            AbstractType::Bool => Ok(ConcreteType::Bool),
        }
    }
}

impl Generalizable for ConcreteType {
    type Generalized = AbstractType;

    fn generalize(&self) -> Self::Generalized {
        match self {
            ConcreteType::FixedPointI64F64 => AbstractType::Fixed(64, 64),
            ConcreteType::Int128 => AbstractType::Integer(128),
            ConcreteType::Bool => AbstractType::Bool,
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
    assert!(tc.impose(second.bound_by_concrete(ConcreteType::Int128)).is_ok());
    assert!(tc.impose(first.more_concrete_than(second)).is_ok());
    assert_eq!(tc.get_type(first), tc.get_type(second));
}

fn build_type_error() -> Expression {
    use Expression::*;
    // Build expression `4.3 + false`
    let const_false = ConstBool(false);
    let const43 = ConstFixed(4, 3);
    PolyFn {
        name: "addition", // Signature: +<T: Numeric>(T, T) -> T
        param_constraints: vec![Some(AbstractType::Numeric)],
        args: vec![(ParamType::ParamId(0), const43), (ParamType::ParamId(0), const_false)],
        returns: ParamType::ParamId(0),
    }
}

fn create_addition(lhs: Expression, rhs: Expression) -> Expression {
    Expression::PolyFn {
        name: "addition", // Signature: +<T: Numeric>(T, T) -> T
        param_constraints: vec![Some(AbstractType::Numeric)],
        args: vec![(ParamType::ParamId(0), lhs), (ParamType::ParamId(0), rhs)],
        returns: ParamType::ParamId(0),
    }
}

fn build_complex_expression_type_checks() -> Expression {
    use Expression::*;
    // Build expression `if true then 2.7^3 + 4.3 else 3`
    let const27 = ConstFixed(2, 7);
    let const3 = ConstInt(3);
    let const43 = ConstFixed(4, 3);
    let const_true = ConstBool(true);
    let exponentiation = PolyFn {
        name: "exponentiation", // Signature: +<T: Numeric>(T, Int<1>) -> T
        param_constraints: vec![Some(AbstractType::Numeric)],
        args: vec![(ParamType::ParamId(0), const27), (ParamType::Abstract(AbstractType::Integer(1)), const3.clone())],
        returns: ParamType::ParamId(0),
    };
    let addition = create_addition(exponentiation, const43);
    Conditional { cond: Box::new(const_true), cons: Box::new(addition), alt: Box::new(const3) }
}

/// This function traverses the expression tree.
/// It creates keys on the fly.  This is not possible for many kinds of type systems, in which case the functions
/// requires a context with a mapping of e.g. Variable -> Key.  The context can be built during a first pass over the
/// tree.
fn tc_expr(
    tc: &mut TypeChecker<Key>,
    expr: &Expression,
) -> Result<TypeCheckKey<Key>, <AbstractType as UnifyValue>::Error> {
    use Expression::*;
    let key_result = tc.new_key(); // will be returned
    match expr {
        ConstInt(c) => {
            let width = (128 - c.leading_zeros()).try_into().unwrap();
            tc.impose(key_result.bound_by_abstract(AbstractType::Integer(width)))?;
        }
        ConstFixed(i, f) => {
            let int_width = (64 - i.leading_zeros()).try_into().unwrap();
            let frac_width = (64 - f.leading_zeros()).try_into().unwrap();
            tc.impose(key_result.bound_by_abstract(AbstractType::Fixed(int_width, frac_width)))?;
        }
        ConstBool(_) => tc.impose(key_result.bound_by_concrete(ConcreteType::Bool))?,
        Conditional { cond, cons, alt } => {
            let key_cond = tc_expr(tc, cond)?;
            let key_cons = tc_expr(tc, cons)?;
            let key_alt = tc_expr(tc, alt)?;
            tc.impose(key_cond.bound_by_abstract(AbstractType::Bool))?;
            // Two things to note regarding the next operation:
            // The meet operation can fail.  Refer to `TypeChecker::check_conflicting(&mut self, TypeCheckerKey)` for
            // detecting this case.  Moreover, if it fails, the conflicting type is persisted in the type table and
            // propagated throughout the remaining type check.  If this is undesired due to the existence of an
            // alternative type rule, refer to the snapshotting mechanism.
            tc.impose(key_result.is_the_meet_of(&[key_cons, key_alt]))?;
        }
        PolyFn { name: _, param_constraints, args, returns } => {
            // Note: The following line cannot be replaced by `vec![param_constraints.len(); tc.new_key()]` as this
            // would copy the keys rather than creating new ones.
            let params: Vec<(Option<AbstractType>, TypeCheckKey<Key>)> =
                param_constraints.iter().map(|p| (*p, tc.new_key())).collect();
            dbg!(&params);
            for (arg_ty, arg_expr) in args {
                let arg_key = tc_expr(tc, arg_expr)?;
                match dbg!(arg_ty) {
                    ParamType::ParamId(id) => {
                        let (p_constr, p_key) = dbg!(params[*id]);
                        // We need to enforce that the parameter is more concrete than the passed argument and that the
                        // passed argument satisfies the constraints imposed on the parametric type.
                        tc.impose(p_key.more_concrete_than(arg_key))?;
                        if let Some(c) = p_constr {
                            tc.impose(dbg!(arg_key).bound_by_abstract(c))?;
                            println!("Argument is of abstract type {:?}.", tc.get_type(arg_key));
                        }
                    }
                    ParamType::Abstract(at) => tc.impose(arg_key.bound_by_abstract(*at))?,
                };
            }
            match returns {
                ParamType::Abstract(at) => tc.impose(key_result.bound_by_abstract(*at))?,
                ParamType::ParamId(id) => {
                    let (constr, key) = params[*id];
                    if let Some(c) = constr {
                        tc.impose(key_result.bound_by_abstract(c))?;
                    }
                    tc.impose(key_result.more_concrete_than(key))?;
                }
            }
        }
    }
    Ok(key_result)
}

#[test]
fn complex_type_check() {
    let expr = build_complex_expression_type_checks();
    let mut tc: TypeChecker<Key> = TypeChecker::new();
    let res = tc_expr(&mut tc, &expr);
    match res {
        Ok(key) => {
            let res_type = tc.get_type(key);
            // Expression `if true then 2.7^3 + 4.3 else 3` should yield type Fixed(3, 3) because the addition requires a
            // Fixed(2,3) and a Fixed(3,3), which results in a Fixed(3, 3).
            assert_eq!(res_type, AbstractType::Fixed(3, 3));
        }
        Err(_) => panic!("Unexpected type error!"),
    }
}

#[test]
fn failing_type_check() {
    let expr = build_type_error();
    let mut tc: TypeChecker<Key> = TypeChecker::new();
    // Expression `4.3 + false` should yield an error.
    let res = tc_expr(&mut tc, &expr);
    match res {
        Ok(key) => {
            let res_type = tc.get_type(key);
            panic!("Unexpectedly got result type {:?}", res_type);
        }
        Err(_) => {}
    }
    println!("{:?}", tc.get_state());
}
