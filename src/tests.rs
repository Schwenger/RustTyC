use crate::type_checker::{TcVar, TypeChecker};
use crate::{Abstract, Generalizable, ReificationError, TcErr, TcKey, TryReifiable, TypeTable};
use std::cmp::max;
use std::convert::TryInto;
use std::hash::Hash;

/// Represents abstract types.  Needs to implement `rusttyc::Abstract`.
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

/// Won't be used.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct Variable(usize);

// ************ IMPLEMENTATION OF REQUIRED TRAITS ************ //

impl TcVar for Variable {}

impl Abstract for AbstractType {
    type Err = ();
    type Variant = crate::Niladic;

    fn unconstrained() -> Self {
        AbstractType::Any
    }

    fn meet(self, right: Self) -> Result<Self, Self::Err> {
        use crate::tests::AbstractType::*;
        match (self, right) {
            (Any, other) | (other, Any) => Ok(other.clone()),
            (Integer(l), Integer(r)) => Ok(Integer(max(r, l))),
            (Fixed(li, lf), Fixed(ri, rf)) => Ok(Fixed(max(li, ri), max(lf, rf))),
            (Fixed(i, f), Integer(u)) | (Integer(u), Fixed(i, f)) if f == 0 => Ok(Integer(max(i, u))),
            (Fixed(i, f), Integer(u)) | (Integer(u), Fixed(i, f)) => Ok(Fixed(max(i, u), f)),
            (Bool, Bool) => Ok(Bool),
            (Bool, _) | (_, Bool) => Err(()),
            (Numeric, Integer(w)) | (Integer(w), Numeric) => Ok(Integer(w)),
            (Numeric, Fixed(i, f)) | (Fixed(i, f), Numeric) => Ok(Fixed(i, f)),
            (Numeric, Numeric) => Ok(Numeric),
        }
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

impl TryReifiable for AbstractType {
    type Reified = ConcreteType;

    fn try_reify(&self) -> Result<Self::Reified, ReificationError> {
        match self {
            AbstractType::Any => Err(ReificationError::TooGeneral("Cannot reify `Any`.".to_string())),
            AbstractType::Integer(w) if *w <= 128 => Ok(ConcreteType::Int128),
            AbstractType::Integer(w) => {
                Err(ReificationError::Conflicting(format!("Integer too wide, {}-bit not supported.", w)))
            }
            AbstractType::Fixed(i, f) if *i <= 64 && *f <= 64 => Ok(ConcreteType::FixedPointI64F64),
            AbstractType::Fixed(i, f) => {
                Err(ReificationError::Conflicting(format!("Fixed point number too wide, I{}F{} not supported.", i, f)))
            }
            AbstractType::Numeric => Err(ReificationError::TooGeneral(
                "Cannot reify a numeric value. Either define a default (int/fixed) or restrict type.".to_string(),
            )),
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
fn tc_expr<Var: TcVar>(
    tc: &mut TypeChecker<AbstractType, Var>,
    expr: &Expression,
) -> Result<TcKey<AbstractType>, TcErr<AbstractType>> {
    // TODO: ERROR TYPE
    use Expression::*;
    let key_result = tc.new_term_key(); // will be returned
    match expr {
        ConstInt(c) => {
            let width = (128 - c.leading_zeros()).try_into().unwrap();
            tc.impose(key_result.captures_abstract(AbstractType::Integer(width)))?;
        }
        ConstFixed(i, f) => {
            let int_width = (64 - i.leading_zeros()).try_into().unwrap();
            let frac_width = (64 - f.leading_zeros()).try_into().unwrap();
            tc.impose(key_result.captures_abstract(AbstractType::Fixed(int_width, frac_width)))?;
        }
        ConstBool(_) => tc.impose(key_result.captures_concrete(ConcreteType::Bool))?,
        Conditional { cond, cons, alt } => {
            let key_cond = tc_expr(tc, cond)?;
            let key_cons = tc_expr(tc, cons)?;
            let key_alt = tc_expr(tc, alt)?;
            tc.impose(key_cond.captures_abstract(AbstractType::Bool))?;
            // Two things to note regarding the next operation:
            // The meet operation can fail.  Refer to `TypeChecker::check_conflicting(&mut self, TypeCheckerKey)` for
            // detecting this case.  Moreover, if it fails, the conflicting type is persisted in the type table and
            // propagated throughout the remaining type check.  If this is undesired due to the existence of an
            // alternative type rule, refer to the snapshotting mechanism.
            tc.impose(key_result.is_linked_symmetrically(key_cons))?;
            tc.impose(key_result.is_linked_symmetrically(key_alt))?;
        }
        PolyFn { name: _, param_constraints, args, returns } => {
            // Note: The following line cannot be replaced by `vec![param_constraints.len(); tc.new_key()]` as this
            // would copy the keys rather than creating new ones.
            let params: Vec<(Option<AbstractType>, TcKey<AbstractType>)> =
                param_constraints.iter().map(|p| (*p, tc.new_term_key())).collect();
            &params;
            for (arg_ty, arg_expr) in args {
                let arg_key = tc_expr(tc, arg_expr)?;
                match arg_ty {
                    ParamType::ParamId(id) => {
                        let (p_constr, p_key) = params[*id];
                        // We need to enforce that the parameter is more concrete than the passed argument and that the
                        // passed argument satisfies the constraints imposed on the parametric type.
                        tc.impose(p_key.is_linked_symmetrically(arg_key))?;
                        if let Some(c) = p_constr {
                            tc.impose(arg_key.captures_abstract(c))?;
                        }
                    }
                    ParamType::Abstract(at) => tc.impose(arg_key.captures_abstract(*at))?,
                };
            }
            match returns {
                ParamType::Abstract(at) => tc.impose(key_result.captures_abstract(*at))?,
                ParamType::ParamId(id) => {
                    let (constr, key) = params[*id];
                    if let Some(c) = constr {
                        tc.impose(key_result.captures_abstract(c))?;
                    }
                    tc.impose(key_result.is_linked_symmetrically(key))?;
                }
            }
        }
    }
    Ok(key_result)
}

#[test]
fn create_different_types() {
    let mut tc: TypeChecker<AbstractType, Variable> = TypeChecker::new();
    let first = tc.new_term_key();
    let second = tc.new_term_key();
    assert_ne!(first, second);
}

#[test]
fn bound_by_concrete_transitive() {
    let mut tc: TypeChecker<AbstractType, Variable> = TypeChecker::new();
    let first = tc.new_term_key();
    let second = tc.new_term_key();
    assert!(tc.impose(second.captures_concrete(ConcreteType::Int128)).is_ok());
    assert!(tc.impose(first.is_linked_symmetrically(second)).is_ok());
    assert_eq!(tc.test_peek(first), tc.test_peek(second));
}

#[test]
fn complex_type_check() {
    let expr = build_complex_expression_type_checks();
    let mut tc: TypeChecker<AbstractType, Variable> = TypeChecker::new();
    let res = tc_expr(&mut tc, &expr);
    match res {
        Ok(key) => {
            let res_type = tc.test_peek(key);
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
    let mut tc: TypeChecker<AbstractType, Variable> = TypeChecker::new();
    // Expression `4.3 + false` should yield an error.
    let res = tc_expr(&mut tc, &expr);
    match res {
        Ok(key) => {
            let res_type = tc.test_peek(key);
            panic!("Unexpectedly got result type {:?}", res_type);
        }
        Err(_) => {}
    }
}

#[test]
fn test_variable_dedup() {
    let mut tc: TypeChecker<AbstractType, Variable> = TypeChecker::new();
    let var_a = tc.get_var_key(&Variable(0));
    let term = tc.new_term_key();
    let var_b = tc.get_var_key(&Variable(1));
    let var_a_2 = tc.get_var_key(&Variable(0));
    assert_eq!(var_a, var_a_2);
    assert_ne!(var_a, term);
    assert_ne!(var_a, var_b);
    assert_ne!(term, var_b);
    // The rest of the comparisons are covered by the first equivalence check.
}

#[test]
fn test_asym_simple() {
    let mut tc: TypeChecker<AbstractType, Variable> = TypeChecker::new();
    let key_a = tc.new_term_key();
    let key_b = tc.new_term_key();

    tc.impose(key_a.captures_abstract(AbstractType::Integer(3))).unwrap();

    tc.impose(key_b.is_more_conc_than(key_a)).unwrap();

    let tt = tc.type_check().expect("Unexpected type error.").as_hashmap();
    assert_eq!(tt[&key_a], tt[&key_b]);
}

#[test]
fn test_asym_order() {
    let mut tc: TypeChecker<AbstractType, Variable> = TypeChecker::new();
    let key_a = tc.new_term_key();
    let key_b = tc.new_term_key();

    tc.impose(key_b.is_more_conc_than(key_a)).unwrap();

    tc.impose(key_a.captures_abstract(AbstractType::Integer(3))).unwrap();

    let tt = tc.type_check().expect("Unexpected type error.").as_hashmap();
    assert_eq!(tt[&key_a], tt[&key_b]);
}

#[test]
fn test_asym_separation() {
    let mut tc: TypeChecker<AbstractType, Variable> = TypeChecker::new();
    let key_a = tc.new_term_key();
    let key_b = tc.new_term_key();
    let key_c = tc.new_term_key();

    let a_type = AbstractType::Integer(3);
    let c_type = AbstractType::Integer(12);

    tc.impose(key_a.captures_abstract(a_type)).unwrap();

    tc.impose(key_b.is_more_conc_than(key_a)).unwrap();

    tc.impose(key_c.captures_abstract(c_type)).unwrap();
    tc.impose(key_b.is_linked_symmetrically(key_c)).unwrap();

    let tt = tc.type_check().expect("Unexpected type error.").as_hashmap();
    assert_eq!(tt[&key_b], tt[&key_c]);
    assert_eq!(tt[&key_a], a_type);
    assert_eq!(tt[&key_b], c_type);
    assert_eq!(tt[&key_c], c_type);
}
