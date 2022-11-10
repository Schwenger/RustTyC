use crate::{
    type_checker::VarlessTypeChecker, types::Arity, Constructable, Partial, PreliminaryTypeTable, TcErr, TcKey, TcVar,
    TypeChecker, TypeTable, Variant as TcVariant,
};
use std::cmp::max;
use std::convert::TryInto;
use std::hash::Hash;

#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Ord, Eq, Hash)]
enum Type {
    Int128,
    FixedPointI64F64,
    Bool,
}

#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Ord, Eq, Hash)]
enum Variant {
    Any,
    Fixed(u8, u8),
    Integer(u8),
    Numeric,
    Bool,
}

#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Ord, Eq, Hash)]
struct Variable(usize);

// ************ IMPLEMENTATION OF REQUIRED TRAITS ************ //

impl TcVar for Variable {}

impl TcVariant for Variant {
    type Err = String;

    fn top() -> Self {
        Self::Any
    }

    fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err> {
        use Variant::*;
        assert_eq!(lhs.least_arity, 0, "spurious child");
        assert_eq!(rhs.least_arity, 0, "spurious child");
        let variant = match (lhs.variant, rhs.variant) {
            (Any, other) | (other, Any) => Ok(other),
            (Integer(l), Integer(r)) => Ok(Integer(max(r, l))),
            (Fixed(li, lf), Fixed(ri, rf)) => Ok(Fixed(max(li, ri), max(lf, rf))),
            (Fixed(i, f), Integer(u)) | (Integer(u), Fixed(i, f)) if f == 0 => Ok(Integer(max(i, u))),
            (Fixed(i, f), Integer(u)) | (Integer(u), Fixed(i, f)) => Ok(Fixed(max(i, u), f)),
            (Bool, Bool) => Ok(Bool),
            (Bool, _) | (_, Bool) => Err("bool can only be combined with bool"),
            (Numeric, Integer(w)) | (Integer(w), Numeric) => Ok(Integer(w)),
            (Numeric, Fixed(i, f)) | (Fixed(i, f), Numeric) => Ok(Fixed(i, f)),
            (Numeric, Numeric) => Ok(Numeric),
        }?;
        Ok(Partial { variant, least_arity: 0 })
    }

    fn arity(&self) -> Arity {
        Arity::Fixed(0)
    }
}

/// Represents a type in a parametrized function; either refers to a type parameter or is an abstract type.
#[derive(Clone, Copy, Debug)]
enum ParamType {
    ParamId(usize),
    Abstract(Variant),
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
        param_constraints: Vec<Option<Variant>>,
        args: Vec<(ParamType, Expression)>,
        returns: ParamType,
    },
    ConstInt(i128),
    ConstBool(bool),
    ConstFixed(i64, u64),
}

impl Constructable for Variant {
    type Type = Type;

    fn construct(&self, children: &[Self::Type], _ctx: &mut Self::Context) -> Result<Self::Type, Self::Err> {
        assert!(children.is_empty(), "spurious children");
        use Variant::*;
        match self {
            Any => Err("Cannot reify `Any`.".to_string()),
            Integer(w) if *w <= 128 => Ok(Type::Int128),
            Integer(w) => Err(format!("Integer too wide, {}-bit not supported.", w)),
            Fixed(i, f) if *i <= 64 && *f <= 64 => Ok(Type::FixedPointI64F64),
            Fixed(i, f) => Err(format!("Fixed point number too wide, I{}F{} not supported.", i, f)),
            Numeric => {
                Err("Cannot reify a numeric value. Either define a default (int/fixed) or restrict type.".to_string())
            }
            Bool => Ok(Type::Bool),
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
        param_constraints: vec![Some(Variant::Numeric)],
        args: vec![(ParamType::ParamId(0), const43), (ParamType::ParamId(0), const_false)],
        returns: ParamType::ParamId(0),
    }
}

fn create_addition(lhs: Expression, rhs: Expression) -> Expression {
    Expression::PolyFn {
        name: "addition", // Signature: +<T: Numeric>(T, T) -> T
        param_constraints: vec![Some(Variant::Numeric)],
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
        param_constraints: vec![Some(Variant::Numeric)],
        args: vec![(ParamType::ParamId(0), const27), (ParamType::Abstract(Variant::Integer(1)), const3.clone())],
        returns: ParamType::ParamId(0),
    };
    let addition = create_addition(exponentiation, const43);
    Conditional { cond: Box::new(const_true), cons: Box::new(addition), alt: Box::new(const3) }
}

fn tc_expr(
    mut tc: VarlessTypeChecker<Variant>,
    expr: &Expression,
) -> Result<(TcKey, TypeTable<Variant>), TcErr<Variant>> {
    let key = _tc_expr(&mut tc, expr)?;
    let tt = tc.type_check()?;
    Ok((key, tt))
}

fn tc_expr_prelim(
    mut tc: VarlessTypeChecker<Variant>,
    expr: &Expression,
) -> Result<(TcKey, PreliminaryTypeTable<Variant>), TcErr<Variant>> {
    let key = _tc_expr(&mut tc, expr)?;
    let tt = tc.type_check_preliminary()?;
    Ok((key, tt))
}

/// This function traverses the expression tree.
/// It creates keys on the fly.  This is not possible for many kinds of type systems, in which case the functions
/// requires a context with a mapping of e.g. Variable -> Key.  The context can be built during a first pass over the
/// tree.
fn _tc_expr(tc: &mut VarlessTypeChecker<Variant>, expr: &Expression) -> Result<TcKey, TcErr<Variant>> {
    use Expression::*;
    let key_result = tc.new_term_key(); // will be returned
    match expr {
        ConstInt(c) => {
            let width = (128 - c.leading_zeros()).try_into().unwrap();
            tc.impose(key_result.concretizes_explicit(Variant::Integer(width)))?;
        }
        ConstFixed(i, f) => {
            let int_width = (64 - i.leading_zeros()).try_into().unwrap();
            let frac_width = (64 - f.leading_zeros()).try_into().unwrap();
            tc.impose(key_result.concretizes_explicit(Variant::Fixed(int_width, frac_width)))?;
        }
        ConstBool(_) => tc.impose(key_result.concretizes_explicit(Variant::Bool))?,
        Conditional { cond, cons, alt } => {
            let key_cond = _tc_expr(tc, cond)?;
            let key_cons = _tc_expr(tc, cons)?;
            let key_alt = _tc_expr(tc, alt)?;
            tc.impose(key_cond.concretizes_explicit(Variant::Bool))?;
            tc.impose(key_result.is_meet_of(key_cons, key_alt))?;
        }
        PolyFn { name: _, param_constraints, args, returns } => {
            // Note: The following line cannot be replaced by `vec![param_constraints.len(); tc.new_key()]` as this
            // would copy the keys rather than creating new ones.
            let params: Vec<(Option<Variant>, TcKey)> =
                param_constraints.iter().map(|p| (*p, tc.new_term_key())).collect();
            for (arg_ty, arg_expr) in args {
                let arg_key = _tc_expr(tc, arg_expr)?;
                match arg_ty {
                    ParamType::ParamId(id) => {
                        let (p_constr, p_key) = params[*id];
                        // We need to enforce that the parameter is more concrete than the passed argument and that the
                        // passed argument satisfies the constraints imposed on the parametric type.
                        tc.impose(p_key.concretizes(arg_key))?;
                        if let Some(c) = p_constr {
                            tc.impose(arg_key.concretizes_explicit(c))?;
                        }
                    }
                    ParamType::Abstract(at) => tc.impose(arg_key.concretizes_explicit(*at))?,
                };
            }
            match returns {
                ParamType::Abstract(at) => tc.impose(key_result.concretizes_explicit(*at))?,
                ParamType::ParamId(id) => {
                    let (constr, key) = params[*id];
                    if let Some(c) = constr {
                        tc.impose(key_result.concretizes_explicit(c))?;
                    }
                    tc.impose(key_result.equate_with(key))?;
                }
            }
        }
    }
    Ok(key_result)
}

#[test]
fn create_different_types() {
    let mut tc: VarlessTypeChecker<Variant> = TypeChecker::without_vars();
    let first = tc.new_term_key();
    let second = tc.new_term_key();
    assert_ne!(first, second);
}

#[test]
fn bound_by_concrete_transitive() {
    let mut tc: VarlessTypeChecker<Variant> = TypeChecker::without_vars();
    let first = tc.new_term_key();
    let second = tc.new_term_key();
    assert!(tc.impose(second.concretizes_explicit(Variant::Integer(128))).is_ok());
    assert!(tc.impose(first.equate_with(second)).is_ok());
    let tt = tc.type_check().expect("unexpected type error");
    assert_eq!(tt[&first], tt[&second]);
}

#[test]
fn complex_type_check() {
    let expr = build_complex_expression_type_checks();
    let tc: VarlessTypeChecker<Variant> = TypeChecker::without_vars();
    let (key, tt) = tc_expr_prelim(tc, &expr).expect("unexpected type error");
    // Expression `if true then 2.7^3 + 4.3 else 3` should yield type Fixed(3, 3) because the addition requires a
    // Fixed(2,3) and a Fixed(3,3), which results in a Fixed(3, 3).
    assert_eq!(tt[&key].variant, Variant::Fixed(3, 3));
}

#[test]
fn failing_type_check() {
    let expr = build_type_error();
    let tc: VarlessTypeChecker<Variant> = TypeChecker::without_vars();
    // Expression `4.3 + false` should yield an error.
    if let Ok((key, tt)) = tc_expr(tc, &expr) {
        panic!("unexpectedly got result type {:?}", tt[&key]);
    }
}

#[test]
fn test_variable_dedup() {
    let mut tc: TypeChecker<Variant, Variable> = TypeChecker::new();
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
    let mut tc: TypeChecker<Variant, Variable> = TypeChecker::new();
    let key_a = tc.new_term_key();
    let key_b = tc.new_term_key();

    tc.impose(key_a.concretizes_explicit(Variant::Integer(3))).unwrap();

    tc.impose(key_b.concretizes(key_a)).unwrap();

    let tt = tc.type_check().expect("Unexpected type error.");
    assert_eq!(tt[&key_a], tt[&key_b]);
}

#[test]
fn test_asym_order() {
    let mut tc: TypeChecker<Variant, Variable> = TypeChecker::new();
    let key_a = tc.new_term_key();
    let key_b = tc.new_term_key();

    tc.impose(key_b.concretizes(key_a)).unwrap();

    tc.impose(key_a.concretizes_explicit(Variant::Integer(3))).unwrap();

    let tt = tc.type_check().expect("Unexpected type error.");
    assert_eq!(tt[&key_a], tt[&key_b]);
}

#[test]
fn test_asym_separation() {
    let mut tc: TypeChecker<Variant, Variable> = TypeChecker::new();
    let key_a = tc.new_term_key();
    let key_b = tc.new_term_key();
    let key_c = tc.new_term_key();

    let a_type = Variant::Integer(3);
    let c_type = Variant::Integer(12);

    tc.impose(key_a.concretizes_explicit(a_type)).unwrap();
    tc.impose(key_b.concretizes(key_a)).unwrap();
    tc.impose(key_b.equate_with(key_c)).unwrap();
    tc.impose(key_c.concretizes_explicit(c_type)).unwrap();

    let tc_clone = tc.clone();

    let tt = tc.type_check().expect("unexpected type error.");
    let prelim_tt = tc_clone.type_check_preliminary().expect("unexpected type error.");
    assert_eq!(tt[&key_b], tt[&key_c]);
    assert_eq!(prelim_tt[&key_a].variant, a_type);
    assert_eq!(prelim_tt[&key_b].variant, c_type);
    assert_eq!(prelim_tt[&key_c].variant, c_type);
}

#[test]
fn test_meet() {
    let mut tc: TypeChecker<Variant, Variable> = TypeChecker::new();
    let key_a = tc.new_term_key();
    let key_b = tc.new_term_key();
    let key_c = tc.new_term_key();

    let a_type = Variant::Integer(3);
    let c_type = Variant::Integer(12);

    tc.impose(key_a.concretizes_explicit(a_type)).unwrap();
    tc.impose(key_c.concretizes_explicit(c_type)).unwrap();

    tc.impose(key_b.is_meet_of(key_a, key_c)).unwrap();

    let tc_clone = tc.clone();

    let tt = tc.type_check().expect("unexpected type error.");
    let prelim_tt = tc_clone.type_check_preliminary().expect("unexpected type error.");
    assert_eq!(tt[&key_b], tt[&key_c]);
    assert_eq!(prelim_tt[&key_a].variant, a_type);
    assert_eq!(prelim_tt[&key_b].variant, c_type);
    assert_eq!(prelim_tt[&key_c].variant, c_type);
}
