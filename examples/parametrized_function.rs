use rusttyc::{
    types::Arity, Constructable, Partial, TcErr, TcKey, TcVar, TypeChecker, Variant as TcVariant, VarlessTypeChecker,
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

    fn construct(&self, children: &[Self::Type]) -> Result<Self::Type, Self::Err> {
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

/// This function traverses the expression tree.
/// It creates keys on the fly.  This is not possible for many kinds of type systems, in which case the functions
/// requires a context with a mapping of e.g. Variable -> Key.  The context can be built during a first pass over the
/// tree.
fn tc_expr(tc: &mut VarlessTypeChecker<Variant>, expr: &Expression) -> Result<TcKey, TcErr<Variant>> {
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
            let key_cond = tc_expr(tc, cond)?;
            let key_cons = tc_expr(tc, cons)?;
            let key_alt = tc_expr(tc, alt)?;
            tc.impose(key_cond.concretizes_explicit(Variant::Bool))?;
            tc.impose(key_result.is_meet_of(key_cons, key_alt))?;
        }
        PolyFn { name: _, param_constraints, args, returns } => {
            // Note: The following line cannot be replaced by `vec![param_constraints.len(); tc.new_key()]` as this
            // would copy the keys rather than creating new ones.
            let params: Vec<(Option<Variant>, TcKey)> =
                param_constraints.iter().map(|p| (*p, tc.new_term_key())).collect();
            &params;
            for (arg_ty, arg_expr) in args {
                let arg_key = tc_expr(tc, arg_expr)?;
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

fn main() {
    // Build an expression to type-check.
    let expr = build_complex_expression_type_checks();
    // Create an empty type checker.
    let mut tc: VarlessTypeChecker<Variant> = TypeChecker::without_vars();
    // Type check the expression.
    let res = tc_expr(&mut tc, &expr).and_then(|key| tc.type_check().map(|tt| (key, tt)));
    match res {
        Ok((key, tt)) => {
            let res_type = tt[&key];
            // Expression `if true then 2.7^3 + 4.3 else 3` should yield type Fixed(3, 3) because the addition requires a
            // Fixed(2,3) and a Fixed(3,3), which results in a Fixed(3, 3).
            // Constructing an actual type yields Type::FixedPointI64F64.
            assert_eq!(res_type, Type::FixedPointI64F64);
        }
        Err(_) => panic!("Unexpected type error!"),
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

fn create_addition(lhs: Expression, rhs: Expression) -> Expression {
    Expression::PolyFn {
        name: "addition", // Signature: +<T: Numeric>(T, T) -> T
        param_constraints: vec![Some(Variant::Numeric)],
        args: vec![(ParamType::ParamId(0), lhs), (ParamType::ParamId(0), rhs)],
        returns: ParamType::ParamId(0),
    }
}
