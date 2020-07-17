use rusttyc::types::Abstract;
use rusttyc::{
    types::{Generalizable, ReificationErr, TryReifiable},
    TcErr, TcKey, TypeChecker,
};
use std::cmp::max;
use std::convert::TryInto;

/// The key used for referencing objects with types.  Needs to implement `EnaKey`.
#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Ord, Eq, Hash)]
struct Key(u32);

/// Represents abstract types.  Needs to implement `EnaValue`.
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

#[derive(Debug, Clone, Eq, PartialEq, Hash, Copy)]
enum Variant {
    Fixed,
    Integer,
    Bool,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
struct Variable(); // Not needed in this example.

// ************ IMPLEMENTATION OF REQUIRED TRAITS ************ //

impl rusttyc::TcVar for Variable {}

impl Abstract for AbstractType {
    type Err = String;
    type VariantTag = Variant;

    fn unconstrained() -> Self {
        AbstractType::Any
    }

    fn meet(&self, other: &Self) -> Result<Self, Self::Err> {
        use crate::AbstractType::*;
        match (self, other) {
            (Any, other) | (other, Any) => Ok(other.clone()),
            (Integer(l), Integer(r)) => Ok(Integer(max(*r, *l))),
            (Fixed(li, lf), Fixed(ri, rf)) => Ok(Fixed(max(*li, *ri), max(*lf, *rf))),
            (Fixed(i, f), Integer(u)) | (Integer(u), Fixed(i, f)) if *f == 0 => Ok(Integer(max(*i, *u))),
            (Fixed(i, f), Integer(u)) | (Integer(u), Fixed(i, f)) => Ok(Fixed(max(*i, *u), *f)),
            (Bool, Bool) => Ok(Bool),
            (Bool, _) | (_, Bool) => Err("bools cannot be met with other types.".to_string()),
            (Numeric, Integer(w)) | (Integer(w), Numeric) => Ok(Integer(*w)),
            (Numeric, Fixed(i, f)) | (Fixed(i, f), Numeric) => Ok(Fixed(*i, *f)),
            (Numeric, Numeric) => Ok(Numeric),
        }
    }
    fn variant(&self) -> Option<Self::VariantTag> {
        match self {
            Self::Bool => Some(Variant::Bool),
            Self::Fixed(_, _) => Some(Variant::Fixed),
            Self::Integer(_) => Some(Variant::Integer),
            _ => None,
        }
    }
    fn variant_arity(_tag: Self::VariantTag) -> usize {
        0
    }
    fn from_tag(tag: Self::VariantTag, children: Vec<Self>) -> Self {
        assert!(children.is_empty());
        match tag {
            Variant::Integer => Self::Integer(0),
            Variant::Fixed => Self::Fixed(0, 0),
            Variant::Bool => Self::Bool,
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

    fn try_reify(&self) -> Result<Self::Reified, ReificationErr> {
        match self {
            AbstractType::Any => Err(ReificationErr::TooGeneral("Cannot reify `Any`.".to_string())),
            AbstractType::Integer(w) if *w <= 128 => Ok(ConcreteType::Int128),
            AbstractType::Integer(w) => {
                Err(ReificationErr::Conflicting(format!("Integer too wide, {}-bit not supported.", w)))
            }
            AbstractType::Fixed(i, f) if *i <= 64 && *f <= 64 => Ok(ConcreteType::FixedPointI64F64),
            AbstractType::Fixed(i, f) => {
                Err(ReificationErr::Conflicting(format!("Fixed point number too wide, I{}F{} not supported.", i, f)))
            }
            AbstractType::Numeric => Err(ReificationErr::TooGeneral(
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
    let addition = Expression::PolyFn {
        name: "addition", // Signature: +<T: Numeric>(T, T) -> T
        param_constraints: vec![Some(AbstractType::Numeric)],
        args: vec![(ParamType::ParamId(0), exponentiation), (ParamType::ParamId(0), const43)],
        returns: ParamType::ParamId(0),
    };
    Conditional { cond: Box::new(const_true), cons: Box::new(addition), alt: Box::new(const3) }
}

/// This function traverses the expression tree.
/// It creates keys on the fly.  This is not possible for many kinds of type systems, in which case the functions
/// requires a context with a mapping of e.g. Variable -> Key.  The context can be built during a first pass over the
/// tree.
fn tc_expr(tc: &mut TypeChecker<AbstractType, Variable>, expr: &Expression) -> Result<TcKey, TcErr<AbstractType>> {
    use Expression::*;
    let key_result = tc.new_term_key(); // will be returned
    match expr {
        ConstInt(c) => {
            let width = (128 - c.leading_zeros()).try_into().unwrap();
            tc.impose(key_result.more_concrete_than_explicit(AbstractType::Integer(width)))?;
        }
        ConstFixed(i, f) => {
            let int_width = (64 - i.leading_zeros()).try_into().unwrap();
            let frac_width = (64 - f.leading_zeros()).try_into().unwrap();
            tc.impose(key_result.more_concrete_than_explicit(AbstractType::Fixed(int_width, frac_width)))?;
        }
        ConstBool(_) => tc.impose(key_result.captures_concrete(ConcreteType::Bool))?,
        Conditional { cond, cons, alt } => {
            let key_cond = tc_expr(tc, cond)?;
            let key_cons = tc_expr(tc, cons)?;
            let key_alt = tc_expr(tc, alt)?;
            tc.impose(key_cond.more_concrete_than_explicit(AbstractType::Bool))?;
            // Two things to note regarding the next operation:
            // The meet operation can fail.  Refer to `TypeChecker::check_conflicting(&mut self, TypeCheckerKey)` for
            // detecting this case.  Moreover, if it fails, the conflicting type is persisted in the type table and
            // propagated throughout the remaining type check.  If this is undesired due to the existence of an
            // alternative type rule, refer to the snapshotting mechanism.
            tc.impose(key_result.is_meet_of(key_cons, key_alt))?;
        }
        PolyFn { name: _, param_constraints, args, returns } => {
            // Note: The following line cannot be replaced by `vec![param_constraints.len(); tc.new_key()]` as this
            // would copy the keys rather than creating new ones.
            let params: Vec<(Option<AbstractType>, TcKey)> =
                param_constraints.iter().map(|p| (*p, tc.new_term_key())).collect();
            for (arg_ty, arg_expr) in args {
                let arg_key = tc_expr(tc, arg_expr)?;
                match arg_ty {
                    ParamType::ParamId(id) => {
                        let (p_constr, p_key) = params[*id];
                        // We need to enforce that the parameter is more concrete than the passed argument and that the
                        // passed argument satisfies the constraints imposed on the parametric type.
                        tc.impose(p_key.more_concrete_than(arg_key))?;
                        if let Some(c) = p_constr {
                            tc.impose(arg_key.more_concrete_than_explicit(c))?;
                        }
                    }
                    ParamType::Abstract(at) => tc.impose(arg_key.more_concrete_than_explicit(*at))?,
                };
            }
            match returns {
                ParamType::Abstract(at) => tc.impose(key_result.more_concrete_than_explicit(*at))?,
                ParamType::ParamId(id) => {
                    let (constr, key) = params[*id];
                    if let Some(c) = constr {
                        tc.impose(key_result.more_concrete_than_explicit(c))?;
                    }
                    tc.impose(key_result.more_concrete_than(key))?;
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
    let mut tc: TypeChecker<AbstractType, Variable> = TypeChecker::new();
    // Type check the expression.
    let res = tc_expr(&mut tc, &expr).and_then(|key| tc.type_check().map(|tt| (key, tt)));
    match res {
        Ok((key, tt)) => {
            let res_type = tt[key];
            // Expression `if true then 2.7^3 + 4.3 else 3` should yield type Fixed(3, 3) because the addition requires a
            // Fixed(2,3) and a Fixed(3,3), which results in a Fixed(3, 3).
            assert_eq!(res_type, AbstractType::Fixed(3, 3));
        }
        Err(_) => panic!("Unexpected type error!"),
    }
}
