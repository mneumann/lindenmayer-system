use std::fmt::Debug;
use std::ops;
use std::num::Zero;
use std::cmp::{PartialEq, PartialOrd};

pub trait NumType: Debug+Clone+Zero+ops::Add<Output=Self>+ops::Sub<Output=Self>+ops::Mul<Output=Self>+ops::Div<Output=Self>+PartialEq+PartialOrd {}

impl NumType for f32 {}
impl NumType for f64 {}
impl NumType for u32 {}
impl NumType for u64 {}

#[derive(Debug, Eq, PartialEq)]
pub enum ExprError {
    /// In case of division by zero.
    DivByZero,
    /// When the argument position `n` in Arg(n) is out of bounds.
    InvalidArg,
    /// In case of an invalid operation.
    InvalidOperation,
}

/// An expression evaluates to a numeric value of `NumType`.
#[derive(Debug, Clone)]
pub enum Expr<T: NumType> {
    // References an actual Argument by position
    Arg(usize),
    Const(T),
    Add(Box<Expr<T>>, Box<Expr<T>>),
    Sub(Box<Expr<T>>, Box<Expr<T>>),
    Mul(Box<Expr<T>>, Box<Expr<T>>),
    Div(Box<Expr<T>>, Box<Expr<T>>),
}

impl<T:NumType> Expr<T> {
    pub fn evaluate(&self, args: &[T]) -> Result<T, ExprError> {
        match *self {
            Expr::Arg(n) => Ok((*try!(args.get(n).ok_or(ExprError::InvalidArg))).clone()),
            Expr::Const(ref c) => Ok(c.clone()),
            Expr::Add(ref e1, ref e2) => Ok(try!(e1.evaluate(args)) + try!(e2.evaluate(args))),
            Expr::Sub(ref e1, ref e2) => Ok(try!(e1.evaluate(args)) - try!(e2.evaluate(args))),
            Expr::Mul(ref e1, ref e2) => Ok(try!(e1.evaluate(args)) * try!(e2.evaluate(args))),
            Expr::Div(ref e1, ref e2) => {
                let a = try!(e1.evaluate(args));
                let b = try!(e2.evaluate(args));
                if b == T::zero() {
                    return Err(ExprError::DivByZero);
                }
                Ok(a / b)
            }
        }
    }
}

/// A condition evaluates to either `true` or `false`.
#[derive(Debug, Clone)]
pub enum Condition<T: NumType> {
    True,
    False,
    Not(Box<Condition<T>>),
    And(Box<Condition<T>>, Box<Condition<T>>),
    Or(Box<Condition<T>>, Box<Condition<T>>),

    /// If two expressions are equal
    Equal(Box<Expr<T>>, Box<Expr<T>>),

    Less(Box<Expr<T>>, Box<Expr<T>>),
    Greater(Box<Expr<T>>, Box<Expr<T>>),

    LessEqual(Box<Expr<T>>, Box<Expr<T>>),
    GreaterEqual(Box<Expr<T>>, Box<Expr<T>>),
}

impl<T:NumType> Condition<T> {
    pub fn evaluate(&self, args: &[T]) -> Result<bool, ExprError> {
        Ok(match *self {
            Condition::True => true,
            Condition::False => false,
            Condition::Not(ref c) => !try!(c.evaluate(args)),
            Condition::And(ref c1, ref c2) => try!(c1.evaluate(args)) && try!(c2.evaluate(args)),
            Condition::Or(ref c1, ref c2) => try!(c1.evaluate(args)) || try!(c2.evaluate(args)),
            Condition::Equal(ref e1, ref e2) => try!(e1.evaluate(args)) == try!(e2.evaluate(args)),
            Condition::Less(ref e1, ref e2) => try!(e1.evaluate(args)) < try!(e2.evaluate(args)),
            Condition::Greater(ref e1, ref e2) => try!(e1.evaluate(args)) > try!(e2.evaluate(args)),
            Condition::LessEqual(ref e1, ref e2) =>
                try!(e1.evaluate(args)) <= try!(e2.evaluate(args)),
            Condition::GreaterEqual(ref e1, ref e2) =>
                try!(e1.evaluate(args)) >= try!(e2.evaluate(args)),
        })
    }
}

#[test]
fn test_expr() {
    let expr = Expr::Sub(box Expr::Const(0.0),
                         box Expr::Div(box Expr::Mul(box Expr::Add(box Expr::Const(1.0),
                                                                   box Expr::Arg(0)),
                                                     box Expr::Arg(1)),
                                       box Expr::Const(2.0)));

    fn fun(a: f32, b: f32) -> f32 {
        0.0 - ((1.0 + a) * b) / 2.0
    }

    fn check(expr: &Expr<f32>, a: f32, b: f32) {
        assert_eq!(Ok(fun(a, b)), expr.evaluate(&[a, b]))
    }

    check(&expr, 123.0, 4444.0);
    check(&expr, 0.0, -12.0);
}

#[test]
fn test_condition() {
    let cond = Condition::Greater(box Expr::Arg(0), box Expr::Const(0.0));

    fn fun(a: f32) -> bool {
        a > 0.0
    }

    fn check(cond: &Condition<f32>, a: f32) {
        assert_eq!(Ok(fun(a)), cond.evaluate(&[a]))
    }

    check(&cond, 123.0);
    check(&cond, 0.0);
    check(&cond, -1.4);

    assert_eq!(Ok(true), (Condition::True::<f32>).evaluate(&[]));
}
