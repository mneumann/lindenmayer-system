use std::fmt;
use std::ops;
use std::num::{Zero, One};
use std::cmp::{PartialEq, PartialOrd};
use asexp::Sexp;

pub trait NumType: fmt::Debug+Copy+Clone+Zero+One+ops::Add<Output=Self>+ops::Sub<Output=Self>+ops::Mul<Output=Self>+ops::Div<Output=Self>+PartialEq+PartialOrd+Default+Into<Sexp> {}
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
#[derive(Clone, PartialEq, Eq)]
pub enum Expr<T: NumType> {
    Const(T),
    // References an actual Argument by position
    Arg(usize),
    Add(Box<Expr<T>>, Box<Expr<T>>),
    Sub(Box<Expr<T>>, Box<Expr<T>>),
    Mul(Box<Expr<T>>, Box<Expr<T>>),
    Div(Box<Expr<T>>, Box<Expr<T>>),

    // Safe division with x/0 = 0.0
    Divz(Box<Expr<T>>, Box<Expr<T>>),

    // Reciprocal (1 / x).
    Recip(Box<Expr<T>>),

    // Reciprocal using safe division
    Recipz(Box<Expr<T>>),
}

impl<'a, T: NumType> Into<Sexp> for &'a Expr<T> {
    fn into(self) -> Sexp {
        match self {
            &Expr::Const(n) => n.into(),
            &Expr::Arg(n) => Sexp::from(format!("${}", n)),
            &Expr::Add(ref a, ref b) => {
                Sexp::from(("+",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &Expr::Sub(ref a, ref b) => {
                Sexp::from(("-",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &Expr::Mul(ref a, ref b) => {
                Sexp::from(("*",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &Expr::Div(ref a, ref b) => {
                Sexp::from(("/",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &Expr::Divz(ref a, ref b) => {
                Sexp::from(("divz",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &Expr::Recip(ref a) => Sexp::from(("recip", Into::<Sexp>::into(a.as_ref()))),
            &Expr::Recipz(ref a) => Sexp::from(("recipz", Into::<Sexp>::into(a.as_ref()))),
        }
    }
}

impl<T: NumType> fmt::Debug for Expr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Expr::Const(ref c) => write!(f, "{:?}", c),
            &Expr::Arg(num) => write!(f, "${}", num),
            &Expr::Add(ref op1, ref op2) => write!(f, "({:?}+{:?})", op1, op2),
            &Expr::Sub(ref op1, ref op2) => write!(f, "({:?}-{:?})", op1, op2),
            &Expr::Mul(ref op1, ref op2) => write!(f, "{:?}*{:?}", op1, op2),
            &Expr::Div(ref op1, ref op2) => write!(f, "{:?}/{:?}", op1, op2),
            &Expr::Divz(ref op1, ref op2) => write!(f, "{:?}\\{:?}", op1, op2),
            &Expr::Recip(ref op) => write!(f, "{:?}/{:?}", T::one(), op),
            &Expr::Recipz(ref op) => write!(f, "{:?}\\{:?}", T::one(), op),
        }
    }
}

impl<T: NumType> Expr<T> {
    pub fn value(&self) -> Result<T, ExprError> {
        if let &Expr::Const(ref c) = self {
            Ok(c.clone())
        } else {
            Err(ExprError::InvalidArg)
        }
    }

    pub fn evaluate(&self, args: &[Expr<T>]) -> Result<T, ExprError> {
        Ok(match *self {
            Expr::Arg(n) => try!(try!(args.get(n).ok_or(ExprError::InvalidArg)).value()),
            Expr::Const(ref c) => c.clone(),
            Expr::Add(ref e1, ref e2) => try!(e1.evaluate(args)) + try!(e2.evaluate(args)),
            Expr::Sub(ref e1, ref e2) => try!(e1.evaluate(args)) - try!(e2.evaluate(args)),
            Expr::Mul(ref e1, ref e2) => try!(e1.evaluate(args)) * try!(e2.evaluate(args)),
            Expr::Div(ref e1, ref e2) => {
                let a = try!(e1.evaluate(args));
                let div = try!(e2.evaluate(args));
                if div == T::zero() {
                    return Err(ExprError::DivByZero);
                }
                a / div
            }
            Expr::Divz(ref e1, ref e2) => {
                let a = try!(e1.evaluate(args));
                let div = try!(e2.evaluate(args));
                if div == T::zero() {
                    div
                } else {
                    a / div
                }
            }
            Expr::Recip(ref e1) => {
                let div = try!(e1.evaluate(args));
                if div == T::zero() {
                    return Err(ExprError::DivByZero);
                } else {
                    T::one() / div
                }
            }
            Expr::Recipz(ref e1) => {
                let div = try!(e1.evaluate(args));
                if div == T::zero() {
                    div
                } else {
                    T::one() / div
                }
            }
        })
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

impl<'a, T: NumType> Into<Sexp> for &'a Condition<T> {
    fn into(self) -> Sexp {
        match self {
            &Condition::True => Sexp::from("true"),
            &Condition::False => Sexp::from("false"),
            &Condition::Not(ref a) => Sexp::from(("not", Into::<Sexp>::into(a.as_ref()))),
            &Condition::And(ref a, ref b) => {
                Sexp::from(("and",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &Condition::Or(ref a, ref b) => {
                Sexp::from(("or",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &Condition::Equal(ref a, ref b) => {
                Sexp::from(("==",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &Condition::Less(ref a, ref b) => {
                Sexp::from(("<",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &Condition::Greater(ref a, ref b) => {
                Sexp::from((">",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &Condition::LessEqual(ref a, ref b) => {
                Sexp::from(("<=",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &Condition::GreaterEqual(ref a, ref b) => {
                Sexp::from((">=",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
        }
    }
}


impl<T: NumType> Condition<T> {
    pub fn evaluate(&self, args: &[Expr<T>]) -> Result<bool, ExprError> {
        Ok(match *self {
            Condition::True => true,
            Condition::False => false,
            Condition::Not(ref c) => !try!(c.evaluate(args)),
            Condition::And(ref c1, ref c2) => try!(c1.evaluate(args)) && try!(c2.evaluate(args)),
            Condition::Or(ref c1, ref c2) => try!(c1.evaluate(args)) || try!(c2.evaluate(args)),
            Condition::Equal(ref e1, ref e2) => try!(e1.evaluate(args)) == try!(e2.evaluate(args)),
            Condition::Less(ref e1, ref e2) => try!(e1.evaluate(args)) < try!(e2.evaluate(args)),
            Condition::Greater(ref e1, ref e2) => try!(e1.evaluate(args)) > try!(e2.evaluate(args)),
            Condition::LessEqual(ref e1, ref e2) => {
                try!(e1.evaluate(args)) <= try!(e2.evaluate(args))
            }
            Condition::GreaterEqual(ref e1, ref e2) => {
                try!(e1.evaluate(args)) >= try!(e2.evaluate(args))
            }
        })
    }
}

#[test]
fn test_expr_divz() {
    let expr = Expr::Divz(box Expr::Const(1.0), box Expr::Const(0.0));
    assert_eq!(Ok(0.0), expr.evaluate(&[]));
}

#[test]
fn test_expr_recipz() {
    let expr = Expr::Recipz(box Expr::Const(0.0));
    assert_eq!(Ok(0.0), expr.evaluate(&[]));

    let expr = Expr::Recipz(box Expr::Const(1.0));
    assert_eq!(Ok(1.0), expr.evaluate(&[]));

    let expr = Expr::Recipz(box Expr::Const(0.5));
    assert_eq!(Ok(2.0), expr.evaluate(&[]));
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
        assert_eq!(Ok(fun(a, b)),
                   expr.evaluate(&[Expr::Const(a), Expr::Const(b)]))
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
        assert_eq!(Ok(fun(a)), cond.evaluate(&[Expr::Const(a)]))
    }

    check(&cond, 123.0);
    check(&cond, 0.0);
    check(&cond, -1.4);

    assert_eq!(Ok(true), (Condition::True::<f32>).evaluate(&[]));
}
