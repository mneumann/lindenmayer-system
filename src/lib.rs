#![feature(box_syntax)]

use std::fmt;

pub trait Alphabet: fmt::Debug + Eq + PartialEq + Clone {}

pub type NumType = f32;

/// An argument is an "actual" parameter.
#[derive(Clone)]
pub struct Argument(pub NumType);

impl fmt::Debug for Argument {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum ExprError {
    /// In case of division by zero.
    DivByZero,
    /// When the argument position `n` in Arg(n) is out of bounds.
    InvalidArg,
}

/// An expression evaluates to a numeric value of `NumType`.
#[derive(Debug, Clone)]
pub enum Expr {
    // References an actual Argument by position
    Arg(usize),
    Const(NumType),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}


impl Expr {
    // XXX: Do we need those checks?
    fn evaluate(&self, args: &[Argument]) -> Result<NumType, ExprError> {
        match *self {
            Expr::Arg(n) => Ok(try!(args.get(n).ok_or(ExprError::InvalidArg)).0),
            Expr::Const(c) => Ok(c),
            Expr::Add(ref e1, ref e2) => Ok(try!(e1.evaluate(args)) + try!(e2.evaluate(args))),
            Expr::Sub(ref e1, ref e2) => Ok(try!(e1.evaluate(args)) - try!(e2.evaluate(args))),
            Expr::Mul(ref e1, ref e2) => Ok(try!(e1.evaluate(args)) * try!(e2.evaluate(args))),
            Expr::Div(ref e1, ref e2) => {
                let a = try!(e1.evaluate(args));
                let b = try!(e2.evaluate(args));
                if b == 0.0 {
                    return Err(ExprError::DivByZero);
                }
                Ok(a / b)
            }
        }
    }
}

/// A condition evaluates to either `true` or `false`.
#[derive(Debug, Clone)]
pub enum Condition {
    True,
    False,
    Not(Box<Condition>),
    And(Box<Condition>, Box<Condition>),
    Or(Box<Condition>, Box<Condition>),

    /// If two expressions are equal
    Equal(Box<Expr>, Box<Expr>),

    Less(Box<Expr>, Box<Expr>),
    Greater(Box<Expr>, Box<Expr>),

    LessEqual(Box<Expr>, Box<Expr>),
    GreaterEqual(Box<Expr>, Box<Expr>),
}

impl Condition {
    // XXX: Do we need those checks?
    fn evaluate(&self, args: &[Argument]) -> Result<bool, ExprError> {
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
    use Expr::{Arg, Const, Add, Sub, Mul, Div};
    let expr = Sub(box Const(0.0),
                   box Div(box Mul(box Add(box Const(1.0), box Arg(0)), box Arg(1)),
                           box Const(2.0)));

    fn fun(a: NumType, b: NumType) -> NumType {
        0.0 - ((1.0 + a) * b) / 2.0
    }

    fn check(expr: &Expr, a: NumType, b: NumType) {
        assert_eq!(Ok(fun(a, b)), expr.evaluate(&[Argument(a), Argument(b)]))
    }

    check(&expr, 123.0, 4444.0);
    check(&expr, 0.0, -12.0);
}

#[test]
fn test_condition() {
    use Expr::{Arg, Const, Add, Sub, Mul, Div};
    use Condition::{Not, And, Greater};
    let cond = Greater(box Arg(0), box Const(0.0));

    fn fun(a: NumType) -> bool {
        a > 0.0
    }

    fn check(cond: &Condition, a: NumType) {
        assert_eq!(Ok(fun(a)), cond.evaluate(&[Argument(a)]))
    }

    check(&cond, 123.0);
    check(&cond, 0.0);
    check(&cond, -1.4);

    assert_eq!(Ok(true), Condition::True.evaluate(&[]));
}


/// A symbol contains actual parameters.
#[derive(Clone)]
pub struct Symbol<A: Alphabet> {
    pub character: A,
    pub arguments: Vec<Argument>,
}

impl<A:Alphabet> fmt::Debug for Symbol<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let res = write!(f, "{:?}", self.character);
        if self.arguments.len() > 0 {
            write!(f, "({:?}", self.arguments[0]);
            for e in &self.arguments[1..] {
                write!(f, ",{:?}", e);
            }
            write!(f, ")")
        } else {
            res
        }
    }
}


/// A parameterized symbol contains formal parameters, which can be
/// evaluated to a Symbol given some actual parameters.
pub struct ParameterizedSymbol<A: Alphabet> {
    pub character: A,
    pub expressions: Vec<Expr>,
}


impl<A:Alphabet> fmt::Debug for ParameterizedSymbol<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let res = write!(f, "{:?}", self.character);
        if self.expressions.len() > 0 {
            write!(f, "({:?}", self.expressions[0]);
            for e in &self.expressions[1..] {
                write!(f, ",{:?}", e);
            }
            write!(f, ")")
        } else {
            res
        }
    }
}


impl<A:Alphabet> ParameterizedSymbol<A> {
    pub fn new(character: A) -> ParameterizedSymbol<A> {
        ParameterizedSymbol {
            character: character,
            expressions: Vec::new(),
        }
    }
    fn evaluate(&self, args: &[Argument]) -> Result<Symbol<A>, ExprError> {
        let mut values = Vec::with_capacity(self.expressions.len());
        for expr in self.expressions.iter() {
            let arg = try!(expr.evaluate(args));
            values.push(Argument(arg));
        }
        assert!(values.len() == self.expressions.len());
        Ok(Symbol {
            character: self.character.clone(),
            arguments: values,
        })
    }
}


// XXX: ParametricWord?
impl<A:Alphabet> Symbol<A> {
    pub fn new(character: A) -> Symbol<A> {
        Symbol {
            character: character,
            arguments: Vec::new(),
        }
    }
}

// XXX: Rename SymbolString to Word
pub struct SymbolString<A: Alphabet>(pub Vec<Symbol<A>>);

impl<A:Alphabet> fmt::Debug for SymbolString<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let v = &self.0;
        try!(write!(f, "\""));
        if !v.is_empty() {
            try!(write!(f, "{:?}", v[0]));
            for e in &v[1..] {
                try!(write!(f, " {:?}", e));
            }
        }
        write!(f, "\"")
    }
}

#[derive(Debug)]
pub struct Rule<A: Alphabet> {
    pub character: A,
    pub arity: usize, // the number of parameters required by this rule.
    pub condition: Condition,
    pub production: Vec<ParameterizedSymbol<A>>,
}

impl<A:Alphabet> Rule<A> {
    pub fn produce(&self, sym: &Symbol<A>) -> Option<SymbolString<A>> {
        let args = &sym.arguments[..];
        if sym.character == self.character && args.len() == self.arity &&
           self.condition.evaluate(args) == Ok(true) {
            let res = SymbolString(self.production
                                       .iter()
                                       .map(|ps| ps.evaluate(args).unwrap() /* XXX */)
                                       .collect());
            Some(res)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct System<A: Alphabet> {
    pub rules: Vec<Rule<A>>,
}

impl<A:Alphabet> System<A> {
    pub fn develop(&self, axiom: SymbolString<A>, iterations: usize) -> (SymbolString<A>, usize) {
        let mut current = axiom;

        for iter in 0..iterations {
            let (next, progress) = self.develop1(&current);
            if !progress {
                return (current, iter);
            }
            current = next;
        }
        return (current, iterations);
    }

    pub fn develop1(&self, axiom: &SymbolString<A>) -> (SymbolString<A>, bool) {
        let mut expanded = Vec::new();
        let mut any_rule_applied = false;

        for symbol in axiom.0.iter() {
            let mut found = false;
            for rule in self.rules.iter() {
                if let Some(rhs) = rule.produce(&symbol) {
                    expanded.extend(rhs.0);
                    any_rule_applied = true;
                    found = true;
                    break;
                }
            }
            if !found {
                expanded.push(symbol.clone());
            }
        }

        (SymbolString(expanded), any_rule_applied)
    }
}
