#![feature(box_syntax)]

extern crate turtle;

use std::fmt;
use std::fs::File;
use turtle::{Canvas, Turtle};

trait Alphabet: fmt::Debug + Eq + PartialEq + Clone {}

type NumType = f32;

/// An argument is an "actual" parameter.
#[derive(Clone)]
struct Argument(pub NumType);

impl fmt::Debug for Argument {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}




#[derive(Debug, Eq, PartialEq)]
enum ExprError {
    /// In case of division by zero.
    DivByZero,
    /// When the argument position `n` in Arg(n) is out of bounds.
    InvalidArg,
}

/// An expression evaluates to a numeric value of `NumType`.
#[derive(Debug, Clone)]
enum Expr {
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
enum Condition {
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
struct Symbol<A: Alphabet> {
    character: A,
    arguments: Vec<Argument>,
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
struct ParameterizedSymbol<A: Alphabet> {
    character: A,
    expressions: Vec<Expr>,
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
    fn new(character: A) -> ParameterizedSymbol<A> {
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


impl<A:Alphabet> Symbol<A> {
    fn new(character: A) -> Symbol<A> {
        Symbol {
            character: character,
            arguments: Vec::new(),
        }
    }
}

// XXX: Rename SymbolString to Word
#[derive(Clone)]
struct SymbolString<A: Alphabet>(Vec<Symbol<A>>);

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
struct Rule<A: Alphabet> {
    character: A,
    arity: usize, // the number of parameters required by this rule.
    condition: Condition,

    production: Vec<ParameterizedSymbol<A>>,
}

impl<A:Alphabet> Rule<A> {
    fn produce(&self, sym: &Symbol<A>) -> Option<SymbolString<A>> {
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
struct System<A: Alphabet> {
    rules: Vec<Rule<A>>,
}

impl<A:Alphabet> System<A> {
    fn develop(&self, axiom: SymbolString<A>, iterations: usize) -> (SymbolString<A>, usize) {
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

    fn develop1(&self, axiom: &SymbolString<A>) -> (SymbolString<A>, bool) {
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

#[derive(Eq, PartialEq, Clone)]
struct Character(char);
impl Alphabet for Character {}

impl fmt::Debug for Character {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

fn symstr_from_str(s: &str) -> SymbolString<Character> {
    SymbolString(s.chars()
                  .filter(|&c| !c.is_whitespace())
                  .map(|c| Symbol::new(Character(c)))
                  .collect())
}

fn production_from_str(s: &str) -> Vec<ParameterizedSymbol<Character>> {
    s.chars()
     .filter(|&c| !c.is_whitespace())
     .map(|c| ParameterizedSymbol::new(Character(c)))
     .collect()
}

/// A simple rule does not have any conditions nor parameters.
fn simple_rule(c: char, production: &str) -> Rule<Character> {
    Rule {
        character: Character(c),
        arity: 0,
        condition: Condition::True,
        production: production_from_str(production),
    }
}

fn draw(symstr: &SymbolString<Character>,
        init_direction: f32,
        angle: f32,
        distance: f32,
        filename: &str) {
    let mut t = Canvas::new();
    t.right(init_direction);
    for sym in symstr.0.iter() {
        match sym.character.0 {
            'F' => t.forward(distance),
            '+' => t.right(angle),
            '-' => t.left(angle),
            '[' => t.push(),
            ']' => t.pop(),
            _ => {}
        }
    }
    t.save_svg(&mut File::create(filename).unwrap()).unwrap();
}

fn koch_curve(maxiter: usize) {
    let axiom = symstr_from_str("F++F++F");

    let system = System { rules: vec![simple_rule('F', "F-F++F-F")] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, -90.0, 60.0, 10.0, &format!("koch_{:02}.svg", iters));
}

fn dragon_curve(maxiter: usize) {
    let axiom = symstr_from_str("FX");

    let system = System { rules: vec![simple_rule('X', "X+YF+"), simple_rule('Y', "-FX-Y")] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 90.0, 10.0, &format!("dragon_{:02}.svg", iters));
}

fn sierpinski_triangle(maxiter: usize) {
    let axiom = symstr_from_str("A");

    let system = System { rules: vec![simple_rule('A', "+B-A-B+"), simple_rule('B', "-A+B+A-")] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    // replace A and B with F
    let system = System {
        rules: vec![
        simple_rule('A', "F"),
        simple_rule('B', "F"),
        ],
    };
    let (after, _iters) = system.develop1(&after);

    draw(&after,
         -90.0,
         60.0,
         10.0,
         &format!("sierpinski_{:02}.svg", iters));
}

fn fractal_plant(maxiter: usize) {
    let axiom = symstr_from_str("X");

    let system = System {
        rules: vec![
        simple_rule('X', "F-[[X]+X]+F[+FX]-X"),
        simple_rule('F', "FF"),
        ],
    };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 25.0, 10.0, &format!("plant_{:02}.svg", iters));
}

fn main() {
    for i in 0..7 {
        koch_curve(i);
    }
    for i in 0..16 {
        dragon_curve(i);
    }
    for i in 0..10 {
        sierpinski_triangle(i);
    }
    for i in 4..8 {
        fractal_plant(i);
    }
}
