#![feature(box_syntax)]
#![feature(zero_one)]

pub mod expr;

use std::fmt;
use expr::NumType;

pub use expr::{Expr, Condition, ExprError};

/// Used to name symbols and variables.
pub trait Alphabet: fmt::Display + fmt::Debug + Eq + PartialEq + Clone {}

impl Alphabet for &'static str {}
impl Alphabet for char {}

/// A parametric symbol
#[derive(Clone, PartialEq, Eq)]
pub struct Symbol<A: Alphabet, T: NumType> {
    pub symbol: A,
    pub args: Vec<Expr<T>>,
}

impl<A:Alphabet, T:NumType> fmt::Debug for Symbol<A, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{}", self.symbol));
        if self.args.is_empty() {
            return Ok(());
        }

        try!(write!(f, "("));
        for (i, expr) in self.args.iter().enumerate() {
            if i > 0 {
                try!(write!(f, ", "));
            }
            try!(write!(f, "{:?}", expr));
        }
        write!(f, ")")
    }
}

impl<A:Alphabet, T:NumType> Symbol<A, T> {
    pub fn new(symbol: A) -> Symbol<A, T> {
        Symbol {
            symbol: symbol,
            args: vec![],
        }
    }

    pub fn new_parametric(symbol: A, args: Vec<Expr<T>>) -> Symbol<A, T> {
        Symbol {
            symbol: symbol,
            args: args,
        }
    }

    pub fn evaluate(&self, args: &[Expr<T>]) -> Result<Symbol<A, T>, ExprError> {
        let mut values = Vec::with_capacity(self.args.len());
        for expr in self.args.iter() {
            values.push(Expr::Const(try!(expr.evaluate(args))));
        }
        assert!(values.len() == self.args.len());
        Ok(Symbol {
            symbol: self.symbol.clone(),
            args: values,
        })
    }
}

/// A list of Symbols.
#[derive(PartialEq, Eq)]
pub struct SymbolString<A: Alphabet, T: NumType>(pub Vec<Symbol<A, T>>);

impl<A:Alphabet, T: NumType> fmt::Debug for SymbolString<A, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for sym in self.0.iter() {
            try!(write!(f, "{:?}", sym));
        }
        Ok(())
    }
}

impl<A:Alphabet, T:NumType> SymbolString<A, T> {
    pub fn evaluate(&self, args: &[Expr<T>]) -> Result<SymbolString<A, T>, ExprError> {
        let mut syms = Vec::with_capacity(self.0.len());
        for sym in self.0.iter() {
            syms.push(try!(sym.evaluate(args)));
        }
        assert!(syms.len() == self.0.len());
        Ok(SymbolString(syms))
    }
}

#[derive(Debug)]
pub struct Rule<A: Alphabet, T: NumType> {
    pub symbol: A,
    pub condition: Condition<T>,
    pub successor: SymbolString<A, T>,
}

#[derive(Debug, Eq, PartialEq)]
pub enum RuleError {
    SymbolMismatch,
    ConditionFalse,
    ConditionFailed,
    ExprFailed(ExprError),
}


impl<A:Alphabet, T:NumType> Rule<A, T> {
    pub fn new(symbol: A, successor: SymbolString<A, T>) -> Rule<A, T> {
        Rule {
            symbol: symbol,
            condition: Condition::True,
            successor: successor,
        }
    }

    pub fn new_conditional(symbol: A,
                           successor: SymbolString<A, T>,
                           condition: Condition<T>)
                           -> Rule<A, T> {
        Rule {
            symbol: symbol,
            condition: condition,
            successor: successor,
        }
    }

    /// Apply the rule to the given (constant) symbol and if possible, produce
    /// a successor.
    pub fn apply(&self, sym: &Symbol<A, T>) -> Result<SymbolString<A, T>, RuleError> {
        if sym.symbol == self.symbol {
            match self.condition.evaluate(&sym.args) {
                Ok(true) => {
                    match self.successor.evaluate(&sym.args) {
                        Ok(symstr) => Ok(symstr),
                        Err(e) => Err(RuleError::ExprFailed(e)),
                    }
                }
                Ok(false) => {
                    Err(RuleError::ConditionFalse)
                }
                _ => {
                    Err(RuleError::ConditionFailed)
                }
            }
        } else {
            Err(RuleError::SymbolMismatch)
        }
    }
}

#[test]
fn test_rule_apply() {
    let p = Symbol::new_parametric("P", vec![Expr::Const(123u32)]);
    let rule = Rule::new("A", SymbolString(vec![p.clone()]));
    assert_eq!(Err(RuleError::SymbolMismatch),
               rule.apply(&Symbol::new("P")));
    assert_eq!(Ok(SymbolString(vec![Symbol::new_parametric("P", vec![Expr::Const(123u32)])])),
               rule.apply(&Symbol::new("A")));

    let rule = Rule::new_conditional("A", SymbolString(vec![p.clone()]), Condition::False);
    assert_eq!(Err(RuleError::ConditionFalse),
               rule.apply(&Symbol::new("A")));
}

#[derive(Debug)]
pub struct System<A: Alphabet, T: NumType> {
    rules: Vec<Rule<A, T>>,
}

impl<A:Alphabet, T:NumType> System<A, T> {
    pub fn new() -> System<A, T> {
        System { rules: vec![] }
    }

    pub fn add_rule(&mut self, rule: Rule<A, T>) {
        self.rules.push(rule);
    }

    /// Apply first matching rule and return expanded successor.
    fn apply_first_rule(&self, sym: &Symbol<A, T>) -> Option<SymbolString<A, T>> {
        for rule in self.rules.iter() {
            if let Ok(successor) = rule.apply(sym) {
                return Some(successor);
            }
        }
        return None;
    }

    /// Apply in parallel the first matching rule to each symbol in the string.
    /// Returns the total number of rule applications.
    pub fn develop_step(&self, axiom: &SymbolString<A, T>) -> (SymbolString<A, T>, usize) {
        let mut expanded = Vec::new();
        let mut rule_applications = 0;

        for sym in axiom.0.iter() {
            match self.apply_first_rule(sym) {
                Some(successor) => {
                    expanded.extend(successor.0);
                    rule_applications += 1;
                    // XXX: Count rule applications of the matching rule.
                }
                None => {
                    expanded.push(sym.clone());
                }
            }
        }

        (SymbolString(expanded), rule_applications)
    }

    /// Develop the system starting with `axiom` up to `max_iterations`. Return iteration count.
    pub fn develop(&self,
                   axiom: SymbolString<A, T>,
                   max_iterations: usize)
                   -> (SymbolString<A, T>, usize) {
        let mut current = axiom;

        for iter in 0..max_iterations {
            let (next, rule_applications) = self.develop_step(&current);
            if rule_applications == 0 {
                return (current, iter);
            }
            current = next;
        }
        return (current, max_iterations);
    }
}
