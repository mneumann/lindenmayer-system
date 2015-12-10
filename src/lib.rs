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

/// A symbol whose arguments are all constant values.
#[derive(Clone, Eq, PartialEq)]
pub struct ConstSymbol<A: Alphabet, T: NumType> {
    pub symbol: A,
    pub args: Vec<T>,
}

impl<A:Alphabet, T:NumType> ConstSymbol<A, T> {
    pub fn new(symbol: A) -> ConstSymbol<A, T> {
        ConstSymbol {
            symbol: symbol,
            args: vec![],
        }
    }

    pub fn new_parametric(symbol: A, args: Vec<T>) -> ConstSymbol<A, T> {
        ConstSymbol {
            symbol: symbol,
            args: args,
        }
    }
}


impl<A:Alphabet, T:NumType> fmt::Debug for ConstSymbol<A, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "({}", self.symbol));
        for arg in self.args.iter() {
            try!(write!(f, " {:?}", arg));
        }

        write!(f, ")")
    }
}

/// A symbol (may contain non-constant expressions)
#[derive(Clone)]
pub struct Symbol<A: Alphabet, T: NumType> {
    symbol: A,
    exprs: Vec<Expr<T>>,
}

impl<A:Alphabet, T:NumType> fmt::Debug for Symbol<A, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "({}", self.symbol));
        for expr in self.exprs.iter() {
            try!(write!(f, " {:?}", expr));
        }

        write!(f, ")")
    }
}

impl<A:Alphabet, T:NumType> Symbol<A, T> {
    pub fn new(symbol: A) -> Symbol<A, T> {
        Symbol {
            symbol: symbol,
            exprs: vec![],
        }
    }

    pub fn new_parametric(symbol: A, exprs: Vec<Expr<T>>) -> Symbol<A, T> {
        Symbol {
            symbol: symbol,
            exprs: exprs,
        }
    }

    pub fn evaluate(&self, args: &[T]) -> Result<ConstSymbol<A, T>, ExprError> {
        let mut values = Vec::with_capacity(self.exprs.len());
        for expr in self.exprs.iter() {
            values.push(try!(expr.evaluate(args)));
        }
        assert!(values.len() == self.exprs.len());
        Ok(ConstSymbol {
            symbol: self.symbol.clone(),
            args: values,
        })
    }
}

/// A list of constant Symbols.
#[derive(Eq, PartialEq)]
pub struct ConstSymbolString<A: Alphabet, T: NumType>(pub Vec<ConstSymbol<A, T>>);

impl<A:Alphabet, T: NumType> fmt::Debug for ConstSymbolString<A, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, sym) in self.0.iter().enumerate() {
            if i > 0 {
                try!(write!(f, " "));
            }
            try!(write!(f, "{:?}", sym));
        }
        Ok(())
    }
}

/// A list of Symbols.
pub struct SymbolString<A: Alphabet, T: NumType>(pub Vec<Symbol<A, T>>);

impl<A:Alphabet, T: NumType> fmt::Debug for SymbolString<A, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, sym) in self.0.iter().enumerate() {
            if i > 0 {
                try!(write!(f, " "));
            }
            try!(write!(f, "{:?}", sym));
        }
        Ok(())
    }
}

impl<A:Alphabet, T:NumType> SymbolString<A, T> {
    pub fn evaluate(&self, args: &[T]) -> Result<ConstSymbolString<A, T>, ExprError> {
        let mut csyms = Vec::with_capacity(self.0.len());
        for sym in self.0.iter() {
            csyms.push(try!(sym.evaluate(args)));
        }
        assert!(csyms.len() == self.0.len());
        Ok(ConstSymbolString(csyms))
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

    /// Apply the rule to the given constant symbol and if possible, produce
    /// a successor.
    pub fn apply(&self, csym: &ConstSymbol<A, T>) -> Result<ConstSymbolString<A, T>, RuleError> {
        if csym.symbol == self.symbol {
            match self.condition.evaluate(&csym.args) {
                Ok(true) => {
                    match self.successor.evaluate(&csym.args) {
                        Ok(csymstr) => Ok(csymstr),
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
    let rule = Rule::new("A", Condition::True, SymbolString(vec![p.clone()]));
    assert_eq!(Err(RuleError::SymbolMismatch),
               rule.apply(&ConstSymbol::new("P")));
    assert_eq!(Ok(ConstSymbolString(vec![ConstSymbol::new_parametric("P", vec![123u32])])),
               rule.apply(&ConstSymbol::new("A")));

    let rule = Rule::new("A", Condition::False, SymbolString(vec![p.clone()]));
    assert_eq!(Err(RuleError::ConditionFalse),
               rule.apply(&ConstSymbol::new("A")));
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
    fn apply_first_rule(&self, csym: &ConstSymbol<A, T>) -> Option<ConstSymbolString<A, T>> {
        for rule in self.rules.iter() {
            if let Ok(successor) = rule.apply(csym) {
                return Some(successor);
            }
        }
        return None;
    }

    /// Apply in parallel the first matching rule to each symbol in the string.
    /// Returns the total number of rule applications.
    pub fn develop_step(&self,
                        axiom: &ConstSymbolString<A, T>)
                        -> (ConstSymbolString<A, T>, usize) {
        let mut expanded = Vec::new();
        let mut rule_applications = 0;

        for csym in axiom.0.iter() {
            match self.apply_first_rule(csym) {
                Some(successor) => {
                    expanded.extend(successor.0);
                    rule_applications += 1;
                    // XXX: Count rule applications of the matching rule.
                }
                None => {
                    expanded.push(csym.clone());
                }
            }
        }

        (ConstSymbolString(expanded), rule_applications)
    }

    /// Develop the system starting with `axiom` up to `max_iterations`. Return iteration count.
    pub fn develop(&self,
                   axiom: ConstSymbolString<A, T>,
                   max_iterations: usize)
                   -> (ConstSymbolString<A, T>, usize) {
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
