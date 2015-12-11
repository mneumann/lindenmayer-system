#![feature(box_syntax)]
#![feature(zero_one)]

pub mod expr;
pub mod symbol;

use std::{fmt, iter};
use expr::NumType;

pub use expr::{Expr, Condition, ExprError};

/// Used to name symbols and variables.
pub trait Alphabet: fmt::Display + fmt::Debug + PartialEq + Eq + Clone {}

impl Alphabet for &'static str {}
impl Alphabet for char {}

/// The common interface for Symbols. Basically this abstracts over
/// the argument implementation.
pub trait Symbol: Clone + PartialEq + fmt::Debug {
    type A: Alphabet;

    type T: NumType;

    fn symbol(&self) -> &Self::A;

    fn args(&self) -> &[Expr<Self::T>];

    fn from_result_iter<I, E>(symbol: Self::A, args_iter: I) -> Result<Self, E> where I: Iterator<Item = Result<Expr<Self::T>, E>>;

    fn new(symbol: Self::A) -> Self {
        Self::from_iter(symbol, iter::empty())
    }

    fn from_iter<I>(symbol: Self::A, args_iter: I) -> Self where I: Iterator<Item = Expr<Self::T>> {
        let res: Result<_, ()> = Self::from_result_iter(symbol, args_iter.map(|i| Ok(i)));
        res.unwrap()
    }

    fn evaluate(&self, bindings: &[Expr<Self::T>]) -> Result<Self, ExprError> {
        Self::from_result_iter((*self.symbol()).clone(),
                          self.args()
                              .iter()
                              .map(|expr| expr.evaluate(bindings).map(|ok| Expr::Const(ok))))

    }

    fn debug_fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let args = self.args();
        try!(write!(f, "{}", *self.symbol()));
        if args.is_empty() {
            return Ok(());
        }

        try!(write!(f, "("));
        for (i, expr) in args.iter().enumerate() {
            if i > 0 {
                try!(write!(f, ", "));
            }
            try!(write!(f, "{:?}", expr));
        }
        write!(f, ")")
    }
}

/// A list of Symbols.
#[derive(PartialEq, Eq)]
pub struct SymbolString<S:Symbol>(pub Vec<S>);

impl<S:Symbol> fmt::Debug for SymbolString<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for sym in self.0.iter() {
            try!(write!(f, "{:?}", sym));
        }
        Ok(())
    }
}

impl<S:Symbol> SymbolString<S> {
    fn from_result_iter<I, E>(symbol_iter: I) -> Result<SymbolString<S>, E>
        where I: Iterator<Item = Result<S, E>>
    {
        let mut symbols = Vec::with_capacity(symbol_iter.size_hint().0);
        for sym in symbol_iter.into_iter() {
            symbols.push(try!(sym));
        }
        Ok(SymbolString(symbols))
    }

    pub fn evaluate(&self, bindings: &[Expr<S::T>]) -> Result<SymbolString<S>, ExprError> {
        SymbolString::from_result_iter(self.0.iter().map(|sym| sym.evaluate(bindings)))
    }
}

#[derive(Debug)]
pub struct Rule<S: Symbol> {
    pub symbol: S::A,
    pub condition: Condition<S::T>,
    pub successor: SymbolString<S>,
}

#[derive(Debug, Eq, PartialEq)]
pub enum RuleError {
    SymbolMismatch,
    ConditionFalse,
    ConditionFailed,
    ExprFailed(ExprError),
}

impl<S:Symbol> Rule<S> {
    pub fn new(symbol: S::A, successor: SymbolString<S>) -> Rule<S> {
        Rule {
            symbol: symbol,
            condition: Condition::True,
            successor: successor,
        }
    }

    pub fn new_conditional(symbol: S::A,
                           successor: SymbolString<S>,
                           condition: Condition<S::T>)
                           -> Rule<S> {
        Rule {
            symbol: symbol,
            condition: condition,
            successor: successor,
        }
    }

    /// Apply the rule to the given (constant) symbol and if possible, produce
    /// a successor.
    pub fn apply(&self, sym: &S) -> Result<SymbolString<S>, RuleError> {
        let args = sym.args();
        if self.symbol.eq(sym.symbol()) {
            match self.condition.evaluate(args) {
                Ok(true) => {
                    match self.successor.evaluate(args) {
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
    use symbol::DSym;
    let p = DSym::new_parametric("P", vec![Expr::Const(123u32)]);
    let rule = Rule::new("A", SymbolString(vec![p.clone()]));
    assert_eq!(Err(RuleError::SymbolMismatch),
               rule.apply(&DSym::new("P")));
    assert_eq!(Ok(SymbolString(vec![DSym::new_parametric("P", vec![Expr::Const(123u32)])])),
               rule.apply(&DSym::new("A")));

    let rule = Rule::new_conditional("A", SymbolString(vec![p.clone()]), Condition::False);
    assert_eq!(Err(RuleError::ConditionFalse),
               rule.apply(&DSym::new("A")));
}

#[derive(Debug)]
pub struct System<S: Symbol> {
    rules: Vec<Rule<S>>,
}

impl<S:Symbol> System<S> {
    pub fn new() -> System<S> {
        System { rules: vec![] }
    }

    pub fn add_rule(&mut self, rule: Rule<S>) {
        self.rules.push(rule);
    }

    /// Apply first matching rule and return expanded successor.
    fn apply_first_rule(&self, sym: &S) -> Option<SymbolString<S>> {
        for rule in self.rules.iter() {
            if let Ok(successor) = rule.apply(sym) {
                return Some(successor);
            }
        }
        return None;
    }

    /// Apply in parallel the first matching rule to each symbol in the string.
    /// Returns the total number of rule applications.
    pub fn develop_step(&self, axiom: &SymbolString<S>) -> (SymbolString<S>, usize) {
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
                   axiom: SymbolString<S>,
                   max_iterations: usize)
                   -> (SymbolString<S>, usize) {
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
