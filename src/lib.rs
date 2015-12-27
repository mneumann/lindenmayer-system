extern crate asexp;
extern crate expression;

pub mod symbol;
pub mod parametric;

use std::{fmt, iter};
use std::fmt::Debug;

use expression::{Expression, ExpressionError, Condition};

/// Used to name symbols and variables.
pub trait Alphabet: Debug + PartialEq + Eq + Clone {}

impl Alphabet for &'static str {}
impl Alphabet for char {}
impl Alphabet for u8 {}
impl Alphabet for u16 {}
impl Alphabet for u32 {}
impl Alphabet for u64 {}
impl Alphabet for usize {}

/// The common interface for Symbols. Basically this abstracts over
/// the argument implementation.
pub trait Symbol: Clone + PartialEq + fmt::Debug {
    type A: Alphabet;
    type Expr: Expression;

    fn symbol(&self) -> &Self::A;

    fn set_symbol(&mut self, symbol: Self::A);

    fn args(&self) -> &[Self::Expr];

    fn from_result_iter<I, E>(symbol: Self::A, args_iter: I) -> Result<Self, E>
        where I: Iterator<Item = Result<Self::Expr, E>>;

    fn new(symbol: Self::A) -> Self {
        Self::from_iter(symbol, iter::empty())
    }

    fn from_iter<I>(symbol: Self::A, args_iter: I) -> Self
        where I: Iterator<Item = Self::Expr>
    {
        let res: Result<_, ()> = Self::from_result_iter(symbol, args_iter.map(|i| Ok(i)));
        res.unwrap()
    }

    fn evaluate(&self, bindings: &[Self::Expr]) -> Result<Self, ExpressionError> {
        // XXX
        let empty: &[<Self::Expr as Expression>::Element] = &[];
        let binds: Vec<_> = bindings.iter().map(|b| b.evaluate(empty).unwrap()).collect();

        Self::from_result_iter((*self.symbol()).clone(),
                               self.args()
                                   .iter()
                                   .map(|expr| {
                                       expr.evaluate(&binds).map(|ok| Self::Expr::make_const(ok))
                                   }))

    }

    fn debug_fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let args = self.args();
        try!(write!(f, "{:?}", *self.symbol()));
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
#[derive(PartialEq, Eq, Clone)]
pub struct SymbolString<S: Symbol>(pub Vec<S>);

impl<S: Symbol> fmt::Debug for SymbolString<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for sym in self.0.iter() {
            try!(write!(f, "{:?}", sym));
        }
        Ok(())
    }
}

impl<S: Symbol> SymbolString<S> {
    fn from_result_iter<I, E>(symbol_iter: I) -> Result<SymbolString<S>, E>
        where I: Iterator<Item = Result<S, E>>
    {
        let mut symbols = Vec::with_capacity(symbol_iter.size_hint().0);
        for sym in symbol_iter.into_iter() {
            symbols.push(try!(sym));
        }
        Ok(SymbolString(symbols))
    }

    pub fn evaluate(&self, bindings: &[S::Expr]) -> Result<SymbolString<S>, ExpressionError> {
        SymbolString::from_result_iter(self.0.iter().map(|sym| sym.evaluate(bindings)))
    }
}


#[derive(Debug, Eq, PartialEq)]
pub enum RuleError {
    SymbolMismatch,
    RuleArityMismatch,
    ArityMismatch,
    ConditionFalse,
    ConditionFailed,
    ExprFailed(ExpressionError),
}

#[derive(Debug, Clone)]
pub struct Rule<S, C>
    where S: Symbol,
          C: Condition<Expr = S::Expr>
{
    pub symbol: S::A,
    pub condition: C,
    pub successor: SymbolString<S>,
}

impl<S, C> Rule<S, C>
    where S: Symbol,
          C: Condition<Expr = S::Expr>
{
    pub fn new(symbol: S::A, condition: C, successor: SymbolString<S>) -> Rule<S, C> {
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

        // XXX
        let empty: &[<C::Expr as Expression>::Element] = &[];
        let args2: Vec<_> = args.iter().map(|b| b.evaluate(empty).unwrap()).collect();




        if self.symbol.eq(sym.symbol()) {
            match self.condition.evaluate(&args2) {
                Ok(true) => {
                    match self.successor.evaluate(args) {
                        Ok(symstr) => Ok(symstr),
                        Err(e) => Err(RuleError::ExprFailed(e)),
                    }
                }
                Ok(false) => Err(RuleError::ConditionFalse),
                _ => Err(RuleError::ConditionFailed),
            }
        } else {
            Err(RuleError::SymbolMismatch)
        }
    }
}

#[test]
fn test_rule_apply() {
    use symbol::DSym;
    use expression::num_expr::NumExpr as Expr;
    use expression::cond::Cond;
    let p = DSym::new_parametric("P", vec![Expr::Const(123u32)]);
    let rule = Rule::new("A", Cond::True, SymbolString(vec![p.clone()]));
    assert_eq!(Err(RuleError::SymbolMismatch), rule.apply(&DSym::new("P")));
    assert_eq!(Ok(SymbolString(vec![DSym::new_parametric("P", vec![Expr::Const(123u32)])])),
               rule.apply(&DSym::new("A")));

    let rule = Rule::new("A", Cond::False, SymbolString(vec![p.clone()]));
    assert_eq!(Err(RuleError::ConditionFalse), rule.apply(&DSym::new("A")));
}

pub trait LSystem<S: Symbol> {
    fn apply_first_rule(&self, sym: &S) -> Option<SymbolString<S>>;

    /// Apply in parallel the first matching rule to each symbol in the string.
    /// Returns the total number of rule applications.
    fn develop_next(&self, axiom: &SymbolString<S>) -> (SymbolString<S>, usize) {
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
    fn develop(&self, axiom: SymbolString<S>, max_iterations: usize) -> (SymbolString<S>, usize) {
        let mut current = axiom;

        for iter in 0..max_iterations {
            let (next, rule_applications) = self.develop_next(&current);
            if rule_applications == 0 {
                return (current, iter);
            }
            current = next;
        }
        return (current, max_iterations);
    }
}

#[derive(Debug, Clone)]
pub struct System<S, C>
    where S: Symbol,
          C: Condition<Expr = S::Expr>
{
    rules: Vec<Rule<S, C>>,
}

impl<S, C> System<S, C>
    where S: Symbol,
          C: Condition<Expr = S::Expr>
{
    pub fn new() -> System<S, C> {
        System { rules: vec![] }
    }

    pub fn add_rule(&mut self, rule: Rule<S, C>) {
        self.rules.push(rule);
    }
}

/// Apply first matching rule and return expanded successor.
pub fn apply_first_rule<S, C>(rules: &[Rule<S, C>], sym: &S) -> Option<SymbolString<S>>
    where S: Symbol,
          C: Condition<Expr = S::Expr>
{
    for rule in rules {
        if let Ok(successor) = rule.apply(sym) {
            return Some(successor);
        }
    }
    return None;
}

impl<S, C> LSystem<S> for System<S, C>
    where S: Symbol,
          C: Condition<Expr = S::Expr>
{
    /// Apply first matching rule and return expanded successor.
    fn apply_first_rule(&self, sym: &S) -> Option<SymbolString<S>> {
        apply_first_rule(&self.rules, sym)
    }
}
