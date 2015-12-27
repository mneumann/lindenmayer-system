use std::fmt::Debug;
use std::marker::PhantomData;
use super::Alphabet;
use super::RuleError;
use expression::{Expression, Condition};

pub trait ParametricSymbol: Clone + PartialEq + Debug
{
    type Sym: Alphabet;
    type Param: Clone + Debug + PartialEq;

    fn symbol(&self) -> &Self::Sym;
    fn symbol_mut(&mut self) -> &mut Self::Sym;

    fn params(&self) -> &[Self::Param];
    fn params_mut(&mut self) -> &mut [Self::Param];

    /// Construct a new ParametricSymbol. If the iterator contains a wrong
    /// number of parameters, return None.
    fn new_from_result_iter<I, E>(symbol: Self::Sym, iter: I) -> Option<Result<Self, E>>
        where I: Iterator<Item = Result<Self::Param, E>>;

    fn new_from_iter<I>(symbol: Self::Sym, iter: I) -> Option<Self>
        where I: Iterator<Item = Self::Param>
    {
        match Self::new_from_result_iter::<_, ()>(symbol, iter.map(|i| Ok(i))) {
            Some(Ok(res)) => Some(res),
            Some(Err(())) => panic!(),
            None => None,
        }
    }

    fn new_from_vec(symbol: Self::Sym, vec: Vec<Self::Param>) -> Option<Self> {
        Self::new_from_iter(symbol, vec.into_iter())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PSym<Sym: Alphabet, Param: Clone + Debug + PartialEq> {
    symbol: Sym,
    params: Vec<Param>,
}

impl<Sym: Alphabet, Param: Clone + Debug + PartialEq> ParametricSymbol for PSym<Sym, Param> {
    type Sym = Sym;
    type Param = Param;

    fn symbol(&self) -> &Self::Sym {
        &self.symbol
    }
    fn symbol_mut(&mut self) -> &mut Self::Sym {
        &mut self.symbol
    }
    fn params(&self) -> &[Self::Param] {
        &self.params
    }
    fn params_mut(&mut self) -> &mut [Self::Param] {
        &mut self.params
    }

    fn new_from_result_iter<I, E>(symbol: Self::Sym, iter: I) -> Option<Result<Self, E>>
        where I: Iterator<Item = Result<Self::Param, E>>
    {
        let mut params = Vec::with_capacity(iter.size_hint().0);
        for p in iter {
            match p {
                Ok(p) => params.push(p),
                Err(e) => return Some(Err(e)),
            }
        }
        Some(Ok(PSym {
            symbol: symbol,
            params: params,
        }))
    }
}

#[derive(Debug, PartialEq)]
pub struct PSym1<Sym: Alphabet, Param: Clone + Debug + PartialEq> {
    symbol: Sym,
    params: [Param; 1],
}

impl<Sym: Alphabet, Param: Clone + Debug + PartialEq> Clone for PSym1<Sym, Param> {
    fn clone(&self) -> Self {
        PSym1 {
            symbol: self.symbol.clone(),
            params: [self.params[0].clone()],
        }
    }
}

impl<Sym: Alphabet, Param: Clone + Debug + PartialEq> ParametricSymbol for PSym1<Sym, Param> {
    type Sym = Sym;
    type Param = Param;

    fn symbol(&self) -> &Self::Sym {
        &self.symbol
    }
    fn symbol_mut(&mut self) -> &mut Self::Sym {
        &mut self.symbol
    }
    fn params(&self) -> &[Self::Param] {
        &self.params
    }
    fn params_mut(&mut self) -> &mut [Self::Param] {
        &mut self.params
    }

    fn new_from_result_iter<I, E>(symbol: Self::Sym, mut iter: I) -> Option<Result<Self, E>>
        where I: Iterator<Item = Result<Self::Param, E>>
    {
        let p1 = match iter.next() {
            Some(Ok(p)) => p,
            Some(Err(e)) => return Some(Err(e)),
            None => return None,
        };
        if let Some(_) = iter.next() {
            return None;
        }

        Some(Ok(PSym1 {
            symbol: symbol,
            params: [p1],
        }))
    }
}

#[derive(Debug, PartialEq)]
pub struct PSym2<Sym: Alphabet, Param: Clone + Debug + PartialEq> {
    symbol: Sym,
    params: [Param; 2],
}

impl<Sym: Alphabet, Param: Clone + Debug + PartialEq> Clone for PSym2<Sym, Param> {
    fn clone(&self) -> Self {
        PSym2 {
            symbol: self.symbol.clone(),
            params: [self.params[0].clone(), self.params[1].clone()],
        }
    }
}

impl<Sym: Alphabet, Param: Clone + Debug + PartialEq> ParametricSymbol for PSym2<Sym, Param> {
    type Sym = Sym;
    type Param = Param;

    fn symbol(&self) -> &Self::Sym {
        &self.symbol
    }
    fn symbol_mut(&mut self) -> &mut Self::Sym {
        &mut self.symbol
    }
    fn params(&self) -> &[Self::Param] {
        &self.params
    }
    fn params_mut(&mut self) -> &mut [Self::Param] {
        &mut self.params
    }

    fn new_from_result_iter<I, E>(symbol: Self::Sym, mut iter: I) -> Option<Result<Self, E>>
        where I: Iterator<Item = Result<Self::Param, E>>
    {
        let p1 = match iter.next() {
            Some(Ok(p)) => p,
            Some(Err(e)) => return Some(Err(e)),
            None => return None,
        };
        let p2 = match iter.next() {
            Some(Ok(p)) => p,
            Some(Err(e)) => return Some(Err(e)),
            None => return None,
        };
        if let Some(_) = iter.next() {
            return None;
        }

        Some(Ok(PSym2 {
            symbol: symbol,
            params: [p1, p2],
        }))
    }
}

#[derive(Debug, Clone)]
pub struct ParametricRule<Sym, PS, PS2, C>
    where Sym: Alphabet,
          PS: ParametricSymbol<Sym = Sym, Param = C::Expr>,
          PS2: ParametricSymbol<Sym = Sym, Param = <C::Expr as Expression>::Element>,
          C: Condition
{
    symbol: Sym,
    condition: C,
    production: Vec<PS>,
    arity: usize,
    _marker: PhantomData<PS2>,
}

impl<Sym, PS, PS2, C> ParametricRule<Sym, PS, PS2, C>
    where Sym: Alphabet,
          PS: ParametricSymbol<Sym = Sym, Param = C::Expr>,
          PS2: ParametricSymbol<Sym = Sym, Param = <C::Expr as Expression>::Element>,
          C: Condition
{
    pub fn new(sym: Sym, cond: C, prod: Vec<PS>, arity: usize) -> ParametricRule<Sym, PS, PS2, C> {
        ParametricRule {
            symbol: sym,
            condition: cond,
            production: prod,
            arity: arity,
            _marker: PhantomData,
        }
    }

    /// Tries to apply the rule and if applicable, produces a successor.
    pub fn apply(&self, psym: &PS2) -> Result<Vec<PS2>, RuleError> {
        if self.arity != psym.params().len() {
            Err(RuleError::RuleArityMismatch)
        } else if self.symbol.eq(psym.symbol()) {
            match self.condition.evaluate(psym.params()) {
                Ok(true) => {
                    let mut new_symbol_string = Vec::with_capacity(self.production.len());

                    // evaluate all parameters of all symbols in the production
                    for prod_sym in self.production.iter() {
                        match PS2::new_from_result_iter(prod_sym.symbol().clone(),
                                                        prod_sym.params().iter().map(|expr| {
                                                            expr.evaluate(psym.params())
                                                        })) {
                            Some(Ok(new_sym)) => {
                                new_symbol_string.push(new_sym);
                            }
                            Some(Err(e)) => {
                                return Err(RuleError::ExprFailed(e));
                            }
                            None => {
                                return Err(RuleError::ArityMismatch);
                            }
                        }
                    }

                    Ok(new_symbol_string)
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
    use expression::num_expr::NumExpr;
    use expression::cond::Cond;
    let expr_s = PSym::new_from_vec('P', vec![NumExpr::Const(123u32)]).unwrap();

    let rule = ParametricRule::<_,
                                PSym<_, NumExpr<u32>>,
                                PSym<_, u32>,
                                _>::new('A', Cond::True, vec![expr_s.clone()], 1);

    let param_s = PSym::new_from_vec('P', vec![123u32]).unwrap();
    assert_eq!(Err(RuleError::SymbolMismatch), rule.apply(&param_s));

    let param_s = PSym::new_from_vec('A', vec![123u32]).unwrap();
    let result_s = PSym::new_from_vec('P', vec![123u32]).unwrap();
    assert_eq!(Ok(vec![result_s]), rule.apply(&param_s));

    let rule = ParametricRule::<_,
                                PSym<_, NumExpr<u32>>,
                                PSym<_, u32>,
                                _>::new('A', Cond::False, vec![expr_s.clone()], 1);
    assert_eq!(Err(RuleError::ConditionFalse), rule.apply(&param_s));
}