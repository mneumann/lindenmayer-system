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
    _marker: PhantomData<PS2>,
}

impl<Sym, PS, PS2, C> ParametricRule<Sym, PS, PS2, C>
    where Sym: Alphabet,
          PS: ParametricSymbol<Sym = Sym, Param = C::Expr>,
          PS2: ParametricSymbol<Sym = Sym, Param = <C::Expr as Expression>::Element>,
          C: Condition
{
    /// Tries to apply the rule and if applicable, produces a successor.
    pub fn apply(&self, psym: &PS) -> Result<Vec<PS2>, RuleError> {
        if self.symbol.eq(psym.symbol()) {
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
