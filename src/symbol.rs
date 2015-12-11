use super::{Alphabet, Symbolic, Expr};
use super::expr::NumType;
use std::fmt;

/// A parametric symbol
#[derive(Clone, PartialEq, Eq)]
pub struct Symbol<A: Alphabet, T: NumType> {
    pub symbol: A,
    pub args: Vec<Expr<T>>,
}

impl<A:Alphabet, T:NumType> fmt::Debug for Symbol<A, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.debug_fmt(f)
    }
}

impl<A:Alphabet, T:NumType> Symbolic for Symbol<A, T> {
    type A = A;
    type T = T;

    fn symbol(&self) -> &A {
        &self.symbol
    }

    fn args(&self) -> &[Expr<T>] {
        &self.args[..]
    }

    fn from_iter<I, E>(symbol: A, args_iter: I) -> Result<Symbol<A, T>, E>
        where I: Iterator<Item = Result<Expr<T>, E>>
    {
        let mut values = Vec::with_capacity(args_iter.size_hint().0);
        for expr in args_iter.into_iter() {
            values.push(try!(expr));
        }
        Ok(Symbol {
            symbol: symbol,
            args: values,
        })
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
}
