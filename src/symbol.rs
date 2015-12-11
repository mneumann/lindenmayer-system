use super::{Alphabet, Symbol, Expr};
use super::expr::NumType;
use std::fmt;

/// A parametric symbol
#[derive(Clone, PartialEq, Eq)]
pub struct DSym<A: Alphabet, T: NumType> {
    symbol: A,
    args: Vec<Expr<T>>,
}

impl<A:Alphabet, T:NumType> fmt::Debug for DSym<A, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.debug_fmt(f)
    }
}

impl<A:Alphabet, T:NumType> Symbol for DSym<A, T> {
    type A = A;
    type T = T;

    fn symbol(&self) -> &A {
        &self.symbol
    }

    fn args(&self) -> &[Expr<T>] {
        &self.args[..]
    }

    fn from_result_iter<I, E>(symbol: A, args_iter: I) -> Result<DSym<A, T>, E>
        where I: Iterator<Item = Result<Expr<T>, E>>
    {
        let mut values = Vec::with_capacity(args_iter.size_hint().0);
        for expr in args_iter.into_iter() {
            values.push(try!(expr));
        }
        Ok(DSym {
            symbol: symbol,
            args: values,
        })
    }
}

impl<A:Alphabet, T:NumType> DSym<A, T> {
    pub fn new_parametric(symbol: A, args: Vec<Expr<T>>) -> DSym<A, T> {
        DSym {
            symbol: symbol,
            args: args,
        }
    }
}

/// A parametric 1-ary symbol
#[derive(PartialEq, Eq)]
pub struct Sym1<A: Alphabet, T: NumType> {
    symbol: A,
    args: [Expr<T>; 1],
}

impl<A:Alphabet, T:NumType> Clone for Sym1<A, T> {
    fn clone(&self) -> Self {
        Sym1 {
            symbol: self.symbol.clone(),
            args: [self.args[0].clone()]
        }
    }
}

impl<A:Alphabet, T:NumType> fmt::Debug for Sym1<A, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.debug_fmt(f)
    }
}

impl<A:Alphabet, T:NumType> Symbol for Sym1<A, T> {
    type A = A;
    type T = T;

    fn symbol(&self) -> &A {
        &self.symbol
    }

    fn args(&self) -> &[Expr<T>] {
        &self.args[..]
    }

    fn from_result_iter<I, E>(symbol: A, args_iter: I) -> Result<Self, E>
        where I: Iterator<Item = Result<Expr<T>, E>>
    {
        let mut i = args_iter.into_iter();

        let arg1 = try!(i.next().unwrap_or(Ok(Expr::Const(T::default()))));

        Ok(Sym1 {
            symbol: symbol,
            args: [arg1]
        })
    }
}

impl<A:Alphabet, T:NumType> Sym1<A, T> {
    pub fn new_parametric(symbol: A, args: (Expr<T>,)) -> Sym1<A, T> {
        Sym1 {
            symbol: symbol,
            args: [args.0],
        }
    }
}

/// A parametric 2-ary symbol
#[derive(PartialEq, Eq)]
pub struct Sym2<A: Alphabet, T: NumType> {
    symbol: A,
    args: [Expr<T>; 2],
}

impl<A:Alphabet, T:NumType> Clone for Sym2<A, T> {
    fn clone(&self) -> Self {
        Sym2 {
            symbol: self.symbol.clone(),
            args: [self.args[0].clone(), self.args[1].clone()]
        }
    }
}

impl<A:Alphabet, T:NumType> fmt::Debug for Sym2<A, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.debug_fmt(f)
    }
}

impl<A:Alphabet, T:NumType> Symbol for Sym2<A, T> {
    type A = A;
    type T = T;

    fn symbol(&self) -> &A {
        &self.symbol
    }

    fn args(&self) -> &[Expr<T>] {
        &self.args[..]
    }

    fn from_result_iter<I, E>(symbol: A, args_iter: I) -> Result<Self, E>
        where I: Iterator<Item = Result<Expr<T>, E>>
    {
        let mut i = args_iter.into_iter();

        let arg1 = try!(i.next().unwrap_or(Ok(Expr::Const(T::default()))));
        let arg2 = try!(i.next().unwrap_or(Ok(Expr::Const(T::default()))));

        Ok(Sym2 {
            symbol: symbol,
            args: [arg1, arg2]
        })
    }
}

impl<A:Alphabet, T:NumType> Sym2<A, T> {
    pub fn new_parametric(symbol: A, args: (Expr<T>, Expr<T>)) -> Sym2<A, T> {
        Sym2 {
            symbol: symbol,
            args: [args.0, args.1],
        }
    }
}
