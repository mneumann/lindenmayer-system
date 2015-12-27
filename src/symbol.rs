use super::{Alphabet, Symbol};
use expression::Expression;
use std::fmt;

/// A parametric symbol
#[derive(Clone, PartialEq, Eq)]
pub struct DSym<A: Alphabet, Expr: Expression> {
    symbol: A,
    args: Vec<Expr>,
}

impl<A: Alphabet, Expr: Expression> fmt::Debug for DSym<A, Expr> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.debug_fmt(f)
    }
}

impl<A: Alphabet, Expr: Expression> Symbol for DSym<A, Expr> {
    type A = A;
    type Expr = Expr;

    fn symbol(&self) -> &A {
        &self.symbol
    }

    fn set_symbol(&mut self, symbol: A) {
        self.symbol = symbol;
    }

    fn args(&self) -> &[Self::Expr] {
        &self.args[..]
    }

    fn from_result_iter<I, E>(symbol: A, args_iter: I) -> Result<Self, E>
        where I: Iterator<Item = Result<Self::Expr, E>>
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

impl<A: Alphabet, Expr: Expression> DSym<A, Expr> {
    pub fn new_parametric(symbol: A, args: Vec<Expr>) -> DSym<A, Expr> {
        DSym {
            symbol: symbol,
            args: args,
        }
    }
}

/// A parametric 1-ary symbol
#[derive(PartialEq, Eq)]
pub struct Sym1<A: Alphabet, Expr: Expression> {
    symbol: A,
    args: [Expr; 1],
}

impl<A: Alphabet, Expr: Expression> Clone for Sym1<A, Expr> {
    fn clone(&self) -> Self {
        Sym1 {
            symbol: self.symbol.clone(),
            args: [self.args[0].clone()],
        }
    }
}

impl<A: Alphabet, Expr: Expression> fmt::Debug for Sym1<A, Expr> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.debug_fmt(f)
    }
}

impl<A: Alphabet, Expr: Expression> Symbol for Sym1<A, Expr> {
    type A = A;
    type Expr = Expr;

    fn symbol(&self) -> &A {
        &self.symbol
    }

    fn set_symbol(&mut self, symbol: A) {
        self.symbol = symbol;
    }

    fn args(&self) -> &[Self::Expr] {
        &self.args[..]
    }

    fn from_result_iter<I, E>(symbol: A, args_iter: I) -> Result<Self, E>
        where I: Iterator<Item = Result<Self::Expr, E>>
    {
        let mut i = args_iter.into_iter();

        // XXX: This should return an error instead of a default value!
        let arg1 = try!(i.next().unwrap_or(Ok(Self::Expr::make_const(<Self::Expr as Expression>::Element::default()))));

        Ok(Sym1 {
            symbol: symbol,
            args: [arg1],
        })
    }
}

impl<A: Alphabet, Expr: Expression> Sym1<A, Expr> {
    pub fn new_parametric(symbol: A, args: (Expr,)) -> Sym1<A, Expr> {
        Sym1 {
            symbol: symbol,
            args: [args.0],
        }
    }
}

/// A parametric 2-ary symbol
#[derive(PartialEq, Eq)]
pub struct Sym2<A: Alphabet, Expr: Expression> {
    symbol: A,
    args: [Expr; 2],
}

impl<A: Alphabet, Expr: Expression> Clone for Sym2<A, Expr> {
    fn clone(&self) -> Self {
        Sym2 {
            symbol: self.symbol.clone(),
            args: [self.args[0].clone(), self.args[1].clone()],
        }
    }
}

impl<A: Alphabet, Expr: Expression> fmt::Debug for Sym2<A, Expr> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.debug_fmt(f)
    }
}

impl<A: Alphabet, Expr: Expression> Symbol for Sym2<A, Expr> {
    type A = A;
    type Expr = Expr;

    fn symbol(&self) -> &A {
        &self.symbol
    }

    fn set_symbol(&mut self, symbol: A) {
        self.symbol = symbol;
    }

    fn args(&self) -> &[Self::Expr] {
        &self.args[..]
    }

    fn from_result_iter<I, E>(symbol: A, args_iter: I) -> Result<Self, E>
        where I: Iterator<Item = Result<Self::Expr, E>>
    {
        let mut i = args_iter.into_iter();

        // XXX: This should return an error instead of a default value!
        let arg1 = try!(i.next().unwrap_or(Ok(Self::Expr::make_const(<Self::Expr as Expression>::Element::default()))));
        let arg2 = try!(i.next().unwrap_or(Ok(Self::Expr::make_const(<Self::Expr as Expression>::Element::default()))));

        Ok(Sym2 {
            symbol: symbol,
            args: [arg1, arg2],
        })
    }
}

impl<A: Alphabet, Expr: Expression> Sym2<A, Expr> {
    pub fn new_parametric(symbol: A, args: (Expr, Expr)) -> Sym2<A, Expr> {
        Sym2 {
            symbol: symbol,
            args: [args.0, args.1],
        }
    }
}
