use turtle_graphics::{Canvas, Turtle};
use std::fs::File;
use std::env;
use std::str::FromStr;
use std::fmt::Debug;
use lindenmayer_system::parametric::{PSym, PRule, PSystem};
pub use lindenmayer_system::parametric::{ParametricSymbol, ParametricRule, ParametricSystem};
pub use expression::cond::Cond;
pub use expression_num::NumExpr as Expr;

pub type Real = f32;
pub type SymExpr = PSym<char, Expr<Real>>;
pub type SymR = PSym<char, Real>;
pub type Rule = PRule<char, SymExpr, SymR, Cond<Expr<Real>>>;
pub type System = PSystem<Rule>;

pub fn num_iterations() -> usize {
    usize::from_str(&env::args().nth(1).unwrap_or("0".to_string())).unwrap()
}

pub fn draw(symstr: &[SymR],
            init_direction: f32,
            default_angle: f32,
            default_distance: f32,
            filename: &str) {
    let mut t = Canvas::new();
    t.right(init_direction);
    for sym in symstr.iter() {
        match (*sym.symbol(), sym.params().get(0)) {
            ('F', Some(&d)) => t.forward(d),
            ('F', None) => t.forward(default_distance),

            ('f', Some(&d)) => t.move_forward(d),
            ('f', None) => t.move_forward(default_distance),

            ('+', Some(&a)) => t.rotate(a),
            ('+', None) => t.rotate(default_angle),

            ('-', Some(&a)) => t.rotate(-a),
            ('-', None) => t.rotate(-default_angle),

            ('[', None) => t.push(),
            (']', None) => t.pop(),
            _ => {}
        }
    }
    t.save_svg(&mut File::create(filename.to_string() + ".svg").unwrap()).unwrap();
    t.save_eps(&mut File::create(filename.to_string() + ".eps").unwrap()).unwrap();
}

#[allow(dead_code)]
pub fn symstr<S, R>(s: &str) -> Vec<S>
    where S: ParametricSymbol<Sym = char, Param = R>,
          R: Clone + Debug + PartialEq
{
    s.chars()
     .filter(|&c| !c.is_whitespace())
     .map(|c| S::new_from_vec(c, vec![]).unwrap())
     .collect()
}

#[allow(dead_code)]
pub fn rule(sym: char, successor: &str) -> Rule {
    Rule::new(sym, Cond::True, symstr(successor), 0)
}
