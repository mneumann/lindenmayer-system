use turtle::{Canvas, Turtle};
use std::fs::File;
use std::env;
use std::str::FromStr;
pub use lindenmayer_system::old::{SymbolString, Rule, System, LSystem, Symbol};
pub use lindenmayer_system::old::symbol::DSym;
pub use expression::num_expr::NumExpr as Expr;
pub use expression::cond::Cond;

pub fn num_iterations() -> usize {
    usize::from_str(&env::args().nth(1).unwrap_or("0".to_string())).unwrap()
}

pub fn draw(symstr: &SymbolString<DSym<char, Expr<f32>>>,
            init_direction: f32,
            default_angle: f32,
            default_distance: f32,
            filename: &str) {
    let mut t = Canvas::new();
    t.right(init_direction);
    for sym in symstr.0.iter() {
        match (*sym.symbol(), sym.args().get(0)) {
            ('F', Some(&Expr::Const(d))) => t.forward(d),
            ('F', None) => t.forward(default_distance),

            ('f', Some(&Expr::Const(d))) => t.move_forward(d),
            ('f', None) => t.move_forward(default_distance),

            ('+', Some(&Expr::Const(a))) => t.rotate(a),
            ('+', None) => t.rotate(default_angle),

            ('-', Some(&Expr::Const(a))) => t.rotate(-a),
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
pub fn symstr(s: &str) -> SymbolString<DSym<char, Expr<f32>>> {
    SymbolString(s.chars()
                  .filter(|&c| !c.is_whitespace())
                  .map(|c| Symbol::new(c))
                  .collect())
}

#[allow(dead_code)]
pub fn rule(sym: char, successor: &str) -> Rule<DSym<char, Expr<f32>>, Cond<Expr<f32>>> {
    Rule::new(sym, Cond::True, symstr(successor))
}
