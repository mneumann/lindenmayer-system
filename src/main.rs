#![feature(box_syntax)]

// SymbolExpr
// abstract over Argument

extern crate turtle;
extern crate lindenmayer_system;

use std::fmt;
use std::fs::File;
use turtle::{Canvas, Turtle};
use lindenmayer_system::{Alphabet, SymbolString, Symbol, Expr, System, NumType,
                         ParameterizedSymbol, Condition, Rule, Argument};

#[derive(Eq, PartialEq, Clone)]
struct Character(char);
impl Alphabet for Character {}

impl fmt::Debug for Character {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

fn symstr_from_str(s: &str) -> SymbolString<Character> {
    SymbolString(s.chars()
                  .filter(|&c| !c.is_whitespace())
                  .map(|c| Symbol::new(Character(c)))
                  .collect())
}

fn production_from_str(s: &str) -> Vec<ParameterizedSymbol<Character>> {
    s.chars()
     .filter(|&c| !c.is_whitespace())
     .map(|c| ParameterizedSymbol::new(Character(c)))
     .collect()
}

/// A simple rule does not have any conditions nor parameters.
fn simple_rule(c: char, production: &str) -> Rule<Character> {
    Rule {
        character: Character(c),
        arity: 0,
        condition: Condition::True,
        production: production_from_str(production),
    }
}

fn psym(c: char, exprs: Vec<Expr>) -> ParameterizedSymbol<Character> {
    ParameterizedSymbol {
        character: Character(c),
        expressions: exprs,
    }
}


fn draw(symstr: &SymbolString<Character>,
        init_direction: f32,
        angle: f32,
        distance: f32,
        filename: &str) {
    let mut t = Canvas::new();
    t.right(init_direction);
    for sym in symstr.0.iter() {
        match sym.character.0 {
            'F' => t.forward(distance),
            'f' => t.move_forward(distance),
            '+' => t.left(angle),
            '-' => t.right(angle),
            '[' => t.push(),
            ']' => t.pop(),
            _ => {}
        }
    }
    t.save_svg(&mut File::create(filename.to_string() + ".svg").unwrap()).unwrap();
    t.save_eps(&mut File::create(filename.to_string() + ".eps").unwrap()).unwrap();
}

fn draw_parametric(symstr: &SymbolString<Character>, default_angle: f32, filename: &str) {
    let mut t = Canvas::new();
    for sym in symstr.0.iter() {
        match (sym.character.0, sym.arguments.get(0).map(|a| a.0)) {
            ('F', Some(d)) => t.forward(d),
            ('f', Some(d)) => t.move_forward(d),
            ('+', Some(a)) => t.rotate(a),
            ('+', None) => t.rotate(default_angle),
            ('-', Some(a)) => t.rotate(-a),
            ('-', None) => t.rotate(-default_angle),
            ('[', None) => t.push(),
            (']', None) => t.pop(),
            _ => {}
        }
    }
    t.save_svg(&mut File::create(filename.to_string() + ".svg").unwrap()).unwrap();
    t.save_eps(&mut File::create(filename.to_string() + ".eps").unwrap()).unwrap();
}



fn koch_curve(maxiter: usize) {
    let axiom = symstr_from_str("F++F++F");

    let system = System { rules: vec![simple_rule('F', "F-F++F-F")] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, -90.0, 60.0, 10.0, &format!("koch_{:02}", iters));
}

fn dragon_curve(maxiter: usize) {
    let axiom = symstr_from_str("FX");

    let system = System { rules: vec![simple_rule('X', "X+YF+"), simple_rule('Y', "-FX-Y")] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 90.0, 10.0, &format!("dragon_{:02}", iters));
}

fn sierpinski_triangle(maxiter: usize) {
    let axiom = symstr_from_str("A");

    let system = System { rules: vec![simple_rule('A', "+B-A-B+"), simple_rule('B', "-A+B+A-")] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    // replace A and B with F
    let system = System {
        rules: vec![
        simple_rule('A', "F"),
        simple_rule('B', "F"),
        ],
    };
    let (after, _iters) = system.develop1(&after);

    draw(&after,
         -90.0,
         60.0,
         10.0,
         &format!("sierpinski_{:02}", iters));
}

fn fractal_plant(maxiter: usize) {
    let axiom = symstr_from_str("X");

    let system = System {
        rules: vec![
        simple_rule('X', "F-[[X]+X]+F[+FX]-X"),
        simple_rule('F', "FF"),
        ],
    };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 25.0, 10.0, &format!("plant_{:02}", iters));
}

fn branching_pattern_abop_1_9(maxiter: usize) {
    const R: NumType = 1.456;
    let axiom = SymbolString(vec![Symbol {
                                      character: Character('A'),
                                      arguments: vec![Argument(300.0)],
                                  }]);

    let system = System {
        rules: vec![Rule {
                        character: Character('A'),
                        arity: 1,
                        condition: Condition::True,
                        production: vec![
                                psym('F', vec![Expr::Arg(0)]),
                                psym('[', vec![]),
                                psym('+', vec![]),
                                psym('A', vec![Expr::Div(box Expr::Arg(0), box Expr::Const(R))]),
                                psym(']', vec![]),
                                psym('[', vec![]),
                                psym('-', vec![]),
                                psym('A', vec![Expr::Div(box Expr::Arg(0), box Expr::Const(R))]),
                                psym(']', vec![]),
                        ],
                    }],
    };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw_parametric(&after, 85.0, &format!("branching_abop_1_9_{:02}", iters));
}


fn main() {
    for i in 0..7 {
        koch_curve(i);
    }
    for i in 0..16 {
        dragon_curve(i);
    }
    for i in 0..10 {
        sierpinski_triangle(i);
    }
    for i in 4..8 {
        fractal_plant(i);
    }
    branching_pattern_abop_1_9(15);
}
