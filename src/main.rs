#![feature(box_syntax)]

extern crate lindenmayer_system;
extern crate turtle;

use lindenmayer_system::{Symbol, SymbolString, Expr, Rule, System};

use std::fs::File;
use turtle::{Canvas, Turtle};

fn draw(symstr: &SymbolString<char, f32>,
        init_direction: f32,
        default_angle: f32,
        default_distance: f32,
        filename: &str) {
    let mut t = Canvas::new();
    t.right(init_direction);
    for sym in symstr.0.iter() {
        match (sym.symbol, sym.args.get(0)) {
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

fn symstr(s: &str) -> SymbolString<char, f32> {
    SymbolString(s.chars()
                  .filter(|&c| !c.is_whitespace())
                  .map(|c| Symbol::new(c))
                  .collect())
}

fn rule(sym: char, successor: &str) -> Rule<char, f32> {
    Rule::new(sym, symstr(successor))
}

fn koch_curve(maxiter: usize) {
    let axiom = symstr("F++F++F");

    let mut system: System<char, f32> = System::new();
    system.add_rule(rule('F', "F-F++F-F"));
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, -90.0, 60.0, 10.0, &format!("koch_{:02}", iters));
}

fn dragon_curve(maxiter: usize) {
    let axiom = symstr("FX");

    let mut system = System::new();
    system.add_rule(rule('X', "X+YF+"));
    system.add_rule(rule('Y', "-FX-Y"));
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 90.0, 10.0, &format!("dragon_{:02}", iters));
}

fn sierpinski_triangle(maxiter: usize) {
    let axiom = symstr("A");

    let mut system = System::new();
    system.add_rule(rule('A', "+B-A-B+"));
    system.add_rule(rule('B', "-A+B+A-"));
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    // replace A and B with F
    let mut system = System::new();
    system.add_rule(rule('A', "F"));
    system.add_rule(rule('B', "F"));
    let (after, _iters) = system.develop_step(&after);

    draw(&after,
         -90.0,
         60.0,
         10.0,
         &format!("sierpinski_{:02}", iters));
}

fn fractal_plant(maxiter: usize) {
    let axiom = symstr("X");

    let mut system = System::new();
    system.add_rule(rule('X', "F-[[X]+X]+F[+FX]-X"));
    system.add_rule(rule('F', "FF"));
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 25.0, 10.0, &format!("plant_{:02}", iters));
}

fn branching_pattern_abop_1_9(maxiter: usize) {
    const R: f32 = 1.456;
    let axiom = SymbolString(vec![Symbol::new_parametric('A', vec![Expr::Const(300.0)])]);

    let mut system = System::new();
    system.add_rule(Rule::new('A',
                              SymbolString(vec![
            Symbol::new_parametric('F', vec![Expr::Arg(0)]),
            Symbol::new('['),
            Symbol::new('+'),
            Symbol::new_parametric('A', vec![Expr::Div(box Expr::Arg(0), box Expr::Const(R))]),
            Symbol::new(']'),
            Symbol::new('['),
            Symbol::new('-'),
            Symbol::new_parametric('A', vec![Expr::Div(box Expr::Arg(0), box Expr::Const(R))]),
            Symbol::new(']'),
        ])));

    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after,
         0.0,
         85.0,
         0.0,
         &format!("branching_abop_1_9_{:02}", iters));
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
