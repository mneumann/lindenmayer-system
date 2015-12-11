#![feature(box_syntax)]

extern crate lindenmayer_system;
extern crate turtle;
mod helper;

use helper::*;

fn branching_pattern_abop_1_9(maxiter: usize) {
    const R: f32 = 1.456;
    let axiom = SymbolString(vec![DSym::new_parametric('A', vec![Expr::Const(300.0)])]);

    let mut system = System::new();
    system.add_rule(Rule::new('A',
                              SymbolString(vec![
            DSym::new_parametric('F', vec![Expr::Arg(0)]),
            DSym::new('['),
            DSym::new('+'),
            DSym::new_parametric('A', vec![Expr::Div(box Expr::Arg(0), box Expr::Const(R))]),
            DSym::new(']'),
            DSym::new('['),
            DSym::new('-'),
            DSym::new_parametric('A', vec![Expr::Div(box Expr::Arg(0), box Expr::Const(R))]),
            DSym::new(']'),
        ])));

    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 85.0, 0.0, &format!("abop_1_9_{:02}", iters));
}

fn main() {
    branching_pattern_abop_1_9(num_iterations());
}
