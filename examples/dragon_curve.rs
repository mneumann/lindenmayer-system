extern crate lindenmayer_system;
extern crate turtle;
extern crate expression;
extern crate expression_num;
mod helper;

use helper::*;

fn dragon_curve(maxiter: usize) {
    let axiom = symstr("FX");

    let mut system = System::new();
    system.add_rule(rule('X', "X+YF+"));
    system.add_rule(rule('Y', "-FX-Y"));
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 90.0, 10.0, &format!("dragon_{:02}", iters));
}


fn main() {
    dragon_curve(num_iterations());
}
