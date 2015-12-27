extern crate lindenmayer_system;
extern crate turtle;
extern crate expression;
extern crate expression_num;
mod helper;

use helper::*;

fn koch_curve(maxiter: usize) {
    let axiom = symstr("F++F++F");

    let mut system = System::new();
    system.add_rule(rule('F', "F-F++F-F"));
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, -90.0, 60.0, 10.0, &format!("koch_{:02}", iters));
}

fn main() {
    koch_curve(num_iterations());
}
