extern crate lindenmayer_system;
extern crate turtle;
mod helper;

use helper::*;

fn sierpinski(maxiter: usize) {
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
    let (after, _iters) = system.develop_next(&after);

    draw(&after,
         -90.0,
         60.0,
         10.0,
         &format!("sierpinski_{:02}", iters));
}

fn main() {
    sierpinski(num_iterations());
}
