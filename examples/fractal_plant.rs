mod helper;

use helper::*;

fn fractal_plant(maxiter: usize) {
    let axiom = symstr("X");

    let mut system = System::new();
    system.add_rule(rule('X', "F-[[X]+X]+F[+FX]-X"));
    system.add_rule(rule('F', "FF"));
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 25.0, 10.0, &format!("plant_{:02}", iters));
}

fn main() {
    fractal_plant(num_iterations());
}
