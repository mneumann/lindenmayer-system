mod helper;

use helper::*;

fn branching_pattern_abop_1_9(maxiter: usize) {
    const R: f32 = 1.456;
    let axiom = vec![SymR::new_from_vec('A', vec![300.0]).unwrap()];

    let mut system = System::new();

    system.add_rule(Rule::new('A', Cond::True,
                              vec![
            SymExpr::new_from_vec('F', vec![Expr::Var(0)]).unwrap(),
            SymExpr::new_from_vec('[', vec![]).unwrap(),
            SymExpr::new_from_vec('+', vec![]).unwrap(),
            SymExpr::new_from_vec('A', vec![Expr::Div(Box::new(Expr::Var(0)), Box::new(Expr::Const(R)))]).unwrap(),
            SymExpr::new_from_vec(']', vec![]).unwrap(),
            SymExpr::new_from_vec('[', vec![]).unwrap(),
            SymExpr::new_from_vec('-', vec![]).unwrap(),
            SymExpr::new_from_vec('A', vec![Expr::Div(Box::new(Expr::Var(0)), Box::new(Expr::Const(R)))]).unwrap(),
            SymExpr::new_from_vec(']', vec![]).unwrap(),
        ], 1));

    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 85.0, 0.0, &format!("abop_1_9_{:02}", iters));
}

fn main() {
    branching_pattern_abop_1_9(num_iterations());
}
