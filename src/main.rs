extern crate turtle;

use std::fmt;
use std::fs::File;
use turtle::{Canvas, Turtle};


#[derive(Debug, Eq, PartialEq, Clone)]
struct Character(char);

#[derive(Eq, PartialEq, Clone)]
struct Symbol {
    character: Character,
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.character.0)
    }
}

#[derive(Clone)]
struct SymbolString(Vec<Symbol>);

impl fmt::Debug for SymbolString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let v = &self.0;
        try!(write!(f, "\""));
        if !v.is_empty() {
            try!(write!(f, "{:?}", v[0]));
            for e in &v[1..] {
                try!(write!(f, " {:?}", e));
            }
        }
        write!(f, "\"")
    }
}

impl SymbolString {
    fn from_str(s: &str) -> SymbolString {
        SymbolString(s.chars().filter(|&c| !c.is_whitespace()).map(|c| Symbol{character: Character(c)}).collect())
    }
}

#[derive(Debug)]
struct Rule {
    lhs: Symbol,
    rhs: SymbolString,
}

impl Rule {
    fn produce(&self, sym: &Symbol) -> Option<SymbolString> {
        if self.lhs.eq(sym) {
            Some(self.rhs.clone())
        } else {
            None
        }
    }
}

#[derive(Debug)]
struct System {
    rules: Vec<Rule>,
}

impl System {
    fn develop(&self, axiom: SymbolString, iterations: usize) -> (SymbolString, usize) {
        let mut current = axiom;

        for iter in 0..iterations {
            let (next, progress) = self.develop1(&current);
            if !progress {
                return (current, iter);
            }
            current = next;
        }
        return (current, iterations);
    }

    fn develop1(&self, axiom: &SymbolString) -> (SymbolString, bool) {
        let mut expanded = Vec::new();
        let mut any_rule_applied = false;

        for symbol in axiom.0.iter() {
            let mut found = false;
            for rule in self.rules.iter() {
                if let Some(rhs) = rule.produce(&symbol) {
                    expanded.extend(rhs.0);
                    any_rule_applied = true;
                    found = true;
                    break;
                }
            }
            if !found {
                expanded.push(symbol.clone());
            }
        }

        (SymbolString(expanded), any_rule_applied)
    }
}
fn sym(c: char) -> Symbol {
    Symbol { character: Character(c) }
}

fn draw(symstr: &SymbolString, init_direction: f32, angle: f32, distance: f32, filename: &str) {
    let mut t = Canvas::new();
    t.pendown();
    t.right(init_direction);
    for sym in symstr.0.iter() {
        match sym.character.0 {
            'F' => t.forward(distance),
            '+' => t.right(angle),
            '-' => t.left(angle),
            '[' => t.push(),
            ']' => t.pop(),
            _   => {}
        }
    }
    t.save_svg(&mut File::create(filename).unwrap()).unwrap();
}  

fn koch_curve(maxiter: usize) {
    let axiom = SymbolString::from_str("F++F++F");

    let system = System { rules: vec![
        Rule {
            lhs: sym('F'),
            rhs: SymbolString::from_str("F-F++F-F")
        }
        ] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 60.0, 10.0, &format!("koch_{:02}.svg", iters));
}

fn dragon_curve(maxiter: usize) {
    let axiom = SymbolString::from_str("FX");

    let system = System { rules: vec![
        Rule {
            lhs: sym('X'),
            rhs: SymbolString::from_str("X+YF+")
        },
        Rule {
            lhs: sym('Y'),
            rhs: SymbolString::from_str("-FX-Y")
        }
        ] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, -90.0, 90.0, 10.0, &format!("dragon_{:02}.svg", iters));
}

fn sierpinski_triangle(maxiter: usize) {
    let axiom = SymbolString::from_str("A");

    let system = System { rules: vec![
        Rule {
            lhs: sym('A'),
            rhs: SymbolString::from_str("+B-A-B+")
        },
        Rule {
            lhs: sym('B'),
            rhs: SymbolString::from_str("-A+B+A-")
        }
        ] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    // replace A and B with F
    let system = System { rules: vec![
        Rule {
            lhs: sym('A'),
            rhs: SymbolString::from_str("F")
        },
        Rule {
            lhs: sym('B'),
            rhs: SymbolString::from_str("F")
        }
        ] };
    let (after, _iters) = system.develop1(&after);

    draw(&after, 0.0, 60.0, 10.0, &format!("sierpinski_{:02}.svg", iters));
}

fn fractal_plant(maxiter: usize) {
    let axiom = SymbolString::from_str("X");

    let system = System { rules: vec![
        Rule {
            lhs: sym('X'),
            rhs: SymbolString::from_str("F-[[X]+X]+F[+FX]-X")
        },
        Rule {
            lhs: sym('F'),
            rhs: SymbolString::from_str("FF")
        }
        ] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, -90.0, 25.0, 10.0, &format!("plant_{:02}.svg", iters));
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
}
