extern crate turtle;

use std::fmt;
use std::fs::File;
use turtle::{Canvas, Turtle};

trait Alphabet: fmt::Debug + Eq + PartialEq + Clone  {}

#[derive(Clone)]
struct Symbol<C:Alphabet> {
    character: C,
}

struct Parameters;

impl<C:Alphabet> Symbol<C> {
    fn matches(&self, other: &Symbol<C>) -> Option<Parameters> {
        if self.character == other.character {
            // XXX: match condition. XXX move into rule
            Some(Parameters)
        }
        else {
            None
        }
    }
}



impl<C:Alphabet> fmt::Debug for Symbol<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.character)
    }
}

// XXX: Rename SymbolString to Word
#[derive(Clone)]
struct SymbolString<C:Alphabet>(Vec<Symbol<C>>);

impl<C:Alphabet> fmt::Debug for SymbolString<C> {
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

impl<C:Alphabet> SymbolString<C> {
    // XXX: Evaluate Parameters
    fn evaluate(&self, _parameters: Parameters) -> SymbolString<C> {
        self.clone()
    }
}


#[derive(Debug)]
struct Rule<C:Alphabet> {
    lhs: Symbol<C>,
    rhs: SymbolString<C>,
}

impl<C:Alphabet> Rule<C> {
    fn produce(&self, sym: &Symbol<C>) -> Option<SymbolString<C>> {
        self.lhs.matches(sym).map(|parameters| self.rhs.evaluate(parameters))
    }
}

#[derive(Debug)]
struct System<C:Alphabet> {
    rules: Vec<Rule<C>>,
}

impl<C:Alphabet> System<C> {
    fn develop(&self, axiom: SymbolString<C>, iterations: usize) -> (SymbolString<C>, usize) {
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

    fn develop1(&self, axiom: &SymbolString<C>) -> (SymbolString<C>, bool) {
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

#[derive(Eq, PartialEq, Clone)]
struct Character(char);
impl Alphabet for Character {}

impl fmt::Debug for Character {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}


fn symstr_from_str(s: &str) -> SymbolString<Character> {
    SymbolString(s.chars().filter(|&c| !c.is_whitespace()).map(|c| Symbol{character: Character(c)}).collect())
}

fn sym(c: char) -> Symbol<Character> {
    Symbol { character: Character(c) }
}

fn draw(symstr: &SymbolString<Character>, init_direction: f32, angle: f32, distance: f32, filename: &str) {
    let mut t = Canvas::new();
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
    let axiom = symstr_from_str("F++F++F");

    let system = System { rules: vec![
        Rule {
            lhs: sym('F'),
            rhs: symstr_from_str("F-F++F-F")
        }
        ] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, -90.0, 60.0, 10.0, &format!("koch_{:02}.svg", iters));
}

fn dragon_curve(maxiter: usize) {
    let axiom = symstr_from_str("FX");

    let system = System { rules: vec![
        Rule {
            lhs: sym('X'),
            rhs: symstr_from_str("X+YF+")
        },
        Rule {
            lhs: sym('Y'),
            rhs: symstr_from_str("-FX-Y")
        }
        ] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 90.0, 10.0, &format!("dragon_{:02}.svg", iters));
}

fn sierpinski_triangle(maxiter: usize) {
    let axiom = symstr_from_str("A");

    let system = System { rules: vec![
        Rule {
            lhs: sym('A'),
            rhs: symstr_from_str("+B-A-B+")
        },
        Rule {
            lhs: sym('B'),
            rhs: symstr_from_str("-A+B+A-")
        }
        ] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    // replace A and B with F
    let system = System { rules: vec![
        Rule {
            lhs: sym('A'),
            rhs: symstr_from_str("F")
        },
        Rule {
            lhs: sym('B'),
            rhs: symstr_from_str("F")
        }
        ] };
    let (after, _iters) = system.develop1(&after);

    draw(&after, -90.0, 60.0, 10.0, &format!("sierpinski_{:02}.svg", iters));
}

fn fractal_plant(maxiter: usize) {
    let axiom = symstr_from_str("X");

    let system = System { rules: vec![
        Rule {
            lhs: sym('X'),
            rhs: symstr_from_str("F-[[X]+X]+F[+FX]-X")
        },
        Rule {
            lhs: sym('F'),
            rhs: symstr_from_str("FF")
        }
        ] };
    println!("{:?}", system);

    let (after, iters) = system.develop(axiom, maxiter);

    draw(&after, 0.0, 25.0, 10.0, &format!("plant_{:02}.svg", iters));
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
