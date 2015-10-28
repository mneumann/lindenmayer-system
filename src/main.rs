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
    fn develop(&self, axiom: &SymbolString, iterations: usize) -> (SymbolString, usize) {

        let (next, progress) = self.develop1(axiom);
        if !progress {
            return (next, 0);
        }

        let mut n = 1;
        let mut current = next;

        for _ in 0..iterations {
            let (next, progress) = self.develop1(&current);
            if progress {
                n += 1;
                current = next;
            } else {
                // XXX: next === current
                break;
            }
        }
        return (current, n);
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

fn main() {
    fn sym(c: char) -> Symbol {
        Symbol { character: Character(c) }
    }

    let axiom = SymbolString::from_str("F++F++F");
    let rule1 = Rule {
        lhs: sym('F'),
        rhs: SymbolString::from_str("F-F++F-F")
    };

    let mut rules = Vec::new();
    rules.push(rule1);

    let system = System { rules: rules };

    println!("{:?}", system);

    println!("before: {:?}", axiom);
    let (after, _iters) = system.develop(&axiom, 5);
    println!("after:  {:?}", after);

    let angle = 60.0;
    let distance = 10.0;
    let mut t = Canvas::new();
    t.pendown();
    for sym in after.0.iter() {
        match sym.character.0 {
            'F' => t.forward(distance),
            '+' => t.right(angle),
            '-' => t.left(angle),
            _   => {}
        }
    }
    t.save_svg(&mut File::create("koch.svg").unwrap()).unwrap();
}
