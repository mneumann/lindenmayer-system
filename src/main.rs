use std::fmt;

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
    fn develop(&self, axiom: &SymbolString) -> (bool, SymbolString) {
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

        (any_rule_applied, SymbolString(expanded))
    }
}

fn main() {
    fn sym(c: char) -> Symbol {
        Symbol { character: Character(c) }
    }

    let axiom = SymbolString(vec![sym('F'), sym('+'), sym('+'), sym('F'), sym('+'), sym('+'),
                                  sym('F')]);
    let rule1 = Rule {
        lhs: sym('F'),
        rhs: SymbolString(vec![sym('F'), sym('-'), sym('F'), sym('+'), sym('+'), sym('F'),
                               sym('-'), sym('F')]),
    };

    let mut rules = Vec::new();
    rules.push(rule1);

    let system = System { rules: rules };

    println!("{:?}", system);

    println!("before: {:?}", axiom);
    let apply = system.develop(&axiom);
    println!("after:  {:?}", apply.1);
}
