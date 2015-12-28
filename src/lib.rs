extern crate expression;
#[cfg(test)]
extern crate expression_num;

pub mod parametric;

use std::fmt::Debug;

/// Used to name symbols and variables.
pub trait Alphabet: Debug + PartialEq + Eq + PartialOrd + Ord + Clone {}

impl Alphabet for &'static str {}
impl Alphabet for char {}
impl Alphabet for u8 {}
impl Alphabet for u16 {}
impl Alphabet for u32 {}
impl Alphabet for u64 {}
impl Alphabet for usize {}

/// An alphabet that distinguishes between terminal
/// and non-terminal symbols.
pub trait DualAlphabet: Alphabet {
    type Terminal: Alphabet;
    type NonTerminal: Alphabet;

    /// If the character is a non-terminal, return Some(..). Otherwise return None.
    fn nonterminal(&self) -> Option<Self::NonTerminal>;

    /// If the character is a terminal, return Some(..). Otherwise return None.
    fn terminal(&self) -> Option<Self::Terminal>;

    /// Constructs non-terminal
    fn make_nonterminal(nt: Self::NonTerminal) -> Self;

    /// Constructs terminal
    fn make_terminal(t: Self::Terminal) -> Self;
}
