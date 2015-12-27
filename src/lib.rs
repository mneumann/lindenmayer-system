extern crate asexp;
extern crate expression;

pub mod old;
pub mod parametric;

use std::fmt::Debug;

/// Used to name symbols and variables.
pub trait Alphabet: Debug + PartialEq + Eq + Clone {}

impl Alphabet for &'static str {}
impl Alphabet for char {}
impl Alphabet for u8 {}
impl Alphabet for u16 {}
impl Alphabet for u32 {}
impl Alphabet for u64 {}
impl Alphabet for usize {}
