pub mod alpha_eq;
pub mod formula;
pub mod system;
pub mod term;

#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct Identifier(pub usize);
