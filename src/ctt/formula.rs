use crate::ctt::Identifier;

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Dir {
    Zero,
    One,
}

impl Dir {
    pub fn negate(&self) -> Dir {
        match self {
            Dir::Zero => Dir::One,
            Dir::One => Dir::Zero,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Formula {
    Dir(Dir),
    Atom(Identifier),
    NegAtom(Identifier),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
}

impl Formula {
    pub fn and(&self, other: &Formula) -> Formula {
        match (self, other) {
            (Formula::Dir(Dir::Zero), _) => Formula::Dir(Dir::Zero),
            (_, Formula::Dir(Dir::Zero)) => Formula::Dir(Dir::Zero),
            (Formula::Dir(Dir::One), rhs) => rhs.clone(),
            (lhs, Formula::Dir(Dir::One)) => lhs.clone(),
            (lhs, rhs) => Formula::And(Box::new(lhs.clone()), Box::new(rhs.clone())),
        }
    }

    pub fn or(&self, other: &Formula) -> Formula {
        match (self, other) {
            (Formula::Dir(Dir::One), _) => Formula::Dir(Dir::One),
            (_, Formula::Dir(Dir::One)) => Formula::Dir(Dir::One),
            (Formula::Dir(Dir::Zero), rhs) => rhs.clone(),
            (lhs, Formula::Dir(Dir::Zero)) => lhs.clone(),
            (lhs, rhs) => Formula::Or(Box::new(lhs.clone()), Box::new(rhs.clone())),
        }
    }

    pub fn negate(&self) -> Formula {
        match self {
            Formula::Dir(d) => Formula::Dir(d.negate()),
            Formula::Atom(name) => Formula::NegAtom(*name),
            Formula::NegAtom(name) => Formula::Atom(*name),
            Formula::And(lhs, rhs) => Formula::Or(Box::new(lhs.negate()), Box::new(rhs.negate())),
            Formula::Or(lhs, rhs) => Formula::And(Box::new(lhs.negate()), Box::new(rhs.negate())),
        }
    }
}
