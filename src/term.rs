use std::collections::HashMap;
use std::hash::{Hash, Hasher};

pub type Identifier = String;

#[derive(Clone)]
pub struct Telescope {
    pub variables: Vec<(Identifier, Term)>,
}

#[derive(Clone)]
pub struct Declaration {
    pub name: Identifier,
    pub tpe: Box<Term>,
    pub body: Box<Term>,
}

#[derive(Clone)]
pub enum DeclarationSet {
    Mutual(Vec<Declaration>),
    Opaque(Identifier),
    Transparent(Identifier),
    TransparentAll,
}

#[derive(Clone)]
pub enum Label {
    OLabel(Identifier, Telescope),
    PLabel(Identifier, Telescope, Vec<Identifier>, System<Term>),
}

#[derive(Clone)]
pub enum Branch {
    OBranch(Identifier, Vec<Identifier>, Box<Term>),
    PBranch(Identifier, Vec<Identifier>, Vec<Identifier>, Box<Term>),
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub enum Dir {
    Zero,
    One,
}

#[derive(Clone)]
pub enum Formula {
    Dir(Dir),
    Atom(Identifier),
    NegAtom(Identifier),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
}

#[derive(Clone, Eq, PartialEq)]
pub struct Face {
    pub binds: HashMap<Identifier, Dir>,
}

impl Hash for Face {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for (key, value) in &self.binds {
            key.hash(state);
            value.hash(state);
        }
    }
}

#[derive(Clone)]
pub struct System<A> {
    pub binds: HashMap<Face, Box<A>>,
}

impl<A> System<A> {
    pub fn empty() -> System<A> {
        System {
            binds: HashMap::new(),
        }
    }
}

#[derive(Clone)]
pub enum Term {
    Pi(Box<Term>),
    App(Box<Term>, Box<Term>),
    Lam(Identifier, Box<Term>, Box<Term>),
    Where(Box<Term>, DeclarationSet),
    Var(Identifier),
    U,
    Sigma(Box<Term>),
    Pair(Box<Term>, Box<Term>),
    Fst(Box<Term>),
    Snd(Box<Term>),
    Con(Identifier, Vec<Term>),
    PCon(Identifier, Box<Term>, Vec<Term>, Vec<Formula>),
    Split(Identifier, Box<Term>, Vec<Branch>),
    Sum(Identifier, Vec<Label>),
    HSum(Identifier, Vec<Label>),
    Undef(Box<Term>),
    Hole,
    PathP(Box<Term>, Box<Term>, Box<Term>),
    PLam(Identifier, Box<Term>),
    AppFormula(Box<Term>, Formula),
    Comp(Box<Term>, Box<Term>, System<Term>),
    Fill(Box<Term>, Box<Term>, System<Term>),
    HComp(Box<Term>, Box<Term>, System<Term>),
    Glue(Box<Term>, System<Term>),
    GlueElem(Box<Term>, System<Term>),
    UnGlueElem(Box<Term>, System<Term>),
    Id(Box<Term>, Box<Term>, Box<Term>),
    IdPair(Box<Term>, System<Term>),
    IdJ(
        Box<Term>,
        Box<Term>,
        Box<Term>,
        Box<Term>,
        Box<Term>,
        Box<Term>,
    ),
}
