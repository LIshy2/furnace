use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;


#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct Identifier(pub usize);

pub fn anon_id() -> Identifier {
    Identifier(9999999999999)
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Telescope<T> {
    pub variables: Vec<(Identifier, Rc<T>)>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Declaration<T> {
    pub name: Identifier,
    pub tpe: Rc<T>,
    pub body: Rc<T>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum DeclarationSet<T> {
    Mutual(Vec<Declaration<T>>),
    Opaque(Identifier),
    Transparent(Identifier),
    TransparentAll,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Label<T> {
    OLabel(Identifier, Telescope<T>),
    PLabel(Identifier, Telescope<T>, Vec<Identifier>, System<T>),
}

impl<T: Clone> Label<T> {
    pub fn name(&self) -> Identifier {
        match self {
            Label::OLabel(name, _) => name.clone(),
            Label::PLabel(name, _, _, _) => name.clone(),
        }
    }

    pub fn telescope(&self) -> Telescope<T> {
        match self {
            Label::OLabel(_, tele) => tele.clone(),
            Label::PLabel(_, tele, _, _) => tele.clone(),
        }
    }

}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Branch<T> {
    OBranch(Identifier, Vec<Identifier>, Rc<T>),
    PBranch(Identifier, Vec<Identifier>, Vec<Identifier>, Rc<T>),
}

impl<T> Branch<T> {
    pub fn name(&self) -> Identifier {
        match self {
            Branch::OBranch(name, _, _) => name.clone(),
            Branch::PBranch(name, _, _, _) => name.clone(),
        }
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
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
            Formula::Atom(name) => Formula::NegAtom(name.clone()),
            Formula::NegAtom(name) => Formula::Atom(name.clone()),
            Formula::And(lhs, rhs) => Formula::Or(Box::new(lhs.negate()), Box::new(rhs.negate())),
            Formula::Or(lhs, rhs) => Formula::And(Box::new(lhs.negate()), Box::new(rhs.negate())),
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Face {
    pub binds: HashMap<Identifier, Dir>,
}

impl Face {
    pub fn cond(name: &Identifier, dir: Dir) -> Face {
        Face {
            binds: HashMap::from([(name.clone(), dir)]),
        }
    }

    pub fn eps() -> Face {
        Face {
            binds: HashMap::new(),
        }
    }

    pub fn domain(&self) -> Vec<Identifier> {
        self.binds.keys().map(|c| c.clone()).collect()
    }

    pub fn compatible(&self, other: &Face) -> bool {
        for (int, dir) in self.binds.iter() {
            if let Some(other_v) = other.binds.get(int) {
                if dir != other_v {
                    return false;
                }
            }
        }
        true
    }

    pub fn removed(&self, i: &Identifier) -> Face {
        let mut result = self.clone();
        result.binds.remove(i);
        result
    }

    pub fn meet(&self, other: &Face) -> Face {
        let mut result = Face::eps();
        for (i, d1) in &self.binds {
            if let Some(d2) = other.binds.get(i) {
                if d2 != d1 {
                    panic!("faces incompatible")
                }
            }
            result.binds.insert(i.clone(), d1.clone());
        }
        for (i, d2) in &other.binds {
            if !self.binds.contains_key(i) {
                result.binds.insert(i.clone(), d2.clone());
            }
        }

        result
    }

    pub fn minus(&self, other: &Face) -> Face {
        let mut result = self.clone();
        for (k, _) in &other.binds {
            result.binds.remove(k);
        }
        result
    }
}

impl Hash for Face {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut entries = self.binds.iter().collect::<Vec<_>>();
        entries.sort_by(|a, b| a.0.cmp(b.0));

        // Hash each entry in order
        for (k, v) in entries {
            k.hash(state);
            v.hash(state);
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct System<A> {
    pub binds: HashMap<Face, Rc<A>>,
}

impl<A: Clone> System<A> {
    pub fn empty() -> System<A> {
        System {
            binds: HashMap::new(),
        }
    }
    pub fn domain(&self) -> Vec<Identifier> {
        self.binds.iter().flat_map(|(f, _)| f.domain()).collect()
    }

    pub fn insert(&self, face: Face, bind: Rc<A>) -> System<A> {
        let mut result = self.clone();
        result.binds.insert(face, bind);
        result
    }
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    Pi(Rc<Term>),
    App(Rc<Term>, Rc<Term>),
    Lam(Identifier, Rc<Term>, Rc<Term>),
    Where(Rc<Term>, DeclarationSet<Term>),
    Var(Identifier),
    U,
    Sigma(Rc<Term>),
    Pair(Rc<Term>, Rc<Term>),
    Fst(Rc<Term>),
    Snd(Rc<Term>),
    Con(Identifier, Vec<Rc<Term>>),
    PCon(Identifier, Rc<Term>, Vec<Rc<Term>>, Vec<Formula>),
    Split(Identifier, Rc<Term>, Vec<Branch<Term>>),
    Sum(Identifier, Vec<Label<Term>>),
    HSum(Identifier, Vec<Label<Term>>),
    Undef(Rc<Term>),
    Hole,
    PathP(Rc<Term>, Rc<Term>, Rc<Term>),
    PLam(Identifier, Rc<Term>),
    AppFormula(Rc<Term>, Formula),
    Comp(Rc<Term>, Rc<Term>, System<Term>),
    Fill(Rc<Term>, Rc<Term>, System<Term>),
    HComp(Rc<Term>, Rc<Term>, System<Term>),
    Glue(Rc<Term>, System<Term>),
    GlueElem(Rc<Term>, System<Term>),
    UnGlueElem(Rc<Term>, System<Term>),
    UnGlueElemU(Rc<Term>, Rc<Term>, System<Term>),
    Id(Rc<Term>, Rc<Term>, Rc<Term>),
    IdPair(Rc<Term>, System<Term>),
    IdJ(Rc<Term>, Rc<Term>, Rc<Term>, Rc<Term>, Rc<Term>, Rc<Term>),
}

