use std::cmp::Ordering;
use std::collections::hash_map::IntoIter;
use std::collections::HashMap;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::hash::{Hash, Hasher};
use std::ops::Index;
use std::rc::Rc;

use rpds::HashTrieMap;
use rpds::HashTrieSet;

use crate::typechecker::context::Entry;
use crate::typechecker::context::EntryValueState;
use crate::utils::intersect;

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
            Label::OLabel(name, _) => *name,
            Label::PLabel(name, _, _, _) => *name,
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
            Branch::OBranch(name, _, _) => *name,
            Branch::PBranch(name, _, _, _) => *name,
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
            Formula::Atom(name) => Formula::NegAtom(*name),
            Formula::NegAtom(name) => Formula::Atom(*name),
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
            binds: HashMap::from([(*name, dir)]),
        }
    }

    pub fn eps() -> Face {
        Face {
            binds: HashMap::new(),
        }
    }

    pub fn domain(&self) -> Vec<Identifier> {
        self.binds.keys().copied().collect()
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
            result.binds.insert(*i, d1.clone());
        }
        for (i, d2) in &other.binds {
            if !self.binds.contains_key(i) {
                result.binds.insert(*i, d2.clone());
            }
        }

        result
    }

    pub fn minus(&self, other: &Face) -> Face {
        let mut result = self.clone();
        for k in other.binds.keys() {
            result.binds.remove(k);
        }
        result
    }

    pub fn leq(&self, other: &Face) -> bool {
        for (b, d1) in &other.binds {
            if let Some(d2) = self.binds.get(b) {
                if d1 != d2 {
                    return false;
                }
            } else {
                return false;
            }
        }
        return true;
    }
}

impl Hash for Face {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut entries = self.binds.iter().collect::<Vec<_>>();
        entries.sort_by(|a, b| a.0.cmp(b.0));

        for (k, v) in entries {
            k.hash(state);
            v.hash(state);
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct System<A> {
    binds: HashMap<Face, Rc<A>>,
}

impl<A> Clone for System<A> {
    fn clone(&self) -> Self {
        Self {
            binds: self.binds.clone(),
        }
    }
}

impl<A> System<A> {
    pub fn empty() -> System<A> {
        System {
            binds: HashMap::new(),
        }
    }

    pub fn domain(&self) -> Vec<Identifier> {
        self.binds.iter().flat_map(|(f, _)| f.domain()).collect()
    }

    pub fn insert(&self, alpha: Face, bind: Rc<A>) -> System<A> {
        let mut result = self.clone();
        if !result.binds.iter().any(|(beta, _)| alpha.leq(beta)) {
            result.binds = result
                .binds
                .into_iter()
                .filter(|(gamma, _)| !gamma.leq(&alpha))
                .map(|(f, a)| (f.clone(), a.clone()))
                .collect();
            result.binds.insert(alpha, bind);
        }
        result
    }

    pub fn get(&self, face: &Face) -> Option<&Rc<A>> {
        self.binds.get(face)
    }

    pub fn contains(&self, face: &Face) -> bool {
        self.binds.contains_key(face)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Face, &Rc<A>)> {
        self.binds.iter()
    }

    pub fn values(&self) -> impl Iterator<Item = &Rc<A>> {
        self.binds.values()
    }

    pub fn len(&self) -> usize {
        self.binds.len()
    }

    pub fn intersect<'a, B>(&'a self, other: &'a System<B>) -> SystemIntersect<'a, A, B> {
        SystemIntersect {
            iter: intersect(&self.binds, &other.binds).into_iter(),
        }
    }
}

impl<A> From<HashMap<Face, Rc<A>>> for System<A> {
    fn from(value: HashMap<Face, Rc<A>>) -> Self {
        let mut result = System::empty();
        for (alpha, v) in value {
            result = result.insert(alpha, v)
        }
        result
    }
}

impl<A> Index<&Face> for System<A> {
    type Output = Rc<A>;

    fn index(&self, index: &Face) -> &Self::Output {
        &self.binds[index]
    }
}

impl<A> FromIterator<(Face, Rc<A>)> for System<A> {
    fn from_iter<T: IntoIterator<Item = (Face, Rc<A>)>>(iter: T) -> Self {
        System::from(HashMap::from_iter(iter))
    }
}

pub struct SystemIntersect<'a, A, B> {
    iter: IntoIter<&'a Face, (&'a Rc<A>, &'a Rc<B>)>,
}

impl<'a, A, B> Iterator for SystemIntersect<'a, A, B> {
    type Item = (&'a Face, (&'a Rc<A>, &'a Rc<B>));

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

#[derive(Clone, Debug)]
pub enum Term<M> {
    Pi(Rc<Term<M>>, M),
    App(Rc<Term<M>>, Rc<Term<M>>, M),
    Lam(Identifier, Rc<Term<M>>, Rc<Term<M>>, M),
    Where(Rc<Term<M>>, DeclarationSet<Term<M>>, M),
    Var(Identifier, M),
    U,
    Sigma(Rc<Term<M>>, M),
    Pair(Rc<Term<M>>, Rc<Term<M>>, M),
    Fst(Rc<Term<M>>, M),
    Snd(Rc<Term<M>>, M),
    Con(Identifier, Vec<Rc<Term<M>>>, M),
    PCon(Identifier, Rc<Term<M>>, Vec<Rc<Term<M>>>, Vec<Formula>, M),
    Split(Identifier, Rc<Term<M>>, Vec<Branch<Term<M>>>, M),
    Sum(Identifier, Vec<Label<Term<M>>>, M),
    HSum(Identifier, Vec<Label<Term<M>>>, M),
    Undef(Rc<Term<M>>, M),
    Hole,
    PathP(Rc<Term<M>>, Rc<Term<M>>, Rc<Term<M>>, M),
    PLam(Identifier, Rc<Term<M>>, M),
    AppFormula(Rc<Term<M>>, Formula, M),
    Comp(Rc<Term<M>>, Rc<Term<M>>, System<Term<M>>, M),
    Fill(Rc<Term<M>>, Rc<Term<M>>, System<Term<M>>, M),
    HComp(Rc<Term<M>>, Rc<Term<M>>, System<Term<M>>, M),
    Glue(Rc<Term<M>>, System<Term<M>>, M),
    GlueElem(Rc<Term<M>>, System<Term<M>>, M),
    UnGlueElem(Rc<Term<M>>, System<Term<M>>, M),
    Id(Rc<Term<M>>, Rc<Term<M>>, Rc<Term<M>>, M),
    IdPair(Rc<Term<M>>, System<Term<M>>, M),
    IdJ(
        Rc<Term<M>>,
        Rc<Term<M>>,
        Rc<Term<M>>,
        Rc<Term<M>>,
        Rc<Term<M>>,
        Rc<Term<M>>,
        M,
    ),
}

impl<M> Term<M> {
    pub fn pi(lam: &Rc<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Pi(lam.clone(), meta))
    }

    pub fn app(fun: &Rc<Term<M>>, arg: &Rc<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::App(fun.clone(), arg.clone(), meta))
    }

    pub fn lam(n: Identifier, tpe: &Rc<Term<M>>, body: &Rc<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Lam(n, tpe.clone(), body.clone(), meta))
    }

    pub fn wher(expr: &Rc<Term<M>>, decls: DeclarationSet<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Where(expr.clone(), decls, meta))
    }

    pub fn var(id: Identifier, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Var(id, meta))
    }

    pub fn u() -> Rc<Term<M>> {
        Rc::new(Term::U)
    }

    pub fn sigma(ty: &Rc<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Sigma(ty.clone(), meta))
    }

    pub fn pair(fst: &Rc<Term<M>>, snd: &Rc<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Pair(fst.clone(), snd.clone(), meta))
    }

    pub fn fst(p: &Rc<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Fst(p.clone(), meta))
    }

    pub fn snd(p: &Rc<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Snd(p.clone(), meta))
    }

    pub fn con(id: Identifier, args: Vec<Rc<Term<M>>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Con(id, args, meta))
    }

    pub fn pcon(
        id: Identifier,
        ty: &Rc<Term<M>>,
        args: Vec<Rc<Term<M>>>,
        formulas: Vec<Formula>,
        meta: M,
    ) -> Rc<Term<M>> {
        Rc::new(Term::PCon(id, ty.clone(), args, formulas, meta))
    }

    pub fn split(
        id: Identifier,
        scrut: &Rc<Term<M>>,
        branches: Vec<Branch<Term<M>>>,
        meta: M,
    ) -> Rc<Term<M>> {
        Rc::new(Term::Split(id, scrut.clone(), branches, meta))
    }

    pub fn sum(id: Identifier, labels: Vec<Label<Term<M>>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Sum(id, labels, meta))
    }

    pub fn hsum(id: Identifier, labels: Vec<Label<Term<M>>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::HSum(id, labels, meta))
    }

    pub fn undef(ty: &Rc<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Undef(ty.clone(), meta))
    }

    pub fn hole() -> Rc<Term<M>> {
        Rc::new(Term::Hole)
    }

    pub fn pathp(a: &Rc<Term<M>>, x: &Rc<Term<M>>, y: &Rc<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::PathP(a.clone(), x.clone(), y.clone(), meta))
    }

    pub fn plam(id: Identifier, body: &Rc<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::PLam(id, body.clone(), meta))
    }

    pub fn app_formula(fun: &Rc<Term<M>>, formula: Formula, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::AppFormula(fun.clone(), formula, meta))
    }

    pub fn comp(a: &Rc<Term<M>>, t: &Rc<Term<M>>, sys: System<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Comp(a.clone(), t.clone(), sys, meta))
    }

    pub fn fill(a: &Rc<Term<M>>, t: &Rc<Term<M>>, sys: System<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Fill(a.clone(), t.clone(), sys, meta))
    }

    pub fn hcomp(a: &Rc<Term<M>>, t: &Rc<Term<M>>, sys: System<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::HComp(a.clone(), t.clone(), sys, meta))
    }

    pub fn glue(a: &Rc<Term<M>>, sys: System<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Glue(a.clone(), sys, meta))
    }

    pub fn glue_elem(a: &Rc<Term<M>>, sys: System<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::GlueElem(a.clone(), sys, meta))
    }

    pub fn unglue_elem(a: &Rc<Term<M>>, sys: System<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::UnGlueElem(a.clone(), sys, meta))
    }

    pub fn id(a: &Rc<Term<M>>, x: &Rc<Term<M>>, y: &Rc<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::Id(a.clone(), x.clone(), y.clone(), meta))
    }

    pub fn id_pair(a: &Rc<Term<M>>, sys: System<Term<M>>, meta: M) -> Rc<Term<M>> {
        Rc::new(Term::IdPair(a.clone(), sys, meta))
    }

    pub fn id_j(
        a: &Rc<Term<M>>,
        m: &Rc<Term<M>>,
        x: &Rc<Term<M>>,
        p: &Rc<Term<M>>,
        y: &Rc<Term<M>>,
        q: &Rc<Term<M>>,
        meta: M,
    ) -> Rc<Term<M>> {
        Rc::new(Term::IdJ(
            a.clone(),
            m.clone(),
            x.clone(),
            p.clone(),
            y.clone(),
            q.clone(),
            meta,
        ))
    }
}

impl<M> PartialEq for Term<M> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Term::Pi(a, _), Term::Pi(b, _)) => a == b,
            (Term::App(f1, a1, _), Term::App(f2, a2, _)) => f1 == f2 && a1 == a2,
            (Term::Lam(id1, ty1, body1, _), Term::Lam(id2, ty2, body2, _)) => {
                id1 == id2 && ty1 == ty2 && body1 == body2
            }
            (Term::Where(t1, ds1, _), Term::Where(t2, ds2, _)) => t1 == t2 && ds1 == ds2,
            (Term::Var(id1, _), Term::Var(id2, _)) => id1 == id2,
            (Term::U, Term::U) => true,
            (Term::Sigma(a, _), Term::Sigma(b, _)) => a == b,
            (Term::Pair(a1, b1, _), Term::Pair(a2, b2, _)) => a1 == a2 && b1 == b2,
            (Term::Fst(p1, _), Term::Fst(p2, _)) => p1 == p2,
            (Term::Snd(p1, _), Term::Snd(p2, _)) => p1 == p2,
            (Term::Con(id1, args1, _), Term::Con(id2, args2, _)) => id1 == id2 && args1 == args2,
            (Term::PCon(id1, ty1, args1, form1, _), Term::PCon(id2, ty2, args2, form2, _)) => {
                id1 == id2 && ty1 == ty2 && args1 == args2 && form1 == form2
            }
            (Term::Split(id1, t1, br1, _), Term::Split(id2, t2, br2, _)) => {
                id1 == id2 && t1 == t2 && br1 == br2
            }
            (Term::Sum(id1, labels1, _), Term::Sum(id2, labels2, _)) => {
                id1 == id2 && labels1 == labels2
            }
            (Term::HSum(id1, labels1, _), Term::HSum(id2, labels2, _)) => {
                id1 == id2 && labels1 == labels2
            }
            (Term::Undef(t1, _), Term::Undef(t2, _)) => t1 == t2,
            (Term::Hole, Term::Hole) => true,
            (Term::PathP(a1, b1, c1, _), Term::PathP(a2, b2, c2, _)) => {
                a1 == a2 && b1 == b2 && c1 == c2
            }
            (Term::PLam(id1, t1, _), Term::PLam(id2, t2, _)) => id1 == id2 && t1 == t2,
            (Term::AppFormula(t1, f1, _), Term::AppFormula(t2, f2, _)) => t1 == t2 && f1 == f2,
            (Term::Comp(t1, u1, sys1, _), Term::Comp(t2, u2, sys2, _)) => {
                t1 == t2 && u1 == u2 && sys1 == sys2
            }
            (Term::Fill(t1, u1, sys1, _), Term::Fill(t2, u2, sys2, _)) => {
                t1 == t2 && u1 == u2 && sys1 == sys2
            }
            (Term::HComp(t1, u1, sys1, _), Term::HComp(t2, u2, sys2, _)) => {
                t1 == t2 && u1 == u2 && sys1 == sys2
            }
            (Term::Glue(t1, sys1, _), Term::Glue(t2, sys2, _)) => t1 == t2 && sys1 == sys2,
            (Term::GlueElem(t1, sys1, _), Term::GlueElem(t2, sys2, _)) => t1 == t2 && sys1 == sys2,
            (Term::UnGlueElem(t1, sys1, _), Term::UnGlueElem(t2, sys2, _)) => {
                t1 == t2 && sys1 == sys2
            }
            (Term::Id(a1, b1, c1, _), Term::Id(a2, b2, c2, _)) => a1 == a2 && b1 == b2 && c1 == c2,
            (Term::IdPair(t1, sys1, _), Term::IdPair(t2, sys2, _)) => t1 == t2 && sys1 == sys2,
            (Term::IdJ(a1, b1, c1, d1, e1, f1, _), Term::IdJ(a2, b2, c2, d2, e2, f2, _)) => {
                a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2 && e1 == e2 && f1 == f2
            }
            _ => false,
        }
    }
}

impl<M> Eq for Term<M> {}

#[derive(Clone, PartialEq, Eq)]
pub struct Closure {
    pub term_binds: HashTrieMap<Identifier, Entry>,
    pub type_binds: HashTrieMap<Identifier, Entry>,
    pub formula_binds: HashTrieMap<Identifier, Formula>,
    pub shadowed: HashTrieSet<Identifier>,
}

impl Debug for Closure {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{terms: {{")?;
        for (name, e) in self.term_binds.iter() {
            name.fmt(f)?;
            write!(f, "- ")?;
            match e.value() {
                EntryValueState::Lazy(term) => {
                    write!(f, "lazy(")?;
                    term.fmt(f)?;
                    write!(f, ")")?;
                }
                EntryValueState::Cached(value) => {
                    value.fmt(f)?;
                }
            }

            write!(f, ", ")?;
        }
        write!(f, "}}, types: {{")?;
        for (name, e) in self.type_binds.iter() {
            name.fmt(f)?;
            write!(f, "- ")?;
            match e.value() {
                EntryValueState::Lazy(term) => {
                    write!(f, "lazy(")?;
                    term.fmt(f)?;
                    write!(f, ")")?;
                }
                EntryValueState::Cached(value) => {
                    value.fmt(f)?;
                }
            }

            write!(f, ", ")?;
        }
        write!(f, "}}, formulas: {{")?;
        for (name, e) in self.formula_binds.iter() {
            name.fmt(f)?;
            write!(f, ": ")?;
            e.fmt(f)?;
            write!(f, ", ")?;
        }
        write!(f, "}} }}")?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum Value<M> {
    Stuck(Term<M>, Closure, M),
    Pi(Rc<Value<M>>, Rc<Value<M>>, M),
    App(Rc<Value<M>>, Rc<Value<M>>, M),
    Var(Identifier, Rc<Value<M>>, M),
    U,
    Sigma(Rc<Value<M>>, Rc<Value<M>>, M),
    Pair(Rc<Value<M>>, Rc<Value<M>>, M),
    Fst(Rc<Value<M>>, M),
    Snd(Rc<Value<M>>, M),
    Con(Identifier, Vec<Rc<Value<M>>>, M),
    PCon(Identifier, Rc<Value<M>>, Vec<Rc<Value<M>>>, Vec<Formula>, M),
    PathP(Rc<Value<M>>, Rc<Value<M>>, Rc<Value<M>>, M),
    PLam(Identifier, Rc<Value<M>>, M),
    AppFormula(Rc<Value<M>>, Formula, M),
    Comp(Rc<Value<M>>, Rc<Value<M>>, System<Value<M>>, M),
    CompU(Rc<Value<M>>, System<Value<M>>, M),
    HComp(Rc<Value<M>>, Rc<Value<M>>, System<Value<M>>, M),
    Glue(Rc<Value<M>>, System<Value<M>>, M),
    GlueElem(Rc<Value<M>>, System<Value<M>>, M),
    UnGlueElem(Rc<Value<M>>, System<Value<M>>, M),
    UnGlueElemU(Rc<Value<M>>, Rc<Value<M>>, System<Value<M>>, M),
    Id(Rc<Value<M>>, Rc<Value<M>>, Rc<Value<M>>, M),
    IdPair(Rc<Value<M>>, System<Value<M>>, M),
    IdJ(
        Rc<Value<M>>,
        Rc<Value<M>>,
        Rc<Value<M>>,
        Rc<Value<M>>,
        Rc<Value<M>>,
        Rc<Value<M>>,
        M,
    ),
}

impl<M> Value<M> {
    pub fn stuck(term: Term<M>, closure: Closure, meta: M) -> Rc<Self> {
        Rc::new(Self::Stuck(term, closure, meta))
    }

    pub fn pi(tpe: &Rc<Self>, a: &Rc<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::Pi(Rc::clone(tpe), Rc::clone(a), meta))
    }

    pub fn app(f: &Rc<Self>, arg: &Rc<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::App(Rc::clone(f), Rc::clone(arg), meta))
    }

    pub fn var(name: Identifier, tpe: &Rc<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::Var(name, Rc::clone(tpe), meta))
    }

    pub fn u() -> Rc<Self> {
        Rc::new(Self::U)
    }

    pub fn sigma(tpe: &Rc<Self>, a: &Rc<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::Sigma(Rc::clone(tpe), Rc::clone(a), meta))
    }

    pub fn pair(a: &Rc<Self>, b: &Rc<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::Pair(Rc::clone(a), Rc::clone(b), meta))
    }

    pub fn fst(p: &Rc<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::Fst(Rc::clone(p), meta))
    }

    pub fn snd(p: &Rc<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::Snd(Rc::clone(p), meta))
    }

    pub fn con(name: Identifier, args: Vec<Rc<Self>>, meta: M) -> Rc<Self> {
        Rc::new(Self::Con(name, args.to_vec(), meta))
    }

    pub fn pcon(
        name: Identifier,
        ty: &Rc<Self>,
        args: Vec<Rc<Self>>,
        faces: Vec<Formula>,
        meta: M,
    ) -> Rc<Self> {
        Rc::new(Self::PCon(name, Rc::clone(ty), args.to_vec(), faces, meta))
    }

    pub fn pathp(a: &Rc<Self>, b: &Rc<Self>, ty: &Rc<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::PathP(Rc::clone(a), Rc::clone(b), Rc::clone(ty), meta))
    }

    pub fn plam(name: Identifier, body: &Rc<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::PLam(name, Rc::clone(body), meta))
    }

    pub fn app_formula(f: &Rc<Self>, formula: Formula, meta: M) -> Rc<Self> {
        Rc::new(Self::AppFormula(Rc::clone(f), formula, meta))
    }

    pub fn comp(a: &Rc<Self>, b: &Rc<Self>, system: System<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::Comp(Rc::clone(a), Rc::clone(b), system, meta))
    }

    pub fn comp_u(a: &Rc<Self>, system: System<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::CompU(Rc::clone(a), system, meta))
    }

    pub fn hcomp(a: &Rc<Self>, b: &Rc<Self>, system: System<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::HComp(Rc::clone(a), Rc::clone(b), system, meta))
    }

    pub fn glue(a: &Rc<Self>, system: System<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::Glue(Rc::clone(a), system, meta))
    }

    pub fn glue_elem(a: &Rc<Self>, system: System<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::GlueElem(Rc::clone(a), system, meta))
    }

    pub fn unglue_elem(a: &Rc<Self>, system: System<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::UnGlueElem(Rc::clone(a), system, meta))
    }

    pub fn unglue_elem_u(a: &Rc<Self>, b: &Rc<Self>, system: System<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::UnGlueElemU(Rc::clone(a), Rc::clone(b), system, meta))
    }

    pub fn id(a: &Rc<Self>, x: &Rc<Self>, y: &Rc<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::Id(Rc::clone(a), Rc::clone(x), Rc::clone(y), meta))
    }

    pub fn id_pair(a: &Rc<Self>, system: System<Self>, meta: M) -> Rc<Self> {
        Rc::new(Self::IdPair(Rc::clone(a), system, meta))
    }

    pub fn id_j(
        a: &Rc<Self>,
        x: &Rc<Self>,
        y: &Rc<Self>,
        p: &Rc<Self>,
        motive: &Rc<Self>,
        case: &Rc<Self>,
        meta: M,
    ) -> Rc<Self> {
        Rc::new(Self::IdJ(
            Rc::clone(a),
            Rc::clone(x),
            Rc::clone(y),
            Rc::clone(p),
            Rc::clone(motive),
            Rc::clone(case),
            meta,
        ))
    }

    pub fn is_neutral(&self) -> bool {
        match self {
            Value::Stuck(Term::Undef(_, _), _, _) => true,
            Value::Stuck(Term::Hole, _, _) => true,
            Value::Var(_, _, _) => true,
            Value::Comp(_, _, _, _) => true,
            Value::Fst(_, _) => true,
            Value::Snd(_, _) => true,
            Value::App(_, _, _) => true,
            Value::AppFormula(_, _, _) => true,
            Value::UnGlueElem(_, _, _) => true,
            Value::UnGlueElemU(_, _, _, _) => true,
            Value::IdJ(_, _, _, _, _, _, _) => true,
            _ => false,
        }
    }
}

impl<M> PartialEq for Value<M> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Stuck(t1, c1, _), Value::Stuck(t2, c2, _)) => t1 == t2 && c1 == c2,
            (Value::Pi(t1, a1, _), Value::Pi(t2, a2, _)) => a1 == a2 && t1 == t2,
            (Value::App(f1, arg1, _), Value::App(f2, arg2, _)) => f1 == f2 && arg1 == arg2,
            (Value::Var(n1, t1, _), Value::Var(n2, t2, _)) => n1 == n2 && t1 == t2,
            (Value::U, Value::U) => true,
            (Value::Sigma(t1, a1, _), Value::Sigma(t2, a2, _)) => a1 == a2 && t1 == t2,
            (Value::Pair(a1, b1, _), Value::Pair(a2, b2, _)) => a1 == a2 && b1 == b2,
            (Value::Fst(p1, _), Value::Fst(p2, _)) => p1 == p2,
            (Value::Snd(p1, _), Value::Snd(p2, _)) => p1 == p2,
            (Value::Con(n1, args1, _), Value::Con(n2, args2, _)) => n1 == n2 && args1 == args2,
            (Value::PCon(n1, ty1, args1, faces1, _), Value::PCon(n2, ty2, args2, faces2, _)) => {
                n1 == n2 && ty1 == ty2 && args1 == args2 && faces1 == faces2
            }
            (Value::PathP(a1, b1, ty1, _), Value::PathP(a2, b2, ty2, _)) => {
                a1 == a2 && b1 == b2 && ty1 == ty2
            }
            (Value::PLam(n1, b1, _), Value::PLam(n2, b2, _)) => n1 == n2 && b1 == b2,
            (Value::AppFormula(f1, form1, _), Value::AppFormula(f2, form2, _)) => {
                f1 == f2 && form1 == form2
            }
            (Value::Comp(a1, b1, sys1, _), Value::Comp(a2, b2, sys2, _)) => {
                a1 == a2 && b1 == b2 && sys1 == sys2
            }
            (Value::CompU(a1, sys1, _), Value::CompU(a2, sys2, _)) => a1 == a2 && sys1 == sys2,
            (Value::HComp(a1, b1, sys1, _), Value::HComp(a2, b2, sys2, _)) => {
                a1 == a2 && b1 == b2 && sys1 == sys2
            }
            (Value::Glue(a1, sys1, _), Value::Glue(a2, sys2, _)) => a1 == a2 && sys1 == sys2,
            (Value::GlueElem(a1, sys1, _), Value::GlueElem(a2, sys2, _)) => {
                a1 == a2 && sys1 == sys2
            }
            (Value::UnGlueElem(a1, sys1, _), Value::UnGlueElem(a2, sys2, _)) => {
                a1 == a2 && sys1 == sys2
            }
            (Value::UnGlueElemU(a1, b1, sys1, _), Value::UnGlueElemU(a2, b2, sys2, _)) => {
                a1 == a2 && b1 == b2 && sys1 == sys2
            }
            (Value::Id(a1, x1, y1, _), Value::Id(a2, x2, y2, _)) => {
                a1 == a2 && x1 == x2 && y1 == y2
            }
            (Value::IdPair(a1, sys1, _), Value::IdPair(a2, sys2, _)) => a1 == a2 && sys1 == sys2,
            (Value::IdJ(a1, x1, y1, p1, m1, c1, _), Value::IdJ(a2, x2, y2, p2, m2, c2, _)) => {
                a1 == a2 && x1 == x2 && y1 == y2 && p1 == p2 && m1 == m2 && c1 == c2
            }
            _ => false,
        }
    }
}

impl<M> Eq for Value<M> {}
