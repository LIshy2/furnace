use crate::ctt::term::{Branch, DeclarationSet, Formula, Identifier, Label, System};
use std::cmp::Ordering;
use std::rc::Rc;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Mod {
    Precise,
    Relaxed,
    Arrow(Box<Mod>, Box<Mod>),
}

#[derive(Clone, Debug)]
pub enum Term {
    Pi(Rc<Term>, Mod),
    App(Rc<Term>, Rc<Term>, Mod),
    Lam(Identifier, Rc<Term>, Rc<Term>, Mod),
    Where(Rc<Term>, DeclarationSet<Term>, Mod),
    Var(Identifier, Mod),
    U,
    Sigma(Rc<Term>, Mod),
    Pair(Rc<Term>, Rc<Term>, Mod),
    Fst(Rc<Term>, Mod),
    Snd(Rc<Term>, Mod),
    Con(Identifier, Vec<Rc<Term>>, Mod),
    PCon(Identifier, Rc<Term>, Vec<Rc<Term>>, Vec<Formula>, Mod),
    Split(Identifier, Rc<Term>, Vec<Branch<Term>>, Mod),
    Sum(Identifier, Vec<Label<Term>>, Mod),
    HSum(Identifier, Vec<Label<Term>>, Mod),
    Undef(Rc<Term>, Mod),
    Hole,
    PathP(Rc<Term>, Rc<Term>, Rc<Term>, Mod),
    PLam(Identifier, Rc<Term>, Mod),
    AppFormula(Rc<Term>, Formula, Mod),
    Comp(Rc<Term>, Rc<Term>, System<Term>, Mod),
    Fill(Rc<Term>, Rc<Term>, System<Term>, Mod),
    HComp(Rc<Term>, Rc<Term>, System<Term>, Mod),
    Glue(Rc<Term>, System<Term>, Mod),
    GlueElem(Rc<Term>, System<Term>, Mod),
    UnGlueElem(Rc<Term>, System<Term>, Mod),
    UnGlueElemU(Rc<Term>, Rc<Term>, System<Term>, Mod),
    Id(Rc<Term>, Rc<Term>, Rc<Term>, Mod),
    IdPair(Rc<Term>, System<Term>, Mod),
    IdJ(
        Rc<Term>,
        Rc<Term>,
        Rc<Term>,
        Rc<Term>,
        Rc<Term>,
        Rc<Term>,
        Mod,
    ),
}

impl PartialEq for Term {
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
            (Term::UnGlueElemU(t1, u1, sys1, _), Term::UnGlueElemU(t2, u2, sys2, _)) => {
                t1 == t2 && u1 == u2 && sys1 == sys2
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

impl Eq for Term {}

impl Term {
    pub fn mode(&self) -> Mod {
        match self {
            Term::Pi(_, m) => m.clone(),
            Term::App(_, _, m) => m.clone(),
            Term::Lam(_, _, _, m) => m.clone(),
            Term::Where(_, _, m) => m.clone(),
            Term::Var(_, m) => m.clone(),
            Term::U => Mod::Relaxed,
            Term::Sigma(_, m) => m.clone(),
            Term::Pair(_, _, m) => m.clone(),
            Term::Fst(_, m) => m.clone(),
            Term::Snd(_, m) => m.clone(),
            Term::Con(_, _, m) => m.clone(),
            Term::PCon(_, _, _, _, m) => m.clone(),
            Term::Split(_, _, _, m) => m.clone(),
            Term::Sum(_, _, m) => m.clone(),
            Term::HSum(_, _, m) => m.clone(),
            Term::Undef(_, m) => m.clone(),
            Term::Hole => Mod::Relaxed,
            Term::PathP(_, _, _, m) => m.clone(),
            Term::PLam(_, _, m) => m.clone(),
            Term::AppFormula(_, _, m) => m.clone(),
            Term::Comp(_, _, _, m) => m.clone(),
            Term::Fill(_, _, _, m) => m.clone(),
            Term::HComp(_, _, _, m) => m.clone(),
            Term::Glue(_, _, m) => m.clone(),
            Term::GlueElem(_, _, m) => m.clone(),
            Term::UnGlueElem(_, _, m) => m.clone(),
            Term::UnGlueElemU(_, _, _, m) => m.clone(),
            Term::Id(_, _, _, m) => m.clone(),
            Term::IdPair(_, _, m) => m.clone(),
            Term::IdJ(_, _, _, _, _, _, m) => m.clone(),
        }
    }
}
