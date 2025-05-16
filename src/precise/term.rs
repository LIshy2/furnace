use crate::ctt::term::{Term as CttTerm, Value as CttValue};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Mod {
    Precise,
    Relaxed,
    Arrow(Box<Mod>, Box<Mod>),
}

pub type Term = CttTerm<Mod>;
pub type Value = CttValue<Mod>;

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
            Term::Id(_, _, _, m) => m.clone(),
            Term::IdPair(_, _, m) => m.clone(),
            Term::IdJ(_, _, _, _, _, _, m) => m.clone(),
        }
    }
}
