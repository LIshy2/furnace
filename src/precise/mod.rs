use crate::ctt::term::Term;


struct Colored {
    t: Term,
    precise: bool
}

fn is_precise(t: Term) -> Colored {
    match t {
        Term::Pi(lam) => {}
        Term::App(f, a) => {}
        Term::Lam(n, t, _) => {}
        Term::Where(e, decls) => {}
        Term::Var(name) => {}
        Term::U => false,
        Term::Sigma(_) => {}
        Term::Pair(_, _) => {}
        Term::Fst(_) => {}
        Term::Snd(_) => {}
        Term::Con(_, _) => {}
        Term::PCon(_, _, _, _) => {}
        Term::Split(_, _, _) => {}
        Term::Sum(_, _) => {}
        Term::HSum(_, _) => {}
        Term::Undef(_) => {}
        Term::Hole => {}
        Term::PathP(_, _, _) =>
        Term::PLam(_, _) => {}
        Term::AppFormula(_, _) => {}
        Term::Comp(_, _, _) => {}
        Term::Fill(_, _, _) => {}
        Term::HComp(_, _, _) => {}
        Term::Glue(_, _) => {}
        Term::GlueElem(_, _) => {}
        Term::UnGlueElem(_, _) => true,
        Term::Id(_, _, _) => {}
        Term::IdPair(_, _) => {}
        Term::IdJ(_, _, _, _, _, _) => {}
        Term::PLam(_, _) => {}
    }
}