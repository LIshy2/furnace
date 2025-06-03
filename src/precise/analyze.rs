use crate::ctt::term::{Branch, Declaration, DeclarationSet, Formula, Label, System, Telescope};
use crate::ctt::term::{Identifier, Term as CttTerm};

use crate::precise::context::PreciseContext;
use crate::precise::term::{Mod, Term};
use std::rc::Rc;

use super::context::Tag;

#[derive(Clone, Debug)]
pub enum PreTerm {
    Pi(Rc<PreTerm>, Tag),
    App(Rc<PreTerm>, Rc<PreTerm>, Tag),
    Lam(Identifier, Rc<PreTerm>, Rc<PreTerm>, Tag),
    Where(Rc<PreTerm>, DeclarationSet<PreTerm>, Tag),
    Var(Identifier, Tag),
    U,
    Sigma(Rc<PreTerm>, Tag),
    Pair(Rc<PreTerm>, Rc<PreTerm>, Tag),
    Fst(Rc<PreTerm>, Tag),
    Snd(Rc<PreTerm>, Tag),
    Con(Identifier, Vec<Rc<PreTerm>>, Tag),
    PCon(Identifier, Rc<PreTerm>, Vec<Rc<PreTerm>>, Vec<Formula>, Tag),
    Split(Identifier, Rc<PreTerm>, Vec<Branch<PreTerm>>, Tag),
    Sum(Identifier, Vec<Label<PreTerm>>, Tag),
    HSum(Identifier, Vec<Label<PreTerm>>, Tag),
    Undef(Rc<PreTerm>, Tag),
    Hole,
    PathP(Rc<PreTerm>, Rc<PreTerm>, Rc<PreTerm>, Tag),
    PLam(Identifier, Rc<PreTerm>, Tag),
    AppFormula(Rc<PreTerm>, Formula, Tag),
    Comp(Rc<PreTerm>, Rc<PreTerm>, System<PreTerm>, Tag),
    Fill(Rc<PreTerm>, Rc<PreTerm>, System<PreTerm>, Tag),
    HComp(Rc<PreTerm>, Rc<PreTerm>, System<PreTerm>, Tag),
    Glue(Rc<PreTerm>, System<PreTerm>, Tag),
    GlueElem(Rc<PreTerm>, System<PreTerm>, Tag),
    UnGlueElem(Rc<PreTerm>, System<PreTerm>, Tag),
    Id(Rc<PreTerm>, Rc<PreTerm>, Rc<PreTerm>, Tag),
    IdPair(Rc<PreTerm>, System<PreTerm>, Tag),
    IdJ(
        Rc<PreTerm>,
        Rc<PreTerm>,
        Rc<PreTerm>,
        Rc<PreTerm>,
        Rc<PreTerm>,
        Rc<PreTerm>,
        Tag,
    ),
}

impl PreTerm {
    fn tag(&self) -> Tag {
        match self {
            PreTerm::Pi(_, m) => m.clone(),
            PreTerm::App(_, _, m) => m.clone(),
            PreTerm::Lam(_, _, _, m) => m.clone(),
            PreTerm::Where(_, _, m) => m.clone(),
            PreTerm::Var(_, m) => m.clone(),
            PreTerm::U => Tag::Var(0),
            PreTerm::Sigma(_, m) => m.clone(),
            PreTerm::Pair(_, _, m) => m.clone(),
            PreTerm::Fst(_, m) => m.clone(),
            PreTerm::Snd(_, m) => m.clone(),
            PreTerm::Con(_, _, m) => m.clone(),
            PreTerm::PCon(_, _, _, _, m) => m.clone(),
            PreTerm::Split(_, _, _, m) => m.clone(),
            PreTerm::Sum(_, _, m) => m.clone(),
            PreTerm::HSum(_, _, m) => m.clone(),
            PreTerm::Undef(_, m) => m.clone(),
            PreTerm::Hole => Tag::Var(0),
            PreTerm::PathP(_, _, _, m) => m.clone(),
            PreTerm::PLam(_, _, m) => m.clone(),
            PreTerm::AppFormula(_, _, m) => m.clone(),
            PreTerm::Comp(_, _, _, m) => m.clone(),
            PreTerm::Fill(_, _, _, m) => m.clone(),
            PreTerm::HComp(_, _, _, m) => m.clone(),
            PreTerm::Glue(_, _, m) => m.clone(),
            PreTerm::GlueElem(_, _, m) => m.clone(),
            PreTerm::UnGlueElem(_, _, m) => m.clone(),
            PreTerm::Id(_, _, _, m) => m.clone(),
            PreTerm::IdPair(_, _, m) => m.clone(),
            PreTerm::IdJ(_, _, _, _, _, _, m) => m.clone(),
        }
    }
}

fn analyze(ctx: &mut PreciseContext, t: &Rc<CttTerm<()>>) -> Rc<PreTerm> {
    // println!("anal {:?}", t);
    match t.as_ref() {
        CttTerm::Pi(pi, _) => {
            let inner = analyze(ctx, pi);
            Rc::new(PreTerm::Pi(inner.clone(), inner.tag()))
        }
        CttTerm::App(f, a, _) => {
            let f_t = analyze(ctx, f);
            let a_t = analyze(ctx, a);
            ctx.unify(&f_t.tag(), &a_t.tag());
            let t = a_t.tag();
            Rc::new(PreTerm::App(f_t, a_t, t))
        }
        CttTerm::Lam(a, t, b, _) => {
            let arg_t = analyze(ctx, t);
            let arg_type = ctx.fresh();
            ctx.add(a, arg_type.clone());
            let bod_t = analyze(ctx, b);
            let bod_type = bod_t.tag();
            ctx.unify(&arg_type, &bod_type);
            Rc::new(PreTerm::Lam(*a, arg_t, bod_t, bod_type))
        }
        CttTerm::Where(e, ds, _) => {
            let decls = analyze_all(ctx, &vec![ds.clone()]).pop().unwrap();
            let tg = ctx.fresh();
            let be = analyze(ctx, e);
            ctx.unify(&tg, &be.tag());
            match &decls {
                DeclarationSet::Mutual(declarations) => {
                    for decl in declarations {
                        ctx.unify(&tg, &decl.body.tag());
                    }
                }
                _ => {}
            }
            Rc::new(PreTerm::Where(be, decls, tg))
        }
        CttTerm::Var(n, _) => Rc::new(PreTerm::Var(*n, ctx.get(n))),
        CttTerm::U => Rc::new(PreTerm::U),
        CttTerm::Sigma(si, _) => {
            let inner = analyze(ctx, si);
            Rc::new(PreTerm::Sigma(inner.clone(), inner.tag()))
        }
        CttTerm::Pair(fst, snd, _) => {
            let fst = analyze(ctx, fst);
            let snd = analyze(ctx, snd);
            ctx.unify(&fst.tag(), &snd.tag());
            let t = fst.tag();
            Rc::new(PreTerm::Pair(fst, snd, t))
        }
        CttTerm::Fst(p, _) => {
            let inner = analyze(ctx, p);
            Rc::new(PreTerm::Fst(inner.clone(), inner.tag()))
        }
        CttTerm::Snd(p, _) => {
            let inner = analyze(ctx, p);
            Rc::new(PreTerm::Snd(inner.clone(), inner.tag()))
        }
        CttTerm::Con(n, fs, _) => {
            let fs = fs.iter().map(|f| analyze(ctx, f)).collect::<Vec<_>>();
            let fresh = ctx.fresh();
            for f in &fs {
                ctx.unify(&f.tag(), &fresh);
            }
            Rc::new(PreTerm::Con(*n, fs, fresh))
        }
        CttTerm::PCon(n, t, fs, i, _) => {
            let fs = fs.iter().map(|f| analyze(ctx, f)).collect::<Vec<_>>();
            let fresh = ctx.fresh();
            for f in &fs {
                ctx.unify(&f.tag(), &fresh);
            }
            Rc::new(PreTerm::PCon(*n, analyze(ctx, t), fs, i.clone(), fresh))
        }
        CttTerm::Split(n, t, b, _) => {
            let mut tpe_vars = vec![];
            let b = b
                .iter()
                .map(|b| match b {
                    Branch::OBranch(n, ars, t) => {
                        for a in ars {
                            let f = ctx.fresh();
                            ctx.add(a, f.clone());
                            tpe_vars.push(f);
                        }
                        Branch::OBranch(*n, ars.clone(), analyze(ctx, t))
                    }
                    Branch::PBranch(n, ars, is, t) => {
                        for a in ars {
                            let f = ctx.fresh();
                            ctx.add(a, f.clone());
                            tpe_vars.push(f);
                        }
                        Branch::PBranch(*n, ars.clone(), is.clone(), analyze(ctx, t))
                    }
                })
                .collect::<Vec<_>>();

            let o = ctx.fresh();

            for t in tpe_vars {
                ctx.unify(&o.clone(), &t.clone())
            }

            Rc::new(PreTerm::Split(*n, analyze(ctx, t), b, o))
        }
        CttTerm::Sum(n, ls, _) => {
            let ls = ls
                .iter()
                .map(|l| match l {
                    Label::OLabel(n, t) => Label::OLabel(*n, analyze_tele(ctx, t)),
                    Label::PLabel(_, _, _, _) => panic!("h-label in sum"),
                })
                .collect();
            let f = ctx.fresh();
            Rc::new(PreTerm::Sum(*n, ls, f))
        }
        CttTerm::HSum(n, ls, _) => {
            let ls = ls
                .iter()
                .map(|l| match l {
                    Label::OLabel(n, t) => Label::OLabel(*n, analyze_tele(ctx, t)),
                    Label::PLabel(n, t, is, s) => {
                        let tele = analyze_tele(ctx, t);
                        let s = analyze_system(ctx, s);
                        for (_, t) in s.iter() {
                            ctx.unify(&t.tag(), &Tag::Precise);
                        }
                        Label::PLabel(*n, tele, is.clone(), s)
                    }
                })
                .collect();

            let f = ctx.fresh();
            Rc::new(PreTerm::HSum(*n, ls, f))
        }
        CttTerm::Undef(tpe, _) => {
            let f = ctx.fresh();
            Rc::new(PreTerm::Undef(analyze(ctx, tpe), f))
        }
        CttTerm::Hole => Rc::new(PreTerm::Hole),
        CttTerm::PathP(a, b, e, _) => {
            let a = analyze(ctx, a);
            let b = analyze(ctx, b);
            let e = analyze(ctx, e);

            ctx.unify(&a.tag(), &Tag::Precise);
            ctx.unify(&b.tag(), &Tag::Precise);
            ctx.unify(&e.tag(), &Tag::Precise);
            let f = ctx.fresh();
            Rc::new(PreTerm::PathP(a, b, e, f))
        }
        CttTerm::PLam(i, p, _) => {
            let inner = analyze(ctx, p);
            let t = inner.tag();
            ctx.unify(&t, &Tag::Precise);
            Rc::new(PreTerm::PLam(*i, inner, t))
        }
        CttTerm::AppFormula(f, a, _) => {
            let inner = analyze(ctx, f);
            let t = inner.tag();
            Rc::new(PreTerm::AppFormula(inner, a.clone(), t))
        }
        CttTerm::Comp(a, b, s, _) => {
            let o = ctx.fresh();
            let s = analyze_system(ctx, s);
            Rc::new(PreTerm::Comp(analyze(ctx, a), analyze(ctx, b), s, o))
        }
        CttTerm::Glue(b, es, _) => Rc::new(PreTerm::Glue(
            analyze(ctx, b),
            analyze_system(ctx, es),
            Tag::Precise,
        )),
        CttTerm::GlueElem(b, es, _) => Rc::new(PreTerm::GlueElem(
            analyze(ctx, b),
            analyze_system(ctx, es),
            Tag::Precise,
        )),
        CttTerm::UnGlueElem(b, es, _) => Rc::new(PreTerm::UnGlueElem(
            analyze(ctx, b),
            analyze_system(ctx, es),
            Tag::Precise,
        )),
        CttTerm::Fill(term, term1, system, _) => {
            let f = ctx.fresh();
            Rc::new(PreTerm::Fill(
                analyze(ctx, term),
                analyze(ctx, term1),
                analyze_system(ctx, system),
                f,
            ))
        }
        CttTerm::HComp(term, term1, system, _) => Rc::new(PreTerm::HComp(
            analyze(ctx, term),
            analyze(ctx, term1),
            analyze_system(ctx, system),
            Tag::Precise,
        )),
        CttTerm::Id(term, term1, term2, _) => Rc::new(PreTerm::Id(
            analyze(ctx, term),
            analyze(ctx, term1),
            analyze(ctx, term2),
            Tag::Precise,
        )),
        CttTerm::IdPair(term, system, _) => Rc::new(PreTerm::IdPair(
            analyze(ctx, term),
            analyze_system(ctx, system),
            Tag::Precise,
        )),
        CttTerm::IdJ(term, term1, term2, term3, term4, term5, _) => Rc::new(PreTerm::IdJ(
            analyze(ctx, term),
            analyze(ctx, term1),
            analyze(ctx, term2),
            analyze(ctx, term3),
            analyze(ctx, term4),
            analyze(ctx, term5),
            Tag::Precise,
        )),
    }
}

fn analyze_tele(ctx: &mut PreciseContext, t: &Telescope<CttTerm<()>>) -> Telescope<PreTerm> {
    Telescope {
        variables: t
            .variables
            .iter()
            .map(|(n, t)| {
                let ft = ctx.fresh();
                ctx.add(n, ft);
                (*n, analyze(ctx, t))
            })
            .collect(),
    }
}

fn analyze_system(ctx: &mut PreciseContext, t: &System<CttTerm<()>>) -> System<PreTerm> {
    t.iter()
        .map(|(f, t)| (f.clone(), analyze(ctx, t)))
        .collect()
}

pub fn analyze_all(
    ctx: &mut PreciseContext,
    decls: &Vec<DeclarationSet<CttTerm<()>>>,
) -> Vec<DeclarationSet<PreTerm>> {
    decls
        .iter()
        .map(|decl| match decl {
            DeclarationSet::Mutual(decls) => {
                // println!("mutual start");
                decls.iter().for_each(|d| {
                    // println!("add {:?}", d.name);
                    let f = ctx.fresh();
                    ctx.add(&d.name, f.clone());
                });
                let res = DeclarationSet::Mutual(
                    decls
                        .iter()
                        .map(|d| {
                            // println!("def {:?}", d.name);
                            let f = ctx.get(&d.name);
                            let t = analyze(ctx, &d.body);
                            ctx.unify(&t.tag(), &f);
                            Declaration {
                                name: d.name,
                                tpe: analyze(ctx, &d.tpe),
                                body: t,
                            }
                        })
                        .collect(),
                );
                // println!("mutual end");
                res
            }
            DeclarationSet::Opaque(s) => DeclarationSet::Opaque(*s),
            DeclarationSet::Transparent(s) => DeclarationSet::Transparent(*s),
            DeclarationSet::TransparentAll => DeclarationSet::TransparentAll,
        })
        .collect()
}

pub fn finalize_mod(ctx: &mut PreciseContext, t: &Tag) -> Mod {
    match ctx.apply(t) {
        Tag::Var(_) => Mod::Relaxed,
        Tag::Precise => Mod::Precise,
    }
}

pub fn finalize_term(ctx: &mut PreciseContext, t: &Rc<PreTerm>) -> Rc<Term> {
    match t.as_ref() {
        PreTerm::Pi(p, t) => Rc::new(Term::Pi(finalize_term(ctx, p), finalize_mod(ctx, t))),
        PreTerm::App(f, a, t) => Rc::new(Term::App(
            finalize_term(ctx, f),
            finalize_term(ctx, a),
            finalize_mod(ctx, t),
        )),
        PreTerm::Lam(n, a, b, t) => Rc::new(Term::Lam(
            *n,
            finalize_term(ctx, a),
            finalize_term(ctx, b),
            finalize_mod(ctx, t),
        )),
        PreTerm::Var(n, t) => Rc::new(Term::Var(*n, finalize_mod(ctx, t))),
        PreTerm::U => Rc::new(Term::U),
        PreTerm::Sigma(si, t) => Rc::new(Term::Sigma(finalize_term(ctx, si), finalize_mod(ctx, t))),
        PreTerm::Pair(f, s, t) => Rc::new(Term::Pair(
            finalize_term(ctx, f),
            finalize_term(ctx, s),
            finalize_mod(ctx, t),
        )),
        PreTerm::Fst(p, t) => Rc::new(Term::Fst(finalize_term(ctx, p), finalize_mod(ctx, t))),
        PreTerm::Snd(p, t) => Rc::new(Term::Snd(finalize_term(ctx, p), finalize_mod(ctx, t))),
        PreTerm::Con(n, f, t) => Rc::new(Term::Con(
            *n,
            f.iter().map(|f| finalize_term(ctx, f)).collect(),
            finalize_mod(ctx, t),
        )),
        PreTerm::PCon(n, tp, f, i, t) => Rc::new(Term::PCon(
            *n,
            finalize_term(ctx, tp),
            f.iter().map(|f| finalize_term(ctx, f)).collect(),
            i.clone(),
            finalize_mod(ctx, t),
        )),
        PreTerm::Split(n, tpe, bs, t) => Rc::new(Term::Split(
            *n,
            finalize_term(ctx, tpe),
            bs.iter()
                .map(|b| match b {
                    Branch::OBranch(n, a, b) => {
                        Branch::OBranch(*n, a.clone(), finalize_term(ctx, b))
                    }
                    Branch::PBranch(n, a, is, b) => {
                        Branch::PBranch(*n, a.clone(), is.clone(), finalize_term(ctx, b))
                    }
                })
                .collect(),
            finalize_mod(ctx, t),
        )),
        PreTerm::Sum(n, ls, t) => Rc::new(Term::Sum(
            *n,
            ls.iter()
                .map(|l| match l {
                    Label::OLabel(n, tele) => Label::OLabel(*n, finalize_tele(ctx, tele)),
                    Label::PLabel(n, tele, is, sys) => Label::PLabel(
                        *n,
                        finalize_tele(ctx, tele),
                        is.clone(),
                        finalize_system(ctx, sys),
                    ),
                })
                .collect(),
            finalize_mod(ctx, t),
        )),
        PreTerm::HSum(n, ls, t) => Rc::new(Term::HSum(
            *n,
            ls.iter()
                .map(|l| match l {
                    Label::OLabel(n, tele) => Label::OLabel(*n, finalize_tele(ctx, tele)),
                    Label::PLabel(n, tele, is, sys) => Label::PLabel(
                        *n,
                        finalize_tele(ctx, tele),
                        is.clone(),
                        finalize_system(ctx, sys),
                    ),
                })
                .collect(),
            finalize_mod(ctx, t),
        )),
        PreTerm::Undef(tpe, t) => {
            Rc::new(Term::Undef(finalize_term(ctx, tpe), finalize_mod(ctx, t)))
        }
        PreTerm::Hole => Rc::new(Term::Hole),
        PreTerm::PathP(a, b, c, t) => Rc::new(Term::PathP(
            finalize_term(ctx, a),
            finalize_term(ctx, b),
            finalize_term(ctx, c),
            finalize_mod(ctx, t),
        )),
        PreTerm::PLam(i, b, t) => {
            Rc::new(Term::PLam(*i, finalize_term(ctx, b), finalize_mod(ctx, t)))
        }
        PreTerm::AppFormula(f, a, t) => Rc::new(Term::AppFormula(
            finalize_term(ctx, f),
            a.clone(),
            finalize_mod(ctx, t),
        )),
        PreTerm::Comp(a, b, sys, t) => Rc::new(Term::Comp(
            finalize_term(ctx, a),
            finalize_term(ctx, b),
            finalize_system(ctx, sys),
            finalize_mod(ctx, t),
        )),
        PreTerm::Fill(a, b, sys, t) => Rc::new(Term::Fill(
            finalize_term(ctx, a),
            finalize_term(ctx, b),
            finalize_system(ctx, sys),
            finalize_mod(ctx, t),
        )),
        PreTerm::HComp(a, b, sys, t) => Rc::new(Term::HComp(
            finalize_term(ctx, a),
            finalize_term(ctx, b),
            finalize_system(ctx, sys),
            finalize_mod(ctx, t),
        )),
        PreTerm::Glue(b, es, t) => Rc::new(Term::Glue(
            finalize_term(ctx, b),
            finalize_system(ctx, es),
            finalize_mod(ctx, t),
        )),
        PreTerm::GlueElem(b, es, t) => Rc::new(Term::GlueElem(
            finalize_term(ctx, b),
            finalize_system(ctx, es),
            finalize_mod(ctx, t),
        )),
        PreTerm::UnGlueElem(b, es, t) => Rc::new(Term::UnGlueElem(
            finalize_term(ctx, b),
            finalize_system(ctx, es),
            finalize_mod(ctx, t),
        )),
        PreTerm::Where(e, declaration_set, t) => Rc::new(Term::Where(
            finalize_term(ctx, e),
            finalize_all(ctx, &vec![declaration_set.clone()])
                .pop()
                .unwrap(),
            finalize_mod(ctx, t),
        )),
        PreTerm::Id(t1, t2, t3, t) => Rc::new(Term::Id(
            finalize_term(ctx, t1),
            finalize_term(ctx, t2),
            finalize_term(ctx, t3),
            finalize_mod(ctx, t),
        )),
        PreTerm::IdPair(t1, sys, t) => Rc::new(Term::IdPair(
            finalize_term(ctx, t1),
            finalize_system(ctx, sys),
            finalize_mod(ctx, t),
        )),
        PreTerm::IdJ(t1, t2, t3, t4, t5, t6, t) => Rc::new(Term::IdJ(
            finalize_term(ctx, t1),
            finalize_term(ctx, t2),
            finalize_term(ctx, t3),
            finalize_term(ctx, t4),
            finalize_term(ctx, t5),
            finalize_term(ctx, t6),
            finalize_mod(ctx, t),
        )),
    }
}

pub fn finalize_system(ctx: &mut PreciseContext, sys: &System<PreTerm>) -> System<Term> {
    sys.iter()
        .map(|(k, v)| (k.clone(), finalize_term(ctx, v)))
        .collect()
}

pub fn finalize_tele(ctx: &mut PreciseContext, tele: &Telescope<PreTerm>) -> Telescope<Term> {
    Telescope {
        variables: tele
            .variables
            .iter()
            .map(|(n, t)| (*n, finalize_term(ctx, t)))
            .collect(),
    }
}

pub fn finalize_all(
    ctx: &mut PreciseContext,
    decls: &Vec<DeclarationSet<PreTerm>>,
) -> Vec<DeclarationSet<Term>> {
    decls
        .iter()
        .map(|decl| match decl {
            DeclarationSet::Mutual(decls) => DeclarationSet::Mutual(
                decls
                    .iter()
                    .map(|d| Declaration {
                        name: d.name,
                        tpe: finalize_term(ctx, &d.tpe),
                        body: finalize_term(ctx, &d.body),
                    })
                    .collect(),
            ),
            DeclarationSet::Opaque(s) => DeclarationSet::Opaque(*s),
            DeclarationSet::Transparent(s) => DeclarationSet::Transparent(*s),
            DeclarationSet::TransparentAll => DeclarationSet::TransparentAll,
        })
        .collect()
}

pub fn mark_erased(decls: &Vec<DeclarationSet<CttTerm<()>>>) -> Vec<DeclarationSet<Term>> {
    let mut ctx = PreciseContext::new();
    let analyzed = analyze_all(&mut ctx, decls);
    finalize_all(&mut ctx, &analyzed)
}
