use crate::ctt::term::{Branch, Dir, Face, Formula, Identifier, Label, System};
use crate::precise::term::{Mod, Term};
use crate::typechecker::context::TypeContext;
use crate::typechecker::equiv::Equiv;
use crate::typechecker::error::{ErrorCause, TypeError};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::app::{app, app_formula};
use super::comp::{comp_line, fill_line, hcomp};
use super::glue::{glue, glue_elem, unglue_elem, unglue_u};
use super::nominal::Facing;

pub fn eval(ctx: &TypeContext, term: &Rc<Term>) -> Result<Rc<Term>, TypeError> {
    let res = match term.as_ref() {
        Term::U => Ok(Term::u()),
        Term::App(fun, arg, _) => app(ctx, &eval(ctx, fun)?, &eval(ctx, arg)?),
        Term::Var(name, _) => Ok(ctx
            .lookup_term(name)
            .ok_or(ErrorCause::UnknownTermName(*name))?
            .value),
        Term::Pi(lam, pi_m) => {
            let Term::Lam(name, tpe, body, lam_m) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let tpe = eval(ctx, tpe)?;
            let body_ctx = ctx.with_term(name, &Term::var(*name, Mod::Precise), &tpe);
            Ok(Term::pi(
                &Term::lam(*name, &tpe, &eval(&body_ctx, body)?, lam_m.clone()),
                pi_m.clone(),
            ))
        }
        Term::Sigma(lam, si_m) => {
            let Term::Lam(name, tpe, body, lam_m) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let body_ctx = ctx.with_term(name, &Term::var(*name, Mod::Precise), tpe);
            Ok(Term::sigma(
                &Term::lam(
                    *name,
                    &eval(ctx, tpe)?,
                    &eval(&body_ctx, body)?,
                    lam_m.clone(),
                ),
                si_m.clone(),
            ))
        }
        Term::Pair(fst, snd, m) => Ok(Term::pair(&eval(ctx, fst)?, &eval(ctx, snd)?, m.clone())),
        Term::Fst(pair, _) => Ok(get_first(&eval(ctx, pair)?)),
        Term::Snd(pair, _) => Ok(get_second(&eval(ctx, pair)?)),
        Term::Where(body, decls, _) => {
            let new_ctx = ctx.with_decl_set(decls)?;
            eval(&new_ctx, body)
        }
        Term::Con(name, fields, m) => Ok(Term::con(
            *name,
            fields
                .iter()
                .map(|f| eval(ctx, f))
                .collect::<Result<_, TypeError>>()?,
            m.clone(),
        )),
        Term::PCon(name, a, fields, intervals, m) => pcon(
            ctx,
            name,
            &eval(ctx, a)?,
            fields
                .iter()
                .map(|f| eval(ctx, f))
                .collect::<Result<_, TypeError>>()?,
            intervals.iter().map(|f| eval_formula(ctx, f)).collect(),
            m.clone(),
        ),
        Term::Lam(name, tpe, body, m) => {
            let tpe = eval(ctx, tpe)?;
            let lam_ctx = ctx.with_term(name, &Term::var(*name, Mod::Precise), &tpe);
            Ok(Term::lam(
                *name,
                &eval(ctx, &tpe)?,
                &eval(&lam_ctx, body)?,
                m.clone(),
            ))
        }
        Term::Split(name, exp, bs, m) => {
            let split_tpe = eval(ctx, exp)?;
            let Term::Pi(lam, _) = split_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Lam(_, sum_tpe, _, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let sum_labels = match sum_tpe.as_ref() {
                Term::Sum(_, labels, _) => labels,
                Term::HSum(_, labels, _) => labels,
                _ => panic!("Not sum"),
            };
            let bs = bs
                .iter()
                .map(|b| match b {
                    Branch::OBranch(name, ps, body) => {
                        let label = sum_labels.iter().find(|l| &l.name() == name).unwrap();

                        let branch_ctx = ps.iter().zip(label.telescope().variables).fold(
                            ctx.clone(),
                            |acc, (name, (_, tpe))| {
                                acc.with_term(name, &Term::var(*name, Mod::Precise), &tpe)
                            },
                        );
                        Ok(Branch::OBranch(
                            *name,
                            ps.clone(),
                            eval(&branch_ctx, body)?,
                        ))
                    }
                    Branch::PBranch(name, ps, is, body) => {
                        let label = sum_labels.iter().find(|l| &l.name() == name).unwrap();

                        let branch_ctx = ps.iter().zip(label.telescope().variables).fold(
                            ctx.clone(),
                            |acc, (name, (_, tpe))| {
                                acc.with_term(name, &Term::var(*name, Mod::Precise), &tpe)
                            },
                        );
                        let branch_ctx = is.iter().fold(branch_ctx, |acc, name| {
                            acc.with_formula(name, Formula::Atom(*name))
                        });
                        Ok(Branch::PBranch(
                            *name,
                            ps.clone(),
                            is.clone(),
                            eval(&branch_ctx, body)?,
                        ))
                    }
                })
                .collect::<Result<_, TypeError>>()?;
            Ok(Term::split(*name, &eval(ctx, exp)?, bs, m.clone()))
        }
        Term::Sum(name, labels, m) => Ok(Term::sum(*name, labels.clone(), m.clone())),
        Term::HSum(name, labels, m) => Ok(Term::hsum(*name, labels.clone(), m.clone())),
        Term::Undef(tpe, m) => Ok(Term::undef(tpe, m.clone())),
        Term::Hole => Ok(Term::hole()),
        Term::PathP(a, e0, e1, m) => Ok(Term::pathp(
            &eval(ctx, a)?,
            &eval(ctx, e0)?,
            &eval(ctx, e1)?,
            m.clone(),
        )),
        Term::PLam(i, t, m) => {
            let plam_ctx = ctx.with_formula(i, Formula::Atom(*i));
            Ok(Term::plam(*i, &eval(&plam_ctx, t)?, m.clone()))
        }
        Term::AppFormula(e, phi, _) => app_formula(ctx, &eval(ctx, e)?, eval_formula(ctx, phi)),
        Term::Comp(a, t0, ts, _) => {
            comp_line(ctx, &eval(ctx, a)?, &eval(ctx, t0)?, eval_system(ctx, ts)?)
        }
        Term::HComp(a, t0, ts, _) => {
            hcomp(ctx, &eval(ctx, a)?, &eval(ctx, t0)?, eval_system(ctx, ts)?)
        }
        Term::Fill(a, t0, ts, _) => {
            fill_line(ctx, &eval(ctx, a)?, &eval(ctx, t0)?, &eval_system(ctx, ts)?)
        }
        Term::Glue(a, ts, m) => Ok(glue(&eval(ctx, a)?, eval_system(ctx, ts)?, m.clone())),
        Term::GlueElem(a, ts, m) => Ok(glue_elem(&eval(ctx, a)?, eval_system(ctx, ts)?, m.clone())),
        Term::UnGlueElem(a, ts, m) => {
            unglue_elem(ctx, &eval(ctx, a)?, eval_system(ctx, ts)?, m.clone())
        }
        Term::UnGlueElemU(a, b, ts, m) => unglue_u(
            ctx,
            &eval(ctx, a)?,
            &eval(ctx, b)?,
            eval_system(ctx, ts)?,
            m.clone(),
        ),
        Term::Id(a, r, c, m) => Ok(Term::id(
            &eval(ctx, a)?,
            &eval(ctx, r)?,
            &eval(ctx, c)?,
            m.clone(),
        )),
        Term::IdPair(b, ts, m) => Ok(Term::id_pair(
            &eval(ctx, b)?,
            eval_system(ctx, ts)?,
            m.clone(),
        )),
        Term::IdJ(a, t, c, d, x, p, m) => idj(
            ctx,
            &eval(ctx, a)?,
            &eval(ctx, t)?,
            &eval(ctx, c)?,
            &eval(ctx, d)?,
            &eval(ctx, x)?,
            &eval(ctx, p)?,
        ),
        _ => panic!("UNEVALUABLE VALUE IN EVAL {:?}", term),
    };
    if term.mode() == Mod::Relaxed {
        Ok(ctx.compact(&res?))
    } else {
        res
    }
}

fn idj(
    ctx: &TypeContext,
    a: &Rc<Term>,
    v: &Rc<Term>,
    c: &Rc<Term>,
    d: &Rc<Term>,
    x: &Rc<Term>,
    p: &Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    todo!()
    // match p.as_ref() {
    //     Term::IdPair(w, ws, _) => {
    //         let i = ctx.fresh();
    //         let j = ctx.fresh();
    //         let ww = Rc::new(Term::IdPair(
    //             Rc::new(Term::PLam(
    //                 j.clone(),
    //                 app_formula(
    //                     ctx.clone(),
    //                     w.clone(),
    //                     Formula::And(
    //                         Box::new(Formula::Atom(i.clone())),
    //                         Box::new(Formula::Atom(j)),
    //                     ),
    //                 )?,
    //             )),
    //             ws.insert(Face::cond(&i, Dir::Zero), v),
    //         ));
    //         comp(
    //             ctx.clone(),
    //             &i,
    //             app(
    //                 ctx.clone(),
    //                 app(
    //                     ctx.clone(),
    //                     c,
    //                     app_formula(ctx.clone(), w.clone(), Formula::Atom(i.clone()))?,
    //                 )?,
    //                 ww,
    //             )?,
    //             d.clone(),
    //             &border(ctx.clone(), d, &shape(&ws))?,
    //         )
    //     }
    //     _ => Ok(Rc::new(Term::IdJ(a, v, c, d, x, p))),
    // }
}

fn shape<A>(system: &System<A>) -> System<()> {
    todo!()
}

pub fn eval_formula(ctx: &TypeContext, formula: &Formula) -> Formula {
    match formula {
        d @ Formula::Dir(_) => d.clone(),
        Formula::Atom(name) => {
            if let Some(form) = ctx.lookup_formula(name) {
                form
            } else {
                Formula::Atom(*name)
            }
        }
        Formula::NegAtom(name) => {
            if let Some(form) = ctx.lookup_formula(name) {
                form.negate()
            } else {
                Formula::NegAtom(*name)
            }
        }
        Formula::And(lhs, rhs) => {
            let el = eval_formula(ctx, lhs.as_ref());
            let er = eval_formula(ctx, rhs.as_ref());
            el.and(&er)
        }
        Formula::Or(lhs, rhs) => {
            let el = eval_formula(ctx, lhs.as_ref());
            let er = eval_formula(ctx, rhs.as_ref());
            el.or(&er)
        }
    }
}

pub fn eval_system(ctx: &TypeContext, system: &System<Term>) -> Result<System<Term>, TypeError> {
    let mut hm = HashMap::new();
    for (alpha, t_alpha) in system.iter() {
        let mut betas: Vec<Face> = vec![Face::eps()];
        for (i, d) in alpha.binds.iter() {
            let i_value = ctx.lookup_formula(i).unwrap_or(Formula::Atom(*i));
            let faces = inv_formula(i_value, d.clone());
            let mut new_betas = vec![];
            for face in faces {
                for beta in &betas {
                    if face.compatible(beta) {
                        new_betas.push(beta.meet(&face));
                    }
                }
            }
            betas = new_betas;
        }
        for beta in betas {
            let new_ctx = ctx.with_face(&beta)?;
            let e = eval(&new_ctx, t_alpha)?;
            hm.insert(beta, e);
        }
    }
    Ok(System::from(hm))
}

pub fn inv_formula(formula: Formula, dir: Dir) -> Vec<Face> {
    match formula {
        Formula::Dir(d) => {
            if d == dir {
                vec![Face::eps()]
            } else {
                vec![]
            }
        }
        Formula::Atom(name) => vec![Face::cond(&name, dir)],
        Formula::NegAtom(name) => vec![Face::cond(&name, dir.negate())],
        Formula::And(phi, psi) => {
            let phi = *phi;
            let psi = *psi;
            match dir {
                Dir::Zero => {
                    let mut lhs = inv_formula(phi, Dir::Zero);
                    let mut rhs = inv_formula(psi, Dir::Zero);
                    lhs.append(&mut rhs);
                    lhs.into_iter()
                        .collect::<HashSet<_>>()
                        .into_iter()
                        .collect()
                }
                Dir::One => {
                    let lhs = inv_formula(phi, Dir::One);
                    let rhs = inv_formula(psi, Dir::One);
                    let mut res = vec![];
                    for l in &lhs {
                        for r in &rhs {
                            if l.compatible(r) {
                                res.push(l.meet(r));
                            }
                        }
                    }
                    res.into_iter()
                        .collect::<HashSet<_>>()
                        .into_iter()
                        .collect()
                }
            }
        }
        Formula::Or(phi, psi) => inv_formula(
            Formula::And(Box::new(phi.negate()), Box::new(psi.negate())),
            dir.negate(),
        ),
    }
}

pub fn is_comp_system(ctx: &TypeContext, system: &System<Term>) -> Result<bool, TypeError> {
    for (alpha, t_alpha) in system.iter() {
        for (beta, t_beta) in system.iter() {
            if alpha.compatible(beta) {
                let face_a = t_alpha.face(ctx, &beta.minus(alpha))?;
                let face_b = t_beta.face(ctx, &alpha.minus(beta))?;
                if !Equiv::equiv(ctx, &face_a, &face_b)? {
                    return Ok(false);
                }
            }
        }
    }
    Ok(true)
}

pub fn get_first(term: &Rc<Term>) -> Rc<Term> {
    match term.as_ref() {
        Term::Pair(fst, _, _) => fst.clone(),
        _ => Term::fst(term, Mod::Precise),
    }
}

pub fn get_second(term: &Rc<Term>) -> Rc<Term> {
    match term.as_ref() {
        Term::Pair(_, snd, _) => snd.clone(),
        _ => Term::snd(term, Mod::Precise),
    }
}

pub fn equiv_fun(term: &Rc<Term>) -> Rc<Term> {
    get_first(&get_second(term))
}

pub fn equiv_dom(term: &Rc<Term>) -> Rc<Term> {
    get_first(term)
}

pub fn equiv_contr(term: &Rc<Term>) -> Rc<Term> {
    get_second(&get_second(term))
}

pub fn pcon(
    ctx: &TypeContext,
    c: &Identifier,
    a: &Rc<Term>,
    us: Vec<Rc<Term>>,
    phis: Vec<Formula>,
    m: Mod,
) -> Result<Rc<Term>, TypeError> {
    match a.as_ref() {
        Term::HSum(_, labels, _) => {
            let Label::PLabel(_, tele, is, ts) =
                labels.iter().find(|label| &label.name() == c).unwrap()
            else {
                Err(ErrorCause::Hole)?
            };
            let new_ctx = tele
                .variables
                .iter()
                .zip(us.iter())
                .fold(ctx.clone(), |ctx, ((name, tpe), val)| {
                    ctx.with_term(name, val, tpe)
                });
            let new_ctx = is
                .iter()
                .zip(phis.iter())
                .fold(new_ctx.clone(), |ctx, (name, i)| {
                    ctx.with_formula(name, i.clone())
                });

            let vs = eval_system(&new_ctx, ts)?;
            if let Some(result) = vs.get(&Face::eps()) {
                Ok(result.clone())
            } else {
                Ok(Term::pcon(*c, a, us, phis, m))
            }
        }
        _ => Ok(Term::pcon(*c, a, us, phis, m)),
    }
}

fn is_id_pair() {
    todo!()
}
