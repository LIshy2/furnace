use std::{collections::HashMap, rc::Rc};

use crate::{
    ctt::term::{Branch, Dir, Formula, System},
    precise::term::{Mod, Term},
    typechecker::{
        context::TypeContext,
        error::{ErrorCause, TypeError},
    },
};

use super::{
    comp::{comp, fill, trans_fill_neg, trans_neg},
    eval::eval,
    nominal::{border, Facing, Nominal},
};

pub fn app(ctx: &TypeContext, fun: &Rc<Term>, arg: &Rc<Term>) -> Result<Rc<Term>, TypeError> {
    match (fun.as_ref(), arg.as_ref()) {
        (Term::Lam(x, tpe, body, _), _) => {
            let new_ctx = ctx.with_term(&x, &arg, tpe);
            eval(&new_ctx, body)
        }
        (Term::Split(_, ty, branches, _), Term::Con(c, vs, _)) => {
            let branch = branches
                .iter()
                .find(|b| &b.name() == c)
                .ok_or(ErrorCause::Hole)?;

            let Term::Pi(lam, _) = ty.as_ref() else {
                Err(ErrorCause::Hole)?
            };

            let Term::Lam(_, data_tpe, _, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };

            let (Term::Sum(_, labels, _) | Term::HSum(_, labels, _)) = data_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };

            match branch {
                Branch::OBranch(c, xs, t) => {
                    let mut body_ctx = ctx.clone();
                    let mut tpe_ctx = ctx.clone();

                    let label = labels.iter().find(|l| &l.name() == c).unwrap();
                    let tele = label.telescope();
                    for ((name, v), (t_name, tpe)) in xs.iter().zip(vs).zip(tele.variables) {
                        let tpe = eval(&tpe_ctx, &tpe)?;
                        tpe_ctx = tpe_ctx.with_term(&t_name, v, &tpe);
                        body_ctx = body_ctx.with_term(name, v, &tpe);
                    }
                    eval(&body_ctx, t)
                }
                Branch::PBranch(_, _, _, _) => Err(ErrorCause::Hole)?,
            }
        }
        (Term::Split(_, ty, branches, _), Term::PCon(c, _, us, phis, _)) => {
            let branch = branches
                .iter()
                .find(|b| &b.name() == c)
                .ok_or(ErrorCause::Hole)?;

            let Term::Pi(lam, _) = ty.as_ref() else {
                Err(ErrorCause::Hole)?
            };

            let Term::Lam(_, data_tpe, _, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };

            let (Term::Sum(_, labels, _) | Term::HSum(_, labels, _)) = data_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };

            match branch {
                Branch::PBranch(_, xs, is, t) => {
                    let mut body_ctx = ctx.clone();
                    let mut tpe_ctx = ctx.clone();

                    let label = labels.iter().find(|l| &l.name() == c).unwrap();
                    let tele = label.telescope();

                    for ((name, v), (t_name, tpe)) in xs.iter().zip(us).zip(tele.variables) {
                        let tpe = eval(&tpe_ctx, &tpe)?;
                        tpe_ctx = tpe_ctx.with_term(&t_name, v, &tpe);
                        body_ctx = body_ctx.with_term(name, v, &tpe);
                    }
                    for (name, v) in is.iter().zip(phis) {
                        body_ctx = body_ctx.with_formula(name, v.clone());
                    }
                    eval(&body_ctx, t)
                }
                Branch::OBranch(_, _, _) => Err(ErrorCause::Hole)?,
            }
        }
        (Term::Split(_, ty, _, _), Term::HComp(a, w, ws, _)) => {
            let obj = eval(ctx, ty)?;
            match obj.as_ref() {
                Term::Pi(lam, _) => {
                    let j = ctx.fresh();
                    let wsj = ws
                        .iter()
                        .map(|(f, v)| Ok((f.clone(), app_formula(ctx, v, Formula::Atom(j))?)))
                        .collect::<Result<_, TypeError>>()?;
                    let w_ = app(ctx, fun, w)?;
                    let ws_ = ws
                        .iter()
                        .map(|(alpha, t_alpha)| {
                            Ok((alpha.clone(), app(ctx, &fun.face(ctx, &alpha)?, t_alpha)?))
                        })
                        .collect::<Result<_, TypeError>>()?;
                    comp(
                        ctx,
                        &j,
                        &app(ctx, lam, &fill(ctx, &j, &a, &w, wsj)?)?,
                        &w_,
                        &ws_,
                    )
                }
                _ => Err(ErrorCause::Hole)?,
            }
        }
        (Term::Split(_, _, _, m), v) if v.is_neutral() => Ok(Term::app(fun, arg, m.clone())),
        (Term::Comp(plam, li0, ts, _), _) => {
            let Term::PLam(i, pi, _) = plam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Pi(f, _) = pi.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Lam(_, a, _, _) = f.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let j = ctx.fresh();
            let ctx = ctx.with_formula(&j, Formula::Atom(j));
            let (aj, fj) = (a.swap(i, &j), f.swap(i, &j));
            let tsj = ts
                .iter()
                .map(|(f, v)| Ok((f.clone(), app_formula(&ctx, v, Formula::Atom(j.clone()))?)))
                .collect::<Result<_, TypeError>>()?;
            let v = trans_fill_neg(&ctx, &j, &aj, arg)?;
            let vi0 = trans_neg(&ctx, &j, &aj, arg)?;
            let mut m = HashMap::new();
            let b = border(&ctx, &v, &tsj)?;
            for (k, v) in tsj.iter() {
                if let Some(v2) = b.get(&k) {
                    m.insert(k.clone(), app(&ctx, &v, v2)?);
                }
            }
            comp(
                &ctx,
                &j,
                &app(&ctx, &fj, &v)?,
                &app(&ctx, li0, &vi0)?,
                &System::from(m),
            )
        }
        _ if fun.is_neutral() => Ok(Term::app(fun, arg, Mod::Precise)),
        _ => {
            println!("fail {:?} {:?}", fun, arg);
            Err(ErrorCause::Hole)?
        }
    }
}

pub fn app_formula(
    ctx: &TypeContext,
    term: &Rc<Term>,
    formula: Formula,
) -> Result<Rc<Term>, TypeError> {
    match term.as_ref() {
        Term::PLam(i, u, _) => u.act(ctx, i, formula),
        Term::Hole => Ok(Term::app_formula(term, formula, Mod::Precise)),
        v if v.is_neutral() => {
            let tpe = infer_neutral(ctx, term)?;
            match (tpe.as_ref(), formula) {
                (Term::PathP(_, a0, _, _), Formula::Dir(Dir::Zero)) => Ok(a0.clone()),
                (Term::PathP(_, _, a1, _), Formula::Dir(Dir::One)) => Ok(a1.clone()),
                (_, phi) => Ok(Term::app_formula(term, phi, Mod::Precise)),
            }
        }
        e => Err(ErrorCause::Hole)?,
    }
}

fn infer_neutral(ctx: &TypeContext, v: &Rc<Term>) -> Result<Rc<Term>, TypeError> {
    match v.as_ref() {
        Term::Var(name, _) => Ok(ctx.lookup_term(name).ok_or(ErrorCause::Hole)?.tpe),
        Term::Undef(t, _) => eval(ctx, t),
        Term::Fst(t, _) => {
            let res = infer_neutral(ctx, t)?;
            match res.as_ref() {
                Term::Sigma(lam, _) => {
                    let Term::Lam(_, tpe, _, _) = lam.as_ref() else {
                        Err(ErrorCause::Hole)?
                    };
                    Ok(tpe.clone())
                }
                _ => Err(ErrorCause::Hole)?,
            }
        }
        Term::Snd(t, _) => {
            let res = infer_neutral(ctx, t)?;
            match res.as_ref() {
                Term::Sigma(lam, _) => Ok(app(ctx, lam, &Term::fst(t, Mod::Precise))?),
                _ => Err(ErrorCause::Hole)?,
            }
        }
        Term::App(t0, t1, _) => {
            let res = infer_neutral(ctx, t0)?;
            match res.as_ref() {
                Term::Pi(lam, _) => Ok(app(ctx, lam, t1)?),
                _ => Err(ErrorCause::Hole)?,
            }
        }
        Term::Split(_, t, _, _) => Ok(t.clone()),
        Term::AppFormula(t, phi, _) => {
            let res = infer_neutral(ctx, t)?;
            match res.as_ref() {
                Term::PathP(a, _, _, _) => app_formula(ctx, a, phi.clone()),
                _ => Err(ErrorCause::Hole)?,
            }
        }
        Term::Comp(a, _, _, _) => app_formula(ctx, a, Formula::Dir(Dir::One)),
        Term::UnGlueElemU(_, b, _, _) => Ok(b.clone()),
        Term::IdJ(_, _, c, _, x, p, _) => app(ctx, &app(ctx, c, x)?, p),
        _ => panic!("NOT VALUE {:?}", v),
    }
}
