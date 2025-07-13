use std::{collections::HashMap, rc::Rc};

use tracing::instrument;

use crate::{
    ctt::{
        formula::{Dir, Formula},
        system::System,
        term::Branch,
    },
    precise::term::{Mod, Term, Value},
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

pub fn app(ctx: &TypeContext, fun: &Rc<Value>, arg: &Rc<Value>) -> Result<Rc<Value>, TypeError> {
    match (fun.as_ref(), arg.as_ref()) {
        (Value::Stuck(Term::Lam(x, _, body, _), e, _), _) => {
            let lambda_ctx = ctx.in_closure(e);
            let body_ctx = lambda_ctx.with_term(x, arg);
            eval(&body_ctx, body)
        }
        (Value::Stuck(Term::Split(_, ty, branches, _), se, _), Value::Con(c, vs, _)) => {
            let branch = branches
                .iter()
                .find(|b| &b.name() == c)
                .ok_or(ErrorCause::Hole)?;

            let split_tpe = eval(&ctx.in_closure(se), ty)?;
            let Value::Pi(data_tpe, lam, _) = split_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };

            let Value::Stuck(Term::Lam(_, _, _, _), e, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };

            let Value::Stuck(Term::Sum(_, labels, _) | Term::HSum(_, labels, _), de, _) =
                data_tpe.as_ref()
            else {
                Err(ErrorCause::ExpectedDataType(lam.clone()))?
            };

            match branch {
                Branch::OBranch(c, xs, t) => {
                    let mut body_ctx = ctx.in_closure(se);
                    let mut tpe_ctx = ctx.in_closure(de).clone();

                    let label = labels.iter().find(|l| &l.name() == c).unwrap();
                    let tele = label.telescope();
                    for ((name, v), (t_name, _)) in xs.iter().zip(vs).zip(tele.variables) {
                        tpe_ctx = tpe_ctx.with_term(&t_name, v);
                        body_ctx = body_ctx.with_term(name, v);
                    }
                    eval(&body_ctx, t)
                }
                Branch::PBranch(_, _, _, _) => Err(ErrorCause::Hole)?,
            }
        }
        (Value::Stuck(Term::Split(_, ty, branches, _), se, _), Value::PCon(c, _, us, phis, _)) => {
            let branch = branches
                .iter()
                .find(|b| &b.name() == c)
                .ok_or(ErrorCause::Hole)?;

            let split_tpe = eval(&ctx.in_closure(se), ty)?;
            let Value::Pi(data_tpe, lam, _) = split_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };

            let Value::Stuck(Term::Sum(_, labels, _) | Term::HSum(_, labels, _), de, _) =
                data_tpe.as_ref()
            else {
                Err(ErrorCause::ExpectedDataType(lam.clone()))?
            };

            match branch {
                Branch::PBranch(_, xs, is, t) => {
                    let mut body_ctx = ctx.in_closure(se);
                    let mut tpe_ctx = ctx.in_closure(de).clone();

                    let label = labels.iter().find(|l| &l.name() == c).unwrap();
                    let tele = label.telescope();

                    for ((name, v), (t_name, _)) in xs.iter().zip(us).zip(tele.variables) {
                        tpe_ctx = tpe_ctx.with_term(&t_name, v);
                        body_ctx = body_ctx.with_term(name, v);
                    }
                    for (name, v) in is.iter().zip(phis) {
                        body_ctx = body_ctx.with_formula(name, v.clone());
                    }
                    eval(&body_ctx, t)
                }
                Branch::OBranch(_, _, _) => Err(ErrorCause::Hole)?,
            }
        }
        (Value::Stuck(Term::Split(_, ty, _, _), e, _), Value::HComp(a, w, ws, _)) => {
            let obj = eval(&ctx.in_closure(e), ty)?;
            match obj.as_ref() {
                Value::Pi(_, lam, _) => {
                    let j = ctx.fresh();
                    let wsj = ws
                        .iter()
                        .map(|(f, v)| Ok((f.clone(), app_formula(ctx, v, Formula::Atom(j))?)))
                        .collect::<Result<System<Rc<Value>>, TypeError>>()?;
                    let w_ = app(ctx, fun, w)?;
                    let ws_ = wsj
                        .iter()
                        .map(|(alpha, t_alpha)| {
                            Ok((alpha.clone(), app(ctx, &fun.face(ctx, alpha)?, t_alpha)?))
                        })
                        .collect::<Result<System<Rc<Value>>, TypeError>>()?;
                    comp(
                        ctx,
                        &j,
                        &app(ctx, lam, &fill(ctx, &j, a, w, wsj)?)?,
                        &w_,
                        &ws_,
                    )
                }
                _ => Err(ErrorCause::Hole)?,
            }
        }
        (Value::Stuck(Term::Split(_, _, _, m), _, _), v) if v.is_neutral() => {
            Ok(Value::app(fun, arg, m.clone()))
        }
        (Value::Comp(plam, li0, ts, _), _) => {
            let Value::PLam(i, pi, _) = plam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Value::Pi(va, f, _) = pi.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let j = ctx.fresh();
            let (aj, fj) = (va.swap(i, &j), f.swap(i, &j));
            let tsj = ts
                .iter()
                .map(|(f, v)| Ok((f.clone(), app_formula(&ctx, v, Formula::Atom(j))?)))
                .collect::<Result<_, TypeError>>()?;
            let v = trans_fill_neg(&ctx, &j, &aj, arg)?;
            let vi0 = trans_neg(&ctx, &j, &aj, arg)?;
            let mut m = HashMap::new();
            let b = border(&ctx, &v, &tsj)?;
            for (k, v) in tsj.iter() {
                if let Some(v2) = b.get(k) {
                    let a = app(&ctx, v, v2)?;
                    m.insert(k.clone(), a);
                }
            }
            let sm = System::from(m);
            let res = comp(&ctx, &j, &app(&ctx, &fj, &v)?, &app(&ctx, li0, &vi0)?, &sm)?;
            // if res.sups(&j) {
            //     panic!("jjjj");
            // }
            Ok(res)
        }
        _ if fun.is_neutral() => Ok(Value::app(fun, arg, Mod::Precise)),
        _ => {
            println!("fail {:?} {:?}", fun, arg);
            Err(ErrorCause::Hole)?
        }
    }
}

// #[instrument(skip_all)]
pub fn app_formula(
    ctx: &TypeContext,
    term: &Rc<Value>,
    formula: Formula,
) -> Result<Rc<Value>, TypeError> {
    match term.as_ref() {
        Value::PLam(i, u, _) => u.act(ctx, i, formula),
        Value::Stuck(Term::Hole, _, _) => Ok(Value::app_formula(term, formula, Mod::Precise)),
        v if v.is_neutral() => {
            // println!("infer_value {:?}", v);
            let tpe = infer_value(ctx, term).inspect_err(|err| {
                println!("erroooor {:?}", term);
            })?;
            match (tpe.as_ref(), formula) {
                (Value::PathP(_, a0, _, _), Formula::Dir(Dir::Zero)) => Ok(a0.clone()),
                (Value::PathP(_, _, a1, _), Formula::Dir(Dir::One)) => Ok(a1.clone()),
                (_, phi) => Ok(Value::app_formula(term, phi, Mod::Precise)),
            }
        }
        _ => Err(ErrorCause::Hole)?,
    }
}

fn infer_value(ctx: &TypeContext, v: &Rc<Value>) -> Result<Rc<Value>, TypeError> {
    match v.as_ref() {
        Value::Var(_, t, _) => Ok(t.clone()),
        Value::Stuck(Term::Undef(t, _), e, _) => eval(&ctx.in_closure(e), t),
        Value::Fst(t, _) => {
            let res = infer_value(ctx, t)?;
            match res.as_ref() {
                Value::Sigma(va, lam, _) => {
                    let Value::Stuck(Term::Lam(_, _, _, _), e, _) = lam.as_ref() else {
                        Err(ErrorCause::Hole)?
                    };
                    Ok(va.clone())
                }
                _ => Err(ErrorCause::Hole)?,
            }
        }
        Value::Snd(t, _) => {
            let res = infer_value(ctx, t)?;
            match res.as_ref() {
                Value::Sigma(_, lam, _) => Ok(app(ctx, lam, &Value::fst(t, Mod::Precise))?),
                _ => {
                    println!("biba {:?}", t);
                    Err(ErrorCause::ExpectedSigma(res))?
                }
            }
        }
        Value::App(t0, t1, _) => {
            let res = infer_value(ctx, t0)?;
            match res.as_ref() {
                Value::Pi(_, lam, _) => Ok(app(ctx, lam, t1)?),
                _ => Err(ErrorCause::Hole)?,
            }
        }
        Value::Stuck(Term::Split(_, t, _, _), e, _) => eval(&ctx.in_closure(e), t),
        Value::AppFormula(t, phi, _) => {
            let res = infer_value(ctx, t)?;
            match res.as_ref() {
                Value::PathP(a, _, _, _) => app_formula(ctx, a, phi.clone()),
                _ => Err(ErrorCause::Hole)?,
            }
        }
        Value::Comp(a, _, _, _) => app_formula(ctx, a, Formula::Dir(Dir::One)),
        Value::UnGlueElemU(_, b, _, _) => Ok(b.clone()),
        Value::IdJ(_, _, c, _, x, p, _) => app(ctx, &app(ctx, c, x)?, p),
        _ => panic!("NOT VALUE {:?}", &format!("{:?}", v)),
    }
}
