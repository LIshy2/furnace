use tracing::instrument;

use crate::ctt::formula::{Dir, Formula};
use crate::ctt::system::{Face, System};
use crate::ctt::term::Label;
use crate::ctt::Identifier;
use crate::precise::term::{Mod, Term, Value};
use crate::typechecker::context::TypeContext;
use crate::typechecker::equiv::Equiv;
use crate::typechecker::error::{ErrorCause, TypeError};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::app::{app, app_formula};
use super::comp::{comp_line, fill_line, hcomp, idj};
use super::glue::{glue, glue_elem, unglue_elem};
use super::nominal::Facing;

pub fn eval(ctx: &TypeContext, term: &Rc<Term>) -> Result<Rc<Value>, TypeError> {
    let res = match term.as_ref() {
        Term::U => Ok(Value::u()),
        Term::App(fun, arg, _) => {
            let f = eval(ctx, fun)?;
            app(ctx, &f, &eval(ctx, arg)?)
        }
        Term::Var(name, _) => Ok(ctx
            .lookup_value(name)
            .ok_or(ErrorCause::UnknownTermName(*name))?),
        Term::Pi(lam, pi_m) => {
            let Term::Lam(_, tpe, _, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            Ok(Value::pi(&eval(ctx, tpe)?, &eval(ctx, lam)?, pi_m.clone()))
        }
        Term::Sigma(lam, si_m) => {
            let Term::Lam(_, tpe, _, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            Ok(Value::sigma(
                &eval(ctx, tpe)?,
                &eval(ctx, lam)?,
                si_m.clone(),
            ))
        }
        Term::Pair(fst, snd, m) => Ok(Value::pair(&eval(ctx, fst)?, &eval(ctx, snd)?, m.clone())),
        Term::Fst(pair, _) => Ok(get_first(&eval(ctx, pair)?)),
        Term::Snd(pair, _) => Ok(get_second(&eval(ctx, pair)?)),
        Term::Where(body, decls, _) => {
            let new_ctx = ctx.with_decl_set(decls)?;
            eval(&new_ctx, body)
        }
        Term::Con(name, fields, m) => Ok(Value::con(
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
        Term::Lam(name, tpe, body, m) => Ok(Value::stuck(
            Term::Lam(*name, tpe.clone(), body.clone(), m.clone()),
            ctx.closure(term),
            m.clone(),
        )),
        Term::Split(name, exp, bs, m) => Ok(Value::stuck(
            Term::Split(*name, exp.clone(), bs.clone(), m.clone()),
            ctx.closure(term),
            m.clone(),
        )),
        Term::Sum(name, labels, m) => Ok(Value::stuck(
            Term::Sum(*name, labels.clone(), m.clone()),
            ctx.closure(term),
            m.clone(),
        )),
        Term::HSum(name, labels, m) => Ok(Value::stuck(
            Term::HSum(*name, labels.clone(), m.clone()),
            ctx.closure(term),
            m.clone(),
        )),
        Term::Undef(tpe, m) => Ok(Value::stuck(
            Term::Undef(tpe.clone(), m.clone()),
            ctx.closure(term),
            Mod::Precise,
        )),
        Term::Hole => Ok(Value::stuck(Term::Hole, ctx.closure(term), Mod::Precise)),
        Term::PathP(a, e0, e1, m) => Ok(Value::pathp(
            &eval(ctx, a)?,
            &eval(ctx, e0)?,
            &eval(ctx, e1)?,
            m.clone(),
        )),
        Term::PLam(i, t, m) => {
            // TODO maybe fresh?
            let plam_ctx = ctx.with_formula(i, Formula::Atom(*i));
            Ok(Value::plam(*i, &eval(&plam_ctx, t)?, m.clone()))
        }
        Term::AppFormula(e, phi, _) => {
            let ee = eval(ctx, e)?;
            match app_formula(ctx, &ee, eval_formula(ctx, phi)) {
                Ok(r) => Ok(r),
                Err(e) => Err(e),
            }
        }
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
        Term::Id(a, r, c, m) => Ok(Value::id(
            &eval(ctx, a)?,
            &eval(ctx, r)?,
            &eval(ctx, c)?,
            m.clone(),
        )),
        Term::IdPair(b, ts, m) => Ok(Value::id_pair(
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
    // if term.mode() == Mod::Relaxed {
    //     // println!("Compacted");
    //     Ok(ctx.compact(&res?))
    // } else {
    res
    // }
}

// #[instrument(skip_all)]
pub fn eval_formula(ctx: &TypeContext, formula: &Formula) -> Formula {
    match formula {
        d @ Formula::Dir(_) => d.clone(),
        Formula::Atom(name) => ctx.lookup_formula(name).unwrap(),
        Formula::NegAtom(name) => ctx.lookup_formula(name).unwrap().negate(),
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

// #[instrument(skip_all)]
pub fn eval_system(
    ctx: &TypeContext,
    system: &System<Rc<Term>>,
) -> Result<System<Rc<Value>>, TypeError> {
    let mut presystem = Vec::new();
    for (alpha, t_alpha) in system.iter() {
        let mut betas = HashSet::from([Face::eps()]);
        for (i, d) in alpha.binds.iter() {
            let i_value = ctx.lookup_formula(i).unwrap();
            let faces = inv_formula(i_value, d.clone());
            let mut new_betas = vec![];
            for face in faces {
                for beta in &betas {
                    if face.compatible(beta) {
                        new_betas.push(beta.meet(&face));
                    }
                }
            }
            betas = new_betas.into_iter().collect::<HashSet<_>>()
        }
        for beta in betas {
            if !presystem.iter().any(|(f, _)| beta.leq(f)) {
                presystem = presystem
                    .into_iter()
                    .filter(|(gamma, _)| !gamma.leq(&beta))
                    .collect();
                presystem.push((beta, t_alpha));
            }
        }
    }
    let mut hm = HashMap::new();
    for (alpha, t_alpha) in presystem {
        let new_ctx = ctx.with_face(&alpha)?;
        let e = eval(&new_ctx, t_alpha)?;
        hm.insert(alpha, e);
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

pub fn is_comp_system(ctx: &TypeContext, system: &System<Rc<Value>>) -> Result<bool, TypeError> {
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

pub fn get_first(term: &Rc<Value>) -> Rc<Value> {
    match term.as_ref() {
        Value::Pair(fst, _, _) => fst.clone(),
        _ => Value::fst(term, Mod::Precise),
    }
}

pub fn get_second(term: &Rc<Value>) -> Rc<Value> {
    match term.as_ref() {
        Value::Pair(_, snd, _) => snd.clone(),
        _ => Value::snd(term, Mod::Precise),
    }
}

pub fn equiv_fun(term: &Rc<Value>) -> Rc<Value> {
    get_first(&get_second(term))
}

pub fn equiv_dom(term: &Rc<Value>) -> Rc<Value> {
    get_first(term)
}

pub fn equiv_contr(term: &Rc<Value>) -> Rc<Value> {
    get_second(&get_second(term))
}

pub fn pcon(
    ctx: &TypeContext,
    c: &Identifier,
    a: &Rc<Value>,
    us: Vec<Rc<Value>>,
    phis: Vec<Formula>,
    m: Mod,
) -> Result<Rc<Value>, TypeError> {
    match a.as_ref() {
        Value::Stuck(Term::HSum(_, labels, _), e, _) => {
            let Label::PLabel(_, tele, is, ts) =
                labels.iter().find(|label| &label.name() == c).unwrap()
            else {
                Err(ErrorCause::Hole)?
            };
            let new_ctx = tele.variables.iter().zip(us.iter()).fold(
                Ok::<TypeContext, TypeError>(ctx.in_closure(e).clone()),
                |ctx, ((name, _), val)| {
                    let ctx = ctx?;
                    Ok(ctx.with_term(name, val))
                },
            )?;
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
                Ok(Value::pcon(*c, a, us, phis, m))
            }
        }
        _ => Ok(Value::pcon(*c, a, us, phis, m)),
    }
}
