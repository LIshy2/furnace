use crate::ctt::term::{anon_id, Branch, Dir, Face, Formula, Identifier, Label, System};
use crate::precise::term::{Mod, Term};
use crate::typechecker::context::TypeContext;
use crate::typechecker::equiv::Equiv;
use crate::typechecker::error::{ErrorCause, TypeError};
use crate::typechecker::infer::{const_path, infer};
use crate::typechecker::nominal::Nominal;
use crate::utils::intersect;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

pub fn eval(ctx: TypeContext, term: &Term) -> Result<Rc<Term>, TypeError> {
    // println!("eval=====> {:?}", term);
    let res = match term {
        Term::U => Ok(Rc::new(Term::U)),
        Term::App(fun, arg, _) => app(
            ctx.clone(),
            eval(ctx.clone(), fun.as_ref())?,
            eval(ctx.clone(), arg.as_ref())?,
        ),
        Term::Var(name, _) => Ok(ctx
            .lookup_term(name)
            .ok_or(ErrorCause::UnknownTermName(name.clone()))?
            .value),
        Term::Pi(lam, pi_m) => {
            let Term::Lam(name, tpe, body, lam_m) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let tpe = eval(ctx.clone(), tpe)?;
            let body_ctx =
                ctx.with_term(name, &Rc::new(Term::Var(name.clone(), Mod::Precise)), &tpe);
            Ok(Rc::new(Term::Pi(
                Rc::new(Term::Lam(
                    name.clone(),
                    tpe,
                    eval(body_ctx, body.as_ref())?,
                    lam_m.clone(),
                )),
                pi_m.clone(),
            )))
        }
        Term::Sigma(lam, si_m) => {
            let Term::Lam(name, tpe, body, lam_m) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let body_ctx =
                ctx.with_term(name, &Rc::new(Term::Var(name.clone(), Mod::Precise)), tpe);
            Ok(Rc::new(Term::Sigma(
                Rc::new(Term::Lam(
                    name.clone(),
                    eval(ctx.clone(), tpe)?,
                    eval(body_ctx, body.as_ref())?,
                    lam_m.clone(),
                )),
                si_m.clone(),
            )))
        }
        Term::Pair(fst, snd, m) => Ok(Rc::new(Term::Pair(
            eval(ctx.clone(), fst.as_ref())?,
            eval(ctx.clone(), snd.as_ref())?,
            m.clone(),
        ))),
        Term::Fst(pair, _) => Ok(get_first(eval(ctx.clone(), pair)?)),
        Term::Snd(pair, _) => Ok(get_second(eval(ctx.clone(), pair)?)),
        Term::Where(body, decls, _) => {
            let new_ctx = ctx.with_decl_set(decls)?;
            eval(new_ctx, body)
        }
        Term::Con(name, fields, m) => Ok(Rc::new(Term::Con(
            name.clone(),
            fields
                .iter()
                .map(|f| eval(ctx.clone(), f))
                .collect::<Result<_, TypeError>>()?,
            m.clone(),
        ))),
        Term::PCon(name, a, fields, intervals, m) => pcon(
            ctx.clone(),
            name,
            eval(ctx.clone(), a)?,
            fields
                .iter()
                .map(|f| eval(ctx.clone(), f))
                .collect::<Result<_, TypeError>>()?,
            intervals
                .iter()
                .map(|f| eval_formula(ctx.clone(), f))
                .collect(),
            m.clone(),
        ),
        Term::Lam(name, tpe, body, m) => {
            let tpe = eval(ctx.clone(), tpe)?;
            let lam_ctx =
                ctx.with_term(name, &Rc::new(Term::Var(name.clone(), Mod::Precise)), &tpe);
            Ok(Rc::new(Term::Lam(
                name.clone(),
                eval(ctx.clone(), tpe.as_ref())?,
                eval(lam_ctx.clone(), body.as_ref())?,
                m.clone(),
            )))
        }
        Term::Split(name, exp, bs, m) => {
            let split_tpe = eval(ctx.clone(), exp)?;
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
                                acc.with_term(
                                    name,
                                    &Rc::new(Term::Var(name.clone(), Mod::Precise)),
                                    &tpe,
                                )
                            },
                        );
                        Ok(Branch::OBranch(
                            name.clone(),
                            ps.clone(),
                            eval(branch_ctx, body)?,
                        ))
                    }
                    Branch::PBranch(name, ps, is, body) => {
                        let label = sum_labels.iter().find(|l| &l.name() == name).unwrap();

                        let branch_ctx = ps.iter().zip(label.telescope().variables).fold(
                            ctx.clone(),
                            |acc, (name, (_, tpe))| {
                                acc.with_term(
                                    name,
                                    &Rc::new(Term::Var(name.clone(), Mod::Precise)),
                                    &tpe,
                                )
                            },
                        );
                        let branch_ctx = is.iter().fold(branch_ctx, |acc, name| {
                            acc.with_formula(name, Formula::Atom(name.clone()))
                        });
                        Ok(Branch::PBranch(
                            name.clone(),
                            ps.clone(),
                            is.clone(),
                            eval(branch_ctx, body)?,
                        ))
                    }
                })
                .collect::<Result<_, TypeError>>()?;
            Ok(Rc::new(Term::Split(
                name.clone(),
                eval(ctx.clone(), exp.as_ref())?,
                bs,
                m.clone(),
            )))
        }
        Term::Sum(name, labels, m) => {
            Ok(Rc::new(Term::Sum(name.clone(), labels.clone(), m.clone())))
        }
        Term::HSum(name, labels, m) => {
            Ok(Rc::new(Term::HSum(name.clone(), labels.clone(), m.clone())))
        }
        Term::Undef(tpe, m) => Ok(Rc::new(Term::Undef(tpe.clone(), m.clone()))),
        Term::Hole => Ok(Rc::new(Term::Hole)),
        Term::PathP(a, e0, e1, m) => Ok(Rc::new(Term::PathP(
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), e0)?,
            eval(ctx.clone(), e1)?,
            m.clone(),
        ))),
        Term::PLam(i, t, m) => {
            let plam_ctx = ctx.with_formula(i, Formula::Atom(i.clone()));
            Ok(Rc::new(Term::PLam(
                i.clone(),
                eval(plam_ctx.clone(), t)?,
                m.clone(),
            )))
        }
        Term::AppFormula(e, phi, _) => app_formula(
            ctx.clone(),
            eval(ctx.clone(), e)?,
            eval_formula(ctx.clone(), phi),
        ),
        Term::Comp(a, t0, ts, _) => {
            let a_res = eval(ctx.clone(), a)?;
            let res = comp_line(
                ctx.clone(),
                a_res,
                eval(ctx.clone(), t0)?,
                eval_system(ctx.clone(), ts)?,
            );
            res
        }
        Term::HComp(a, t0, ts, _) => hcomp(
            ctx.clone(),
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), t0)?,
            eval_system(ctx.clone(), ts)?,
        ),
        Term::Fill(a, t0, ts, _) => fill_line(
            ctx.clone(),
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), t0)?,
            eval_system(ctx.clone(), ts)?,
        ),
        Term::Glue(a, ts, m) => Ok(glue(
            eval(ctx.clone(), a)?,
            eval_system(ctx.clone(), ts)?,
            m.clone(),
        )),
        Term::GlueElem(a, ts, m) => Ok(glue_elem(
            eval(ctx.clone(), a)?,
            eval_system(ctx.clone(), ts)?,
            m.clone(),
        )),
        Term::UnGlueElem(a, ts, m) => unglue_elem(
            ctx.clone(),
            eval(ctx.clone(), a)?,
            eval_system(ctx.clone(), ts)?,
            m.clone(),
        ),
        Term::UnGlueElemU(a, b, ts, m) => unglue_u(
            ctx.clone(),
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), b)?,
            eval_system(ctx.clone(), ts)?,
            m.clone(),
        ),
        Term::Id(a, r, c, m) => Ok(Rc::new(Term::Id(
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), r)?,
            eval(ctx.clone(), c)?,
            m.clone(),
        ))),
        Term::IdPair(b, ts, m) => Ok(Rc::new(Term::IdPair(
            eval(ctx.clone(), b)?,
            eval_system(ctx.clone(), ts)?,
            m.clone(),
        ))),
        Term::IdJ(a, t, c, d, x, p, m) => idj(
            ctx.clone(),
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), t)?,
            eval(ctx.clone(), c)?,
            eval(ctx.clone(), d)?,
            eval(ctx.clone(), x)?,
            eval(ctx.clone(), p)?,
        ),
        _ => panic!("UNEVALED {:?}", term),
    };
    if term.mode() == Mod::Relaxed {
        Ok(ctx.compact(&res?))
    } else {
        res
    }
}

fn idj(
    ctx: TypeContext,
    a: Rc<Term>,
    v: Rc<Term>,
    c: Rc<Term>,
    d: Rc<Term>,
    x: Rc<Term>,
    p: Rc<Term>,
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

pub fn border<A, B>(
    ctx: TypeContext,
    value: Rc<A>,
    shape: &System<B>,
) -> Result<System<A>, TypeError>
where
    Rc<A>: Facing,
{
    Ok(System {
        binds: shape
            .binds
            .iter()
            .map(|(f, b)| Ok((f.clone(), value.clone().face(ctx.clone(), f)?)))
            .collect::<Result<_, TypeError>>()?,
    })
}

fn shape<A>(system: &System<A>) -> System<()> {
    todo!()
}

pub fn glue(v: Rc<Term>, system: System<Term>, m: Mod) -> Rc<Term> {
    if let Some(result) = system.binds.get(&Face::eps()) {
        equiv_dom(result.clone())
    } else {
        Rc::new(Term::Glue(v, system, m))
    }
}

pub fn glue_elem(v: Rc<Term>, system: System<Term>, m: Mod) -> Rc<Term> {
    if let Some(result) = system.binds.get(&Face::eps()) {
        result.clone()
    } else {
        Rc::new(Term::GlueElem(v, system, m))
    }
}

pub fn unglue_u(
    ctx: TypeContext,
    w: Rc<Term>,
    b: Rc<Term>,
    es: System<Term>,
    m: Mod,
) -> Result<Rc<Term>, TypeError> {
    if let Some(result) = es.binds.get(&Face::eps()) {
        eq_fun(ctx, result.clone(), w)
    } else {
        match w.as_ref() {
            Term::GlueElem(v, _, _) => Ok(v.clone()),
            _ => Ok(Rc::new(Term::UnGlueElemU(w, b, es, m))),
        }
    }
}

pub fn unglue(ctx: TypeContext, v: Rc<Term>, system: System<Term>) -> Result<Rc<Term>, TypeError> {
    if let Some(result) = system.binds.get(&Face::eps()) {
        app(ctx, equiv_fun(result.clone()), v)
    } else {
        match v.as_ref() {
            Term::GlueElem(v, _, _) => Ok(v.clone()),
            _ => panic!("AAAA"),
        }
    }
}

pub fn unglue_elem(
    ctx: TypeContext,
    v: Rc<Term>,
    system: System<Term>,
    m: Mod,
) -> Result<Rc<Term>, TypeError> {
    if let Some(result) = system.binds.get(&Face::eps()) {
        app(ctx, equiv_fun(result.clone()), v)
    } else {
        match v.as_ref() {
            Term::GlueElem(v, _, _) => Ok(v.clone()),
            _ => Ok(Rc::new(Term::UnGlueElem(v, system, m))),
        }
    }
}

fn fill_line(
    ctx: TypeContext,
    a: Rc<Term>,
    u: Rc<Term>,
    ts: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let i = ctx.fresh();
    let ctx = ctx.with_formula(&i, Formula::Atom(i.clone()));

    let new_system = System {
        binds: ts
            .binds
            .into_iter()
            .map(|(k, v)| Ok((k, app_formula(ctx.clone(), v, Formula::Atom(i.clone()))?)))
            .collect::<Result<_, TypeError>>()?,
    };
    Ok(Rc::new(Term::PLam(
        i.clone(),
        fill(
            ctx.with_formula(&i, Formula::Atom(i.clone())),
            &i,
            app_formula(ctx.clone(), a, Formula::Atom(i.clone()))?,
            u,
            new_system,
        )?,
        Mod::Precise,
    )))
}

fn fill(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    u: Rc<Term>,
    ts: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let j = ctx.fresh();
    let ctx = ctx.with_formula(&j, Formula::Atom(j.clone()));
    comp(
        ctx.clone(),
        &j,
        conj(ctx.clone(), a, i, &j)?,
        u.clone(),
        &conj(ctx.clone(), ts, i, &j)?.insert(Face::cond(i, Dir::Zero), u),
    )
}

pub fn comp_line(
    ctx: TypeContext,
    a: Rc<Term>,
    u: Rc<Term>,
    ts: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let i = ctx.fresh();

    let ctx = ctx.with_formula(&i, Formula::Atom(i));
    let new_system = System {
        binds: ts
            .binds
            .into_iter()
            .map(|(k, v)| {
                Ok((
                    k,
                    app_formula(ctx.clone(), v.clone(), Formula::Atom(i.clone()))?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };
    comp(
        ctx.clone(),
        &i,
        app_formula(ctx.clone(), a, Formula::Atom(i.clone()))?,
        u,
        &new_system,
    )
}

pub fn hcomp(
    ctx: TypeContext,
    a: Rc<Term>,
    u: Rc<Term>,
    us: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    if let Some(result) = us.binds.get(&Face::eps()) {
        app_formula(ctx, result.clone(), Formula::Dir(Dir::One))
    } else {
        Ok(Rc::new(Term::HComp(a, u, us, Mod::Precise)))
    }
}

pub fn eval_formula(ctx: TypeContext, formula: &Formula) -> Formula {
    match formula {
        d @ Formula::Dir(_) => d.clone(),
        Formula::Atom(name) => {
            if let Some(form) = ctx.lookup_formula(name) {
                form
            } else {
                Formula::Atom(name.clone())
            }
        }
        Formula::NegAtom(name) => {
            if let Some(form) = ctx.lookup_formula(name) {
                form.negate()
            } else {
                Formula::NegAtom(name.clone())
            }
        }
        Formula::And(lhs, rhs) => {
            let el = eval_formula(ctx.clone(), lhs.as_ref());
            let er = eval_formula(ctx.clone(), rhs.as_ref());
            el.and(&er)
        }
        Formula::Or(lhs, rhs) => {
            let el = eval_formula(ctx.clone(), lhs.as_ref());
            let er = eval_formula(ctx.clone(), rhs.as_ref());
            el.or(&er)
        }
    }
}
pub fn eval_system(ctx: TypeContext, system: &System<Term>) -> Result<System<Term>, TypeError> {
    let mut hm = HashMap::new();
    for (alpha, t_alpha) in system.binds.clone() {
        let mut betas: Vec<Face> = vec![Face::eps()];
        for (i, d) in alpha.binds {
            let i_value = ctx.lookup_formula(&i).unwrap_or(Formula::Atom(i));
            let faces = inv_formula(i_value, d);
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
            let e = eval(new_ctx, t_alpha.as_ref())?;
            hm.insert(beta, e);
        }
    }
    Ok(System { binds: hm })
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
                                res.push(l.meet(&r));
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

pub fn is_comp_system(ctx: TypeContext, system: &System<Term>) -> Result<bool, TypeError> {
    for alpha in system.binds.keys() {
        for beta in system.binds.keys() {
            if alpha.compatible(beta) {
                let face_a = system.binds[alpha]
                    .clone()
                    .face(ctx.clone(), &beta.minus(alpha))?;
                let face_b = system.binds[beta]
                    .clone()
                    .face(ctx.clone(), &alpha.minus(beta))?;
                if !Equiv::equiv(ctx.clone(), face_a.clone(), face_b.clone())? {
                    return Ok(false);
                }
            }
        }
    }
    Ok(true)
}

pub fn app(ctx: TypeContext, fun: Rc<Term>, arg: Rc<Term>) -> Result<Rc<Term>, TypeError> {
    // println!("app==// {:?}/{:?}", fun.as_ref(), arg.as_ref());
    match (fun.as_ref(), arg.as_ref()) {
        (Term::Lam(x, tpe, body, _), _) => {
            let new_ctx = ctx.with_term(&x, &arg, tpe);
            // println!("new sub {:?}", new_ctx);
            eval(new_ctx, body.as_ref())
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
                    let mut new_ctx = ctx.clone();
                    let mut tpe_ctx = ctx.clone();

                    let label = labels.iter().find(|l| &l.name() == c).unwrap();
                    let tele = label.telescope();
                    // println!("BRANCHCON {:?} {:?}", branch, arg);
                    for ((name, v), (t_name, tpe)) in xs.iter().zip(vs).zip(tele.variables) {
                        // println!("ADDD {} {}", name, t_name);
                        let tpe = eval(tpe_ctx.clone(), tpe.as_ref())?;
                        tpe_ctx = tpe_ctx.with_term(&t_name, v, &tpe);
                        new_ctx = new_ctx.with_term(name, v, &tpe);
                    }
                    eval(new_ctx, t)
                }
                Branch::PBranch(_, _, _, _) => Err(ErrorCause::Hole)?,
            }
        }
        (Term::Split(_, _, branches, _), Term::PCon(c, _, us, phis, _)) => {
            let branch = branches
                .iter()
                .find(|b| &b.name() == c)
                .ok_or(ErrorCause::Hole)?;
            match branch {
                Branch::PBranch(_, xs, is, t) => {
                    let mut new_ctx = ctx.clone();
                    for (name, v) in xs.iter().zip(us) {
                        new_ctx = new_ctx.with_term(name, v, &infer(ctx.clone(), v)?);
                    }
                    for (name, v) in is.iter().zip(phis) {
                        new_ctx = new_ctx.with_formula(name, v.clone());
                    }
                    eval(new_ctx, t)
                }
                Branch::OBranch(_, _, _) => Err(ErrorCause::Hole)?,
            }
        }
        (Term::Split(_, ty, _, _), Term::HComp(a, w, ws, _)) => {
            let obj = eval(ctx.clone(), ty.as_ref())?;
            match obj.as_ref() {
                Term::Pi(lam, _) => {
                    let j = ctx.fresh();
                    let wsj = System {
                        binds: ws
                            .binds
                            .iter()
                            .map(|(k, v)| {
                                Ok((
                                    k.clone(),
                                    app_formula(ctx.clone(), v.clone(), Formula::Atom(j.clone()))?,
                                ))
                            })
                            .collect::<Result<_, TypeError>>()?,
                    };
                    let w_ = app(ctx.clone(), fun.clone(), w.clone())?;
                    let ws_ = System {
                        binds: ws
                            .binds
                            .iter()
                            .map(|(alpha, t_alpha)| {
                                Ok((
                                    alpha.clone(),
                                    app(
                                        ctx.clone(),
                                        fun.clone().face(ctx.clone(), &alpha)?,
                                        t_alpha.clone(),
                                    )?,
                                ))
                            })
                            .collect::<Result<_, TypeError>>()?,
                    };
                    comp(
                        ctx.clone(),
                        &j,
                        app(
                            ctx.clone(),
                            lam.clone(),
                            fill(ctx, &j, a.clone(), w.clone(), wsj)?,
                        )?,
                        w_,
                        &ws_,
                    )
                }
                _ => Err(ErrorCause::Hole)?,
            }
        }
        (Term::Split(_, _, _, m), v) if is_neutral(v) => {
            Ok(Rc::new(Term::App(fun.clone(), arg.clone(), m.clone())))
        }
        (Term::Comp(plam, li0, ts, _), _) => {
            // println!("Apping comp {:?} {:?}", plam, li0);
            let Term::PLam(i, pi, _) = plam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Pi(lam, _) = pi.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Lam(_, a, _, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let f = lam.clone();
            let j = ctx.fresh();
            let ctx = ctx.with_formula(&j, Formula::Atom(j));
            let (aj, fj) = (a.swap(i, &j), f.swap(i, &j));
            let tsj = System {
                binds: ts
                    .binds
                    .iter()
                    .map(|(k, v)| {
                        Ok((
                            k.clone(),
                            app_formula(ctx.clone(), v.clone(), Formula::Atom(j.clone()))?,
                        ))
                    })
                    .collect::<Result<_, TypeError>>()?,
            };
            let v = trans_fill_neg(ctx.clone(), &j, aj.clone(), arg.clone())?;
            let vi0 = trans_neg(ctx.clone(), &j, aj, arg)?;
            let mut m = HashMap::new();
            let b = border(ctx.clone(), v.clone(), &tsj)?;
            for (k, v) in tsj.binds {
                if let Some(v2) = b.binds.get(&k) {
                    m.insert(k, app(ctx.clone(), v, v2.clone())?);
                }
            }
            comp(
                ctx.clone(),
                &j,
                app(ctx.clone(), fj, v)?,
                app(ctx.clone(), li0.clone(), vi0)?,
                &System { binds: m },
            )
        }
        _ if is_neutral(fun.as_ref()) => Ok(Rc::new(Term::App(fun, arg, Mod::Precise))),
        _ => {
            println!("fail {:?} {:?}", fun, arg);
            Err(ErrorCause::Hole)?
        }
    }
}

pub fn get_first(term: Rc<Term>) -> Rc<Term> {
    match term.as_ref() {
        Term::Pair(fst, _, _) => fst.clone(),
        _ => Rc::new(Term::Fst(term, Mod::Precise)),
    }
}

pub fn get_second(term: Rc<Term>) -> Rc<Term> {
    match term.as_ref() {
        Term::Pair(_, snd, _) => snd.clone(),
        _ => Rc::new(Term::Snd(term, Mod::Precise)),
    }
}

pub fn equiv_fun(term: Rc<Term>) -> Rc<Term> {
    get_first(get_second(term))
}

pub fn equiv_dom(term: Rc<Term>) -> Rc<Term> {
    get_first(term)
}

pub fn equiv_contr(term: Rc<Term>) -> Rc<Term> {
    get_second(get_second(term))
}

pub fn eq_fun(ctx: TypeContext, ve: Rc<Term>, ve_alpha: Rc<Term>) -> Result<Rc<Term>, TypeError> {
    trans_neg_line(ctx, ve, ve_alpha)
}

fn trans_fill(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    u: Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    fill(ctx, i, a, u, System::empty())
}

fn trans_fill_neg(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    u: Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    sym(
        ctx.clone(),
        trans_fill(ctx.clone(), i, sym(ctx.clone(), a, i)?, u)?,
        i,
    )
}

fn trans(
    ctx: TypeContext,
    i: &Identifier,
    v0: Rc<Term>,
    v1: Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    comp(ctx, i, v0, v1, &System::empty())
}

fn trans_neg(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    u: Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    trans(ctx.clone(), i, sym(ctx.clone(), a, i)?, u)
}

fn trans_neg_line(ctx: TypeContext, u: Rc<Term>, v: Rc<Term>) -> Result<Rc<Term>, TypeError> {
    let i = ctx.fresh();
    trans_neg(
        ctx.clone(),
        &i,
        app_formula(ctx.clone(), u.clone(), Formula::Atom(i.clone()))?,
        v,
    )
}

fn is_id_pair() {}

fn comp(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    u: Rc<Term>,
    ts: &System<Term>,
) -> Result<Rc<Term>, TypeError> {
    if let Some(t) = ts.binds.get(&Face::eps()) {
        return t.clone().face(ctx, &Face::cond(i, Dir::One));
    }
    match a.as_ref() {
        Term::PathP(p, v0, v1, _) => {
            let j = ctx.fresh();
            let ctx = ctx.with_formula(&j, Formula::Atom(j));
            let system = System {
                binds: ts
                    .binds
                    .iter()
                    .map(|(k, v)| {
                        Ok((
                            k.clone(),
                            app_formula(ctx.clone(), v.clone(), Formula::Atom(j.clone()))?,
                        ))
                    })
                    .collect::<Result<_, TypeError>>()?,
            }
            .insert(Face::cond(&j, Dir::Zero), v0.clone())
            .insert(Face::cond(&j, Dir::One), v1.clone());
            Ok(Rc::new(Term::PLam(
                j.clone(),
                comp(
                    ctx.clone(),
                    i,
                    app_formula(ctx.clone(), p.clone(), Formula::Atom(j.clone()))?,
                    app_formula(ctx.clone(), u, Formula::Atom(j.clone()))?,
                    &system,
                )?,
                Mod::Precise,
            )))
        }
        Term::Id(b, v0, v1, _) => match u.as_ref() {
            Term::IdPair(r, _, _) /* TODO */ => {
                let j = ctx.fresh();
                let ctx = ctx.with_formula(&j, Formula::Atom(j));

                let system = System {
                    binds: ts
                        .binds
                        .iter()
                        .map(|(k, v)| {
                            let Term::IdPair(z, _, _) = v.as_ref() else { Err(ErrorCause::Hole)? };
                            Ok((k.clone(), app_formula(ctx.clone(), z.clone(), Formula::Atom(j.clone()))?))
                        })
                        .collect::<Result<_, TypeError>>()?,
                }
                    .insert(Face::cond(&j, Dir::Zero), v0.clone())
                    .insert(Face::cond(&j, Dir::One), v1.clone());
                let w = Rc::new(Term::PLam(
                    j.clone(),
                    comp(ctx.clone(), i, b.clone(), app_formula(ctx.clone(), r.clone(), Formula::Atom(j.clone()))?, &system)?,
                    Mod::Precise
                ));
                let sys = ts.clone().face(ctx, &Face::cond(i, Dir::One))?;
                let mut system_join = HashMap::new();
                for (_, term) in sys.binds {
                    let Term::IdPair(_, s, _) = term.as_ref() else { Err(ErrorCause::Hole)? };
                    for (f, t) in s.binds.iter() {
                        system_join.insert(f.clone(), t.clone());
                    }
                }
                Ok(Rc::new(Term::IdPair(w, System {
                    binds: system_join
                }, Mod::Precise)))
            }
            _ => {
                let system = System {
                    binds: ts.binds.iter().map(|(k, v)|
                        (k.clone(), Rc::new(Term::PLam(i.clone(), v.clone(), Mod::Precise)))).collect()
                };
                Ok(Rc::new(Term::Comp(Rc::new(Term::PLam(i.clone(), a, Mod::Precise)), u, system, Mod::Precise)))
            }
        },
        Term::Sigma(f, _) => {
            let Term::Lam(_, a, _, _) = f.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let t1s = System {
                binds: ts
                    .binds
                    .iter()
                    .map(|(k, v)| (k.clone(), get_first(v.clone())))
                    .collect(),
            };
            let t2s = System {
                binds: ts
                    .binds
                    .iter()
                    .map(|(k, v)| (k.clone(), get_second(v.clone())))
                    .collect(),
            };
            let u1 = get_first(u.clone());
            let u2 = get_second(u);
            let ui1 = comp(ctx.clone(), i, a.clone(), u1.clone(), &t1s)?;
            let fill_u1 = fill(ctx.clone(), i, a.clone(), u1.clone(), t1s)?;
            let comp_u2 = comp(
                ctx.clone(),
                i,
                app(ctx.clone(), f.clone(), fill_u1)?,
                u2,
                &t2s,
            )?;
            Ok(Rc::new(Term::Pair(ui1, comp_u2, Mod::Precise)))
        }
        Term::U => {
            let ts_ = System {
                binds: ts
                    .binds
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            Rc::new(Term::PLam(i.clone(), v.clone(), Mod::Precise)),
                        )
                    })
                    .collect(),
            };
            comp_univ(ctx, u, ts_)
        }
        Term::Comp(univ, a, es, _)
            if &Term::PLam(anon_id(), Rc::new(Term::U), Mod::Precise) == univ.as_ref()
                && !is_comp_neutral(ctx.clone(), i, es, u.clone(), ts)? =>
        {
            comp_u(ctx, i, a.clone(), es.clone(), u, ts.clone())
        }
        Term::Glue(b, equivs, _) if !is_comp_neutral(ctx.clone(), i, equivs, u.clone(), ts)? => {
            comp_glue(ctx, i, b.clone(), equivs.clone(), u, ts.clone())
        }
        Term::Sum(_, labels, _) => match u.as_ref() {
            Term::Con(n, ns, _) => {
                let label = labels.iter().find(|x| &x.name() == n).unwrap();

                let tele = label.telescope();

                let mut new_ctx = ctx;

                let mut vs = vec![];

                for ind in 0..ns.len() {
                    let system = System {
                        binds: ts
                            .binds
                            .iter()
                            .map(|(k, v)| {
                                let Term::Con(_, fields, _) = v.as_ref() else {
                                    Err(ErrorCause::Hole)?
                                };
                                Ok((k.clone(), fields[ind].clone()))
                            })
                            .collect::<Result<_, TypeError>>()?,
                    };
                    let (name, tpe) = &tele.variables[ind];
                    let et = eval(new_ctx.clone(), tpe)?;
                    let v = fill(
                        new_ctx.clone(),
                        i,
                        et.clone(),
                        ns[ind].clone(),
                        system.clone(),
                    )?;
                    let vi1 = comp(new_ctx.clone(), &i, et, ns[ind].clone(), &system)?;
                    new_ctx = new_ctx.with_term(name, &v, &infer(new_ctx.clone(), v.as_ref())?);
                    vs.push(vi1);
                }
                Ok(Rc::new(Term::Con(n.clone(), vs, Mod::Precise)))
            }
            _ => {
                let system = System {
                    binds: ts
                        .binds
                        .iter()
                        .map(|(k, v)| {
                            (
                                k.clone(),
                                Rc::new(Term::PLam(i.clone(), v.clone(), Mod::Precise)),
                            )
                        })
                        .collect(),
                };
                Ok(Rc::new(Term::Comp(
                    Rc::new(Term::PLam(i.clone(), a, Mod::Precise)),
                    u,
                    system,
                    Mod::Precise,
                )))
            }
        },
        Term::HSum(_, _, _) if !is_neutral(u.as_ref()) && !is_system_neutral(ts) => {
            comp_hit(ctx, i, a, u, ts.clone())
        }
        _ => {
            let system = System {
                binds: ts
                    .binds
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            Rc::new(Term::PLam(i.clone(), v.clone(), Mod::Precise)),
                        )
                    })
                    .collect(),
            };
            Ok(Rc::new(Term::Comp(
                Rc::new(Term::PLam(i.clone(), a, Mod::Precise)),
                u,
                system,
                Mod::Precise,
            )))
        }
    }
}

fn is_comp_neutral(
    ctx: TypeContext,
    i: &Identifier,
    equivs: &System<Term>,
    u0: Rc<Term>,
    ts: &System<Term>,
) -> Result<bool, TypeError> {
    let equivsi0 = equivs.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?;
    Ok(
        (!equivsi0.binds.contains_key(&Face::eps()) && is_neutral(u0.as_ref()))
            || ts
                .binds
                .iter()
                .fold(Ok::<bool, TypeError>(false), |acc, (alpha, t_alpha)| {
                    Ok(acc? || {
                        let eq_face = equivs.clone().face(ctx.clone(), alpha)?;
                        Ok::<bool, TypeError>(
                            !eq_face.binds.contains_key(&Face::eps())
                                && is_neutral(t_alpha.as_ref()),
                        )
                    }?)
                })?,
    )
}

fn is_system_neutral(s: &System<Term>) -> bool {
    s.binds.values().any(|x| is_neutral(x.as_ref()))
}

fn comp_u(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    eqs: System<Term>,
    wi0: Rc<Term>,
    ws: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let ai1 = a.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?;

    let vs = System {
        binds: ws
            .binds
            .iter()
            .map(|(alpha, w_alpha)| {
                let a_face = a.clone().face(ctx.clone(), alpha)?;
                let eqs_face = eqs.clone().face(ctx.clone(), alpha)?;
                Ok((
                    alpha.clone(),
                    unglue_u(ctx.clone(), w_alpha.clone(), a_face, eqs_face, Mod::Precise)?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let vsi1 = vs.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?;
    let vi0 = unglue_u(
        ctx.clone(),
        wi0.clone(),
        a.clone().face(ctx.clone(), &Face::cond(i, Dir::Zero))?,
        eqs.clone().face(ctx.clone(), &Face::cond(i, Dir::Zero))?,
        Mod::Precise,
    )?;

    let vi1_prime = comp(ctx.clone(), i, a.clone(), vi0.clone(), &vs)?;
    let eqs_i1 = eqs.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?;
    let eqs_prime = System {
        binds: eqs
            .binds
            .iter()
            .filter(|(alpha, _)| !alpha.binds.contains_key(i))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect(),
    };

    let us_prime = System {
        binds: eqs_prime
            .binds
            .iter()
            .map(|(gamma, eq_g)| {
                let wi0_face = wi0.clone().face(ctx.clone(), gamma)?;
                let ws_face = ws.clone().face(ctx.clone(), gamma)?;
                Ok((
                    gamma.clone(),
                    fill(
                        ctx.clone(),
                        i,
                        app_formula(ctx.clone(), eq_g.clone(), Formula::Dir(Dir::One))?,
                        wi0_face,
                        ws_face,
                    )?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let usi1_prime = System {
        binds: eqs_prime
            .binds
            .iter()
            .map(|(gamma, eq_g)| {
                let wi0_face = wi0.clone().face(ctx.clone(), gamma)?;
                let ws_face = ws.clone().face(ctx.clone(), gamma)?;
                Ok((
                    gamma.clone(),
                    comp(ctx.clone(), i, equiv_dom(eq_g.clone()), wi0_face, &ws_face)?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let ls_prime = System {
        binds: eqs_prime
            .binds
            .iter()
            .map(|(gamma, eq_g)| {
                let a_face = a.clone().face(ctx.clone(), gamma)?;
                let vi0_face = vi0.clone().face(ctx.clone(), gamma)?;
                let us_gamma = us_prime.binds[gamma].clone();
                let vs_face = vs.clone().face(ctx.clone(), gamma)?;
                Ok((
                    gamma.clone(),
                    path_comp(
                        ctx.clone(),
                        i,
                        a_face,
                        vi0_face,
                        eq_fun(ctx.clone(), eq_g.clone(), us_gamma)?,
                        vs_face,
                    )?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let fibersys = intersect(&usi1_prime.binds, &ls_prime.binds);

    let wsi1 = ws.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?;
    let fibersys_prime = eqs_i1
        .binds
        .iter()
        .map(|(gamma, eq_g)| {
            let mut fibs_gamma = intersect(
                &wsi1.clone().face(ctx.clone(), gamma)?.binds,
                &vsi1.clone().face(ctx.clone(), gamma)?.binds,
            )
            .into_iter()
            .map(|(k, (w_val, v_val))| (k.clone(), (w_val.clone(), const_path(v_val.clone()))))
            .collect::<HashMap<_, _>>();

            let united = {
                let mut system1 = System::empty();
                let mut system2 = System::empty();
                for (k, (v1, v2)) in &fibersys {
                    system1.insert((*k).clone(), (*v1).clone());
                    system2.insert((*k).clone(), (*v2).clone());
                }
                let sys1_face = system1.face(ctx.clone(), gamma)?;
                let sys2_face = system2.face(ctx.clone(), gamma)?;

                for (k, _) in &sys1_face.binds {
                    fibs_gamma.insert(
                        k.clone(),
                        (sys1_face.binds[k].clone(), sys2_face.binds[k].clone()),
                    );
                }
                fibs_gamma
            };

            Ok((
                gamma.clone(),
                lem_eq(
                    ctx.clone(),
                    eq_g.clone(),
                    vi1_prime.clone().face(ctx.clone(), gamma)?,
                    united,
                )?,
            ))
        })
        .collect::<Result<HashMap<_, _>, TypeError>>()?;

    let mut united = System {
        binds: fibersys_prime
            .iter()
            .map(|(k, path)| (k.clone(), path.1.clone()))
            .collect(),
    };

    united.binds.extend(
        vsi1.binds
            .iter()
            .map(|(k, v)| (k.clone(), const_path(v.clone()))),
    );

    let vi1 = comp_const_line(ctx.clone(), ai1, vi1_prime, united)?;

    let usi1 = System {
        binds: fibersys_prime
            .iter()
            .map(|(k, v)| (k.clone(), v.1.clone()))
            .collect(),
    };

    Ok(glue_elem(vi1, usi1, Mod::Precise))
}

fn comp_neg(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    u: Rc<Term>,
    ts: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    comp(
        ctx.clone(),
        i,
        sym(ctx.clone(), a, i)?,
        u,
        &sym(ctx.clone(), ts, i)?,
    )
}

fn lem_eq(
    ctx: TypeContext,
    eq: Rc<Term>,
    b: Rc<Term>,
    aps: HashMap<Face, (Rc<Term>, Rc<Term>)>,
) -> Result<(Rc<Term>, Rc<Term>), TypeError> {
    let i = ctx.fresh();
    let j = ctx.fresh();
    let ta = app_formula(ctx.clone(), eq.clone(), Formula::Dir(Dir::One))?;
    let p1s = System {
        binds: aps
            .iter()
            .map(|(alpha, (aa, pa))| {
                let eqaj = app_formula(
                    ctx.clone(),
                    eq.clone().face(ctx.clone(), alpha)?,
                    Formula::Atom(j),
                )?;
                let ba = b.clone().face(ctx.clone(), alpha)?;
                let c = comp(
                    ctx.clone(),
                    &j,
                    eqaj.clone(),
                    app_formula(ctx.clone(), pa.clone(), Formula::Atom(i))?,
                    &System::empty()
                        .insert(
                            Face::cond(&i, Dir::Zero),
                            trans_fill(ctx.clone(), &j, eqaj.clone(), ba.clone())?,
                        )
                        .insert(
                            Face::cond(&i, Dir::One),
                            trans_fill_neg(ctx.clone(), &j, eqaj.clone(), aa.clone())?,
                        ),
                )?;
                Ok((alpha.clone(), c))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let thetas = System {
        binds: aps
            .iter()
            .map(|(alpha, (aa, pa))| {
                let eqaj = app_formula(
                    ctx.clone(),
                    eq.clone().face(ctx.clone(), alpha)?,
                    Formula::Atom(j),
                )?;
                let ba = b.clone().face(ctx.clone(), alpha)?;
                let c = fill(
                    ctx.clone(),
                    &j,
                    eqaj.clone(),
                    app_formula(ctx.clone(), pa.clone(), Formula::Atom(i))?,
                    System::empty()
                        .insert(
                            Face::cond(&i, Dir::Zero),
                            trans_fill(ctx.clone(), &j, eqaj.clone(), ba.clone())?,
                        )
                        .insert(
                            Face::cond(&i, Dir::One),
                            trans_fill_neg(ctx.clone(), &j, eqaj.clone(), aa.clone())?,
                        ),
                )?;
                Ok((alpha.clone(), c))
            })
            .collect::<Result<_, TypeError>>()?,
    };
    let a = comp(
        ctx.clone(),
        &i,
        ta.clone(),
        trans(
            ctx.clone(),
            &i,
            app_formula(ctx.clone(), eq.clone(), Formula::Atom(i))?,
            b.clone(),
        )?,
        &p1s,
    )?;
    let p1 = fill(
        ctx.clone(),
        &i,
        ta,
        trans(
            ctx.clone(),
            &i,
            app_formula(ctx.clone(), eq.clone(), Formula::Atom(i))?,
            b.clone(),
        )?,
        p1s,
    )?;
    let thetas_ = thetas
        .insert(
            Face::cond(&i, Dir::Zero),
            trans_fill(
                ctx.clone(),
                &j,
                app_formula(ctx.clone(), eq.clone(), Formula::Atom(j))?,
                b.clone(),
            )?,
        )
        .insert(
            Face::cond(&i, Dir::One),
            trans_fill_neg(
                ctx.clone(),
                &j,
                app_formula(ctx.clone(), eq.clone(), Formula::Atom(j))?,
                a.clone(),
            )?,
        );
    Ok((
        a,
        Rc::new(Term::PLam(
            i,
            comp_neg(
                ctx.clone(),
                &j,
                app_formula(ctx.clone(), eq, Formula::Atom(j))?,
                p1,
                thetas_,
            )?,
            Mod::Precise,
        )),
    ))
}

fn comp_glue(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    eqs: System<Term>,
    wi0: Rc<Term>,
    ws: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let ai1 = a.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?;

    let vs = System {
        binds: ws
            .binds
            .iter()
            .map(|(alpha, w_alpha)| {
                let eqs_face = eqs.clone().face(ctx.clone(), alpha)?;
                Ok((
                    alpha.clone(),
                    unglue(ctx.clone(), w_alpha.clone(), eqs_face)?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let vsi1 = vs.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?;
    let vi0 = unglue(
        ctx.clone(),
        wi0.clone(),
        eqs.clone().face(ctx.clone(), &Face::cond(i, Dir::Zero))?,
    )?;

    let vi1_prime = comp(ctx.clone(), i, a.clone(), vi0.clone(), &vs)?;

    let eqs_i1 = eqs.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?;
    let eqs_prime = System {
        binds: eqs
            .binds
            .iter()
            .filter(|(alpha, _)| !alpha.binds.contains_key(i))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect(),
    };
    // println!("FILTERED COMP GLUE {:?}", eqs_prime);

    let us_prime = System {
        binds: eqs_prime
            .binds
            .iter()
            .map(|(gamma, eq_g)| {
                let wi0_face = wi0.clone().face(ctx.clone(), gamma)?;
                let ws_face = ws.clone().face(ctx.clone(), gamma)?;
                Ok((
                    gamma.clone(),
                    fill(ctx.clone(), i, equiv_dom(eq_g.clone()), wi0_face, ws_face)?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let usi1_prime = System {
        binds: eqs_prime
            .binds
            .iter()
            .map(|(gamma, eq_g)| {
                let wi0_face = wi0.clone().face(ctx.clone(), gamma)?;
                let ws_face = ws.clone().face(ctx.clone(), gamma)?;
                Ok((
                    gamma.clone(),
                    comp(ctx.clone(), i, equiv_dom(eq_g.clone()), wi0_face, &ws_face)?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let ls_prime = System {
        binds: eqs_prime
            .binds
            .iter()
            .map(|(gamma, eq_g)| {
                let a_face = a.clone().face(ctx.clone(), gamma)?;
                let vi0_face = vi0.clone().face(ctx.clone(), gamma)?;
                let us_gamma = us_prime.binds[gamma].clone();
                let vs_face = vs.clone().face(ctx.clone(), gamma)?;
                Ok((
                    gamma.clone(),
                    path_comp(
                        ctx.clone(),
                        i,
                        a_face,
                        vi0_face,
                        app(ctx.clone(), equiv_fun(eq_g.clone()), us_gamma)?,
                        vs_face,
                    )?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let fibersys = System {
        binds: intersect(&usi1_prime.binds, &ls_prime.binds)
            .into_iter()
            .map(|(k, (us_val, ls_val))| {
                (
                    k.clone(),
                    Rc::new(Term::Pair(us_val.clone(), ls_val.clone(), Mod::Precise)),
                )
            })
            .collect(),
    };

    let wsi1 = ws.face(ctx.clone(), &Face::cond(i, Dir::One))?;
    let fibersys_prime = System {
        binds: eqs_i1
            .binds
            .iter()
            .map(|(gamma, equiv_g)| {
                let mut fibs_gamma = System {
                    binds: intersect(
                        &wsi1.clone().face(ctx.clone(), gamma)?.binds,
                        &vsi1.clone().face(ctx.clone(), gamma)?.binds,
                    )
                    .into_iter()
                    .map(|(k, (w_val, v_val))| {
                        (
                            k.clone(),
                            Rc::new(Term::Pair(
                                w_val.clone(),
                                const_path(v_val.clone()),
                                Mod::Precise,
                            )),
                        )
                    })
                    .collect(),
                };
                fibs_gamma
                    .binds
                    .extend(fibersys.clone().face(ctx.clone(), gamma)?.binds);
                let combined = fibs_gamma;
                let fiber_type = mk_fiber_type(
                    ctx.clone(),
                    ai1.clone().face(ctx.clone(), gamma)?,
                    vi1_prime.clone().face(ctx.clone(), gamma)?,
                    equiv_g.clone(),
                )?;
                Ok((
                    gamma.clone(),
                    extend(
                        ctx.clone(),
                        fiber_type,
                        app(
                            ctx.clone(),
                            equiv_contr(equiv_g.clone()),
                            vi1_prime.clone().face(ctx.clone(), gamma)?,
                        )?,
                        combined,
                    )?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let mut united = System {
        binds: fibersys_prime
            .binds
            .iter()
            .map(|(k, v)| (k.clone(), get_second(v.clone())))
            .collect(),
    };

    united.binds.extend(
        vsi1.binds
            .iter()
            .map(|(k, v)| (k.clone(), const_path(v.clone()))),
    );

    let vi1 = comp_const_line(ctx.clone(), ai1, vi1_prime, united)?;

    let usi1 = System {
        binds: fibersys_prime
            .binds
            .iter()
            .map(|(k, v)| (k.clone(), get_first(v.clone())))
            .collect(),
    };

    Ok(glue_elem(vi1, usi1, Mod::Precise))
}

fn comp_hit(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    u: Rc<Term>,
    us: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    hcomp(
        ctx.clone(),
        a.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?,
        transp_hit(ctx.clone(), i, a.clone(), u)?,
        System {
            binds: us
                .binds
                .iter()
                .map(|(alpha, u_alpha)| {
                    let v = Rc::new(Term::PLam(
                        i.clone(),
                        squeeze_hit(
                            ctx.clone(),
                            i,
                            a.clone().face(ctx.clone(), alpha)?,
                            u_alpha.clone(),
                        )?,
                        Mod::Precise,
                    ));
                    Ok((alpha.clone(), v))
                })
                .collect::<Result<_, TypeError>>()?,
        },
    )
}

fn squeeze_hit(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    u: Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    let j = ctx.fresh();
    let Term::HSum(_, labels, _) = a.as_ref() else {
        Err(ErrorCause::Hole)?
    };
    match u.as_ref() {
        Term::Con(n, us, m) => {
            // println!("squeeze_hit {} {:?}", n, labels);
            let label = labels.iter().find(|l| &l.name() == n).unwrap();
            let tele = label.telescope();
            Ok(Rc::new(Term::Con(
                n.clone(),
                squeezes(i, &tele.variables, ctx, us)?,
                m.clone(),
            )))
        }
        Term::PCon(c, _, ws0, phis, m) => {
            let label = labels.iter().find(|l| &l.name() == c).unwrap();
            let tele = label.telescope();
            Ok(pcon(
                ctx.clone(),
                c,
                a.face(ctx.clone(), &Face::cond(i, Dir::One))?,
                squeezes(i, &tele.variables, ctx, ws0)?,
                phis.clone(),
                m.clone(),
            )?)
        }
        Term::HComp(_, v, vs, _) => {
            let ai1 = a.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?;
            let squeezed = squeeze_hit(ctx.clone(), &i, a.clone(), v.clone())?;

            let processed_system = System {
                binds: vs
                    .binds
                    .iter()
                    .map(|(alpha, v_alpha)| match alpha.binds.get(i) {
                        None => Ok((
                            alpha.clone(),
                            Rc::new(Term::PLam(
                                j.clone(),
                                squeeze_hit(
                                    ctx.clone(),
                                    i,
                                    a.clone().face(ctx.clone(), alpha)?,
                                    app_formula(
                                        ctx.clone(),
                                        v_alpha.clone(),
                                        Formula::Atom(j.clone()),
                                    )?,
                                )?,
                                Mod::Precise,
                            )),
                        )),
                        Some(Dir::Zero) => Ok((
                            alpha.clone(),
                            Rc::new(Term::PLam(
                                j.clone(),
                                transp_hit(
                                    ctx.clone(),
                                    i,
                                    a.clone().face(ctx.clone(), &alpha.removed(i))?,
                                    app_formula(
                                        ctx.clone(),
                                        v_alpha.clone(),
                                        Formula::Atom(j.clone()),
                                    )?,
                                )?,
                                Mod::Precise,
                            )),
                        )),
                        Some(Dir::One) => Ok((alpha.clone(), v_alpha.clone())),
                    })
                    .collect::<Result<_, TypeError>>()?,
            };
            hcomp(ctx.clone(), ai1, squeezed, processed_system)
        }
        _ => Err(ErrorCause::Hole)?,
    }
}

fn transp_hit(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    u: Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    let j = ctx.fresh();
    let Term::HSum(name, labels, _) = a.as_ref() else {
        Err(ErrorCause::Hole)?
    };
    match u.as_ref() {
        Term::Con(n, us, m) => {
            let label = labels.iter().find(|l| &l.name() == n).unwrap();
            let tele = label.telescope();
            Ok(Rc::new(Term::Con(
                n.clone(),
                transps(i, tele.variables, ctx, us)?,
                m.clone(),
            )))
        }
        Term::PCon(c, _, ws0, phis, m) => {
            let label = labels.iter().find(|l| &l.name() == c).unwrap();
            let tele = label.telescope();
            pcon(
                ctx.clone(),
                c,
                a.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?,
                transps(i, tele.variables, ctx, ws0)?,
                phis.clone(),
                m.clone(),
            )
        }
        Term::HComp(_, v, vs, _) => hcomp(
            ctx.clone(),
            a.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?,
            transp_hit(ctx.clone(), i, a.clone(), v.clone())?,
            System {
                binds: vs
                    .binds
                    .iter()
                    .map(|(alpha, v_alpha)| {
                        let v = Rc::new(Term::PLam(
                            j.clone(),
                            transp_hit(
                                ctx.clone(),
                                &j,
                                a.clone().face(ctx.clone(), alpha)?,
                                app_formula(ctx.clone(), v_alpha.clone(), Formula::Atom(j))?,
                            )?,
                            Mod::Precise,
                        ));
                        Ok((alpha.clone(), v))
                    })
                    .collect::<Result<_, TypeError>>()?,
            },
        ),
        _ => Err(ErrorCause::Hole)?,
    }
}

fn comp_univ(ctx: TypeContext, b: Rc<Term>, es: System<Term>) -> Result<Rc<Term>, TypeError> {
    if let Some(res) = es.binds.get(&Face::eps()) {
        app_formula(ctx.clone(), res.clone(), Formula::Dir(Dir::One))
    } else {
        Ok(Rc::new(Term::Comp(
            Rc::new(Term::PLam(anon_id(), Rc::new(Term::U), Mod::Precise)),
            b.clone(),
            es,
            Mod::Precise,
        )))
    }
}

fn path_comp(
    ctx: TypeContext,
    i: &Identifier,
    a: Rc<Term>,
    u0: Rc<Term>,
    u: Rc<Term>,
    us: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let j = ctx.fresh();
    let us_ = us.insert(Face::cond(&j, Dir::One), u);
    Ok(Rc::new(Term::PLam(
        j.clone(),
        comp(ctx, i, a, u0, &us_)?,
        Mod::Precise,
    )))
}

pub fn pcon(
    ctx: TypeContext,
    c: &Identifier,
    a: Rc<Term>,
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
                .fold(ctx, |ctx, ((name, tpe), val)| ctx.with_term(name, val, tpe));
            let new_ctx = is
                .iter()
                .zip(phis.iter())
                .fold(new_ctx, |ctx, (name, i)| ctx.with_formula(name, i.clone()));
            let vs = eval_system(new_ctx, ts)?;
            if let Some(result) = vs.binds.get(&Face::eps()) {
                Ok(result.clone())
            } else {
                Ok(Rc::new(Term::PCon(c.clone(), a, us, phis, m)))
            }
        }
        _ => Ok(Rc::new(Term::PCon(c.clone(), a, us, phis, m))),
    }
}

fn transps(
    i: &Identifier,
    telescope: Vec<(Identifier, Rc<Term>)>,
    ctx: TypeContext,
    us: &Vec<Rc<Term>>,
) -> Result<Vec<Rc<Term>>, TypeError> {
    let mut vs = vec![];
    let mut new_ctx = ctx;
    for ((x, a), u) in telescope.iter().zip(us) {
        let t = eval(new_ctx.clone(), a)?;
        let v = trans_fill(new_ctx.clone(), i, t.clone(), u.clone())?;
        let vi1 = trans(new_ctx.clone(), i, t.clone(), u.clone())?;
        new_ctx.with_term(x, &v, &t);
        vs.push(vi1);
    }

    Ok(vs)
}

fn squeezes(
    i: &Identifier,
    xas: &[(Identifier, Rc<Term>)],
    ctx: TypeContext,
    us: &[Rc<Term>],
) -> Result<Vec<Rc<Term>>, TypeError> {
    let j = ctx.fresh();

    let mut ctx = ctx;
    let mut vs = vec![];

    for ((x, a), u) in xas.iter().zip(us) {
        let ts = System {
            binds: HashMap::from([(
                Face::cond(i, Dir::One),
                u.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?,
            )]),
        };
        let va = disj(ctx.clone(), eval(ctx.clone(), a)?, i, &j)?;
        let v = disj(
            ctx.clone(),
            fill(ctx.clone(), &j, va.clone(), u.clone(), ts.clone())?,
            i,
            &j,
        )?;
        let vi1 = disj(
            ctx.clone(),
            comp(ctx.clone(), &j, va.clone(), u.clone(), &ts)?,
            i,
            &j,
        )?;
        ctx = ctx.with_term(x, &v, &va);
        vs.push(vi1);
    }
    Ok(vs)
}

fn extend(
    ctx: TypeContext,
    b: Rc<Term>,
    q: Rc<Term>,
    ts: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let i = ctx.fresh();
    let ts_ = System {
        binds: ts
            .binds
            .iter()
            .map(|(alpha, t_alpha)| {
                Ok((
                    alpha.clone(),
                    app_formula(
                        ctx.clone(),
                        app(
                            ctx.clone(),
                            get_second(q.clone()).face(ctx.clone(), alpha)?,
                            t_alpha.clone(),
                        )?,
                        Formula::Atom(i),
                    )?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };
    let res = comp(ctx.clone(), &i, b, get_first(q), &ts_);
    // println!("EXTEND FINAL");
    res
}

fn mk_fiber_type(
    ctx: TypeContext,
    a: Rc<Term>,
    x: Rc<Term>,
    equiv: Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    // println!("mk fiber type {:?} {:?} {:?}", a, x, equiv);
    let a_lit = ctx.fresh();
    let x_lit = ctx.fresh();
    let y_lit = ctx.fresh();
    let f_lit = ctx.fresh();
    let t_lit = ctx.fresh();

    let ta = Rc::new(Term::Var(a_lit, Mod::Precise));
    let tx = Rc::new(Term::Var(x_lit, Mod::Precise));
    let ty = Rc::new(Term::Var(y_lit, Mod::Precise));
    let tf = Rc::new(Term::Var(f_lit, Mod::Precise));
    let tt = Rc::new(Term::Var(t_lit, Mod::Precise));
    let ctx = ctx
        .with_term(&a_lit, &a, &Rc::new(Term::Hole))
        .with_term(&x_lit, &x, &Rc::new(Term::Hole))
        .with_term(&f_lit, &equiv_fun(equiv.clone()), &Rc::new(Term::Hole))
        .with_term(&t_lit, &equiv_dom(equiv.clone()), &Rc::new(Term::Hole));

    let res = eval(
        ctx,
        &Term::Sigma(
            Rc::new(Term::Lam(
                y_lit,
                tt,
                Rc::new(Term::PathP(
                    Rc::new(Term::PLam(anon_id(), ta, Mod::Precise)),
                    tx,
                    Rc::new(Term::App(tf, ty, Mod::Precise)),
                    Mod::Precise,
                )),
                Mod::Precise,
            )),
            Mod::Precise,
        ),
    );
    // println!("EVALED");
    res
}

fn comp_const_line(
    ctx: TypeContext,
    a: Rc<Term>,
    u: Rc<Term>,
    ts: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let i = ctx.fresh();
    let ts_ = System {
        binds: ts
            .binds
            .iter()
            .map(|(alpha, t_alpha)| {
                Ok((
                    alpha.clone(),
                    app_formula(ctx.clone(), t_alpha.clone(), Formula::Atom(i.clone()))?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };
    comp(ctx, &i, a, u, &ts_)
}

fn is_neutral(v: &Term) -> bool {
    match v {
        Term::Undef(_, _) => true,
        Term::Hole => true,
        Term::Var(_, _) => true,
        Term::Comp(_, _, _, _) => true,
        Term::Fst(_, _) => true,
        Term::Snd(_, _) => true,
        Term::Split(_, _, _, _) => true,
        Term::App(_, _, _) => true,
        Term::AppFormula(_, _, _) => true,
        Term::UnGlueElem(_, _, _) => true,
        Term::UnGlueElemU(_, _, _, _) => true,
        Term::IdJ(_, _, _, _, _, _, _) => true,
        _ => false,
    }
}

pub trait Facing: Sized {
    fn face(self, ctx: TypeContext, face: &Face) -> Result<Self, TypeError>;
}

impl<A: Nominal> Facing for A {
    fn face(self, ctx: TypeContext, face: &Face) -> Result<A, TypeError> {
        face.binds.iter().fold(Ok(self), |a, (i, d)| {
            a?.act(ctx.clone(), i, Formula::Dir(d.clone()))
        })
    }
}

fn conj<A: Nominal>(
    ctx: TypeContext,
    a: A,
    i: &Identifier,
    j: &Identifier,
) -> Result<A, TypeError> {
    a.act(
        ctx,
        i,
        Formula::And(
            Box::new(Formula::Atom(i.clone())),
            Box::new(Formula::Atom(j.clone())),
        ),
    )
}

fn disj<A: Nominal>(
    ctx: TypeContext,
    a: A,
    i: &Identifier,
    j: &Identifier,
) -> Result<A, TypeError> {
    a.act(
        ctx,
        i,
        Formula::Or(
            Box::new(Formula::Atom(i.clone())),
            Box::new(Formula::Atom(j.clone())),
        ),
    )
}

fn sym<A: Nominal>(ctx: TypeContext, a: A, i: &Identifier) -> Result<A, TypeError> {
    a.act(ctx, i, Formula::NegAtom(i.clone()))
}

pub fn app_formula(
    ctx: TypeContext,
    term: Rc<Term>,
    formula: Formula,
) -> Result<Rc<Term>, TypeError> {
    match term.as_ref() {
        Term::PLam(i, u, _) => u.act(ctx.clone(), i, formula),
        Term::Hole => Ok(Rc::new(Term::AppFormula(term, formula, Mod::Precise))),
        v if is_neutral(v) => {
            let tpe = infer_type(ctx, v)?;
            match (tpe.as_ref(), formula) {
                (Term::PathP(_, a0, _, _), Formula::Dir(Dir::Zero)) => Ok(a0.clone()),
                (Term::PathP(_, _, a1, _), Formula::Dir(Dir::One)) => Ok(a1.clone()),
                (_, phi) => Ok(Rc::new(Term::AppFormula(term.clone(), phi, Mod::Precise))),
            }
        }
        e => {
            println!("{:?}", e);
            Err(ErrorCause::Hole)?
        }
    }
}

fn infer_type(ctx: TypeContext, v: &Term) -> Result<Rc<Term>, TypeError> {
    // println!("infer type {:?}", v);
    match v {
        Term::Var(name, _) => Ok(ctx.lookup_term(name).ok_or(ErrorCause::Hole)?.tpe),
        Term::Undef(t, _) => eval(ctx.clone(), t),
        Term::Fst(t, _) => {
            let res = infer_type(ctx.clone(), t)?;
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
            let res = infer_type(ctx.clone(), t)?;
            match res.as_ref() {
                Term::Sigma(lam, _) => Ok(app(
                    ctx.clone(),
                    lam.clone(),
                    Rc::new(Term::Fst(t.clone(), Mod::Precise)),
                )?),
                _ => Err(ErrorCause::Hole)?,
            }
        }
        Term::App(t0, t1, _) => {
            let res = infer_type(ctx.clone(), t0)?;
            match res.as_ref() {
                Term::Pi(lam, _) => Ok(app(ctx.clone(), lam.clone(), t1.clone())?),
                _ => Err(ErrorCause::Hole)?,
            }
        }
        Term::Split(_, t, _, _) => Ok(t.clone()),
        Term::AppFormula(t, phi, _) => {
            let res = infer_type(ctx.clone(), t)?;
            match res.as_ref() {
                Term::PathP(a, _, _, _) => app_formula(ctx, a.clone(), phi.clone()),
                _ => Err(ErrorCause::Hole)?,
            }
        }
        Term::Comp(a, _, _, _) => app_formula(ctx.clone(), a.clone(), Formula::Dir(Dir::One)),
        Term::UnGlueElemU(_, b, _, _) => Ok(b.clone()),
        Term::IdJ(_, _, c, _, x, p, _) => app(
            ctx.clone(),
            app(ctx.clone(), c.clone(), x.clone())?,
            p.clone(),
        ),
        _ => panic!("NOT VALUE {:?}", v),
    }
}
