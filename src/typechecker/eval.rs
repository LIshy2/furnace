use crate::ctt::term::{
    anon_id, Branch, Dir, Face, Formula, Identifier, Label, System, Telescope, Term,
};
use crate::typechecker::check::check_declaration_set;
use crate::typechecker::context::TypeContext;
use crate::typechecker::equiv::Equiv;
use crate::typechecker::error::{ErrorCause, TypeError};
use crate::typechecker::infer::{const_path, infer};
use crate::typechecker::nominal::Nominal;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub fn eval(ctx: TypeContext, term: &Term) -> Result<Rc<Term>, TypeError> {
    // println!("eval===> {:?}", term);
    // println!("{:?}", ctx);
    match term {
        Term::U => Ok(Rc::new(Term::U)),
        Term::App(fun, arg) => app(
            ctx.clone(),
            eval(ctx.clone(), fun.as_ref())?,
            eval(ctx.clone(), arg.as_ref())?,
        ),
        Term::Var(name) => {

            Ok(ctx
                .lookup_term(name)
                .ok_or(ErrorCause::UnknownTermName(name.clone()))?
                .value)
        }
        Term::Pi(lam) => {
            let Term::Lam(name, tpe, body) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let tpe = eval(ctx.clone(), tpe)?;
            let body_ctx = ctx.with_term(name, &Rc::new(Term::Var(name.clone())), &tpe);
            Ok(Rc::new(Term::Pi(Rc::new(Term::Lam(
                name.clone(),
                tpe,
                eval(body_ctx, body.as_ref())?,
            )))))
        }
        Term::Sigma(lam) => {
            let Term::Lam(name, tpe, body) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let body_ctx = ctx.with_term(name, &Rc::new(Term::Var(name.clone())), tpe);
            Ok(Rc::new(Term::Sigma(Rc::new(Term::Lam(
                name.clone(),
                eval(ctx, tpe)?,
                eval(body_ctx, body.as_ref())?,
            )))))
        }
        Term::Pair(fst, snd) => Ok(Rc::new(Term::Pair(
            eval(ctx.clone(), fst.as_ref())?,
            eval(ctx.clone(), snd.as_ref())?,
        ))),
        Term::Fst(pair) => Ok(get_first(eval(ctx, pair)?)),
        Term::Snd(pair) => Ok(get_second(eval(ctx, pair)?)),
        Term::Where(body, decls) => {
            let new_ctx = ctx.with_decl_set(decls)?;
            eval(new_ctx, body)
        }
        Term::Con(name, fields) => Ok(Rc::new(Term::Con(
            name.clone(),
            fields
                .iter()
                .map(|f| eval(ctx.clone(), f))
                .collect::<Result<_, TypeError>>()?,
        ))),
        Term::PCon(name, a, fields, intervals) => Ok(Rc::new(Term::PCon(
            name.clone(),
            eval(ctx.clone(), a)?,
            fields
                .iter()
                .map(|f| eval(ctx.clone(), f))
                .collect::<Result<_, TypeError>>()?,
            intervals
                .iter()
                .map(|f| eval_formula(ctx.clone(), f))
                .collect(),
        ))),
        Term::Lam(name, tpe, body) => {
            let tpe = eval(ctx.clone(), tpe)?;
            let lam_ctx = ctx.with_term(name, &Rc::new(Term::Var(name.clone())), &tpe);
            Ok(Rc::new(Term::Lam(
                name.clone(),
                eval(ctx.clone(), tpe.as_ref())?,
                eval(lam_ctx.clone(), body.as_ref())?,
            )))
        }
        Term::Split(name, exp, bs) => {
            let split_tpe = eval(ctx.clone(), exp)?;
            let Term::Pi(lam) = split_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Lam(_, sum_tpe, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let sum_labels = match sum_tpe.as_ref() {
                Term::Sum(_, labels) => labels,
                Term::HSum(_, labels) => labels,
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
                                    &Rc::new(Term::Var(name.clone())),
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
                                    &Rc::new(Term::Var(name.clone())),
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
            )))
        }
        Term::Sum(name, labels) => {
            let labels = labels
                .into_iter()
                .map(|l| match l {
                    Label::OLabel(name, tele) => {
                        let mut new_variables = vec![];
                        let mut ctx = ctx.clone();
                        for (i, t) in &tele.variables {
                            let tpe = eval(ctx.clone(), t.as_ref())?;
                            new_variables.push((i.clone(), tpe.clone()));
                            ctx = ctx.with_term(&i, &Rc::new(Term::Var(i.clone())), &tpe);
                        }
                        Ok(Label::OLabel(
                            name.clone(),
                            Telescope {
                                variables: new_variables,
                            },
                        ))
                    }
                    Label::PLabel(name, tele, ids, sys) => {
                        let mut new_variables = vec![];
                        let mut ctx = ctx.clone();
                        for (i, t) in &tele.variables {
                            let tpe = eval(ctx.clone(), t.as_ref())?;
                            new_variables.push((i.clone(), tpe.clone()));
                            ctx = ctx.with_term(&i, &Rc::new(Term::Var(i.clone())), &tpe);
                        }
                        Ok(Label::PLabel(
                            name.clone(),
                            Telescope {
                                variables: new_variables,
                            },
                            ids.clone(),
                            eval_system(ctx, sys)?,
                        ))
                    }
                })
                .collect::<Result<Vec<_>, TypeError>>()?;
            Ok(Rc::new(Term::Sum(name.clone(), labels.clone())))
        }
        Term::HSum(name, labels) => Ok(Rc::new(Term::Sum(name.clone(), labels.clone()))),
        Term::Undef(tpe) => Ok(Rc::new(Term::Undef(tpe.clone()))),
        Term::Hole => Ok(Rc::new(Term::Hole)),
        Term::PathP(a, e0, e1) => Ok(Rc::new(Term::PathP(
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), e0)?,
            eval(ctx, e1)?,
        ))),
        Term::PLam(i, t) => {
            let plam_ctx = ctx.with_formula(i, Formula::Atom(i.clone()));
            Ok(Rc::new(Term::PLam(i.clone(), eval(plam_ctx.clone(), t)?)))
        }
        Term::AppFormula(e, phi) => app_formula(
            ctx.clone(),
            eval(ctx.clone(), e)?,
            eval_formula(ctx.clone(), phi),
        ),
        Term::Comp(a, t0, ts) => comp_line(
            ctx.clone(),
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), t0)?,
            eval_system(ctx, ts)?,
        ),
        Term::HComp(a, t0, ts) => hcomp(
            ctx.clone(),
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), t0)?,
            eval_system(ctx.clone(), ts)?,
        ),
        Term::Fill(a, t0, ts) => fill_line(
            ctx.clone(),
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), t0)?,
            eval_system(ctx.clone(), ts)?,
        ),
        Term::Glue(a, ts) => Ok(glue(eval(ctx.clone(), a)?, eval_system(ctx.clone(), ts)?)),
        Term::GlueElem(a, ts) => Ok(glue_elem(
            eval(ctx.clone(), a)?,
            eval_system(ctx.clone(), ts)?,
        )),
        Term::UnGlueElem(a, ts) => unglue_elem(
            ctx.clone(),
            eval(ctx.clone(), a)?,
            eval_system(ctx.clone(), ts)?,
        ),
        Term::Id(a, r, c) => Ok(Rc::new(Term::Id(
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), r)?,
            eval(ctx.clone(), c)?,
        ))),
        Term::IdPair(b, ts) => Ok(Rc::new(Term::IdPair(
            eval(ctx.clone(), b)?,
            eval_system(ctx.clone(), ts)?,
        ))),
        Term::IdJ(a, t, c, d, x, p) => idj(
            ctx.clone(),
            eval(ctx.clone(), a)?,
            eval(ctx.clone(), t)?,
            eval(ctx.clone(), c)?,
            eval(ctx.clone(), d)?,
            eval(ctx.clone(), x)?,
            eval(ctx.clone(), p)?,
        ),
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
    match p.as_ref() {
        Term::IdPair(w, ws) => {
            let i = ctx.fresh();
            let j = ctx.fresh();
            let ww = Rc::new(Term::IdPair(
                Rc::new(Term::PLam(
                    j.clone(),
                    app_formula(
                        ctx.clone(),
                        w.clone(),
                        Formula::And(
                            Box::new(Formula::Atom(i.clone())),
                            Box::new(Formula::Atom(j)),
                        ),
                    )?,
                )),
                ws.insert(Face::cond(&i, Dir::Zero), v),
            ));
            comp(
                ctx.clone(),
                &i,
                app(
                    ctx.clone(),
                    app(
                        ctx.clone(),
                        c,
                        app_formula(ctx, w.clone(), Formula::Atom(i.clone()))?,
                    )?,
                    ww,
                )?,
                d.clone(),
                &border(d, &shape(&ws)),
            )
        }
        _ => Ok(Rc::new(Term::IdJ(a, v, c, d, x, p))),
    }
}

pub fn border<A, B>(value: Rc<A>, shape: &System<B>) -> System<A> {
    System {
        binds: shape
            .binds
            .iter()
            .map(|(f, b)| (f.clone(), value.clone()))
            .collect(),
    }
}

fn shape<A>(system: &System<A>) -> System<()> {
    todo!()
}

pub fn glue(v: Rc<Term>, system: System<Term>) -> Rc<Term> {
    if let Some(result) = system.binds.get(&Face::eps()) {
        equiv_dom(result.clone())
    } else {
        Rc::new(Term::Glue(v, system))
    }
}

pub fn glue_elem(v: Rc<Term>, system: System<Term>) -> Rc<Term> {
    if let Some(result) = system.binds.get(&Face::eps()) {
        result.clone()
    } else {
        Rc::new(Term::GlueElem(v, system))
    }
}

fn unglue_u(
    ctx: TypeContext,
    w: Rc<Term>,
    b: Rc<Term>,
    es: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    if let Some(result) = es.binds.get(&Face::eps()) {
        eq_fun(ctx, result.clone(), w)
    } else {
        match w.as_ref() {
            Term::GlueElem(v, _) => Ok(v.clone()),
            _ => Ok(Rc::new(Term::UnGlueElem(w, es))), // TODO add b
        }
    }
}

pub fn unglue_elem(
    ctx: TypeContext,
    v: Rc<Term>,
    system: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    if let Some(result) = system.binds.get(&Face::eps()) {
        app(ctx, equiv_fun(result.clone()), v)
    } else {
        match v.as_ref() {
            Term::GlueElem(v, _) => Ok(v.clone()),
            _ => Ok(Rc::new(Term::UnGlueElem(v, system))),
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
    let res = Ok(Rc::new(Term::PLam(
        i.clone(),
        fill(
            ctx.with_formula(&i, Formula::Atom(i.clone())),
            &i,
            app_formula(ctx.clone(), a, Formula::Atom(i.clone()))?,
            u,
            new_system,
        )?,
    )));
    // println!("fill result {:?}", res);
    res
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

    // println!("EVALING COMP-{:?}({:?}, {:?}, {:?})", i, a, u, ts);

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
        app_formula(ctx, equiv_fun(result.clone()), Formula::Dir(Dir::One))
    } else {
        Ok(Rc::new(Term::HComp(a, u, us)))
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
            let i_value = ctx
                .lookup_formula(&i)
                .ok_or(ErrorCause::UnknownTermName(i.clone()))?;
            let faces = inv_formula(i_value, d);
            let mut new_betas = vec![];
            for face in faces {
                for beta in &betas {
                    new_betas.push(beta.meet(&face));
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
                if !Equiv::equiv(ctx.clone(), face_a, face_b)? {
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
        (Term::Lam(x, tpe, body), _) => {
            let new_ctx = ctx.with_term(&x, &arg, tpe);
            // println!("new sub {:?}", new_ctx);
            eval(new_ctx, body.as_ref())
        }
        (Term::Split(_, _, branches), Term::Con(c, vs)) => {
            let branch = branches
                .iter()
                .find(|b| &b.name() == c)
                .ok_or(ErrorCause::Hole)?;
            match branch {
                Branch::OBranch(_, xs, t) => {
                    let mut new_ctx = ctx.clone();
                    for (name, v) in xs.iter().zip(vs) {
                        // println!("infering brnached {:?} {:?}", name, v);
                        new_ctx = new_ctx.with_term(name, v, &infer(ctx.clone(), v)?);
                    }
                    eval(new_ctx, t)
                }
                Branch::PBranch(_, _, _, _) => Err(ErrorCause::Hole)?,
            }
        }
        (Term::Split(_, _, branches), Term::PCon(c, _, us, phis)) => {
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
        (Term::Split(_, ty, _), Term::HComp(a, w, ws)) => {
            let obj = eval(ctx.clone(), ty.as_ref())?;
            match obj.as_ref() {
                Term::Pi(lam) => {
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
        (Term::Split(_, _, _), v) if is_neutral(v) => {
            Ok(Rc::new(Term::App(fun.clone(), arg.clone())))
        }
        (Term::Comp(plam, li0, ts), _) => {
            // println!("Apping comp {:?} {:?}", plam, li0);
            let Term::PLam(i, pi) = plam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Pi(lam) = pi.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Lam(_, a, _) = lam.as_ref() else {
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
            let b = border(v.clone(), &tsj);
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
        _ if is_neutral(fun.as_ref()) => Ok(Rc::new(Term::App(fun, arg))),
        _ => {
            println!("{:?} {:?}", fun, arg);
            Err(ErrorCause::Hole)?
        }
    }
}

pub fn get_first(term: Rc<Term>) -> Rc<Term> {
    match term.as_ref() {
        Term::Pair(fst, _) => fst.clone(),
        _ => Rc::new(Term::Fst(term)),
    }
}

pub fn get_second(term: Rc<Term>) -> Rc<Term> {
    match term.as_ref() {
        Term::Pair(_, snd) => snd.clone(),
        _ => Rc::new(Term::Snd(term)),
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
        Term::PathP(p, v0, v1) => {
            let j = ctx.fresh();
            let ctx = ctx.with_formula(&j, Formula::Atom(j));
            let system = System {
                binds: ts
                    .binds
                    .iter()
                    .map(|(k, v)| Ok((k.clone(), app_formula(ctx.clone(), v.clone(), Formula::Atom(j.clone()))?)))
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
            )))
        }
        Term::Id(b, v0, v1) => match u.as_ref() {
            Term::IdPair(r, _) /* TODO */ => {
                let j = ctx.fresh();
                let ctx = ctx.with_formula(&j, Formula::Atom(j));

                let system = System {
                    binds: ts
                        .binds
                        .iter()
                        .map(|(k, v)| {
                            let Term::IdPair(z, _) = v.as_ref() else { Err(ErrorCause::Hole)? };
                            Ok((k.clone(), app_formula(ctx.clone(), z.clone(), Formula::Atom(j.clone()))?))
                        })
                        .collect::<Result<_, TypeError>>()?,
                }
                    .insert(Face::cond(&j, Dir::Zero), v0.clone())
                    .insert(Face::cond(&j, Dir::One), v1.clone());
                let w = Rc::new(Term::PLam(
                    j.clone(),
                    comp(ctx.clone(), i, b.clone(), app_formula(ctx.clone(), r.clone(), Formula::Atom(j.clone()))?, &system)?,
                ));
                let sys = ts.clone().face(ctx, &Face::cond(i, Dir::One))?;
                let mut system_join = HashMap::new();
                for (_, term) in sys.binds {
                    let Term::IdPair(_, s) = term.as_ref() else { Err(ErrorCause::Hole)? };
                    for (f, t) in s.binds.iter() {
                        system_join.insert(f.clone(), t.clone());
                    }
                }
                Ok(Rc::new(Term::IdPair(w, System {
                    binds: system_join
                })))
            }
            _ => {
                let system = System {
                    binds: ts.binds.iter().map(|(k, v)|
                        (k.clone(), Rc::new(Term::PLam(i.clone(), v.clone())))).collect()
                };
                Ok(Rc::new(Term::Comp(Rc::new(Term::PLam(i.clone(), a)), u, system)))
            }
        },
        Term::Sigma(f) => {
            let Term::Lam(_, a, _) = f.as_ref() else { Err(ErrorCause::Hole)? };
            let t1s = System {
                binds: ts
                    .binds
                    .iter()
                    .map(|(k, v)| (k.clone(), get_first(v.clone())))
                    .collect()
            };
            let t2s = System {
                binds: ts
                    .binds
                    .iter()
                    .map(|(k, v)| (k.clone(), get_second(v.clone())))
                    .collect()
            };
            let u1 = get_first(u.clone());
            let u2 = get_second(u);
            let ui1 = comp(ctx.clone(), i, a.clone(), u1.clone(), &t1s)?;
            let fill_u1 = fill(ctx.clone(), i, a.clone(), u1.clone(), t1s)?;
            let comp_u2 = comp(ctx.clone(), i, app(ctx.clone(), f.clone(), fill_u1)?, u2, &t2s)?;
            Ok(Rc::new(Term::Pair(ui1, comp_u2)))
        }
        Term::U => {
            let ts_ = System {
                binds: ts.binds.iter().map(|(k, v)| {
                    (k.clone(), Rc::new(Term::PLam(i.clone(), v.clone())))
                }).collect(),
            };
            comp_univ(ctx, u, ts_)
        }
        Term::Comp(univ, a, es) if &Term::U == univ.as_ref() => {
            comp_u(ctx, i, a.clone(), es.clone(), u, ts.clone())
        }
        Term::Glue(b, equivs) /* TODO */ => {
            comp_glue(ctx, i, b.clone(), equivs.clone(), u, ts.clone())
        }
        Term::Sum(_, labels) => {
            match u.as_ref() {
                Term::Con(n, ns) => {
                    let label = labels.iter().find(|x| &x.name() == n).unwrap();

                    let tele = label.telescope();

                    let mut new_ctx = ctx;

                    let mut vs = vec![];

                    for ind in 0..ns.len() {
                        let system =
                            System {
                                binds: ts.binds.iter().map(|(k, v)| {
                                    let Term::Con(_, fields) = v.as_ref() else { Err(ErrorCause::Hole)? };
                                    Ok((k.clone(), fields[ind].clone()))
                                }).collect::<Result<_, TypeError>>()?
                            };
                        let (name, tpe) = &tele.variables[ind];
                        let et = eval(new_ctx.clone(), tpe)?;
                        let v = fill(new_ctx.clone(), i, et.clone(), ns[ind].clone(), system.clone())?;
                        let vi1 = comp(new_ctx.clone(), &i, et, ns[ind].clone(), &system)?;
                        new_ctx = new_ctx.with_term(name, &v, &infer(new_ctx.clone(), v.as_ref())?);
                        vs.push(vi1);
                    }
                    Ok(Rc::new(Term::Con(n.clone(), vs)))
                }
                _ => {
                    let system = System {
                        binds: ts.binds.iter().map(|(k, v)| (k.clone(), Rc::new(Term::PLam(i.clone(), v.clone())))).collect()
                    };
                    Ok(Rc::new(Term::Comp(Rc::new(Term::PLam(i.clone(), a)), u, system)))
                }
            }
        }
        Term::HSum(_, _) => comp_hit(ctx, i, a, u, ts.clone()),
        _ => {
            let system = System {
                binds: ts.binds.iter().map(|(k, v)| (k.clone(), Rc::new(Term::PLam(i.clone(), v.clone())))).collect()
            };
            Ok(Rc::new(Term::Comp(Rc::new(Term::PLam(i.clone(), a)), u, system)))
        }
    }
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
                    unglue_u(ctx.clone(), w_alpha.clone(), a_face, eqs_face)?,
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

    let fibersys = (usi1_prime, ls_prime);

    let wsi1 = ws.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?;
    let fibersys_prime = System {
        binds: eqs_i1
            .binds
            .iter()
            .map(|(gamma, eq_g)| {
                let mut fibs_gamma = (
                    wsi1.clone().face(ctx.clone(), gamma)?,
                    System {
                        binds: vsi1
                            .clone()
                            .face(ctx.clone(), gamma)?
                            .binds
                            .iter()
                            .map(|(k, v_val)| (k.clone(), const_path(v_val.clone())))
                            .collect(),
                    },
                );
                fibs_gamma
                    .0
                    .binds
                    .extend(fibersys.0.clone().face(ctx.clone(), gamma)?.binds);
                fibs_gamma
                    .1
                    .binds
                    .extend(fibersys.1.clone().face(ctx.clone(), gamma)?.binds);
                let combined = fibs_gamma;
                Ok((
                    gamma.clone(),
                    lem_eq(
                        eq_g.clone(),
                        vi1_prime.clone().face(ctx.clone(), gamma)?,
                        combined,
                    ),
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let mut united = System {
        binds: fibersys_prime
            .binds
            .iter()
            .map(|(k, path)| (k.clone(), path.clone()))
            .collect(),
    };
    united.binds.extend(
        vsi1.binds
            .iter()
            .map(|(k, v)| (k.clone(), const_path(v.clone()))),
    );

    let vi1 = comp_const_line(ctx.clone(), ai1, vi1_prime, united)?;

    Ok(glue_elem(
        vi1,
        System {
            binds: fibersys_prime
                .binds
                .into_iter()
                .map(|(k, x)| (k, x))
                .collect(),
        },
    ))
}

fn lem_eq(eq: Rc<Term>, b: Rc<Term>, aps: (System<Term>, System<Term>)) -> Rc<Term> {
    todo!()
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
                let a_face = a.clone().face(ctx.clone(), alpha)?;
                let eqs_face = eqs.clone().face(ctx.clone(), alpha)?;
                Ok((
                    alpha.clone(),
                    unglue_u(ctx.clone(), w_alpha.clone(), a_face, eqs_face)?,
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
                        equiv_fun(app(ctx.clone(), eq_g.clone(), us_gamma)?),
                        vs_face,
                    )?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let fibersys = System {
        binds: usi1_prime
            .binds
            .iter()
            .zip(ls_prime.binds.iter())
            .map(|((k, us_val), (_, ls_val))| {
                (
                    k.clone(),
                    Rc::new(Term::Pair(us_val.clone(), ls_val.clone())),
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
                    binds: wsi1
                        .clone()
                        .face(ctx.clone(), gamma)?
                        .binds
                        .iter()
                        .zip(vsi1.clone().face(ctx.clone(), gamma)?.binds.iter())
                        .map(|((k, w_val), (_, v_val))| {
                            (
                                k.clone(),
                                Rc::new(Term::Pair(w_val.clone(), const_path(v_val.clone()))),
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
                        equiv_contr(equiv_g.clone()),
                        combined,
                    )?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };

    let mut united = fibersys_prime.clone();

    united.binds.extend(
        vsi1.binds
            .iter()
            .map(|(k, v)| (k.clone(), const_path(v.clone()))),
    );

    let vi1 = comp_const_line(ctx.clone(), ai1, vi1_prime, united)?;

    Ok(glue_elem(vi1, fibersys_prime))
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
    let Term::HSum(name, labels) = a.as_ref() else {
        Err(ErrorCause::Hole)?
    };
    match u.as_ref() {
        Term::Con(n, us) => {
            let label = labels.iter().find(|l| &l.name() == name).unwrap();
            let tele = label.telescope();
            Ok(Rc::new(Term::Con(
                n.clone(),
                squeezes(i, &tele.variables, ctx, us),
            )))
        }
        Term::PCon(c, _, ws0, phis) => {
            let label = labels.iter().find(|l| &l.name() == name).unwrap();
            let tele = label.telescope();
            Ok(pcon(
                ctx.clone(),
                c,
                a.face(ctx.clone(), &Face::cond(i, Dir::One))?,
                squeezes(i, &tele.variables, ctx, ws0),
                phis.clone(),
            )?)
        }
        Term::HComp(_, v, vs) => {
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
    let Term::HSum(name, labels) = a.as_ref() else {
        Err(ErrorCause::Hole)?
    };
    match u.as_ref() {
        Term::Con(n, us) => {
            let label = labels.iter().find(|l| &l.name() == name).unwrap();
            let tele = label.telescope();
            Ok(Rc::new(Term::Con(
                n.clone(),
                transps(i, tele.variables, ctx, us)?,
            )))
        }
        Term::PCon(c, _, ws0, phis) => {
            let label = labels.iter().find(|l| &l.name() == name).unwrap();
            let tele = label.telescope();
            pcon(
                ctx.clone(),
                c,
                a.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?,
                transps(i, tele.variables, ctx, ws0)?,
                phis.clone(),
            )
        }
        Term::HComp(_, v, vs) => hcomp(
            ctx.clone(),
            a.clone().face(ctx.clone(), &Face::cond(i, Dir::One))?,
            transp_hit(ctx.clone(), i, a.clone(), u.clone())?,
            System {
                binds: vs
                    .binds
                    .iter()
                    .map(|(alpha, v_alpha)| {
                        let v = Rc::new(Term::PLam(
                            i.clone(),
                            transp_hit(
                                ctx.clone(),
                                i,
                                a.clone().face(ctx.clone(), alpha)?,
                                v_alpha.clone(),
                            )?,
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
        Ok(Rc::new(Term::Comp(Rc::new(Term::U), b.clone(), es)))
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
    Ok(Rc::new(Term::PLam(j.clone(), comp(ctx, i, a, u0, &us_)?)))
}

pub fn pcon(
    ctx: TypeContext,
    c: &Identifier,
    a: Rc<Term>,
    us: Vec<Rc<Term>>,
    phis: Vec<Formula>,
) -> Result<Rc<Term>, TypeError> {
    match a.as_ref() {
        Term::HSum(_, labels) => {
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
                Ok(Rc::new(Term::PCon(c.clone(), a, us, phis)))
            }
        }
        _ => Ok(Rc::new(Term::PCon(c.clone(), a, us, phis))),
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
    name: &Identifier,
    xas: &Vec<(Identifier, Rc<Term>)>,
    ctx: TypeContext,
    us: &Vec<Rc<Term>>,
) -> Vec<Rc<Term>> {
    todo!()
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
                    app(
                        ctx.clone(),
                        get_second(q.clone()).face(ctx.clone(), alpha)?,
                        app_formula(ctx.clone(), t_alpha.clone(), Formula::Atom(i))?,
                    )?,
                ))
            })
            .collect::<Result<_, TypeError>>()?,
    };
    comp(ctx.clone(), &i, b, get_first(q), &ts_)
}

fn mk_fiber_type(
    ctx: TypeContext,
    a: Rc<Term>,
    x: Rc<Term>,
    equiv: Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    let a_lit = ctx.fresh();
    let x_lit = ctx.fresh();
    let y_lit = ctx.fresh();
    let f_lit = ctx.fresh();
    let t_lit = ctx.fresh();

    let ta = Rc::new(Term::Var(a_lit));
    let tx = Rc::new(Term::Var(x_lit));
    let ty = Rc::new(Term::Var(y_lit));
    let tf = Rc::new(Term::Var(f_lit));
    let tt = Rc::new(Term::Var(t_lit));
    let ctx = ctx
        .with_term(&a_lit, &a, &infer(ctx.clone(), a.as_ref())?)
        .with_term(&x_lit, &x, &infer(ctx.clone(), x.as_ref())?)
        .with_term(
            &f_lit,
            &equiv_fun(equiv.clone()),
            &infer(ctx.clone(), equiv_fun(equiv.clone()).as_ref())?,
        )
        .with_term(
            &t_lit,
            &equiv_dom(equiv.clone()),
            &infer(ctx.clone(), equiv_dom(equiv).as_ref())?,
        );

    eval(
        ctx,
        &Term::Sigma(Rc::new(Term::Lam(
            y_lit,
            tt,
            Rc::new(Term::PathP(
                Rc::new(Term::PLam(anon_id(), ta)),
                tx,
                Rc::new(Term::App(tf, ty)),
            )),
        ))),
    )
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
        Term::Undef(_) => true,
        Term::Hole => true,
        Term::Var(_) => true,
        Term::Comp(_, _, _) => true,
        Term::Fst(_) => true,
        Term::Snd(_) => true,
        Term::Split(_, _, _) => true,
        Term::App(_, _) => true,
        Term::AppFormula(_, _) => true,
        Term::UnGlueElem(_, _) => true,
        Term::IdJ(_, _, _, _, _, _) => true,
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

fn sym(ctx: TypeContext, a: Rc<Term>, i: &Identifier) -> Result<Rc<Term>, TypeError> {
    a.act(ctx, i, Formula::NegAtom(i.clone()))
}

pub fn app_formula(
    ctx: TypeContext,
    term: Rc<Term>,
    formula: Formula,
) -> Result<Rc<Term>, TypeError> {
    match term.as_ref() {
        Term::PLam(i, u) => u.act(ctx.clone(), i, formula),
        Term::Hole => Ok(Rc::new(Term::AppFormula(term, formula))),
        v if is_neutral(v) => {
            let tpe = infer(ctx, v)?;
            match (tpe.as_ref(), formula) {
                (Term::PathP(_, a0, _), Formula::Dir(Dir::Zero)) => Ok(a0.clone()),
                (Term::PathP(_, _, a1), Formula::Dir(Dir::One)) => Ok(a1.clone()),
                (_, phi) => Ok(Rc::new(Term::AppFormula(term.clone(), phi))),
            }
        }
        _ => Err(ErrorCause::Hole)?,
    }
}
