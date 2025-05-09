use std::{collections::HashMap, iter, rc::Rc};

use crate::{
    ctt::term::{anon_id, Dir, Face, Formula, Identifier, Label, System},
    precise::term::{Mod, Term},
    typechecker::{
        context::TypeContext,
        error::{ErrorCause, TypeError},
        infer::{const_path, infer},
    },
    utils::intersect,
};

use super::{
    app::{app, app_formula},
    eval::{equiv_contr, equiv_dom, equiv_fun, eval, eval_system, get_first, get_second, pcon},
    glue::{glue_elem, unglue, unglue_u},
    nominal::{conj, disj, sym, Facing},
};

pub fn fill_line(
    ctx: &TypeContext,
    a: &Rc<Term>,
    u: &Rc<Term>,
    ts: &System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let i = ctx.fresh();
    let ctx = ctx.with_formula(&i, Formula::Atom(i.clone()));

    let new_system = ts
        .iter()
        .map(|(f, v)| Ok((f.clone(), app_formula(&ctx, &v, Formula::Atom(i.clone()))?)))
        .collect::<Result<_, TypeError>>()?;
    Ok(Term::plam(
        i.clone(),
        &fill(
            &ctx.with_formula(&i, Formula::Atom(i.clone())),
            &i,
            &app_formula(&ctx, a, Formula::Atom(i.clone()))?,
            u,
            new_system,
        )?,
        Mod::Precise,
    ))
}

pub fn fill(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    u: &Rc<Term>,
    ts: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let j = ctx.fresh();
    let ctx = ctx.with_formula(&j, Formula::Atom(j.clone()));
    comp(
        &ctx,
        &j,
        &conj(&ctx, a, i, &j)?,
        u,
        &conj(&ctx, &ts, i, &j)?.insert(Face::cond(i, Dir::Zero), u.clone()),
    )
}

pub fn comp_line(
    ctx: &TypeContext,
    a: &Rc<Term>,
    u: &Rc<Term>,
    ts: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let i = ctx.fresh();

    let ctx = ctx.with_formula(&i, Formula::Atom(i));
    let new_system = ts
        .iter()
        .map(|(f, v)| Ok((f.clone(), app_formula(&ctx, v, Formula::Atom(i.clone()))?)))
        .collect::<Result<_, TypeError>>()?;
    comp(
        &ctx,
        &i,
        &app_formula(&ctx, &a, Formula::Atom(i.clone()))?,
        &u,
        &new_system,
    )
}

pub fn hcomp(
    ctx: &TypeContext,
    a: &Rc<Term>,
    u: &Rc<Term>,
    us: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    if let Some(result) = us.get(&Face::eps()) {
        app_formula(ctx, result, Formula::Dir(Dir::One))
    } else {
        Ok(Term::hcomp(a, u, us, Mod::Precise))
    }
}

fn trans_fill(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    u: &Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    fill(ctx, i, a, u, System::empty())
}

pub fn trans_fill_neg(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    u: &Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    sym(ctx, &trans_fill(ctx, i, &sym(ctx, a, i)?, u)?, i)
}

fn trans(
    ctx: &TypeContext,
    i: &Identifier,
    v0: &Rc<Term>,
    v1: &Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    comp(ctx, i, v0, v1, &System::empty())
}

pub fn trans_neg(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    u: &Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    trans(ctx, i, &sym(ctx, a, i)?, u)
}

fn trans_neg_line(ctx: &TypeContext, u: &Rc<Term>, v: &Rc<Term>) -> Result<Rc<Term>, TypeError> {
    let i = ctx.fresh();
    trans_neg(ctx, &i, &app_formula(ctx, u, Formula::Atom(i.clone()))?, v)
}

pub fn comp(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    u: &Rc<Term>,
    ts: &System<Term>,
) -> Result<Rc<Term>, TypeError> {
    if let Some(t) = ts.get(&Face::eps()) {
        return t.face(ctx, &Face::cond(i, Dir::One));
    }
    match a.as_ref() {
        Term::PathP(p, v0, v1, _) => {
            let j = ctx.fresh();
            let ctx = ctx.with_formula(&j, Formula::Atom(j));
            let system = ts
                .iter()
                .map(|(k, v)| Ok((k.clone(), app_formula(&ctx, v, Formula::Atom(j.clone()))?)))
                .collect::<Result<System<_>, TypeError>>()?
                .insert(Face::cond(&j, Dir::Zero), v0.clone())
                .insert(Face::cond(&j, Dir::One), v1.clone());
            Ok(Term::plam(
                j.clone(),
                &comp(
                    &ctx,
                    i,
                    &app_formula(&ctx, p, Formula::Atom(j.clone()))?,
                    &app_formula(&ctx, u, Formula::Atom(j.clone()))?,
                    &system,
                )?,
                Mod::Precise,
            ))
        }
        Term::Id(b, v0, v1, _) => match u.as_ref() {
            Term::IdPair(r, _, _) /* TODO */ => {
                let j = ctx.fresh();
                let ctx = ctx.with_formula(&j, Formula::Atom(j));

                let system =
                    ts
                        .iter().map(|(k, v)| {
                            let Term::IdPair(z, _, _) = v.as_ref() else { Err(ErrorCause::Hole)? };
                            Ok((k.clone(), app_formula(&ctx, z, Formula::Atom(j.clone()))?))
                        })
                        .collect::<Result<System<_>, TypeError>>()?
                    .insert(Face::cond(&j, Dir::Zero), v0.clone())
                    .insert(Face::cond(&j, Dir::One), v1.clone());
                let w = Term::plam(
                    j.clone(),
                    &comp(&ctx, i, b, &app_formula(&ctx, r, Formula::Atom(j.clone()))?, &system)?,
                    Mod::Precise
                );
                let sys = ts.face(&ctx, &Face::cond(i, Dir::One))?;
                let mut system_join = HashMap::new();
                for (_, term) in sys.iter() {
                    let Term::IdPair(_, s, _) = term.as_ref() else { Err(ErrorCause::Hole)? };
                    for (f, t) in s.iter() {
                        system_join.insert(f.clone(), t.clone());
                    }
                }
                Ok(Term::id_pair(&w, System::from(system_join), Mod::Precise))
            }
            _ => {
                let system =
                    ts.iter().map(|(k, v)|
                        (k.clone(), Term::plam(i.clone(), v, Mod::Precise))).collect();
                Ok(Term::comp(&Term::plam(i.clone(), a, Mod::Precise), u, system, Mod::Precise))
            }
        },
        Term::Sigma(f, _) => {
            let Term::Lam(_, a, _, _) = f.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let t1s = ts.iter().map(|(k, v)| (k.clone(), get_first(v))).collect();
            let t2s = ts.iter().map(|(k, v)| (k.clone(), get_second(v))).collect();
            let u1 = get_first(u);
            let u2 = get_second(u);
            let ui1 = comp(ctx, i, a, &u1, &t1s)?;
            let fill_u1 = fill(ctx, i, a, &u1, t1s)?;
            let comp_u2 = comp(ctx, i, &app(ctx, f, &fill_u1)?, &u2, &t2s)?;
            Ok(Term::pair(&ui1, &comp_u2, Mod::Precise))
        }
        Term::U => {
            let ts_ = ts
                .iter()
                .map(|(k, v)| (k.clone(), Term::plam(i.clone(), v, Mod::Precise)))
                .collect();
            comp_univ(ctx, u, ts_)
        }
        Term::Comp(univ, a, es, _)
            if &Term::PLam(anon_id(), Term::u(), Mod::Precise) == univ.as_ref()
                && !is_comp_neutral(ctx, i, es, u, ts)? =>
        {
            comp_u(ctx, i, a, es.clone(), u, ts.clone())
        }
        Term::Glue(b, equivs, _) if !is_comp_neutral(ctx, i, equivs, u, ts)? => {
            comp_glue(ctx, i, b, equivs.clone(), u, ts.clone())
        }
        Term::Sum(_, labels, _) => match u.as_ref() {
            Term::Con(n, ns, _) => {
                let label = labels.iter().find(|x| &x.name() == n).unwrap();

                let tele = label.telescope();

                let mut new_ctx = ctx.clone();

                let mut vs = vec![];

                for ind in 0..ns.len() {
                    let system = ts
                        .iter()
                        .map(|(k, v)| {
                            let Term::Con(_, fields, _) = v.as_ref() else {
                                Err(ErrorCause::Hole)?
                            };
                            Ok((k.clone(), fields[ind].clone()))
                        })
                        .collect::<Result<System<_>, TypeError>>()?;
                    let (name, tpe) = &tele.variables[ind];
                    let et = eval(&new_ctx, tpe)?;
                    let v = fill(&new_ctx, i, &et, &ns[ind], system.clone())?;
                    let vi1 = comp(&new_ctx, &i, &et, &ns[ind], &system)?;
                    // TODO remove infer
                    new_ctx = new_ctx.with_term(name, &v, &infer(&new_ctx, &v)?);
                    vs.push(vi1);
                }
                Ok(Term::con(n.clone(), vs, Mod::Precise))
            }
            _ => {
                let system = ts
                    .iter()
                    .map(|(k, v)| (k.clone(), Term::plam(i.clone(), v, Mod::Precise)))
                    .collect();
                Ok(Term::comp(
                    &Term::plam(i.clone(), a, Mod::Precise),
                    u,
                    system,
                    Mod::Precise,
                ))
            }
        },
        Term::HSum(_, _, _) if !u.is_neutral() && !is_system_neutral(ts) => {
            comp_hit(ctx, i, a, u, ts.clone())
        }
        _ => {
            let system = ts
                .iter()
                .map(|(k, v)| (k.clone(), Term::plam(i.clone(), v, Mod::Precise)))
                .collect();
            Ok(Term::comp(
                &Term::plam(i.clone(), a, Mod::Precise),
                u,
                system,
                Mod::Precise,
            ))
        }
    }
}

fn is_comp_neutral(
    ctx: &TypeContext,
    i: &Identifier,
    equivs: &System<Term>,
    u0: &Rc<Term>,
    ts: &System<Term>,
) -> Result<bool, TypeError> {
    let equivsi0 = equivs.face(ctx, &Face::cond(i, Dir::One))?;
    Ok((!equivsi0.contains(&Face::eps()) && u0.is_neutral())
        || ts
            .iter()
            .fold(Ok::<bool, TypeError>(false), |acc, (alpha, t_alpha)| {
                Ok(acc? || {
                    let eq_face = equivs.face(ctx, alpha)?;
                    Ok::<bool, TypeError>(!eq_face.contains(&Face::eps()) && t_alpha.is_neutral())
                }?)
            })?)
}

fn is_system_neutral(s: &System<Term>) -> bool {
    s.values().any(|x| x.is_neutral())
}

fn comp_u(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    eqs: System<Term>,
    wi0: &Rc<Term>,
    ws: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let ai1 = a.face(&ctx, &Face::cond(i, Dir::One))?;

    let vs = ws
        .iter()
        .map(|(alpha, w_alpha)| {
            let a_face = a.face(&ctx, alpha)?;
            let eqs_face = eqs.face(&ctx, alpha)?;
            Ok((
                alpha.clone(),
                unglue_u(&ctx, w_alpha, &a_face, eqs_face, Mod::Precise)?,
            ))
        })
        .collect::<Result<System<_>, TypeError>>()?;

    let vsi1 = vs.face(ctx, &Face::cond(i, Dir::One))?;
    let vi0 = unglue_u(
        ctx,
        wi0,
        &a.face(&ctx, &Face::cond(i, Dir::Zero))?,
        eqs.face(ctx, &Face::cond(i, Dir::Zero))?,
        Mod::Precise,
    )?;

    let vi1_prime = comp(ctx, i, a, &vi0, &vs)?;
    let eqs_i1 = eqs.face(ctx, &Face::cond(i, Dir::One))?;
    let eqs_prime = eqs
        .iter()
        .filter(|(alpha, _)| !alpha.binds.contains_key(i))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect::<System<_>>();

    let us_prime = eqs_prime
        .iter()
        .map(|(gamma, eq_g)| {
            let wi0_face = wi0.face(ctx, gamma)?;
            let ws_face = ws.face(ctx, gamma)?;
            Ok((
                gamma.clone(),
                fill(
                    ctx,
                    i,
                    &app_formula(ctx, eq_g, Formula::Dir(Dir::One))?,
                    &wi0_face,
                    ws_face,
                )?,
            ))
        })
        .collect::<Result<System<_>, TypeError>>()?;

    let usi1_prime = eqs_prime
        .iter()
        .map(|(gamma, eq_g)| {
            let wi0_face = wi0.face(ctx, gamma)?;
            let ws_face = ws.face(ctx, gamma)?;
            Ok((
                gamma.clone(),
                comp(ctx, i, &equiv_dom(eq_g), &wi0_face, &ws_face)?,
            ))
        })
        .collect::<Result<_, TypeError>>()?;

    let ls_prime = eqs_prime
        .iter()
        .map(|(gamma, eq_g)| {
            let a_face = a.face(ctx, gamma)?;
            let vi0_face = vi0.face(ctx, gamma)?;
            let vs_face = vs.face(ctx, gamma)?;
            Ok((
                gamma.clone(),
                path_comp(
                    ctx,
                    i,
                    &a_face,
                    &vi0_face,
                    &eq_fun(ctx, eq_g, &us_prime[gamma])?,
                    vs_face,
                )?,
            ))
        })
        .collect::<Result<_, TypeError>>()?;

    let fibersys = System::<Term>::intersect(&usi1_prime, &ls_prime).collect::<HashMap<_, _>>();

    let wsi1 = ws.face(ctx, &Face::cond(i, Dir::One))?;
    let fibersys_prime = eqs_i1
        .iter()
        .map(|(gamma, eq_g)| {
            let mut fibs_gamma =
                System::intersect(&wsi1.face(ctx, gamma)?, &vsi1.face(ctx, gamma)?)
                    .into_iter()
                    .map(|(k, (w_val, v_val))| (k.clone(), (w_val.clone(), const_path(v_val))))
                    .collect::<HashMap<_, _>>();

            let united = {
                let mut system1 = System::empty();
                let mut system2 = System::empty();
                for (k, (v1, v2)) in &fibersys {
                    system1 = system1.insert((*k).clone(), (*v1).clone());
                    system2 = system2.insert((*k).clone(), (*v2).clone());
                }
                let sys1_face = system1.face(ctx, gamma)?;
                let sys2_face = system2.face(ctx, gamma)?;

                for (k, _) in sys1_face.iter() {
                    fibs_gamma.insert(k.clone(), (sys1_face[k].clone(), sys2_face[k].clone()));
                }
                fibs_gamma
            };

            Ok((
                gamma.clone(),
                lem_eq(ctx, eq_g, &vi1_prime.face(ctx, gamma)?, united)?,
            ))
        })
        .collect::<Result<HashMap<_, _>, TypeError>>()?;

    let vi1 = {
        let united = iter::chain(
            fibersys_prime
                .iter()
                .map(|(k, path)| (k.clone(), path.1.clone())),
            vsi1.iter().map(|(k, v)| (k.clone(), const_path(&v))),
        )
        .collect();

        comp_const_line(ctx, &ai1, &vi1_prime, united)?
    };

    let usi1 = fibersys_prime
        .iter()
        .map(|(k, v)| (k.clone(), v.1.clone()))
        .collect();

    Ok(glue_elem(&vi1, usi1, Mod::Precise))
}

fn comp_neg(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    u: &Rc<Term>,
    ts: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    comp(ctx, i, &sym(ctx, a, i)?, u, &sym(ctx, &ts, i)?)
}

fn lem_eq(
    ctx: &TypeContext,
    eq: &Rc<Term>,
    b: &Rc<Term>,
    aps: HashMap<Face, (Rc<Term>, Rc<Term>)>,
) -> Result<(Rc<Term>, Rc<Term>), TypeError> {
    let i = ctx.fresh();
    let j = ctx.fresh();
    let ta = app_formula(ctx, eq, Formula::Dir(Dir::One))?;
    let p1s = aps
        .iter()
        .map(|(alpha, (aa, pa))| {
            let eqaj = app_formula(ctx, &eq.face(ctx, alpha)?, Formula::Atom(j))?;
            let ba = b.face(ctx, alpha)?;
            let c = comp(
                ctx,
                &j,
                &eqaj,
                &app_formula(ctx, pa, Formula::Atom(i))?,
                &System::empty()
                    .insert(Face::cond(&i, Dir::Zero), trans_fill(ctx, &j, &eqaj, &ba)?)
                    .insert(
                        Face::cond(&i, Dir::One),
                        trans_fill_neg(ctx, &j, &eqaj, aa)?,
                    ),
            )?;
            Ok((alpha.clone(), c))
        })
        .collect::<Result<_, TypeError>>()?;

    let thetas = aps
        .iter()
        .map(|(alpha, (aa, pa))| {
            let eqaj = app_formula(ctx, &eq.face(ctx, alpha)?, Formula::Atom(j))?;
            let ba = b.face(ctx, alpha)?;
            let c = fill(
                ctx,
                &j,
                &eqaj,
                &app_formula(ctx, &pa, Formula::Atom(i))?,
                System::empty()
                    .insert(Face::cond(&i, Dir::Zero), trans_fill(ctx, &j, &eqaj, &ba)?)
                    .insert(
                        Face::cond(&i, Dir::One),
                        trans_fill_neg(ctx, &j, &eqaj, aa)?,
                    ),
            )?;
            Ok((alpha.clone(), c))
        })
        .collect::<Result<System<_>, TypeError>>()?;
    let a = comp(
        ctx,
        &i,
        &ta,
        &trans(ctx, &i, &app_formula(ctx, eq, Formula::Atom(i))?, b)?,
        &p1s,
    )?;
    let p1 = fill(
        ctx,
        &i,
        &ta,
        &trans(ctx, &i, &app_formula(ctx, eq, Formula::Atom(i))?, b)?,
        p1s,
    )?;
    let thetas_ = thetas
        .insert(
            Face::cond(&i, Dir::Zero),
            trans_fill(ctx, &j, &app_formula(ctx, eq, Formula::Atom(j))?, b)?,
        )
        .insert(
            Face::cond(&i, Dir::One),
            trans_fill_neg(ctx, &j, &app_formula(ctx, eq, Formula::Atom(j))?, &a)?,
        );
    Ok((
        a,
        Term::plam(
            i,
            &comp_neg(
                ctx,
                &j,
                &app_formula(ctx, eq, Formula::Atom(j))?,
                &p1,
                thetas_,
            )?,
            Mod::Precise,
        ),
    ))
}

fn comp_glue(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    eqs: System<Term>,
    wi0: &Rc<Term>,
    ws: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let ai1 = a.face(ctx, &Face::cond(i, Dir::One))?;

    let vs = ws
        .iter()
        .map(|(alpha, w_alpha)| {
            let eqs_face = eqs.face(ctx, alpha)?;
            Ok((alpha.clone(), unglue(ctx, w_alpha, eqs_face)?))
        })
        .collect::<Result<System<_>, TypeError>>()?;

    let vsi1 = vs.face(ctx, &Face::cond(i, Dir::One))?;
    let vi0 = unglue(ctx, &wi0, eqs.face(ctx, &Face::cond(i, Dir::Zero))?)?;

    let vi1_prime = comp(ctx, i, &a, &vi0, &vs)?;

    let eqs_i1 = eqs.face(ctx, &Face::cond(i, Dir::One))?;
    let eqs_prime = eqs
        .iter()
        .filter(|(alpha, _)| !alpha.binds.contains_key(i))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect::<System<_>>();

    let us_prime = eqs_prime
        .iter()
        .map(|(gamma, eq_g)| {
            let wi0_face = wi0.face(ctx, gamma)?;
            let ws_face = ws.face(ctx, gamma)?;
            Ok((
                gamma.clone(),
                fill(ctx, i, &equiv_dom(eq_g), &wi0_face, ws_face)?,
            ))
        })
        .collect::<Result<System<_>, TypeError>>()?;

    let usi1_prime = eqs_prime
        .iter()
        .map(|(gamma, eq_g)| {
            let wi0_face = wi0.face(ctx, gamma)?;
            let ws_face = ws.face(ctx, gamma)?;
            Ok((
                gamma.clone(),
                comp(ctx, i, &equiv_dom(eq_g), &wi0_face, &ws_face)?,
            ))
        })
        .collect::<Result<System<_>, TypeError>>()?;

    let ls_prime = eqs_prime
        .iter()
        .map(|(gamma, eq_g)| {
            let a_face = a.face(ctx, gamma)?;
            let vi0_face = vi0.face(ctx, gamma)?;
            let us_gamma = &us_prime[gamma];
            let vs_face = vs.face(ctx, gamma)?;
            Ok((
                gamma.clone(),
                path_comp(
                    ctx,
                    i,
                    &a_face,
                    &vi0_face,
                    &app(ctx, &equiv_fun(eq_g), us_gamma)?,
                    vs_face,
                )?,
            ))
        })
        .collect::<Result<_, TypeError>>()?;

    let fibersys = System::intersect(&usi1_prime, &ls_prime)
        .map(|(k, (us_val, ls_val))| (k.clone(), Term::pair(us_val, ls_val, Mod::Precise)))
        .collect::<System<_>>();

    let wsi1 = ws.face(ctx, &Face::cond(i, Dir::One))?;
    let fibersys_prime = eqs_i1
        .iter()
        .map(|(gamma, equiv_g)| {
            let fibs_gamma = iter::chain(
                System::intersect(&wsi1.face(ctx, gamma)?, &vsi1.face(ctx, gamma)?).map(
                    |(k, (w_val, v_val))| {
                        (
                            k.clone(),
                            Term::pair(w_val, &const_path(v_val), Mod::Precise),
                        )
                    },
                ),
                fibersys.face(ctx, gamma)?.into_iter(),
            )
            .collect();
            let combined = fibs_gamma;
            let fiber_type = mk_fiber_type(
                ctx,
                &ai1.face(ctx, gamma)?,
                &vi1_prime.face(ctx, gamma)?,
                equiv_g,
            )?;
            Ok((
                gamma.clone(),
                extend(
                    ctx,
                    &fiber_type,
                    &app(ctx, &equiv_contr(equiv_g), &vi1_prime.face(ctx, gamma)?)?,
                    combined,
                )?,
            ))
        })
        .collect::<Result<System<_>, TypeError>>()?;

    let united = iter::chain(
        fibersys_prime
            .iter()
            .map(|(k, v)| (k.clone(), get_second(v))),
        vsi1.iter().map(|(k, v)| (k.clone(), const_path(v))),
    )
    .collect();

    let vi1 = comp_const_line(ctx, &ai1, &vi1_prime, united)?;

    let usi1 = fibersys_prime
        .iter()
        .map(|(k, v)| (k.clone(), get_first(v)))
        .collect();

    Ok(glue_elem(&vi1, usi1, Mod::Precise))
}

fn comp_hit(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    u: &Rc<Term>,
    us: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    hcomp(
        ctx,
        &a.face(ctx, &Face::cond(i, Dir::One))?,
        &transp_hit(ctx, i, a, u)?,
        us.iter()
            .map(|(alpha, u_alpha)| {
                let v = Term::plam(
                    i.clone(),
                    &squeeze_hit(ctx, i, &a.face(ctx, alpha)?, u_alpha)?,
                    Mod::Precise,
                );
                Ok((alpha.clone(), v))
            })
            .collect::<Result<_, TypeError>>()?,
    )
}

fn squeeze_hit(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    u: &Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    let j = ctx.fresh();
    let Term::HSum(_, labels, _) = a.as_ref() else {
        Err(ErrorCause::Hole)?
    };
    match u.as_ref() {
        Term::Con(n, us, m) => {
            let label = labels.iter().find(|l| &l.name() == n).unwrap();
            let tele = label.telescope();
            Ok(Term::con(
                n.clone(),
                squeezes(i, &tele.variables, ctx, us)?,
                m.clone(),
            ))
        }
        Term::PCon(c, _, ws0, phis, m) => {
            let label = labels.iter().find(|l| &l.name() == c).unwrap();
            let tele = label.telescope();
            Ok(pcon(
                ctx,
                c,
                &a.face(ctx, &Face::cond(i, Dir::One))?,
                squeezes(i, &tele.variables, ctx, ws0)?,
                phis.clone(),
                m.clone(),
            )?)
        }
        Term::HComp(_, v, vs, _) => {
            let ai1 = a.face(ctx, &Face::cond(i, Dir::One))?;
            let squeezed = squeeze_hit(ctx, &i, a, v)?;

            let processed_system = vs
                .iter()
                .map(|(alpha, v_alpha)| match alpha.binds.get(i) {
                    None => Ok((
                        alpha.clone(),
                        Term::plam(
                            j.clone(),
                            &squeeze_hit(
                                ctx,
                                i,
                                &a.face(ctx, alpha)?,
                                &app_formula(ctx, v_alpha, Formula::Atom(j.clone()))?,
                            )?,
                            Mod::Precise,
                        ),
                    )),
                    Some(Dir::Zero) => Ok((
                        alpha.clone(),
                        Term::plam(
                            j.clone(),
                            &transp_hit(
                                ctx,
                                i,
                                &a.face(ctx, &alpha.removed(i))?,
                                &app_formula(ctx, v_alpha, Formula::Atom(j.clone()))?,
                            )?,
                            Mod::Precise,
                        ),
                    )),
                    Some(Dir::One) => Ok((alpha.clone(), v_alpha.clone())),
                })
                .collect::<Result<_, TypeError>>()?;
            hcomp(ctx, &ai1, &squeezed, processed_system)
        }
        _ => Err(ErrorCause::Hole)?,
    }
}

fn transp_hit(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    u: &Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    let j = ctx.fresh();
    let Term::HSum(name, labels, _) = a.as_ref() else {
        Err(ErrorCause::Hole)?
    };
    match u.as_ref() {
        Term::Con(n, us, m) => {
            let label = labels.iter().find(|l| &l.name() == n).unwrap();
            let tele = label.telescope();
            Ok(Term::con(
                n.clone(),
                transps(i, tele.variables, ctx, us)?,
                m.clone(),
            ))
        }
        Term::PCon(c, _, ws0, phis, m) => {
            let label = labels.iter().find(|l| &l.name() == c).unwrap();
            let tele = label.telescope();
            pcon(
                ctx,
                c,
                &a.face(ctx, &Face::cond(i, Dir::One))?,
                transps(i, tele.variables, ctx, ws0)?,
                phis.clone(),
                m.clone(),
            )
        }
        Term::HComp(_, v, vs, _) => hcomp(
            ctx,
            &a.face(ctx, &Face::cond(i, Dir::One))?,
            &transp_hit(ctx, i, a, v)?,
            vs.iter()
                .map(|(alpha, v_alpha)| {
                    let v = Term::plam(
                        j.clone(),
                        &transp_hit(
                            ctx,
                            &j,
                            &a.face(ctx, alpha)?,
                            &app_formula(ctx, v_alpha, Formula::Atom(j))?,
                        )?,
                        Mod::Precise,
                    );
                    Ok((alpha.clone(), v))
                })
                .collect::<Result<_, TypeError>>()?,
        ),
        _ => Err(ErrorCause::Hole)?,
    }
}

fn comp_univ(ctx: &TypeContext, b: &Rc<Term>, es: System<Term>) -> Result<Rc<Term>, TypeError> {
    if let Some(res) = es.get(&Face::eps()) {
        app_formula(ctx, res, Formula::Dir(Dir::One))
    } else {
        Ok(Term::comp(
            &Term::plam(anon_id(), &Term::u(), Mod::Precise),
            b,
            es,
            Mod::Precise,
        ))
    }
}

fn path_comp(
    ctx: &TypeContext,
    i: &Identifier,
    a: &Rc<Term>,
    u0: &Rc<Term>,
    u: &Rc<Term>,
    us: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let j = ctx.fresh();
    let us_ = us.insert(Face::cond(&j, Dir::One), u.clone());
    Ok(Term::plam(
        j.clone(),
        &comp(ctx, i, a, u0, &us_)?,
        Mod::Precise,
    ))
}

fn transps(
    i: &Identifier,
    telescope: Vec<(Identifier, Rc<Term>)>,
    ctx: &TypeContext,
    us: &Vec<Rc<Term>>,
) -> Result<Vec<Rc<Term>>, TypeError> {
    let mut vs = vec![];
    let mut new_ctx = ctx.clone();
    for ((x, a), u) in telescope.iter().zip(us) {
        let t = eval(&new_ctx, a)?;
        let v = trans_fill(&new_ctx, i, &t, u)?;
        let vi1 = trans(&new_ctx, i, &t, u)?;
        new_ctx = new_ctx.with_term(x, &v, &t);
        vs.push(vi1);
    }

    Ok(vs)
}

fn squeezes(
    i: &Identifier,
    xas: &[(Identifier, Rc<Term>)],
    ctx: &TypeContext,
    us: &[Rc<Term>],
) -> Result<Vec<Rc<Term>>, TypeError> {
    let j = ctx.fresh();

    let mut ctx = ctx.clone();
    let mut vs = vec![];

    for ((x, a), u) in xas.iter().zip(us) {
        let ts = System::from(HashMap::from([(
            Face::cond(i, Dir::One),
            u.face(&ctx, &Face::cond(i, Dir::One))?,
        )]));
        let va = disj(&ctx, &eval(&ctx, a)?, i, &j)?;
        let v = disj(&ctx, &fill(&ctx, &j, &va, u, ts.clone())?, i, &j)?;
        let vi1 = disj(&ctx, &comp(&ctx, &j, &va, u, &ts)?, i, &j)?;
        ctx = ctx.with_term(x, &v, &va);
        vs.push(vi1);
    }
    Ok(vs)
}

fn extend(
    ctx: &TypeContext,
    b: &Rc<Term>,
    q: &Rc<Term>,
    ts: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let i = ctx.fresh();
    let ts_ = ts
        .iter()
        .map(|(alpha, t_alpha)| {
            Ok((
                alpha.clone(),
                app_formula(
                    ctx,
                    &app(ctx, &get_second(q).face(ctx, alpha)?, t_alpha)?,
                    Formula::Atom(i),
                )?,
            ))
        })
        .collect::<Result<_, TypeError>>()?;
    comp(ctx, &i, b, &get_first(q), &ts_)
}

fn mk_fiber_type(
    ctx: &TypeContext,
    a: &Rc<Term>,
    x: &Rc<Term>,
    equiv: &Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    let a_lit = ctx.fresh();
    let x_lit = ctx.fresh();
    let y_lit = ctx.fresh();
    let f_lit = ctx.fresh();
    let t_lit = ctx.fresh();

    let ta = Term::var(a_lit, Mod::Precise);
    let tx = Term::var(x_lit, Mod::Precise);
    let ty = Term::var(y_lit, Mod::Precise);
    let tf = Term::var(f_lit, Mod::Precise);
    let tt = Term::var(t_lit, Mod::Precise);
    let ctx = ctx
        .with_term(&a_lit, &a, &Term::hole())
        .with_term(&x_lit, &x, &Term::hole())
        .with_term(&f_lit, &equiv_fun(equiv), &Term::hole())
        .with_term(&t_lit, &equiv_dom(equiv), &Term::hole());

    let res = eval(
        &ctx,
        &Term::sigma(
            &Term::lam(
                y_lit,
                &tt,
                &Term::pathp(
                    &Term::plam(anon_id(), &ta, Mod::Precise),
                    &tx,
                    &Term::app(&tf, &ty, Mod::Precise),
                    Mod::Precise,
                ),
                Mod::Precise,
            ),
            Mod::Precise,
        ),
    );
    res
}

fn comp_const_line(
    ctx: &TypeContext,
    a: &Rc<Term>,
    u: &Rc<Term>,
    ts: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    let i = ctx.fresh();
    let ts_ = ts
        .iter()
        .map(|(alpha, t_alpha)| {
            Ok((
                alpha.clone(),
                app_formula(ctx, t_alpha, Formula::Atom(i.clone()))?,
            ))
        })
        .collect::<Result<_, TypeError>>()?;
    comp(ctx, &i, a, u, &ts_)
}

pub fn eq_fun(
    ctx: &TypeContext,
    ve: &Rc<Term>,
    ve_alpha: &Rc<Term>,
) -> Result<Rc<Term>, TypeError> {
    trans_neg_line(ctx, ve, ve_alpha)
}
