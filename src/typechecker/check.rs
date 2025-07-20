use tracing::{span, trace_span, Level};

use crate::ctt::formula::{Dir, Formula};
use crate::ctt::system::System;
use crate::ctt::term::{anon_id, Branch, DeclarationSet, Label, Telescope};
use crate::ctt::Identifier;
use crate::precise::term::{Mod, Term, Value};
use crate::typechecker::canon::app::{app, app_formula};
use crate::typechecker::canon::comp::eq_fun;
use crate::typechecker::canon::eval::{equiv_dom, equiv_fun, eval, eval_system, is_comp_system};
use crate::typechecker::canon::nominal::{border, Facing, Nominal};
use crate::typechecker::context::{ProgressNotifier, TypeContext};
use crate::typechecker::equiv::Equiv;
use crate::typechecker::error::{ErrorCause, TypeError};
use crate::typechecker::infer::{const_path, infer, label_type};
use std::collections::HashSet;
use std::rc::Rc;

fn check_family(ctx: &TypeContext, f: &Rc<Term>) -> Result<(), TypeError> {
    let Term::Lam(name, tpe, body, _) = f.as_ref() else {
        Err(ErrorCause::Hole)?
    };
    check(ctx, tpe, &Value::u())?;
    let tpe = eval(ctx, tpe)?;
    let body_ctx = ctx.with_term(name, &Value::var(*name, &tpe, Mod::Precise));
    check(&body_ctx, body, &Value::u())
}

fn check_tele(ctx: &TypeContext, tele: &Telescope<Term>) -> Result<TypeContext, TypeError> {
    let mut result = ctx.clone();
    for (name, tpe) in tele.variables.iter() {
        check(&result, tpe, &Value::u())?;
        result = result.with_term(name, &Value::var(*name, &eval(&result, tpe)?, Mod::Precise));
    }
    Ok(result)
}

fn check_branch(
    ctx: &TypeContext,
    data_ctx: &TypeContext,
    label: &Label<Term>,
    branch: &Branch<Term>,
    split: &Rc<Value>,
    split_tpe: &Rc<Value>,
    tpe: &Rc<Value>,
) -> Result<(), TypeError> {
    match (label, branch) {
        (Label::OLabel(_, tele), Branch::OBranch(c, ns, body)) => {
            let mut vars = vec![];
            let mut branch_ctx = ctx.clone();
            let mut data_ctx = data_ctx.clone();
            for ((tpe_bind, tpe), bind) in tele.variables.iter().zip(ns) {
                let etpe = eval(&data_ctx, tpe)?;
                let var = Value::var(*bind, &etpe, Mod::Precise);
                branch_ctx = branch_ctx.with_term(bind, &var);
                data_ctx = data_ctx.with_term(tpe_bind, &var);
                vars.push(var);
            }
            let f_tpe = app(&branch_ctx, split_tpe, &Value::con(*c, vars, Mod::Precise))?;
            check(&branch_ctx, body, &f_tpe)
        }
        (Label::PLabel(_, tele, is, ts), Branch::PBranch(c, ns, js, body)) => {
            let mut sys_ctx = data_ctx.uncompacted();

            let mut tpe_ctx = data_ctx.clone();

            for ((name, tpe), bind) in tele.variables.iter().zip(ns) {
                let etpe = eval(&tpe_ctx, tpe)?;
                sys_ctx = sys_ctx.with_term(bind, &Value::var(*bind, &etpe, Mod::Precise));
                sys_ctx = sys_ctx.with_term(name, &Value::var(*bind, &etpe, Mod::Precise));
                tpe_ctx = tpe_ctx.with_term(name, &Value::var(*bind, &etpe, Mod::Precise));
            }
            for (i, j) in is.iter().zip(js) {
                sys_ctx = sys_ctx.with_formula(i, Formula::Atom(*j));
            }
            let vts = eval_system(&sys_ctx, ts)?;
            let vgts = System::intersect(&border(&sys_ctx, split, &vts)?, &vts)
                .map(|(k, (a, b))| Ok((k.clone(), app(&sys_ctx, a, b)?)))
                .collect::<Result<_, TypeError>>()?;
            let mut branch_ctx = ctx.uncompacted();
            let mut vars = vec![];
            let mut tpe_ctx = data_ctx.clone();
            for ((tpe_bind, tpe), bind) in tele.variables.iter().zip(ns) {
                let etpe = eval(&tpe_ctx, tpe)?;
                let var = Value::var(*bind, &etpe, Mod::Precise);
                vars.push(var.clone());
                branch_ctx = branch_ctx.with_term(bind, &var);
                tpe_ctx = tpe_ctx.with_term(tpe_bind, &var);
            }
            for j in js {
                branch_ctx = branch_ctx.with_formula(j, Formula::Atom(*j));
            }
            let b_tpe = app(
                &branch_ctx,
                split_tpe,
                &Value::pcon(
                    *c,
                    tpe,
                    vars,
                    js.iter().map(|j| Formula::Atom(*j)).collect(),
                    Mod::Precise,
                ),
            )?;

            check(&branch_ctx, body, &b_tpe)?;
            let ve = eval(&branch_ctx, body)?;
            if Equiv::equiv(&branch_ctx, &border(&branch_ctx, &ve, &vts)?, &vgts)? {
                Ok(())
            } else {
                Err(ErrorCause::UneqInHSumSplit(
                    border(&branch_ctx, &ve, &vts)?,
                    vgts,
                ))?
            }
        }
        _ => Err(ErrorCause::Hole)?,
    }
}

pub fn check_formula(ctx: &TypeContext, formula: &Formula) -> Result<(), TypeError> {
    match formula {
        Formula::Dir(_) => Ok(()),
        Formula::Atom(name) | Formula::NegAtom(name) => {
            if ctx.lookup_formula(name).is_some() {
                Ok(())
            } else {
                Err(ErrorCause::UnknownInterval)?
            }
        }
        Formula::And(lhs, rhs) | Formula::Or(lhs, rhs) => {
            check_formula(ctx, lhs).and(check_formula(ctx, rhs))
        }
    }
}
pub fn check_declaration_set(
    ctx: &TypeContext,
    set: &DeclarationSet<Term>,
) -> Result<TypeContext, TypeError> {
    match set {
        DeclarationSet::Mutual(decls) => {
            let mut new_ctx = ctx.clone();

            for decl in decls {
                new_ctx = new_ctx.with_lazy_term(&decl.name, &decl.body, &decl.tpe);
            }
            for decl in decls {
                new_ctx.decl_check_started(&decl.name);
                let tpe = eval(&new_ctx, &decl.tpe)?;
                check(&new_ctx, &decl.body, &tpe)?;
                new_ctx.decl_check_finished(&decl.name);
            }
            Ok(new_ctx)
        }
        DeclarationSet::Opaque(name) => Ok(ctx.opaque(*name)),
        DeclarationSet::Transparent(name) => Ok(ctx.transparent(*name)),
        DeclarationSet::TransparentAll => Ok(ctx.transparent_all()),
    }
}

pub fn check_plam(
    ctx: &TypeContext,
    term: &Rc<Term>,
    tpe: &Rc<Value>,
) -> Result<(Rc<Value>, Rc<Value>), TypeError> {
    match term.as_ref() {
        Term::PLam(int, body, _) => {
            let new_ctx = ctx.with_formula(int, Formula::Atom(*int));
            check(&new_ctx, body, &app_formula(ctx, tpe, Formula::Atom(*int))?)?;
            Ok((
                eval(&new_ctx.with_formula(int, Formula::Dir(Dir::Zero)), body)?,
                eval(&new_ctx.with_formula(int, Formula::Dir(Dir::One)), body)?,
            ))
        }
        _ => {
            let vt = infer(ctx, term)?;
            match vt.as_ref() {
                Value::PathP(a, a0, a1, _) => {
                    if Equiv::equiv(ctx, a, tpe)? {
                        Ok((a0.clone(), a1.clone()))
                    } else {
                        Err(ErrorCause::Hole)?
                    }
                }
                _ => Err(ErrorCause::Hole)?,
            }
        }
    }
}

fn check_comp_system(ctx: &TypeContext, sys: &System<Rc<Value>>) -> Result<(), TypeError> {
    if is_comp_system(ctx, sys)? {
        Ok(())
    } else {
        Err(ErrorCause::Hole)?
    }
}

pub fn check_plam_system(
    ctx: &TypeContext,
    t0: &Rc<Term>,
    va: &Rc<Value>,
    ps: &System<Rc<Term>>,
) -> Result<System<Rc<Value>>, TypeError> {
    let et0 = eval(&ctx, t0)?;
    let v = ps
        .iter()
        .map(|(alpha, p_alpha)| {
            let face_ctx = ctx.with_face(alpha)?;
            let (a0, a1) = check_plam(&face_ctx, p_alpha, &va.face(ctx, alpha)?)?;
            if Equiv::equiv(&ctx, &a0, &et0.face(ctx, alpha)?)? {
                Ok((alpha.clone(), a1))
            } else {
                Err(ErrorCause::Hole)?
            }
        })
        .collect::<Result<_, TypeError>>()?;
    check_comp_system(ctx, &eval_system(ctx, ps)?)?;
    Ok(v)
}

fn check_equiv(ctx: &TypeContext, term: &Rc<Term>, tpe: &Rc<Value>) -> Result<(), TypeError> {
    let eq_tpe = {
        let a_lit = Identifier(1);
        let t_lit = Identifier(2);
        let x_lit = Identifier(3);
        let f_lit = Identifier(4);
        let y_lit = Identifier(5);
        let s_lit = Identifier(6);
        let z_lit = Identifier(7);

        let new_ctx = ctx.with_term(&a_lit, tpe);
        let t = Term::var(t_lit, Mod::Precise);
        let a = Term::var(a_lit, Mod::Precise);
        let x = Term::var(x_lit, Mod::Precise);
        let f = Term::var(f_lit, Mod::Precise);
        let y = Term::var(y_lit, Mod::Precise);
        let s = Term::var(s_lit, Mod::Precise);
        let z = Term::var(z_lit, Mod::Precise);
        let fib = Term::sigma(
            &Term::lam(
                y_lit,
                &t,
                &Term::pathp(
                    &Term::plam(anon_id(), &a, Mod::Precise),
                    &x,
                    &Term::app(&f, &y, Mod::Precise),
                    Mod::Precise,
                ),
                Mod::Precise,
            ),
            Mod::Precise,
        );
        let iscontrfib = Term::sigma(
            &Term::lam(
                s_lit,
                &fib,
                &Term::pi(
                    &Term::lam(
                        z_lit,
                        &fib,
                        &Term::pathp(
                            &Term::plam(anon_id(), &fib, Mod::Precise),
                            &s,
                            &z,
                            Mod::Precise,
                        ),
                        Mod::Precise,
                    ),
                    Mod::Precise,
                ),
                Mod::Precise,
            ),
            Mod::Precise,
        );

        eval(
            &new_ctx,
            &Term::sigma(
                &Term::lam(
                    t_lit,
                    &Term::u(),
                    &Term::sigma(
                        &Term::lam(
                            f_lit,
                            &Term::pi(&Term::lam(anon_id(), &t, &a, Mod::Precise), Mod::Precise),
                            &Term::pi(
                                &Term::lam(x_lit, &a, &iscontrfib, Mod::Precise),
                                Mod::Precise,
                            ),
                            Mod::Precise,
                        ),
                        Mod::Precise,
                    ),
                    Mod::Precise,
                ),
                Mod::Precise,
            ),
        )?
    };
    check(ctx, term, &eq_tpe)
}

fn check_glue(
    ctx: &TypeContext,
    tpe: &Rc<Value>,
    system: &System<Rc<Term>>,
) -> Result<(), TypeError> {
    for (alpha, t_alpha) in system.iter() {
        check_equiv(ctx, t_alpha, &tpe.face(ctx, alpha)?)?;
    }
    check_comp_system(ctx, &eval_system(ctx, system)?)
}

fn check_glue_elem(
    ctx: &TypeContext,
    term: &Rc<Value>,
    system1: &System<Rc<Value>>,
    system2: &System<Rc<Term>>,
) -> Result<(), TypeError> {
    if system1.domain() != system2.domain() {
        Err(ErrorCause::Hole)?
    }

    for (alpha, (vt, u)) in System::intersect(system1, system2) {
        let face_ctx = ctx.with_face(alpha)?;
        check(&face_ctx, u, &equiv_dom(vt))?;
    }

    let vus = eval_system(ctx, system2)?;

    for (alpha, (vt, v_alpha)) in System::intersect(system1, &vus) {
        if !Equiv::equiv(
            ctx,
            &app(ctx, &equiv_fun(vt), v_alpha)?,
            &term.face(ctx, alpha)?,
        )? {
            Err(ErrorCause::Hole)?;
        }
    }

    check_comp_system(ctx, &vus)
}

fn check_glue_elem_u(
    ctx: &TypeContext,
    term: &Rc<Value>,
    system1: &System<Rc<Value>>,
    system2: &System<Rc<Term>>,
) -> Result<(), TypeError> {
    if system1.domain() != system2.domain() {
        Err(ErrorCause::Hole)?
    }

    for (alpha, (ve, u)) in System::intersect(system1, system2) {
        let face_ctx = ctx.with_face(alpha)?;
        check(&face_ctx, u, &app_formula(ctx, ve, Formula::Dir(Dir::One))?)?;
    }

    let vus = eval_system(ctx, system2)?;

    for (alpha, (ve, v_alpha)) in System::intersect(system1, &vus) {
        if !Equiv::equiv(ctx, &eq_fun(ctx, ve, v_alpha)?, &term.face(ctx, alpha)?)? {
            Err(ErrorCause::Hole)?;
        }
    }

    check_comp_system(ctx, &vus)
}

pub fn check(ctx: &TypeContext, term: &Rc<Term>, tpe: &Rc<Value>) -> Result<(), TypeError> {
    match (tpe.as_ref(), term.as_ref()) {
        (_, Term::Undef(_, _)) => Ok(()),
        (_, Term::Hole) => Err(ErrorCause::Hole)?,
        (_, Term::Con(c, cs, _)) => {
            let Value::Stuck(_, de, _) = tpe.as_ref() else {
                Err(ErrorCause::ExpectedDataType(tpe.clone()))?
            };
            let tele = label_type(c, tpe)?;
            let mut tpe_ctx = ctx.in_closure(de);

            for (arg, (name, tpe)) in cs.iter().zip(tele.variables) {
                let tpe = eval(&tpe_ctx, &tpe)?;
                check(&ctx, arg, &tpe)?;
                let arg_v = eval(ctx, arg)?;
                tpe_ctx = tpe_ctx.with_term(&name, &arg_v);
            }
            Ok(())
        }
        (Value::U, Term::Pi(f, _)) => check_family(ctx, f),
        (Value::U, Term::Sigma(f, _)) => check_family(ctx, f),
        (Value::U, Term::Sum(_, labels, _)) => {
            for label in labels {
                match label {
                    Label::OLabel(_, tele) => check_tele(ctx, tele).map(|_| ())?,
                    Label::PLabel(_, _, _, _) => panic!("h-label in data"),
                }
            }
            Ok(())
        }
        (Value::U, Term::HSum(_, labels, _)) => {
            let data = eval(ctx, term)?;
            for label in labels {
                match label {
                    Label::OLabel(_, tele) => {
                        check_tele(ctx, tele)?;
                    }
                    Label::PLabel(_, tele, is, ts) => {
                        let domain = ts.domain();
                        if !domain.iter().all(|name| is.contains(name)) {
                            Err(ErrorCause::UnknownNameInSystem)?
                        }
                        let tele_ctx = check_tele(ctx, tele)?;
                        let inter_ctx = is
                            .iter()
                            .fold(tele_ctx, |acc, i| acc.with_formula(i, Formula::Atom(*i)));
                        for (face, term) in ts.iter() {
                            let face_ctx = inter_ctx.with_face(face)?;
                            check(&face_ctx, term, &data)?
                        }
                    }
                }
            }
            Ok(())
        }
        (Value::Pi(va, lam, _), Term::Split(_, ty, ces, _)) => {
            let (cas, de) = match va.as_ref() {
                Value::Stuck(Term::Sum(_, cas, _), e, _) => (cas, e),
                Value::Stuck(Term::HSum(_, cas, _), e, _) => (cas, e),
                _ => panic!(""),
            };
            check(ctx, ty, &Value::u())?;
            if !Equiv::equiv(ctx, tpe, &eval(ctx, ty)?)? {
                Err(ErrorCause::Hole)?;
            }
            if cas
                .iter()
                .map(|l| l.name())
                .collect::<HashSet<Identifier>>()
                != ces.iter().map(|b| b.name()).collect()
            {
                Err(ErrorCause::MissingBranch)?;
            }
            for (brc, lbl) in ces.iter().zip(cas) {
                check_branch(
                    &ctx,
                    &ctx.in_closure(de),
                    lbl,
                    brc,
                    &eval(ctx, term)?,
                    lam,
                    va,
                )?;
            }
            Ok(())
        }
        (Value::Pi(va_, lam, _), Term::Lam(x, a, t, _)) => {
            let va = eval(&ctx, a)?;
            if !Equiv::equiv(ctx, &va, va_)? {
                Err(ErrorCause::Hole)?;
            }
            let nx = ctx.fresh();
            let ctx = ctx.with_term(&x, &Value::var(nx, &va, Mod::Precise));

            check(
                &ctx,
                t,
                &app(&ctx, lam, &Value::var(nx, &va, Mod::Precise))?,
            )
        }
        (Value::Sigma(va, lam, _), Term::Pair(t1, t2, _)) => {
            check(ctx, t1, va)?;
            let v = eval(ctx, t1)?;
            check(ctx, t2, &app(ctx, lam, &v)?)
        }
        (_, Term::Where(exp, decls, _)) => {
            let new_ctx = check_declaration_set(ctx, decls)?;
            check(&new_ctx, exp, tpe)
        }
        (Value::U, Term::PathP(a, e0, e1, _)) => {
            let (a0, a1) = check_plam(ctx, a, &const_path(&Value::u()))?;
            check(ctx, e0, &a0)?;
            check(ctx, e1, &a1)
        }
        (Value::PathP(p, a0, a1, _), Term::PLam(_, _, _)) => {
            let (u0, u1) = check_plam(ctx, term, p)?;

            if Equiv::equiv(ctx, a0, &u0)? && Equiv::equiv(ctx, a1, &u1)? {
                Ok(())
            } else {
                println!("wrong term {:?}", term);
                Err(ErrorCause::WrongPathEnd((a0.clone(), a1.clone()), (u0, u1)))?
            }
        }
        (Value::U, Term::Glue(a, ts, _)) => {
            check(ctx, a, &Value::u())?;
            check_glue(ctx, &eval(ctx, a)?, ts)
        }
        (Value::Glue(va, ts, _), Term::GlueElem(u, us, _)) => {
            check(ctx, u, va)?;
            let vu = eval(ctx, u)?;
            check_glue_elem(ctx, &vu, ts, us)
        }
        (Value::CompU(_, _, _), Term::GlueElem(_, _, _)) => {
            todo!()
        }
        (Value::U, Term::Id(a, a0, a1, _)) => {
            check(ctx, a, &Value::u())?;
            let va = eval(ctx, a)?;
            check(ctx, a0, &va)?;
            check(ctx, a1, &va)
        }
        (Value::Id(va, va0, va1, _), Term::IdPair(w, ts, _)) => {
            check(
                ctx,
                w,
                &Value::pathp(&const_path(va), va0, va1, Mod::Precise),
            )?;
            let vw = eval(ctx, w)?;
            for (alpha, term) in ts.iter() {
                let face_ctx = ctx.with_face(alpha)?;
                check(&face_ctx, term, &va.face(&face_ctx, alpha)?)?;
                let vt_alpha = eval(&face_ctx, term)?;
                let alpha_vw = vw.face(&face_ctx, alpha)?;
                let p_vt_alpha = const_path(&vt_alpha);
                if !Equiv::equiv(&face_ctx, &alpha_vw, &p_vt_alpha)? {
                    Err(ErrorCause::UnEqInIdSystem(alpha_vw, p_vt_alpha))?
                }
            }
            Ok(())
        }
        _ => {
            let term_tpe = infer(ctx, term)?;

            if Equiv::equiv(ctx, &term_tpe, tpe)? {
                Ok(())
            } else {
                Err(ErrorCause::UnexpectedTypeInfered {
                    term: term.clone(),
                    expected: tpe.clone(),
                    infered: term_tpe,
                })?
            }
        }
    }
}
