use crate::ctt::term::{
    anon_id, Branch, DeclarationSet, Dir, Formula, Identifier, Label, System, Telescope,
};
use crate::precise::term::{Mod, Term};
use crate::typechecker::canon::app::{app, app_formula};
use crate::typechecker::canon::comp::eq_fun;
use crate::typechecker::canon::eval::{equiv_dom, equiv_fun, eval, eval_system, is_comp_system};
use crate::typechecker::canon::nominal::{border, Facing};
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
    let tpe = eval(ctx, tpe)?;
    check(ctx, &tpe, &Term::u())?;
    let body_ctx = ctx.with_term(name, &Term::var(*name, Mod::Precise), &tpe);
    check(&body_ctx, body, &Term::u())
}

fn check_tele(ctx: &TypeContext, tele: &Telescope<Term>) -> Result<TypeContext, TypeError> {
    let mut result = ctx.clone();
    for (name, tpe) in tele.variables.iter() {
        check(&result, tpe, &Term::u())?;
        result = result.with_term(
            name,
            &Term::var(*name, Mod::Precise),
            &eval(&result, tpe)?,
        );
    }
    Ok(result)
}

fn check_branch(
    ctx: &TypeContext,
    label: &Label<Term>,
    branch: &Branch<Term>,
    split: &Rc<Term>,
    split_tpe: &Rc<Term>,
    tpe: &Rc<Term>,
) -> Result<(), TypeError> {
    match (label, branch) {
        (Label::OLabel(_, tele), Branch::OBranch(c, ns, body)) => {
            let mut branch_ctx = ctx.clone();
            let mut vars = vec![];
            for ((_, tpe), bind) in tele.variables.iter().zip(ns) {
                let var = Term::var(*bind, Mod::Precise);
                vars.push(var.clone());
                branch_ctx = branch_ctx.with_term(bind, &var, &eval(&branch_ctx, tpe)?);
            }
            let f_tpe = app(
                &branch_ctx,
                split_tpe,
                &Term::con(*c, vars, Mod::Precise),
            )?;
            check(&branch_ctx, body, &f_tpe)
        }
        (Label::PLabel(_, tele, is, ts), Branch::PBranch(c, ns, js, body)) => {
            let mut sys_ctx = ctx.uncompacted();
            for (i, j) in is.iter().zip(js) {
                sys_ctx = sys_ctx.with_formula(i, Formula::Atom(*j));
            }
            for (name, tpe) in &tele.variables {
                sys_ctx = sys_ctx.with_term(
                    name,
                    &Term::var(*name, Mod::Precise),
                    &eval(&sys_ctx, tpe)?,
                );
            }
            let vts = eval_system(&sys_ctx, ts)?;
            let vgts = System::intersect(&border(&sys_ctx, split, &vts)?, &vts)
                .map(|(k, (a, b))| Ok((k.clone(), app(&sys_ctx, a, b)?)))
                .collect::<Result<_, TypeError>>()?;
            let mut branch_ctx = ctx.uncompacted();
            let mut vars = vec![];
            for ((_, tpe), bind) in tele.variables.iter().zip(ns) {
                let var = Rc::new(Term::Var(*bind, Mod::Precise));
                vars.push(var.clone());
                branch_ctx = branch_ctx.with_term(bind, &var, &eval(&branch_ctx, tpe)?);
            }
            for j in js {
                branch_ctx = branch_ctx.with_formula(j, Formula::Atom(*j));
            }
            let b_tpe = app(
                &branch_ctx,
                split_tpe,
                &Term::pcon(
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
                Err(ErrorCause::Hole)?
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

            for decl in decls.iter() {
                ctx.decl_check_started(&decl.name);
                let tpe = eval(&new_ctx, &decl.tpe)?;
                let pre_ctx = new_ctx.with_term(&decl.name, &decl.body, &tpe);
                check(&pre_ctx, &decl.body, &tpe)?;
                let b = eval(&pre_ctx, &decl.body)?;
                new_ctx = new_ctx.with_term(&decl.name, &b, &tpe);
                ctx.decl_check_finished(&decl.name);
            }
            Ok(new_ctx)
        }
        DeclarationSet::Opaque(_) => Ok(ctx.clone()),
        DeclarationSet::Transparent(_) => Ok(ctx.clone()),
        DeclarationSet::TransparentAll => Ok(ctx.clone()),
    }
}

pub fn check_plam(
    ctx: &TypeContext,
    term: &Rc<Term>,
    tpe: &Rc<Term>,
) -> Result<(Rc<Term>, Rc<Term>), TypeError> {
    // println!("CHECKING PLAM {:?} {:?}", term, tpe);
    match term.as_ref() {
        Term::PLam(int, body, _) => {
            let new_ctx = ctx.with_formula(int, Formula::Atom(*int));
            check(
                &new_ctx,
                body,
                &app_formula(ctx, tpe, Formula::Atom(*int))?,
            )?;
            Ok((
                eval(&new_ctx.with_formula(int, Formula::Dir(Dir::Zero)), body)?,
                eval(&new_ctx.with_formula(int, Formula::Dir(Dir::One)), body)?,
            ))
        }
        _ => {
            let vt = infer(ctx, term)?;
            match vt.as_ref() {
                Term::PathP(a, a0, a1, _) => {
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

fn check_comp_system(ctx: &TypeContext, sys: &System<Term>) -> Result<(), TypeError> {
    if is_comp_system(ctx, sys)? {
        Ok(())
    } else {
        Err(ErrorCause::Hole)?
    }
}

pub fn check_plam_system(
    ctx: &TypeContext,
    t0: &Rc<Term>,
    va: &Rc<Term>,
    ps: &System<Term>,
) -> Result<System<Term>, TypeError> {
    let v = ps
        .iter()
        .map(|(alpha, p_alpha)| {
            let face_ctx = ctx.with_face(alpha)?;
            let (a0, a1) = check_plam(&face_ctx, p_alpha, &va.face(ctx, alpha)?)?;
            if Equiv::equiv(&face_ctx, &a0, &eval(&face_ctx, t0)?)? {
                Ok((alpha.clone(), a1))
            } else {
                Err(ErrorCause::Hole)?
            }
        })
        .collect::<Result<_, TypeError>>()?;
    check_comp_system(ctx, &eval_system(ctx, ps)?)?;
    Ok(v)
}

fn check_equiv(ctx: &TypeContext, term: &Rc<Term>, tpe: &Rc<Term>) -> Result<(), TypeError> {
    let eq_tpe = {
        let a_lit = ctx.fresh();
        let t_lit = ctx.fresh();
        let x_lit = ctx.fresh();
        let f_lit = ctx.fresh();
        let y_lit = ctx.fresh();
        let s_lit = ctx.fresh();
        let z_lit = ctx.fresh();

        let new_ctx = ctx.with_term(&a_lit, tpe, &Term::u());
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

fn check_glue(ctx: &TypeContext, tpe: &Rc<Term>, system: &System<Term>) -> Result<(), TypeError> {
    for (alpha, t_alpha) in system.iter() {
        check_equiv(ctx, t_alpha, &tpe.face(ctx, alpha)?)?;
    }
    check_comp_system(ctx, &eval_system(ctx, system)?)
}

fn check_glue_elem(
    ctx: &TypeContext,
    term: &Rc<Term>,
    system1: &System<Term>,
    system2: &System<Term>,
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
    term: &Rc<Term>,
    system1: &System<Term>,
    system2: &System<Term>,
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

pub fn check(ctx: &TypeContext, term: &Rc<Term>, tpe: &Rc<Term>) -> Result<(), TypeError> {
    match (tpe.as_ref(), term.as_ref()) {
        (_, Term::Undef(_, _)) => Ok(()),
        (_, Term::Hole) => Err(ErrorCause::Hole)?,
        (_, Term::Con(c, cs, _)) => {
            let con = label_type(c, tpe)?;
            let mut con_type = con;
            let mut arg_ctx = ctx.clone();

            for arg in cs {
                let Term::Pi(arg_lam, _) = &con_type.as_ref() else {
                    Err(ErrorCause::Hole)?
                };
                let Term::Lam(name, tpe, body, _) = arg_lam.as_ref() else {
                    Err(ErrorCause::Hole)?
                };
                let tpe = eval(&arg_ctx, tpe)?;
                check(&arg_ctx, arg, &tpe)?;
                arg_ctx = arg_ctx.with_term(name, arg, &tpe);
                con_type = body.clone();
            }
            Ok(())
        }
        (Term::U, Term::Pi(f, _)) => check_family(ctx, f),
        (Term::U, Term::Sigma(f, _)) => check_family(ctx, f),
        (Term::U, Term::Sum(_, labels, _)) => {
            for label in labels {
                match label {
                    Label::OLabel(_, tele) => check_tele(ctx, tele).map(|_| ())?,
                    Label::PLabel(_, _, _, _) => panic!("h-label in data"),
                }
            }
            Ok(())
        }
        (Term::U, Term::HSum(_, labels, _)) => {
            let data = term;
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
                        let inter_ctx = is.iter().fold(tele_ctx, |acc, i| {
                            acc.with_formula(i, Formula::Atom(*i))
                        });
                        for (face, term) in ts.iter() {
                            let face_ctx = inter_ctx.with_face(face)?;
                            check(&face_ctx, term, data)?
                        }
                    }
                }
            }
            Ok(())
        }
        (Term::Pi(lam, _), Term::Split(_, ty, ces, _)) => {
            let Term::Lam(_, va, _, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let cas = match va.as_ref() {
                Term::Sum(_, cas, _) => cas,
                Term::HSum(_, cas, _) => cas,
                _ => panic!(""),
            };
            check(ctx, ty, &Term::u())?;
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
                check_branch(ctx, lbl, brc, &eval(ctx, term)?, lam, va)?;
            }
            Ok(())
        }
        (Term::Pi(lam, _), Term::Lam(x, a, t, _)) => {
            let Term::Lam(name, tpe, body, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let a = eval(ctx, a)?;
            let tpe = eval(ctx, tpe)?;
            if !Equiv::equiv(ctx, &a, &tpe)? {
                Err(ErrorCause::Hole)?;
            }
            let new_ctx = ctx
                .with_term(name, &Term::var(*x, Mod::Precise), &tpe)
                .with_term(x, &Term::var(*x, Mod::Precise), &tpe);
            let new_result = eval(&new_ctx, body)?;
            check(&new_ctx, t, &new_result)
        }
        (Term::Sigma(lam, _), Term::Pair(t1, t2, _)) => {
            let Term::Lam(name, tpe, body, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            check(ctx, t1, &eval(ctx, tpe)?)?;
            let v = eval(ctx, t1)?;
            let new_ctx = ctx.with_term(name, &v, tpe);
            check(ctx, t2, &eval(&new_ctx, body)?)
        }
        (_, Term::Where(exp, decls, _)) => {
            let new_ctx = check_declaration_set(ctx, decls)?;
            check(&new_ctx, exp, tpe)
        }
        (Term::U, Term::PathP(a, e0, e1, _)) => {
            let (a0, a1) = check_plam(ctx, a, &const_path(&Term::u()))?;
            check(ctx, e0, &a0)?;
            check(ctx, e1, &a1)
        }
        (Term::PathP(p, a0, a1, _), Term::PLam(name, _, _)) => {
            let name = *name;

            let (u0, u1) = check_plam(ctx, term, p)?;

            let conv = Equiv::equiv(ctx, a0, &u0)? && Equiv::equiv(ctx, a1, &u1)?;
            if conv {
                Ok(())
            } else {
                Err(ErrorCause::Hole)?
            }
        }
        (Term::U, Term::Glue(a, ts, _)) => {
            check(ctx, a, &Term::u())?;
            check_glue(ctx, &eval(ctx, a)?, ts)
        }
        (Term::Glue(va, ts, _), Term::GlueElem(u, us, _)) => {
            check(ctx, u, va)?;
            let vu = eval(ctx, u)?;
            check_glue_elem(ctx, &vu, ts, us)
        }
        (Term::Comp(tu, va, ves, _), Term::GlueElem(u, us, _)) if tu.as_ref() == &Term::U => {
            todo!()
        }
        (Term::U, Term::Id(a, a0, a1, _)) => {
            check(ctx, a, &Term::u())?;
            let va = eval(ctx, a)?;
            check(ctx, a0, &va)?;
            check(ctx, a1, &va)
        }
        (Term::Id(va, va0, va1, _), Term::IdPair(w, ts, _)) => {
            check(
                ctx,
                &Term::pathp(&const_path(va), va0, va1, Mod::Precise),
                w,
            )?;
            let vw = eval(ctx, w)?;
            for (face, term) in ts.iter() {
                let face_ctx = ctx.with_face(face)?;
                check(&face_ctx, term, &va.face(ctx, face)?)?;
                let vt_alpha = eval(&face_ctx, term)?;
                if Equiv::equiv(ctx, &vw.face(ctx, face)?, &const_path(&vt_alpha))? {
                    Err(ErrorCause::Hole)?
                }
            }
            Ok(())
        }
        (_, Term::IdJ(_, _, _, _, _, _, _)) => {
            todo!()
        }
        _ => {
            let term_tpe = infer(ctx, term)?;

            if Equiv::equiv(ctx, &term_tpe, tpe)? {
                Ok(())
            } else {
                Err(ErrorCause::Hole)?
            }
        }
    }
}
