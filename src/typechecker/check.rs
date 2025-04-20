use crate::ctt::term::{
    anon_id, Branch, DeclarationSet, Dir, Face, Formula, Identifier, Label, System, Telescope, Term,
};
use crate::typechecker::context::TypeContext;
use crate::typechecker::equiv::Equiv;
use crate::typechecker::error::{ErrorCause, TypeError};
use crate::typechecker::eval::{
    app, app_formula, eq_fun, equiv_dom, equiv_fun, eval, eval_system, is_comp_system, Facing,
};
use crate::typechecker::infer::{const_path, infer, label_type};
use crate::utils::intersect;
use std::collections::HashSet;
use std::rc::Rc;

fn check_family(ctx: TypeContext, f: &Term) -> Result<(), TypeError> {
    let Term::Lam(name, tpe, body) = f else {
        todo!()
    };
    let tpe = eval(ctx.clone(), tpe)?;
    check(ctx.clone(), tpe.clone(), Rc::new(Term::U))?;
    let body_ctx = ctx.with_term(name, &Rc::new(Term::Var(name.clone())), &tpe);
    check(body_ctx, body.clone(), Rc::new(Term::U))
}

fn check_tele(ctx: TypeContext, tele: &Telescope) -> Result<TypeContext, TypeError> {
    let mut result = ctx;
    for (name, tpe) in tele.variables.iter() {
        check(result.clone(), tpe.clone(), Rc::new(Term::U))?;
        result = result.with_term(
            &name,
            &Rc::new(Term::Var(name.clone())),
            &eval(result.clone(), tpe.as_ref())?,
        );
    }
    Ok(result)
}

fn check_branch(
    ctx: TypeContext,
    label: &Label,
    branch: &Branch,
    split_tpe: Rc<Term>,
    tpe: Rc<Term>,
) -> Result<(), TypeError> {
    match (label, branch) {
        (Label::OLabel(_, tele), Branch::OBranch(c, ns, body)) => {
            let mut branch_ctx = ctx.clone();
            let mut vars = vec![];
            for ((_, tpe), bind) in tele.variables.iter().zip(ns) {

                let var = Rc::new(Term::Var(bind.clone()));
                vars.push(var.clone());
                branch_ctx = branch_ctx.with_term(bind, &var, &eval(branch_ctx.clone(), &tpe)?);
            }
            let res = check(
                branch_ctx.clone(),
                body.clone(),
                app(branch_ctx, split_tpe, Rc::new(Term::Con(c.clone(), vars)))?,
            );
            res

        }
        (Label::PLabel(_, _, _, _), Branch::PBranch(_, _, _, _)) => {
            todo!()
        }
        _ => Err(ErrorCause::Hole)?,
    }
}

pub fn check_formula(ctx: TypeContext, formula: &Formula) -> Result<(), TypeError> {
    match formula {
        Formula::Dir(_) => Ok(()),
        Formula::Atom(name) | Formula::NegAtom(name) => {
            if ctx.lookup_formula(name).is_some() {
                Ok(())
            } else {
                println!("AAAAA {:?}", name);
                Err(ErrorCause::UnknownInterval)?
            }
        }
        Formula::And(lhs, rhs) | Formula::Or(lhs, rhs) => {
            check_formula(ctx.clone(), lhs).and(check_formula(ctx, rhs))
        }
    }
}
pub fn check_declaration_set(
    ctx: TypeContext,
    set: &DeclarationSet,
) -> Result<TypeContext, TypeError> {
    match set {
        DeclarationSet::Mutual(decls) => {
            let mut new_ctx = ctx.clone();

            for decl in decls.iter() {
                let tpe = eval(new_ctx.clone(), decl.tpe.as_ref())?;
                println!("decl: {} {:?}: {:?}", decl.name, decl.body, tpe);
                check(new_ctx.clone(), decl.body.clone(), tpe.clone())?;
                new_ctx = new_ctx.with_term(
                    &decl.name,
                    &eval(new_ctx.clone(), decl.body.as_ref())?,
                    &tpe,
                );
            }
            Ok(new_ctx)
        }
        DeclarationSet::Opaque(_) => Ok(ctx),
        DeclarationSet::Transparent(_) => Ok(ctx),
        DeclarationSet::TransparentAll => Ok(ctx),
    }
}

pub fn check_plam(
    ctx: TypeContext,
    term: Rc<Term>,
    tpe: Rc<Term>,
) -> Result<(Rc<Term>, Rc<Term>), TypeError> {
    // println!("CHECKING PLAM {:?} {:?}", term, tpe);
    match term.as_ref() {
        Term::PLam(int, body) => {
            let new_ctx = ctx.with_formula(&int, Formula::Atom(int.clone()));
            check(
                new_ctx.clone(),
                body.clone(),
                app_formula(ctx, tpe, Formula::Atom(int.clone()))?,
            )?;
            Ok((
                eval(
                    new_ctx.with_formula(&int, Formula::Dir(Dir::Zero)),
                    body.as_ref(),
                )?,
                eval(
                    new_ctx.with_formula(&int, Formula::Dir(Dir::One)),
                    body.as_ref(),
                )?,
            ))
        }
        _ => {
            let vt = infer(ctx.clone(), term.as_ref())?;
            match vt.as_ref() {
                Term::PathP(a, a0, a1) => {
                    if Equiv::equiv(ctx, a.clone(), tpe)? {
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

fn check_comp_system(ctx: TypeContext, sys: &System<Term>) -> Result<(), TypeError> {
    if is_comp_system(ctx, sys)? {
        Ok(())
    } else {
        Err(ErrorCause::Hole)?
    }
}

pub fn check_plam_system(
    ctx: TypeContext,
    t0: Rc<Term>,
    va: Rc<Term>,
    ps: &System<Term>,
) -> Result<System<Term>, TypeError> {
    // println!("CHECKING SYSTEM {:?} {:?}", t0, va);
    let v = System {
        binds: ps
            .binds
            .iter()
            .map(|(alpha, p_alpha)| {
                let face_ctx = ctx.with_face(&alpha)?;
                let (a0, a1) = check_plam(
                    face_ctx.clone(),
                    p_alpha.clone(),
                    va.clone().face(ctx.clone(), &alpha)?,
                )?;
                if Equiv::equiv(face_ctx.clone(), a0, eval(face_ctx, t0.as_ref())?)? {
                    Ok((alpha.clone(), a1))
                } else {
                    Err(ErrorCause::Hole)?
                }
            })
            .collect::<Result<_, TypeError>>()?,
    };
    check_comp_system(ctx, &v)?;
    Ok(v)
}

fn check_equiv(ctx: TypeContext, term: Rc<Term>, tpe: Rc<Term>) -> Result<(), TypeError> {
    let eq_tpe = {
        let a_lit = ctx.fresh();
        let t_lit = ctx.fresh();
        let x_lit = ctx.fresh();
        let f_lit = ctx.fresh();
        let y_lit = ctx.fresh();
        let s_lit = ctx.fresh();
        let z_lit = ctx.fresh();

        let new_ctx = TypeContext::new().with_term(&a_lit, &term, &tpe);
        let t = Rc::new(Term::Var(t_lit));
        let a = Rc::new(Term::Var(a_lit));
        let x = Rc::new(Term::Var(x_lit));
        let f = Rc::new(Term::Var(f_lit));
        let y = Rc::new(Term::Var(y_lit));
        let s = Rc::new(Term::Var(s_lit));
        let z = Rc::new(Term::Var(z_lit));
        let fib = Rc::new(Term::Sigma(Rc::new(Term::Lam(
            y_lit,
            t.clone(),
            Rc::new(Term::PathP(
                Rc::new(Term::PLam(anon_id(), a.clone())),
                x,
                Rc::new(Term::App(f, y)),
            )),
        ))));
        let iscontrfib = Rc::new(Term::Sigma(Rc::new(Term::Lam(
            s_lit,
            fib.clone(),
            Rc::new(Term::Pi(Rc::new(Term::Lam(
                z_lit,
                fib.clone(),
                Rc::new(Term::PathP(Rc::new(Term::PLam(anon_id(), fib)), s, z)),
            )))),
        ))));

        eval(
            new_ctx,
            &Term::Sigma(Rc::new(Term::Lam(
                t_lit,
                Rc::new(Term::U),
                Rc::new(Term::Sigma(Rc::new(Term::Lam(
                    f_lit,
                    Rc::new(Term::Pi(Rc::new(Term::Lam(anon_id(), t, a.clone())))),
                    Rc::new(Term::Pi(Rc::new(Term::Lam(x_lit, a, iscontrfib)))),
                )))),
            ))),
        )?
    };
    check(ctx, term, eq_tpe)
}

fn check_glue(ctx: TypeContext, term: Rc<Term>, system: &System<Term>) -> Result<(), TypeError> {
    for (alpha, t_alpha) in system.binds.iter() {
        check_equiv(
            ctx.clone(),
            term.clone().face(ctx.clone(), &alpha)?,
            t_alpha.clone(),
        )?;
    }
    check_comp_system(ctx.clone(), &eval_system(ctx, system)?)
}

fn check_glue_elem(
    ctx: TypeContext,
    term: Rc<Term>,
    system1: &System<Term>,
    system2: &System<Term>,
) -> Result<(), TypeError> {
    if system1.domain() != system2.domain() {
        Err(ErrorCause::Hole)?
    }

    for (alpha, (vt, u)) in intersect(&system1.binds, &system2.binds) {
        let face_ctx = ctx.with_face(alpha)?;
        check(face_ctx, u.clone(), equiv_dom(vt.clone()))?;
    }

    let vus = eval_system(ctx.clone(), system2)?;

    for (alpha, (vt, v_alpha)) in intersect(&system1.binds, &vus.binds) {
        if !Equiv::equiv(
            ctx.clone(),
            app(ctx.clone(), equiv_fun(vt.clone()), v_alpha.clone())?,
            term.clone().face(ctx.clone(), &alpha)?,
        )? {
            Err(ErrorCause::Hole)?;
        }
    }

    check_comp_system(ctx, &vus)
}

fn check_glue_elem_u(
    ctx: TypeContext,
    term: Rc<Term>,
    system1: &System<Term>,
    system2: &System<Term>,
) -> Result<(), TypeError> {
    if system1.domain() != system2.domain() {
        Err(ErrorCause::Hole)?
    }

    for (alpha, (ve, u)) in intersect(&system1.binds, &system2.binds) {
        let face_ctx = ctx.with_face(&alpha)?;
        check(
            face_ctx,
            u.clone(),
            app_formula(ctx.clone(), ve.clone(), Formula::Dir(Dir::One))?,
        )?;
    }

    let vus = eval_system(ctx.clone(), system2)?;

    for (alpha, (ve, v_alpha)) in intersect(&system1.binds, &vus.binds) {
        if !Equiv::equiv(
            ctx.clone(),
            eq_fun(ctx.clone(), ve.clone(), v_alpha.clone())?,
            term.clone().face(ctx.clone(), &alpha)?,
        )? {
            Err(ErrorCause::Hole)?;
        }
    }

    check_comp_system(ctx, &vus)
}

pub fn check(ctx: TypeContext, term: Rc<Term>, tpe: Rc<Term>) -> Result<(), TypeError> {
    println!("check? {:?}: {:?}", term.as_ref(), tpe.as_ref());

    match (tpe.as_ref(), term.as_ref()) {
        (_, Term::Undef(_)) => Ok(()),
        (_, Term::Hole) => Err(ErrorCause::Hole)?,
        (_, Term::Con(c, cs)) => {
            let con = label_type(c, tpe)?;

            let mut con_type = con;
            let mut arg_ctx = ctx.clone();

            for arg in cs {
                let Term::Pi(arg_lam) = &con_type.as_ref() else {
                    Err(ErrorCause::Hole)?
                };
                let Term::Lam(name, tpe, body) = arg_lam.as_ref() else {
                    Err(ErrorCause::Hole)?
                };
                let tpe = eval(arg_ctx.clone(), tpe)?;
                check(arg_ctx.clone(), arg.clone(), tpe.clone())?;
                arg_ctx = arg_ctx.with_term(&name, &arg, &tpe);
                con_type = body.clone();
            }
            Ok(())
        }
        (Term::U, Term::Pi(f)) => check_family(ctx, f),
        (Term::U, Term::Sigma(f)) => check_family(ctx, f),
        (Term::U, Term::Sum(_, labels)) => {
            for label in labels {
                match label {
                    Label::OLabel(_, tele) => check_tele(ctx.clone(), tele).map(|_| ())?,
                    Label::PLabel(_, _, _, _) => panic!("h-label in data"),
                }
            }
            Ok(())
        }
        (Term::U, Term::HSum(_, labels)) => {
            for label in labels {
                match label {
                    Label::OLabel(_, tele) => {
                        check_tele(ctx.clone(), tele)?;
                    }
                    Label::PLabel(_, tele, is, ts) => {
                        let domain = ts.domain();
                        if !domain.iter().all(|name| is.contains(name)) {
                            Err(ErrorCause::UnknownNameInSystem)?
                        }
                        let tele_ctx = check_tele(ctx.clone(), tele)?;
                        let inter_ctx = is.iter().fold(tele_ctx, |acc, i| {
                            acc.with_formula(i, Formula::Atom(i.clone()))
                        });
                        for (face, term) in ts.binds.iter() {
                            let face_ctx = inter_ctx.with_face(face)?;
                            check(face_ctx, term.clone(), tpe.clone())?
                        }
                    }
                }
            }
            Ok(())
        }
        (Term::Pi(lam), Term::Split(_, ty, ces)) => {
            println!("split {:?} {:?}", ty, tpe);
            let Term::Lam(_, va, f) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let cas = match va.as_ref() {
                Term::Sum(_, cas) => cas,
                Term::HSum(_, cas) => cas,
                _ => panic!(""),
            };
            check(ctx.clone(), ty.clone(), Rc::new(Term::U))?;
            if !Equiv::equiv(ctx.clone(), tpe.clone(), eval(ctx.clone(), ty)?)? {
                Err(ErrorCause::Hole)?;
            }
            if cas
                .iter()
                .map(|l| l.name())
                .collect::<HashSet<Identifier>>()
                != ces.iter().map(|b| b.name()).collect()
            {
                println!(
                    "{:?} {:?}",
                    cas.iter()
                        .map(|l| l.name())
                        .collect::<HashSet<Identifier>>(),
                    ces.iter().map(|b| b.name()).collect::<HashSet<Identifier>>()
                );
                Err(ErrorCause::MissingBranch)?;
            }
            for (brc, lbl) in ces.iter().zip(cas) {
                check_branch(ctx.clone(), lbl, brc, lam.clone(), va.clone())?;
            }
            Ok(())
        }
        (Term::Pi(lam), Term::Lam(x, a, t)) => {
            let Term::Lam(name, tpe, body) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let a = eval(ctx.clone(), a)?;
            let tpe = eval(ctx.clone(), tpe)?;
            if !Equiv::equiv(ctx.clone(), a.clone(), tpe.clone())? {
                Err(ErrorCause::Hole)?;
            }
            let new_ctx = ctx
                .with_term(&name, &Rc::new(Term::Var(x.clone())), &tpe)
                .with_term(x, &Rc::new(Term::Var(x.clone())), &tpe);
            let new_result = eval(new_ctx.clone(), body)?;
            check(new_ctx, t.clone(), new_result)
        }
        (Term::Sigma(lam), Term::Pair(t1, t2)) => {
            let Term::Lam(name, tpe, body) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            check(ctx.clone(), t1.clone(), eval(ctx.clone(), tpe)?)?;
            let v = eval(ctx.clone(), t1)?;
            let new_ctx = ctx.with_term(name, &v, tpe);
            check(ctx, t2.clone(), eval(new_ctx, body)?)
        }
        (_, Term::Where(exp, decls)) => {
            let new_ctx = check_declaration_set(ctx, decls)?;
            check(new_ctx, exp.clone(), tpe)
        }
        (Term::U, Term::PathP(a, e0, e1)) => {
            let (a0, a1) = check_plam(ctx.clone(), a.clone(), const_path(Rc::new(Term::U)))?;
            check(ctx.clone(), e0.clone(), a0)?;
            check(ctx.clone(), e1.clone(), a1)
        }
        (Term::PathP(p, a0, a1), Term::PLam(name, _)) => {
            let name = name.clone();

            if name == 121838 {
                println!("AAAA");
            }

            let (u0, u1) = check_plam(ctx.clone(), term, p.clone())?;

            let conv = Equiv::equiv(ctx.clone(), a0.clone(), u0.clone())?
                && Equiv::equiv(ctx.clone(), a1.clone(), u1.clone())?;
            if conv {
                Ok(())
            } else {
                println!("plam {:?}", name);

                println!("CHECKING PATH EQ {:?} =? {:?}", a0, u0);
                println!("CHECKING PATH EQ {:?} =? {:?}", a1, u1);


                println!("{:?}", ctx.lookup_formula(&167905));
                println!("{:?}", ctx.lookup_formula(&407));
                Err(ErrorCause::Hole)?
            }
        }
        (Term::U, Term::Glue(a, ts)) => {
            check(ctx.clone(), a.clone(), Rc::new(Term::U))?;
            check_glue(ctx.clone(), eval(ctx, a)?, ts)
        }
        (Term::U, Term::Glue(a, ts)) => {
            check(ctx.clone(), a.clone(), Rc::new(Term::U))?;
            check_glue(ctx.clone(), eval(ctx, a)?, ts)
        }
        (Term::Comp(tu, va, ves), Term::GlueElem(u, us)) if tu.as_ref() == &Term::U => {
            todo!()
        }
        (Term::U, Term::Id(a, a0, a1)) => {
            check(ctx.clone(), a.clone(), Rc::new(Term::U))?;
            let va = eval(ctx.clone(), a)?;
            check(ctx.clone(), a0.clone(), va.clone())?;
            check(ctx.clone(), a1.clone(), va)
        }
        (Term::Id(va, va0, va1), Term::IdPair(w, ts)) => {
            check(
                ctx.clone(),
                Rc::new(Term::PathP(
                    const_path(va.clone()),
                    va0.clone(),
                    va1.clone(),
                )),
                w.clone(),
            )?;
            let vw = eval(ctx.clone(), w)?;
            for (face, term) in ts.binds.iter() {
                let face_ctx = ctx.with_face(&face)?;
                check(
                    face_ctx.clone(),
                    term.clone(),
                    va.clone().face(ctx.clone(), &face)?,
                )?;
                let vt_alpha = eval(face_ctx.clone(), term.as_ref())?;
                if Equiv::equiv(
                    ctx.clone(),
                    vw.clone().face(ctx.clone(), face)?,
                    const_path(vt_alpha),
                )? {
                    Err(ErrorCause::Hole)?
                }
            }
            Ok(())
        }
        (_, Term::IdJ(_, _, _, _, _, _)) => {
            todo!()
        }
        _ => {
            // println!("START INFERENCE IN CHECKER");

            let term_tpe = infer(ctx.clone(), term.as_ref())?;
            // println!("END INFERENCE");

            // println!(
            //     "eq? {:?} : {:?} === {:?}",
            //     term.as_ref(),
            //     term_tpe.as_ref(),
            //     tpe.as_ref()
            // );
            if Equiv::equiv(ctx.clone(), term_tpe.clone(), tpe.clone())? {
                Ok(())
            } else {
                println!("FAIL {:?} {:?}", term_tpe, tpe);
                Err(ErrorCause::Hole)?
            }
        }
    }
}
