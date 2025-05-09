use crate::ctt::term::{anon_id, Face, Identifier, System};
use crate::precise::term::{Mod, Term};
use crate::typechecker::check::{
    check, check_declaration_set, check_formula, check_plam, check_plam_system,
};
use crate::typechecker::context::TypeContext;
use crate::typechecker::error::{ErrorCause, TypeError};
use std::collections::HashMap;
use std::rc::Rc;

use super::canon::app::{app, app_formula};
use super::canon::comp::comp_line;
use super::canon::eval::{eval, eval_formula, eval_system, get_first};

pub fn const_path(body: &Rc<Term>) -> Rc<Term> {
    Term::plam(anon_id(), body, Mod::Precise)
}

pub fn label_type(name: &Identifier, tpe: &Rc<Term>) -> Result<Rc<Term>, TypeError> {
    let (Term::Sum(_, labels, _) | Term::HSum(_, labels, _)) = tpe.as_ref() else {
        Err(ErrorCause::Hole)?
    };
    let label = labels
        .iter()
        .find(|p| &p.name() == name)
        .ok_or(ErrorCause::Hole)?;
    let mut res = tpe.clone();
    for (var, tpe) in label.telescope().variables.iter().rev() {
        res = Term::pi(
            &Term::lam(var.clone(), tpe, &res, Mod::Precise),
            Mod::Precise,
        )
    }
    Ok(res)
}

pub fn infer(ctx: &TypeContext, term: &Rc<Term>) -> Result<Rc<Term>, TypeError> {
    match term.as_ref() {
        Term::U => Ok(Rc::new(Term::U)),
        Term::Var(name, _) => Ok(ctx
            .lookup_term(name)
            .ok_or(ErrorCause::UnknownTermName(name.clone()))?
            .tpe),
        Term::App(f, a, _) => {
            let fun_tpe = infer(ctx, f)?;
            let Term::Pi(lam, _) = fun_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Lam(_, tpe, _, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };

            check(ctx, a, tpe)?;
            eval(ctx, &Term::app(lam, a, Mod::Precise))
        }
        Term::Fst(pair, _) => {
            let pair_tpe = infer(ctx, pair)?;
            let Term::Sigma(pair_tpe, _) = pair_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Lam(_, param, _, _) = pair_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            Ok(param.clone())
        }
        Term::Snd(pair, _) => {
            let pair_tpe = infer(ctx, pair)?;
            let Term::Sigma(lam, _) = pair_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let p = eval(ctx, pair)?;
            app(ctx, lam, &get_first(&p))
        }
        Term::Where(t, d, _) => {
            let new_ctx = check_declaration_set(ctx, d)?;
            infer(&new_ctx, t)
        }
        Term::UnGlueElem(e, _, _) => {
            let glue_type = infer(ctx, e)?;
            let Term::Glue(t, _, _) = glue_type.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            Ok(t.clone())
        }
        Term::AppFormula(e, phi, _) => {
            check_formula(ctx, phi)?;
            let path_p = infer(ctx, e)?;
            let Term::PathP(a, _, _, _) = path_p.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            app_formula(ctx, &eval(ctx, a)?, eval_formula(ctx, phi))
        }
        Term::Split(_, tpe, _, _) => Ok(eval(ctx, tpe)?),
        Term::Comp(a, t0, ps, _) => {
            let (va0, va1) = check_plam(ctx, a, &const_path(&Term::u()))?;
            let va = eval(ctx, a)?;
            check(ctx, t0, &va0)?;
            check_plam_system(ctx, t0, &va, ps)?;
            Ok(va1)
        }
        Term::HComp(a, u0, us, _) => {
            check(ctx, a, &Term::u())?;
            let va = eval(ctx, a)?;
            check(ctx, u0, &va)?;
            check_plam_system(ctx, u0, &const_path(&Term::u()), us)?;
            Ok(va)
        }
        Term::Fill(a, t0, ps, _) => {
            let (va0, _) = check_plam(ctx, a, &const_path(&Term::u()))?;
            let va = eval(ctx, a)?;
            check(ctx, t0, &va0)?;
            check_plam_system(ctx, t0, &va, ps)?;
            let vt = eval(ctx, t0)?;
            let vps = eval_system(ctx, ps)?;
            let line = comp_line(ctx, &va, &vt, vps)?;
            Ok(Term::pathp(&va, &vt, &line, Mod::Precise))
        }
        Term::PCon(c, a, es, phis, _) => {
            let va = eval(ctx, a)?;

            check(ctx, &va, &Term::u())?;

            let con = label_type(c, &va)?;

            let mut con_type = con;
            let mut arg_ctx = ctx.clone();

            for arg in es {
                let Term::Pi(arg_lam, _) = &con_type.as_ref() else {
                    Err(ErrorCause::Hole)?
                };
                let Term::Lam(name, tpe, body, _) = arg_lam.as_ref() else {
                    Err(ErrorCause::Hole)?
                };
                let tpe = eval(&arg_ctx, tpe)?;
                arg_ctx = arg_ctx.with_term(&name, arg, &tpe);
                con_type = body.clone();
                check(&arg_ctx, arg, &tpe)?;
            }

            for formula in phis {
                check_formula(ctx, formula)?
            }
            Ok(va)
        }
        Term::IdJ(a, u, c, d, x, p, _) => {
            check(ctx, a, &Term::u())?;
            let va = eval(ctx, a)?;
            check(ctx, u, &va)?;
            let vu = eval(ctx, u)?;
            let refu = Term::id_pair(
                &const_path(&Term::u()),
                System::from(HashMap::from([(Face::eps(), vu.clone())])),
                Mod::Precise,
            );
            let z_lit = ctx.fresh();

            let z = Term::var(z_lit, Mod::Precise);
            let ctype = eval(
                ctx,
                &Term::pi(
                    &Term::lam(
                        z_lit,
                        a,
                        &Term::pi(
                            &Term::lam(
                                anon_id(),
                                &Term::id(a, u, &z, Mod::Precise),
                                &Term::u(),
                                Mod::Precise,
                            ),
                            Mod::Precise,
                        ),
                        Mod::Precise,
                    ),
                    Mod::Precise,
                ),
            )?;
            check(ctx, c, &ctype)?;
            let vc = eval(ctx, c)?;

            check(
                ctx,
                d,
                &eval(
                    ctx,
                    &Term::app(&Term::app(&vc, &vu, Mod::Precise), &refu, Mod::Precise),
                )?,
            )?;
            check(ctx, x, &va)?;
            let vx = eval(ctx, x)?;
            check(ctx, p, &Term::id(&va, &vu, &vx, Mod::Precise))?;
            let vp = eval(ctx, p)?;
            eval(
                ctx,
                &Term::app(&Term::app(&vc, &vx, Mod::Precise), &vp, Mod::Precise),
            )
        }
        _ => panic!("uninferable state {:?}", term),
    }
}
