use crate::ctt::{system::Face, system::System, term::anon_id, term::Telescope, Identifier};
use crate::precise::term::{Mod, Term, Value};
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

pub fn const_path(body: &Rc<Value>) -> Rc<Value> {
    Value::plam(anon_id(), body, Mod::Precise)
}

pub fn label_type(name: &Identifier, tpe: &Rc<Value>) -> Result<Telescope<Term>, TypeError> {
    let (Value::Stuck(Term::Sum(_, labels, _), _, _)
    | Value::Stuck(Term::HSum(_, labels, _), _, _)) = tpe.as_ref()
    else {
        Err(ErrorCause::Hole)?
    };
    let label = labels
        .iter()
        .find(|p| &p.name() == name)
        .ok_or(ErrorCause::Hole)?;
    Ok(label.telescope())
}

// #[instrument(skip_all)]
pub fn infer(ctx: &TypeContext, term: &Rc<Term>) -> Result<Rc<Value>, TypeError> {
    match term.as_ref() {
        Term::U => Ok(Rc::new(Value::U)),
        Term::Var(name, _) => Ok(ctx
            .lookup_tpe(name)
            .ok_or(ErrorCause::UnknownTermName(*name))?),
        Term::App(f, a, _) => {
            let fun_tpe = infer(ctx, f)?;
            let Value::Pi(tpe, lam, _) = fun_tpe.as_ref() else {
                Err(ErrorCause::ExpectedPi(fun_tpe))?
            };
            check(ctx, a, tpe)?;
            app(ctx, lam, &eval(ctx, a)?)
        }
        Term::Fst(pair, _) => {
            let pair_tpe = infer(ctx, pair)?;
            let Value::Sigma(tpe, _, _) = pair_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            Ok(tpe.clone())
        }
        Term::Snd(pair, _) => {
            let pair_tpe = infer(ctx, pair)?;
            let Value::Sigma(_, lam, _) = pair_tpe.as_ref() else {
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
            let Value::Glue(t, _, _) = glue_type.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            Ok(t.clone())
        }
        Term::AppFormula(e, phi, _) => {
            check_formula(ctx, phi)?;
            let path_p = infer(ctx, e)?;
            let Value::PathP(a, _, _, _) = path_p.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            app_formula(ctx, a, eval_formula(ctx, phi))
        }
        Term::Split(_, tpe, _, _) => Ok(eval(ctx, tpe)?),
        Term::Comp(a, t0, ps, _) => {
            let (va0, va1) = check_plam(ctx, a, &const_path(&Value::u()))?;
            let va = eval(ctx, a)?;
            check(ctx, t0, &va0)?;
            check_plam_system(ctx, t0, &va, ps)?;
            Ok(va1)
        }
        Term::HComp(a, u0, us, _) => {
            check(ctx, a, &Value::u())?;
            let va = eval(ctx, a)?;
            check(ctx, u0, &va)?;
            check_plam_system(ctx, u0, &const_path(&Value::u()), us)?;
            Ok(va)
        }
        Term::Fill(a, t0, ps, _) => {
            let (va0, _) = check_plam(ctx, a, &const_path(&Value::u()))?;
            let va = eval(ctx, a)?;
            check(ctx, t0, &va0)?;
            check_plam_system(ctx, t0, &va, ps)?;
            let vt = eval(ctx, t0)?;
            let vps = eval_system(ctx, ps)?;
            let line = comp_line(ctx, &va, &vt, vps)?;
            Ok(Value::pathp(&va, &vt, &line, Mod::Precise))
        }
        Term::PCon(c, a, es, phis, _) => {
            check(ctx, a, &Value::u())?;

            let va = eval(ctx, a)?;

            let Value::Stuck(Term::HSum(_, _, _), e, _) = va.as_ref() else {
                Err(ErrorCause::ExpectedDataType(va))?
            };

            let tele = label_type(c, &va)?;

            let mut tpe_ctx = ctx.in_closure(e).clone();

            for (arg, (name, tpe)) in es.iter().zip(tele.variables) {
                let arg_v = eval(&ctx, arg)?;
                let tpe = eval(&tpe_ctx, &tpe)?;
                tpe_ctx = tpe_ctx.with_term(&name, &arg_v);
                check(&ctx, arg, &tpe)?;
            }

            for formula in phis {
                check_formula(ctx, formula)?
            }
            Ok(va)
        }
        Term::IdJ(a, u, c, d, x, p, _) => {
            check(ctx, a, &Value::u())?;
            let va = eval(ctx, a)?;
            check(ctx, u, &va)?;
            let vu = eval(ctx, u)?;
            let refu = Value::id_pair(
                &const_path(&vu),
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

            check(ctx, d, &app(ctx, &app(ctx, &vc, &vu)?, &refu)?)?;
            check(ctx, x, &va)?;
            let vx = eval(ctx, x)?;
            check(ctx, p, &Value::id(&va, &vu, &vx, Mod::Precise))?;
            let vp = eval(ctx, p)?;

            app(ctx, &app(ctx, &vc, &vx)?, &vp)
        }
        _ => panic!("uninferable state {:?}", term),
    }
}
