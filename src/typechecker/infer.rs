use crate::ctt::term::{anon_id, Face, Identifier, System};
use crate::precise::term::{Mod, Term};
use crate::typechecker::check::{
    check, check_declaration_set, check_formula, check_plam, check_plam_system,
};
use crate::typechecker::context::TypeContext;
use crate::typechecker::error::{ErrorCause, TypeError};
use crate::typechecker::eval::{
    app_formula, comp_line, eval, eval_formula, eval_system, get_first,
};
use std::collections::HashMap;
use std::rc::Rc;

pub fn const_path(body: Rc<Term>) -> Rc<Term> {
    Rc::new(Term::PLam(anon_id(), body, Mod::Precise))
}

pub fn label_type(name: &Identifier, tpe: Rc<Term>) -> Result<Rc<Term>, TypeError> {
    let binding = tpe.clone();
    let (Term::Sum(_, labels, _) | Term::HSum(_, labels, _)) = binding.as_ref() else {
        Err(ErrorCause::Hole)?
    };
    let label = labels
        .iter()
        .find(|p| &p.name() == name)
        .ok_or(ErrorCause::Hole)?;
    let mut res = tpe;
    for (var, tpe) in label.telescope().variables.iter().rev() {
        res = Rc::new(Term::Pi(
            Rc::new(Term::Lam(var.clone(), tpe.clone(), res, Mod::Precise)),
            Mod::Precise,
        ))
    }
    Ok(res)
}

pub fn infer(ctx: TypeContext, term: &Term) -> Result<Rc<Term>, TypeError> {
    match term {
        Term::U => Ok(Rc::new(Term::U)),
        Term::Var(name, _) => Ok(ctx
            .lookup_term(name)
            .ok_or(ErrorCause::UnknownTermName(name.clone()))?
            .tpe),
        Term::App(f, a, _) => {
            let fun_tpe = infer(ctx.clone(), f)?;
            // println!("fun_tpe {:?}", fun_tpe);
            let Term::Pi(lam, _) = fun_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Lam(_, tpe, _, _) = lam.as_ref() else {
                Err(ErrorCause::Hole)?
            };

            check(ctx.clone(), a.clone(), tpe.clone())?;
            eval(ctx, &Term::App(lam.clone(), a.clone(), Mod::Precise))
        }
        Term::Fst(pair, _) => {
            let pair_tpe = infer(ctx, pair.as_ref())?;
            let Term::Sigma(pair_tpe, _) = pair_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let Term::Lam(_, param, _, _) = pair_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            Ok(Rc::new(param.as_ref().clone()))
        }
        Term::Snd(pair, _) => {
            let pair_tpe = infer(ctx.clone(), pair.as_ref())?;
            let Term::Sigma(lam, _) = pair_tpe.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            let p = eval(ctx.clone(), pair)?;
            eval(ctx, &Term::App(lam.clone(), get_first(p), Mod::Precise))
        }
        Term::Where(t, d, _) => {
            let new_ctx = check_declaration_set(ctx.clone(), d)?;
            infer(new_ctx, t)
        }
        Term::UnGlueElem(e, _, _) => {
            let glue_type = infer(ctx.clone(), e)?;
            let Term::Glue(t, _, _) = glue_type.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            Ok(t.clone())
        }
        Term::AppFormula(e, phi, _) => {
            check_formula(ctx.clone(), phi)?;
            let path_p = infer(ctx.clone(), e)?;
            let Term::PathP(a, _, _, _) = path_p.as_ref() else {
                Err(ErrorCause::Hole)?
            };
            app_formula(
                ctx.clone(),
                eval(ctx.clone(), a.as_ref())?,
                eval_formula(ctx.clone(), phi),
            )
        }
        Term::Split(_, tpe, _, _) => Ok(eval(ctx.clone(), tpe)?),
        Term::Comp(a, t0, ps, _) => {
            let (va0, va1) = check_plam(ctx.clone(), a.clone(), const_path(Rc::new(Term::U)))?;
            let va = eval(ctx.clone(), a)?;
            check(ctx.clone(), t0.clone(), va0)?;
            check_plam_system(ctx, t0.clone(), va, ps)?;
            Ok(va1)
        }
        Term::HComp(a, u0, us, _) => {
            check(ctx.clone(), a.clone(), Rc::new(Term::U))?;
            let va = eval(ctx.clone(), a)?;
            check(ctx.clone(), u0.clone(), va.clone())?;
            check_plam_system(ctx, u0.clone(), const_path(Rc::new(Term::U)), us)?;
            Ok(va)
        }
        Term::Fill(a, t0, ps, _) => {
            let (va0, _) = check_plam(ctx.clone(), a.clone(), const_path(Rc::new(Term::U)))?;
            let va = eval(ctx.clone(), a)?;
            check(ctx.clone(), t0.clone(), va0)?;
            check_plam_system(ctx.clone(), t0.clone(), va.clone(), ps)?;
            let vt = eval(ctx.clone(), t0)?;
            let vps = eval_system(ctx.clone(), ps)?;
            let line = comp_line(ctx, va.clone(), vt.clone(), vps)?;
            Ok(Rc::new(Term::PathP(va, vt, line, Mod::Precise)))
        }
        Term::PCon(c, a, es, phis, _) => {
            let va = eval(ctx.clone(), a.as_ref())?;

            check(ctx.clone(), va.clone(), Rc::new(Term::U))?;

            let con = label_type(c, va.clone())?;

            let mut con_type = con;
            let mut arg_ctx = ctx.clone();

            for arg in es {
                let Term::Pi(arg_lam, _) = &con_type.as_ref() else {
                    Err(ErrorCause::Hole)?
                };
                let Term::Lam(name, tpe, body, _) = arg_lam.as_ref() else {
                    Err(ErrorCause::Hole)?
                };
                let tpe = eval(arg_ctx.clone(), tpe)?;
                arg_ctx = arg_ctx.with_term(&name, arg, &tpe);
                con_type = body.clone();
                check(arg_ctx.clone(), arg.clone(), tpe)?;
            }

            for formula in phis {
                check_formula(ctx.clone(), formula)?
            }
            Ok(va)
        }
        Term::IdJ(a, u, c, d, x, p, _) => {
            check(ctx.clone(), a.clone(), Rc::new(Term::U))?;
            let va = eval(ctx.clone(), a)?;
            check(ctx.clone(), u.clone(), va.clone())?;
            let vu = eval(ctx.clone(), u)?;
            let refu = Rc::new(Term::IdPair(
                const_path(Rc::new(Term::U)),
                System {
                    binds: HashMap::from([(Face::eps(), vu.clone())]),
                },
                Mod::Precise,
            ));
            let z_lit = ctx.fresh();

            let z = Term::Var(z_lit, Mod::Precise);
            let ctype = eval(
                ctx.clone(),
                &Term::Pi(
                    Rc::new(Term::Lam(
                        z_lit,
                        a.clone(),
                        Rc::new(Term::Pi(
                            Rc::new(Term::Lam(
                                anon_id(),
                                Rc::new(Term::Id(a.clone(), u.clone(), Rc::new(z), Mod::Precise)),
                                Rc::new(Term::U),
                                Mod::Precise,
                            )),
                            Mod::Precise,
                        )),
                        Mod::Precise,
                    )),
                    Mod::Precise,
                ),
            )?;
            check(ctx.clone(), c.clone(), ctype)?;
            let vc = eval(ctx.clone(), c)?;

            check(
                ctx.clone(),
                d.clone(),
                eval(
                    ctx.clone(),
                    &Term::App(
                        Rc::new(Term::App(vc.clone(), vu.clone(), Mod::Precise)),
                        refu,
                        Mod::Precise,
                    ),
                )?,
            )?;
            check(ctx.clone(), x.clone(), va.clone())?;
            let vx = eval(ctx.clone(), x)?;
            check(
                ctx.clone(),
                p.clone(),
                Rc::new(Term::Id(va, vu, vx.clone(), Mod::Precise)),
            )?;
            let vp = eval(ctx.clone(), p)?;
            eval(
                ctx.clone(),
                &Term::App(Rc::new(Term::App(vc, vx, Mod::Precise)), vp, Mod::Precise),
            )
        }
        _ => panic!("uninferable state {:?}", term),
    }
}
