use crate::ctt::term::{Dir, Formula, Identifier, System};
use crate::precise::term::{Mod, Term};
use crate::typechecker::context::TypeContext;
use crate::typechecker::error::TypeError;
use crate::typechecker::eval::{
    app, app_formula, border, eval, eval_formula, get_first, get_second,
};
use crate::typechecker::nominal::Nominal;
use std::collections::HashSet;
use std::rc::Rc;

pub trait Equiv {
    fn equiv(ctx: TypeContext, lhs: Self, rhs: Self) -> Result<bool, TypeError>;
}

impl Equiv for Rc<Term> {
    fn equiv(ctx: TypeContext, lhs: Self, rhs: Self) -> Result<bool, TypeError> {
        // println!("eq? {:?} === {:?}", lhs.as_ref(), rhs.as_ref());

        match (lhs.as_ref(), rhs.as_ref()) {
            (l, r) if l == r => Ok(true),
            (Term::Lam(x, a, u, _), Term::Lam(x_prime, a_prime, u_prime, _)) => {
                let y = ctx.fresh();
                let eq_ctx = ctx.with_term(&y, &Rc::new(Term::Var(y.clone(), Mod::Precise)), a);

                let ctx_lhs = eq_ctx.with_term(x, &Rc::new(Term::Var(y.clone(), Mod::Precise)), a);
                let ctx_rhs = eq_ctx.with_term(
                    x_prime,
                    &Rc::new(Term::Var(y.clone(), Mod::Precise)),
                    a_prime,
                );

                Ok(Equiv::equiv(ctx.clone(), a.clone(), a_prime.clone())?
                    && Equiv::equiv(eq_ctx.clone(), eval(ctx_lhs, u)?, eval(ctx_rhs, u_prime)?)?)
            }
            (Term::Lam(x, tpe, u, _), _) => {
                let new_ctx = ctx.with_term(&x, &Rc::new(Term::Var(x.clone(), Mod::Precise)), tpe);

                Equiv::equiv(
                    new_ctx.clone(),
                    eval(
                        new_ctx.with_term(&x, &Rc::new(Term::Var(x.clone(), Mod::Precise)), tpe),
                        u,
                    )?,
                    app(new_ctx.clone(), rhs, Rc::new(Term::Var(x.clone(), Mod::Precise)))?,
                )
            }
            (_, Term::Lam(x, tpe, u, _)) => {
                let new_ctx = ctx.with_term(&x, &Rc::new(Term::Var(x.clone(), Mod::Precise)), tpe);
                Equiv::equiv(
                    new_ctx.clone(),
                    app(new_ctx.clone(), lhs, Rc::new(Term::Var(x.clone(), Mod::Precise)))?,
                    eval(new_ctx, u)?,
                )
            }
            (Term::Split(p, _, _, _), Term::Split(p_prime, _, _, _)) => Ok(p == p_prime),
            (Term::Sum(p, _, _), Term::Sum(p_prime, _, _)) => Ok(p == p_prime),
            (Term::HSum(p, _, _), Term::HSum(p_prime, _, _)) => Ok(p == p_prime),
            (Term::Undef(p, _), Term::Undef(p_prime, _)) => Ok(p == p_prime),
            (Term::Hole, Term::Hole) => Ok(false),
            (Term::Pi(lam1, _), Term::Pi(lam2, _)) => Equiv::equiv(ctx, lam1.clone(), lam2.clone()),
            (Term::Sigma(lam1, _), Term::Sigma(lam2, _)) => {
                Equiv::equiv(ctx, lam1.clone(), lam2.clone())
            }
            (Term::Con(c, us, _), Term::Con(c_prime, us_prime, _)) => {
                let field_eq = us.len() == us_prime.len()
                    && us
                        .iter()
                        .zip(us_prime.iter())
                        .fold(Ok::<bool, TypeError>(true), |acc, (l, r)| {
                            Ok(acc? && Equiv::equiv(ctx.clone(), l.clone(), r.clone())?)
                        })?;
                Ok(c == c_prime && field_eq)
            }
            (
                Term::PCon(c, v, us, phis, _),
                Term::PCon(c_prime, v_prime, us_prime, phis_prime, _),
            ) => {
                let field_eq = us.len() == us_prime.len()
                    && us
                        .iter()
                        .zip(us_prime.iter())
                        .fold(Ok::<bool, TypeError>(true), |acc, (l, r)| {
                            Ok(acc? && Equiv::equiv(ctx.clone(), l.clone(), r.clone())?)
                        })?;

                let interval_eq = phis.len() == phis_prime.len()
                    && phis
                        .iter()
                        .zip(phis_prime.iter())
                        .fold(Ok::<bool, TypeError>(true), |acc, (l, r)| {
                            Ok(acc? && Equiv::equiv(ctx.clone(), l, r)?)
                        })?;

                Ok(c == c_prime
                    && field_eq
                    && interval_eq
                    && Equiv::equiv(ctx, v.clone(), v_prime.clone())?)
            }
            (Term::Pair(u, v, _), Term::Pair(u_prime, v_prime, _)) => {
                Ok(Equiv::equiv(ctx.clone(), u.clone(), u_prime.clone())?
                    && Equiv::equiv(ctx, v.clone(), v_prime.clone())?)
            }
            (Term::Pair(u, v, _), _) => Ok(Equiv::equiv(
                ctx.clone(),
                u.clone(),
                get_first(rhs.clone()),
            )? && Equiv::equiv(ctx, v.clone(), get_second(rhs))?),
            (_, Term::Pair(u, v, _)) => Ok(Equiv::equiv(
                ctx.clone(),
                get_first(lhs.clone()),
                u.clone(),
            )? && Equiv::equiv(ctx, get_second(lhs), v.clone())?),
            (Term::Fst(u, _), Term::Fst(u_prime, _)) => {
                Equiv::equiv(ctx, u.clone(), u_prime.clone())
            }
            (Term::Snd(u, _), Term::Snd(u_prime, _)) => {
                Equiv::equiv(ctx, u.clone(), u_prime.clone())
            }
            (Term::App(u, v, _), Term::App(u_prime, v_prime, _)) => {
                Ok(Equiv::equiv(ctx.clone(), u.clone(), u_prime.clone())?
                    && Equiv::equiv(ctx.clone(), v.clone(), v_prime.clone())?)
            }
            (Term::Var(x, _), Term::Var(x_prime, _)) => Ok(x == x_prime),
            (Term::PathP(a, b, c, _), Term::PathP(a_prime, b_prime, c_prime, _)) => {
                Ok(Equiv::equiv(ctx.clone(), a.clone(), a_prime.clone())?
                    && Equiv::equiv(ctx.clone(), b.clone(), b_prime.clone())?
                    && Equiv::equiv(ctx, c.clone(), c_prime.clone())?)
            }
            (Term::PLam(i, a, _), Term::PLam(i_prime, a_prime, _)) => {
                let j = ctx.fresh();
                let ctx = ctx.with_formula(&j, Formula::Atom(j));
                Equiv::equiv(ctx, a.swap(i, &j), a_prime.swap(i_prime, &j))
            }

            (Term::PLam(i, a, _), _) => {
                let j = ctx.fresh();
                let new_ctx = ctx.with_formula(&j, Formula::Atom(j));
                Equiv::equiv(
                    new_ctx.clone(),
                    a.swap(i, &j),
                    app_formula(new_ctx, rhs, Formula::Atom(j.clone()))?,
                )
            }
            (_, Term::PLam(i_prime, a_prime, _)) => {
                let j = ctx.fresh();
                let new_ctx = ctx.with_formula(&j, Formula::Atom(j));
                Equiv::equiv(
                    new_ctx.clone(),
                    app_formula(new_ctx, lhs, Formula::Atom(j.clone()))?,
                    a_prime.swap(i_prime, &j),
                )
            }
            (Term::AppFormula(u, x, _), Term::AppFormula(u_prime, x_prime, _)) => {
                Ok(Equiv::equiv(ctx.clone(), u.clone(), u_prime.clone())?
                    && Equiv::equiv(ctx, x, x_prime)?)
            }
            (Term::Comp(a, u, ts, _), Term::Comp(a_prime, u_prime, ts_prime, _)) => {
                Ok(Equiv::equiv(ctx.clone(), a.clone(), a_prime.clone())?
                    && Equiv::equiv(ctx.clone(), u.clone(), u_prime.clone())?
                    && Equiv::equiv(ctx, ts, ts_prime)?)
            }
            (Term::HComp(a, u, ts, _), Term::HComp(a_prime, u_prime, ts_prime, _)) => {
                Ok(Equiv::equiv(ctx.clone(), a.clone(), a_prime.clone())?
                    && Equiv::equiv(ctx.clone(), u.clone(), u_prime.clone())?
                    && Equiv::equiv(ctx, ts, ts_prime)?)
            }
            (Term::Glue(v, equivs, _), Term::Glue(v_prime, equivs_prime, _)) => {
                Ok(Equiv::equiv(ctx.clone(), v.clone(), v_prime.clone())?
                    && Equiv::equiv(ctx, equivs, equivs_prime)?)
            }
            (Term::GlueElem(u, ts, _), other) => match (u.as_ref(), other) {
                (Term::UnGlueElem(b, equivs, _), _) | (Term::UnGlueElemU(b, _, equivs, _), _) => {
                    Ok(
                        Equiv::equiv(ctx.clone(), &border(ctx.clone(), b.clone(), equivs)?, ts)?
                            && Equiv::equiv(ctx.clone(), b.clone(), rhs)?,
                    )
                }
                (_, Term::GlueElem(u_prime, us_prime, _)) => {
                    Ok(Equiv::equiv(ctx.clone(), u.clone(), u_prime.clone())?
                        && Equiv::equiv(ctx, ts, us_prime)?)
                }
                _ => Ok(false),
            },
            (other, Term::GlueElem(u, ts, _)) => match (u.as_ref(), other) {
                (Term::UnGlueElem(b, equivs, _), _) | (Term::UnGlueElemU(b, _, equivs, _), _) => {
                    Ok(
                        Equiv::equiv(ctx.clone(), &border(ctx.clone(), b.clone(), equivs)?, ts)?
                            && Equiv::equiv(ctx.clone(), lhs, b.clone())?,
                    )
                }
                (_, Term::GlueElem(u_prime, us_prime, _)) => {
                    Ok(Equiv::equiv(ctx.clone(), u.clone(), u_prime.clone())?
                        && Equiv::equiv(ctx, ts, us_prime)?)
                }
                _ => Ok(false),
            },
            (Term::UnGlueElem(u, _, _), Term::UnGlueElem(u_prime, _, _)) => {
                Equiv::equiv(ctx, u.clone(), u_prime.clone())
            }
            (Term::UnGlueElemU(u, _, _, _), Term::UnGlueElemU(u_prime, _, _, _)) => {
                Equiv::equiv(ctx, u.clone(), u_prime.clone())
            }
            (Term::Comp(tpe1, u, es, _), Term::Comp(tpe2, u_prime, es_prime, _))
                if tpe1.as_ref() == &Term::U && tpe2.as_ref() == &Term::U =>
            {
                Ok(Equiv::equiv(ctx.clone(), u.clone(), u_prime.clone())?
                    && Equiv::equiv(ctx, es, es_prime)?)
            }
            (Term::IdPair(v, vs, _), Term::IdPair(v_prime, vs_prime, _)) => {
                Ok(Equiv::equiv(ctx.clone(), v.clone(), v_prime.clone())?
                    && Equiv::equiv(ctx, vs, vs_prime)?)
            }
            (Term::Id(a, u, v, _), Term::Id(a_prime, u_prime, v_prime, _)) => {
                Ok(Equiv::equiv(ctx.clone(), a.clone(), a_prime.clone())?
                    && Equiv::equiv(ctx.clone(), u.clone(), u_prime.clone())?
                    && Equiv::equiv(ctx, v.clone(), v_prime.clone())?)
            }
            (
                Term::IdJ(a, u, c, d, x, p, _),
                Term::IdJ(a_prime, u_prime, c_prime, d_prime, x_prime, p_prime, _),
            ) => Ok(Equiv::equiv(ctx.clone(), a.clone(), a_prime.clone())?
                && Equiv::equiv(ctx.clone(), u.clone(), u_prime.clone())?
                && Equiv::equiv(ctx.clone(), c.clone(), c_prime.clone())?
                && Equiv::equiv(ctx.clone(), d.clone(), d_prime.clone())?
                && Equiv::equiv(ctx.clone(), x.clone(), x_prime.clone())?
                && Equiv::equiv(ctx.clone(), p.clone(), p_prime.clone())?),
            _ => Ok(false),
        }
    }
}

impl Equiv for &System<Term> {
    fn equiv(ctx: TypeContext, lhs: Self, rhs: Self) -> Result<bool, TypeError> {
        // println!("System eq");
        if lhs.binds.keys().len() == rhs.binds.keys().len() {
            let mut eq = true;
            for (k, v1) in lhs.binds.iter() {
                if let Some(v2) = rhs.binds.get(k) {
                    if !Equiv::equiv(ctx.clone(), v1.clone(), v2.clone())? {
                        eq = false;
                    }
                } else {
                    // println!("NOT FOUND");
                    eq = false;
                }
            }
            Ok(eq)
        } else {
            Ok(false)
        }
    }
}

impl Equiv for &Formula {
    fn equiv(ctx: TypeContext, lhs: Self, rhs: Self) -> Result<bool, TypeError> {
        let atoms = {
            let mut l_atoms = lhs
                .support()
                .into_iter()
                .filter(|i| ctx.lookup_formula(i).is_none())
                .collect::<HashSet<Identifier>>();

            let r_atoms = rhs
                .support()
                .into_iter()
                .filter(|i| ctx.lookup_formula(i).is_none())
                .collect::<HashSet<Identifier>>();

            l_atoms.extend(r_atoms);
            l_atoms.into_iter().collect::<Vec<_>>()
        };

        fn inner(
            i: usize,
            atoms: &[Identifier],
            dirs: &mut [Dir],
            ctx: TypeContext,
            l: &Formula,
            r: &Formula,
        ) -> bool {
            if i == atoms.len() {
                let mut new_ctx = ctx;
                for j in 0..i {
                    new_ctx = new_ctx.with_formula(&atoms[j], Formula::Dir(dirs[j].clone()));
                }
                eval_formula(new_ctx.clone(), l) == eval_formula(new_ctx.clone(), r)
            } else {
                dirs[i] = Dir::Zero;
                let res_zero = inner(i + 1, atoms, dirs, ctx.clone(), l, r);
                dirs[i] = Dir::One;
                let res_one = inner(i + 1, atoms, dirs, ctx, l, r);
                res_zero && res_one
            }
        }
        let mut buffer = vec![Dir::Zero; atoms.len()];
        Ok(inner(0, &atoms, &mut buffer, ctx, lhs, rhs))
    }
}
