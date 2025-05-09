use crate::ctt::term::{Dir, Formula, Identifier, System};
use crate::precise::term::{Mod, Term};
use crate::typechecker::canon::eval::eval_formula;
use crate::typechecker::context::TypeContext;
use crate::typechecker::error::TypeError;
use std::collections::HashSet;
use std::rc::Rc;

use super::canon::app::{app, app_formula};
use super::canon::eval::{eval, get_first, get_second};
use super::canon::nominal::{border, Nominal};

pub trait Equiv {
    fn equiv(ctx: &TypeContext, lhs: Self, rhs: Self) -> Result<bool, TypeError>;
}

impl Equiv for &Rc<Term> {
    fn equiv(ctx: &TypeContext, lhs: Self, rhs: Self) -> Result<bool, TypeError> {
        match (lhs.as_ref(), rhs.as_ref()) {
            (l, r) if l == r => Ok(true),
            (Term::Lam(x, a, u, _), Term::Lam(x_, a_, u_, _)) => {
                let y = ctx.fresh();
                let eq_ctx = ctx.with_term(&y, &Term::var(y, Mod::Precise), a);

                let ctx_lhs = eq_ctx.with_term(x, &Term::var(y, Mod::Precise), a);
                let ctx_rhs = eq_ctx.with_term(x_, &Term::var(y, Mod::Precise), a_);

                Ok(Equiv::equiv(ctx, a, a_)?
                    && Equiv::equiv(&eq_ctx, &eval(&ctx_lhs, u)?, &eval(&ctx_rhs, u_)?)?)
            }
            (Term::Lam(x, tpe, u, _), _) => {
                let new_ctx = ctx.with_term(x, &Term::var(*x, Mod::Precise), tpe);

                Equiv::equiv(
                    &new_ctx,
                    &eval(
                        &new_ctx.with_term(x, &Rc::new(Term::Var(*x, Mod::Precise)), tpe),
                        u,
                    )?,
                    &app(&new_ctx, rhs, &Term::var(*x, Mod::Precise))?,
                )
            }
            (_, Term::Lam(x, tpe, u, _)) => {
                let new_ctx = ctx.with_term(x, &Term::var(*x, Mod::Precise), tpe);
                Equiv::equiv(
                    &new_ctx,
                    &app(&new_ctx, lhs, &Term::var(*x, Mod::Precise))?,
                    &eval(&new_ctx, u)?,
                )
            }
            (Term::Split(p, _, _, _), Term::Split(p_, _, _, _)) => Ok(p == p_),
            (Term::Sum(p, _, _), Term::Sum(p_, _, _)) => Ok(p == p_),
            (Term::HSum(p, _, _), Term::HSum(p_, _, _)) => Ok(p == p_),
            (Term::Undef(p, _), Term::Undef(p_, _)) => Ok(p == p_),
            (Term::Hole, Term::Hole) => Ok(false),
            (Term::Pi(lam1, _), Term::Pi(lam2, _)) => Equiv::equiv(ctx, lam1, lam2),
            (Term::Sigma(lam1, _), Term::Sigma(lam2, _)) => Equiv::equiv(ctx, lam1, lam2),
            (Term::Con(c, us, _), Term::Con(c_, us_, _)) => {
                let field_eq = us.len() == us_.len()
                    && us
                        .iter()
                        .zip(us_.iter())
                        .fold(Ok::<bool, TypeError>(true), |acc, (l, r)| {
                            Ok(acc? && Equiv::equiv(ctx, l, r)?)
                        })?;
                Ok(c == c_ && field_eq)
            }
            (Term::PCon(c, v, us, phis, _), Term::PCon(c_, v_, us_, phis_, _)) => {
                let field_eq = us.len() == us_.len()
                    && us
                        .iter()
                        .zip(us_.iter())
                        .fold(Ok::<bool, TypeError>(true), |acc, (l, r)| {
                            Ok(acc? && Equiv::equiv(ctx, l, r)?)
                        })?;

                let interval_eq = phis.len() == phis_.len()
                    && phis
                        .iter()
                        .zip(phis_.iter())
                        .fold(Ok::<bool, TypeError>(true), |acc, (l, r)| {
                            Ok(acc? && Equiv::equiv(ctx, l, r)?)
                        })?;

                Ok(c == c_ && field_eq && interval_eq && Equiv::equiv(ctx, v, v_)?)
            }
            (Term::Pair(u, v, _), Term::Pair(u_, v_, _)) => {
                Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, v, v_)?)
            }
            (Term::Pair(u, v, _), _) => {
                Ok(Equiv::equiv(ctx, u, &get_first(rhs))?
                    && Equiv::equiv(ctx, v, &get_second(rhs))?)
            }
            (_, Term::Pair(u, v, _)) => {
                Ok(Equiv::equiv(ctx, &get_first(lhs), u)?
                    && Equiv::equiv(ctx, &get_second(lhs), v)?)
            }
            (Term::Fst(u, _), Term::Fst(u_, _)) => Equiv::equiv(ctx, u, u_),
            (Term::Snd(u, _), Term::Snd(u_, _)) => Equiv::equiv(ctx, u, u_),
            (Term::App(u, v, _), Term::App(u_, v_, _)) => {
                Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, v, v_)?)
            }
            (Term::Var(x, _), Term::Var(x_, _)) => Ok(x == x_),
            (Term::PathP(a, b, c, _), Term::PathP(a_, b_, c_, _)) => Ok(Equiv::equiv(ctx, a, a_)?
                && Equiv::equiv(ctx, b, b_)?
                && Equiv::equiv(ctx, c, c_)?),
            (Term::PLam(i, a, _), Term::PLam(i_, a_, _)) => {
                let j = ctx.fresh();
                let ctx = ctx.with_formula(&j, Formula::Atom(j));
                Equiv::equiv(&ctx, &a.swap(i, &j), &a_.swap(i_, &j))
            }

            (Term::PLam(i, a, _), _) => {
                let j = ctx.fresh();
                let new_ctx = ctx.with_formula(&j, Formula::Atom(j));
                Equiv::equiv(
                    &new_ctx,
                    &a.swap(i, &j),
                    &app_formula(&new_ctx, rhs, Formula::Atom(j))?,
                )
            }
            (_, Term::PLam(i_, a_, _)) => {
                let j = ctx.fresh();
                let new_ctx = ctx.with_formula(&j, Formula::Atom(j));
                Equiv::equiv(
                    &new_ctx,
                    &app_formula(&new_ctx, lhs, Formula::Atom(j))?,
                    &a_.swap(i_, &j),
                )
            }
            (Term::AppFormula(u, x, _), Term::AppFormula(u_, x_, _)) => {
                Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, x, x_)?)
            }
            (Term::Comp(tpe1, u, es, _), Term::Comp(tpe2, u_, es_, _))
                if tpe1.as_ref() == &Term::U && tpe2.as_ref() == &Term::U =>
            {
                Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, es, es_)?)
            }
            (Term::Comp(a, u, ts, _), Term::Comp(a_, u_, ts_, _)) => Ok(Equiv::equiv(ctx, a, a_)?
                && Equiv::equiv(ctx, u, u_)?
                && Equiv::equiv(ctx, ts, ts_)?),
            (Term::HComp(a, u, ts, _), Term::HComp(a_, u_, ts_, _)) => {
                Ok(Equiv::equiv(ctx, a, a_)?
                    && Equiv::equiv(ctx, u, u_)?
                    && Equiv::equiv(ctx, ts, ts_)?)
            }
            (Term::Glue(v, equivs, _), Term::Glue(v_, equivs_, _)) => {
                Ok(Equiv::equiv(ctx, v, v_)? && Equiv::equiv(ctx, equivs, equivs_)?)
            }
            (Term::GlueElem(u, ts, _), other) => match (u.as_ref(), other) {
                (Term::UnGlueElem(b, equivs, _), _) | (Term::UnGlueElemU(b, _, equivs, _), _) => {
                    Ok(Equiv::equiv(ctx, &border(ctx, b, equivs)?, ts)?
                        && Equiv::equiv(ctx, b, rhs)?)
                }
                (_, Term::GlueElem(u_, us_, _)) => {
                    Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, ts, us_)?)
                }
                _ => Ok(false),
            },
            (other, Term::GlueElem(u, ts, _)) => match (u.as_ref(), other) {
                (Term::UnGlueElem(b, equivs, _), _) | (Term::UnGlueElemU(b, _, equivs, _), _) => {
                    Ok(Equiv::equiv(ctx, &border(ctx, b, equivs)?, ts)?
                        && Equiv::equiv(ctx, lhs, b)?)
                }
                (_, Term::GlueElem(u_, us_, _)) => {
                    Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, ts, us_)?)
                }
                _ => Ok(false),
            },
            (Term::UnGlueElem(u, _, _), Term::UnGlueElem(u_, _, _)) => Equiv::equiv(ctx, u, u_),
            (Term::UnGlueElemU(u, _, _, _), Term::UnGlueElemU(u_, _, _, _)) => {
                Equiv::equiv(ctx, u, u_)
            }
            (Term::IdPair(v, vs, _), Term::IdPair(v_, vs_, _)) => {
                Ok(Equiv::equiv(ctx, v, v_)? && Equiv::equiv(ctx, vs, vs_)?)
            }
            (Term::Id(a, u, v, _), Term::Id(a_, u_, v_, _)) => Ok(Equiv::equiv(ctx, a, a_)?
                && Equiv::equiv(ctx, u, u_)?
                && Equiv::equiv(ctx, v, v_)?),
            (Term::IdJ(a, u, c, d, x, p, _), Term::IdJ(a_, u_, c_, d_, x_, p_, _)) => {
                Ok(Equiv::equiv(ctx, a, a_)?
                    && Equiv::equiv(ctx, u, u_)?
                    && Equiv::equiv(ctx, c, c_)?
                    && Equiv::equiv(ctx, d, d_)?
                    && Equiv::equiv(ctx, x, x_)?
                    && Equiv::equiv(ctx, p, p_)?)
            }
            _ => Ok(false),
        }
    }
}

impl Equiv for &System<Term> {
    fn equiv(ctx: &TypeContext, lhs: Self, rhs: Self) -> Result<bool, TypeError> {
        // println!("System eq");
        if lhs.len() == rhs.len() {
            let mut eq = true;
            for (k, v1) in lhs.iter() {
                if let Some(v2) = rhs.get(k) {
                    if !Equiv::equiv(ctx, v1, v2)? {
                        eq = false;
                    }
                } else {
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
    fn equiv(ctx: &TypeContext, lhs: Self, rhs: Self) -> Result<bool, TypeError> {
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
            ctx: &TypeContext,
            l: &Formula,
            r: &Formula,
        ) -> bool {
            if i == atoms.len() {
                let mut new_ctx = ctx.clone();
                for j in 0..i {
                    new_ctx = new_ctx.with_formula(&atoms[j], Formula::Dir(dirs[j].clone()));
                }
                eval_formula(&new_ctx, l) == eval_formula(&new_ctx, r)
            } else {
                dirs[i] = Dir::Zero;
                let res_zero = inner(i + 1, atoms, dirs, ctx, l, r);
                dirs[i] = Dir::One;
                let res_one = inner(i + 1, atoms, dirs, ctx, l, r);
                res_zero && res_one
            }
        }
        let mut buffer = vec![Dir::Zero; atoms.len()];
        Ok(inner(0, &atoms, &mut buffer, ctx, lhs, rhs))
    }
}
