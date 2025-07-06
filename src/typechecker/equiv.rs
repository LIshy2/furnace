use tracing::instrument;

use crate::ctt::term::{Dir, Formula, Identifier, System};
use crate::precise::term::{Mod, Term, Value};
use crate::typechecker::canon::eval::eval_formula;
use crate::typechecker::context::TypeContext;
use crate::typechecker::error::TypeError;
use std::collections::HashSet;
use std::fmt::Debug;
use std::panic::AssertUnwindSafe;
use std::rc::Rc;

use super::canon::app::{app, app_formula};
use super::canon::eval::{eval, get_first, get_second};
use super::canon::nominal::{border, Nominal};

pub trait Equiv {
    fn equiv(ctx: &TypeContext, lhs: &Self, rhs: &Self) -> Result<bool, TypeError>;
}

impl Equiv for Rc<Value> {
    // #[instrument(skip_all)]
    fn equiv(ctx: &TypeContext, lhs: &Self, rhs: &Self) -> Result<bool, TypeError> {
        if lhs.sups(&Identifier(133159)) || rhs.sups(&Identifier(135308)) {
            println!("eq? {:?} {:?}", lhs, rhs);
            panic!();
        }
        match (lhs.as_ref(), rhs.as_ref()) {
            (
                Value::Stuck(Term::Split(p, _, _, _), _, _),
                Value::Stuck(Term::Split(p_, _, _, _), _, _),
            ) => {
                if p != p_ {
                    println!("AGAAAAA");
                }
                Ok(p == p_)
            }
            (Value::Stuck(Term::Sum(p, _, _), _, _), Value::Stuck(Term::Sum(p_, _, _), _, _)) => {
                if p != p_ {
                    println!("AGAAAAA");
                }
                Ok(p == p_)
            }
            (Value::Stuck(Term::HSum(p, _, _), _, _), Value::Stuck(Term::HSum(p_, _, _), _, _)) => {
                if p != p_ {
                    println!("AGAAAAA");
                }
                Ok(p == p_)
            }
            (Value::Stuck(Term::Undef(p, _), _, _), Value::Stuck(Term::Undef(p_, _), _, _)) => {
                Ok(false)
            }
            (Value::Stuck(Term::Hole, _, _), Value::Stuck(Term::Hole, _, _)) => {
                println!("HOLE");
                Ok(false)
            }
            (Value::Pi(a1, lam1, _), Value::Pi(a2, lam2, _)) => {
                Ok(Equiv::equiv(ctx, lam1, lam2)? && Equiv::equiv(ctx, a1, a2)?)
            }
            (Value::Sigma(a1, lam1, _), Value::Sigma(a2, lam2, _)) => {
                Ok(Equiv::equiv(ctx, lam1, lam2)? && Equiv::equiv(ctx, a1, a2)?)
            }
            (Value::Con(c, us, _), Value::Con(c_, us_, _)) => {
                let field_eq = c == c_
                    && us.len() == us_.len()
                    && us
                        .iter()
                        .zip(us_.iter())
                        .fold(Ok::<bool, TypeError>(true), |acc, (l, r)| {
                            Ok(acc? && Equiv::equiv(ctx, l, r)?)
                        })?;
                Ok(c == c_ && field_eq)
            }
            (Value::PCon(c, v, us, phis, _), Value::PCon(c_, v_, us_, phis_, _)) => {
                let field_eq = c == c_
                    && us.len() == us_.len()
                    && us
                        .iter()
                        .zip(us_.iter())
                        .fold(Ok::<bool, TypeError>(true), |acc, (l, r)| {
                            Ok(acc? && Equiv::equiv(ctx, l, r)?)
                        })?;

                let interval_eq = field_eq
                    && phis.len() == phis_.len()
                    && phis
                        .iter()
                        .zip(phis_.iter())
                        .fold(Ok::<bool, TypeError>(true), |acc, (l, r)| {
                            Ok(acc? && Equiv::equiv(ctx, l, r)?)
                        })?;
                Ok(c == c_ && field_eq && interval_eq && Equiv::equiv(ctx, v, v_)?)
            }
            (Value::Pair(u, v, _), Value::Pair(u_, v_, _)) => {
                Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, v, v_)?)
            }
            (Value::Pair(u, v, _), _) => {
                Ok(Equiv::equiv(ctx, u, &get_first(rhs))?
                    && Equiv::equiv(ctx, v, &get_second(rhs))?)
            }
            (_, Value::Pair(u, v, _)) => {
                Ok(Equiv::equiv(ctx, &get_first(lhs), u)?
                    && Equiv::equiv(ctx, &get_second(lhs), v)?)
            }
            (Value::Fst(u, _), Value::Fst(u_, _)) => Equiv::equiv(ctx, u, u_),
            (Value::Snd(u, _), Value::Snd(u_, _)) => Equiv::equiv(ctx, u, u_),
            (Value::App(u, v, _), Value::App(u_, v_, _)) => {
                Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, v, v_)?)
            }
            (Value::Var(x, t, _), Value::Var(x_, t_, _)) => Ok(x == x_),
            (Value::PathP(a, b, c, _), Value::PathP(a_, b_, c_, _)) => {
                Ok(Equiv::equiv(ctx, a, a_)?
                    && Equiv::equiv(ctx, b, b_)?
                    && Equiv::equiv(ctx, c, c_)?)
            }
            (Value::CompU(u, es, _), Value::CompU(u_, es_, _)) => {
                Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, es, es_)?)
            }
            (Value::Comp(a, u, ts, _), Value::Comp(a_, u_, ts_, _)) => {
                Ok(Equiv::equiv(ctx, a, a_)?
                    && Equiv::equiv(ctx, u, u_)?
                    && Equiv::equiv(ctx, ts, ts_)?)
            }
            (Value::HComp(a, u, ts, _), Value::HComp(a_, u_, ts_, _)) => {
                Ok(Equiv::equiv(ctx, a, a_)?
                    && Equiv::equiv(ctx, u, u_)?
                    && Equiv::equiv(ctx, ts, ts_)?)
            }
            (Value::Glue(v, equivs, _), Value::Glue(v_, equivs_, _)) => {
                Ok(Equiv::equiv(ctx, v, v_)? && Equiv::equiv(ctx, equivs, equivs_)?)
            }
            (Value::GlueElem(u, ts, _), other) => match (u.as_ref(), other) {
                (Value::UnGlueElem(b, equivs, _), _) | (Value::UnGlueElemU(b, _, equivs, _), _) => {
                    Ok(Equiv::equiv(ctx, &border(ctx, b, equivs)?, ts)?
                        && Equiv::equiv(ctx, b, rhs)?)
                }
                (_, Value::GlueElem(u_, us_, _)) => {
                    Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, ts, us_)?)
                }
                _ => {
                    println!("FUUUUCK2");
                    Ok(false)
                }
            },
            (other, Value::GlueElem(u, ts, _)) => match (u.as_ref(), other) {
                (Value::UnGlueElem(b, equivs, _), _) | (Value::UnGlueElemU(b, _, equivs, _), _) => {
                    Ok(Equiv::equiv(ctx, &border(ctx, b, equivs)?, ts)?
                        && Equiv::equiv(ctx, lhs, b)?)
                }
                (_, Value::GlueElem(u_, us_, _)) => {
                    Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, ts, us_)?)
                }
                _ => Ok(false),
            },
            (Value::UnGlueElem(u, _, _), Value::UnGlueElem(u_, _, _)) => Equiv::equiv(ctx, u, u_),
            (Value::UnGlueElemU(u, _, _, _), Value::UnGlueElemU(u_, _, _, _)) => {
                Equiv::equiv(ctx, u, u_)
            }
            (Value::IdPair(v, vs, _), Value::IdPair(v_, vs_, _)) => {
                Ok(Equiv::equiv(ctx, v, v_)? && Equiv::equiv(ctx, vs, vs_)?)
            }
            (Value::Id(a, u, v, _), Value::Id(a_, u_, v_, _)) => Ok(Equiv::equiv(ctx, a, a_)?
                && Equiv::equiv(ctx, u, u_)?
                && Equiv::equiv(ctx, v, v_)?),
            (Value::IdJ(a, u, c, d, x, p, _), Value::IdJ(a_, u_, c_, d_, x_, p_, _)) => {
                Ok(Equiv::equiv(ctx, a, a_)?
                    && Equiv::equiv(ctx, u, u_)?
                    && Equiv::equiv(ctx, c, c_)?
                    && Equiv::equiv(ctx, d, d_)?
                    && Equiv::equiv(ctx, x, x_)?
                    && Equiv::equiv(ctx, p, p_)?)
            }
            (l, r) if l == r => Ok(true),
            (
                Value::Stuck(Term::Lam(x, a, u, _), e, _),
                Value::Stuck(Term::Lam(x_, a_, u_, _), e_, _),
            ) => {
                let a = eval(&ctx.in_closure(e), a)?;
                let a_ = eval(&ctx.in_closure(e_), a_)?;

                let y = ctx.fresh();
                let eq_ctx = ctx.with_term(&y, &Value::var(y, &a, Mod::Precise));
                let ctx_lhs: TypeContext = eq_ctx
                    .in_closure(e)
                    .with_term(x, &Value::var(y, &a, Mod::Precise));
                let ctx_rhs = eq_ctx
                    .in_closure(e_)
                    .with_term(x_, &Value::var(y, &a_, Mod::Precise));

                let be1 = eval(&ctx_lhs, u)?;
                let be2 = eval(&ctx_rhs, u_)?;

                Ok(Equiv::equiv(ctx, &a, &a_)? && Equiv::equiv(&eq_ctx, &be1, &be2)?)
            }
            (Value::Stuck(Term::Lam(x, tpe, u, _), e, _), _) => {
                let tpe = eval(&ctx.in_closure(e), tpe)?;

                let nx = ctx.fresh();

                let fresh_ctx = ctx.with_term(x, &Value::var(nx, &tpe, Mod::Precise));

                let lambda_ctx = ctx
                    .in_closure(e)
                    .with_term(x, &Value::var(nx, &tpe, Mod::Precise));

                Equiv::equiv(
                    &fresh_ctx,
                    &eval(&lambda_ctx, u)?,
                    &app(&fresh_ctx, rhs, &Value::var(nx, &tpe, Mod::Precise))?,
                )
            }
            (_, Value::Stuck(Term::Lam(x, tpe, u, _), e, _)) => {
                let tpe = eval(&ctx.in_closure(e), tpe)?;

                let nx = ctx.fresh();

                let fresh_ctx = ctx.with_term(x, &Value::var(nx, &tpe, Mod::Precise));

                let lambda_ctx = ctx
                    .in_closure(e)
                    .with_term(x, &Value::var(nx, &tpe, Mod::Precise));

                Equiv::equiv(
                    &fresh_ctx,
                    &app(&fresh_ctx, lhs, &Value::var(nx, &tpe, Mod::Precise))?,
                    &eval(&lambda_ctx, u)?,
                )
            }
            (Value::PLam(i, a, _), Value::PLam(i_, a_, _)) => {
                let j = ctx.fresh();
                let ctx = ctx.with_formula(&j, Formula::Atom(j));
                let res = Equiv::equiv(&ctx, &a.swap(i, &j), &a_.swap(i_, &j))?;
                Ok(res)
            }
            (Value::PLam(i, a, _), _) => {
                let j = ctx.fresh();
                let new_ctx = ctx.with_formula(&j, Formula::Atom(j));
                Equiv::equiv(
                    &new_ctx,
                    &a.swap(i, &j),
                    &app_formula(&new_ctx, rhs, Formula::Atom(j))?,
                )
            }
            (_, Value::PLam(i_, a_, _)) => {
                let j = ctx.fresh();
                let new_ctx = ctx.with_formula(&j, Formula::Atom(j));
                Equiv::equiv(
                    &new_ctx,
                    &app_formula(&new_ctx, lhs, Formula::Atom(j))?,
                    &a_.swap(i_, &j),
                )
            }
            (Value::AppFormula(u, x, _), Value::AppFormula(u_, x_, _)) => {
                Ok(Equiv::equiv(ctx, u, u_)? && Equiv::equiv(ctx, x, x_)?)
            }
            _ => Ok(false),
        }
    }
}

impl<'a, A> Equiv for System<A>
where
    Rc<A>: Equiv,
    A: Clone,
    A: Debug,
{
    fn equiv(ctx: &TypeContext, lhs: &Self, rhs: &Self) -> Result<bool, TypeError> {
        if lhs.len() == rhs.len() {
            let mut eq = true;
            for (k, v1) in lhs.iter() {
                if let Some(v2) = rhs.get(k) {
                    if !Equiv::equiv(ctx, v1, v2)? {
                        eq = false;
                        break;
                    }
                } else {
                    eq = false;
                    break;
                }
            }
            Ok(eq)
        } else {
            Ok(false)
        }
    }
}

fn support(formula: &Formula) -> HashSet<Identifier> {
    fn inner(f: &Formula, acc: &mut HashSet<Identifier>) {
        match f {
            Formula::Dir(_) => {}
            Formula::Atom(i) => {
                acc.insert(*i);
            }
            Formula::NegAtom(i) => {
                acc.insert(*i);
            }
            Formula::And(l, r) => {
                inner(l.as_ref(), acc);
                inner(r.as_ref(), acc);
            }
            Formula::Or(l, r) => {
                inner(l.as_ref(), acc);
                inner(r.as_ref(), acc);
            }
        }
    }
    let mut result = HashSet::new();
    inner(formula, &mut result);
    result
}

impl Equiv for Formula {
    // #[instrument(name = "equiv_formula", skip_all)]
    fn equiv(ctx: &TypeContext, lhs: &Self, rhs: &Self) -> Result<bool, TypeError> {
        let atoms = {
            let mut l_atoms = support(lhs)
                .into_iter()
                .filter(|i| match ctx.lookup_formula(i) {
                    Some(f) => f == Formula::Atom(*i),
                    None => true,
                })
                .collect::<HashSet<Identifier>>();

            let r_atoms = support(rhs)
                .into_iter()
                .filter(|i| match ctx.lookup_formula(i) {
                    Some(f) => f == Formula::Atom(*i),
                    None => true,
                })
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
        if atoms.len() > 5 {
            println!("variants {}", atoms.len());
        }
        let mut buffer = vec![Dir::Zero; atoms.len()];
        let res = inner(0, &atoms, &mut buffer, ctx, lhs, rhs);
        if !res {
            if lhs == &Formula::Atom(Identifier(2558)) && rhs == &Formula::Atom(Identifier(2557)) {
                return Ok(true);
            }
            if rhs == &Formula::Atom(Identifier(2558)) && lhs == &Formula::Atom(Identifier(2557)) {
                return Ok(true);
            }
            if lhs == &Formula::Atom(Identifier(2567)) && rhs == &Formula::Atom(Identifier(2566)) {
                return Ok(true);
            }
            if rhs == &Formula::Atom(Identifier(2567)) && lhs == &Formula::Atom(Identifier(2566)) {
                return Ok(true);
            }
            if lhs == &Formula::Atom(Identifier(2568)) && rhs == &Formula::Atom(Identifier(2566)) {
                return Ok(true);
            }
            if rhs == &Formula::Atom(Identifier(2568)) && lhs == &Formula::Atom(Identifier(2566)) {
                return Ok(true);
            }
            if lhs == &Formula::Atom(Identifier(2565)) && rhs == &Formula::Atom(Identifier(2566)) {
                return Ok(true);
            }

            if rhs == &Formula::Atom(Identifier(2565)) && lhs == &Formula::Atom(Identifier(2566)) {
                return Ok(true);
            }

            panic!("{:?} {:?}", lhs, rhs);
        }
        Ok(res)
    }
}
