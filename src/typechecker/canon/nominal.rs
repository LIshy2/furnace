use crate::ctt::term::{Branch, Face, Formula, Identifier, System};
use crate::precise::term::{Mod, Term};
use crate::typechecker::canon::app::{app, app_formula};
use crate::typechecker::canon::comp::{comp_line, hcomp};
use crate::typechecker::canon::eval::{get_first, get_second, inv_formula, pcon};
use crate::typechecker::canon::glue::{glue, glue_elem, unglue_elem, unglue_u};
use crate::typechecker::context::TypeContext;
use crate::typechecker::error::TypeError;
use std::collections::HashMap;
use std::rc::Rc;

pub trait Nominal: Sized {
    fn support(&self) -> Vec<Identifier>;

    fn act(&self, ctx: &TypeContext, i: &Identifier, f: Formula) -> Result<Self, TypeError>;

    fn swap(&self, from: &Identifier, to: &Identifier) -> Self;
}

impl Nominal for Rc<Term> {
    fn support(&self) -> Vec<Identifier> {
        let mut result = Vec::new();
        match self.as_ref() {
            Term::Pi(t, _) => result.extend(t.support()),
            Term::App(t1, t2, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
            }
            Term::Lam(_, t1, t2, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
            }
            Term::Where(t, _, _) => result.extend(t.support()),
            Term::Var(_, _) => (),
            Term::U => (),
            Term::Sigma(t, _) => result.extend(t.support()),
            Term::Pair(t1, t2, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
            }
            Term::Fst(t, _) => result.extend(t.support()),
            Term::Snd(t, _) => result.extend(t.support()),
            Term::Con(_, ts, _) => {
                for t in ts {
                    result.extend(t.support());
                }
            }
            Term::PCon(_, t, ts, is, _) => {
                result.extend(t.support());
                for t in ts {
                    result.extend(t.support());
                }
                for i in is {
                    result.extend(i.support());
                }
            }
            Term::Split(_, t, branches, _) => {
                result.extend(t.support());
                for branch in branches {
                    match branch {
                        Branch::OBranch(_, _, b) => result.extend(b.support()),
                        Branch::PBranch(_, _, _, b) => result.extend(b.support()),
                    }
                }
            }
            Term::Sum(_, _, _) => (),
            Term::HSum(_, _, _) => (),
            Term::Undef(t, _) => result.extend(t.support()),
            Term::Hole => (),
            Term::PathP(t1, t2, t3, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(t3.support());
            }
            Term::PLam(n, t, _) => result.extend(t.support().iter().filter(|x| x != &n)),
            Term::AppFormula(t, f, _) => {
                result.extend(t.support());
                result.extend(f.support())
            }
            Term::Comp(t1, t2, system, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(system.support());
            }
            Term::Fill(t1, t2, system, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(system.support());
            }
            Term::HComp(t1, t2, system, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(system.support());
            }
            Term::Glue(t, system, _) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Term::GlueElem(t, system, _) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Term::UnGlueElem(t, system, _) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Term::UnGlueElemU(t, b, system, _) => {
                result.extend(t.support());
                result.extend(b.support());
                result.extend(system.support());
            }
            Term::Id(t1, t2, t3, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(t3.support());
            }
            Term::IdPair(t, system, _) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Term::IdJ(t1, t2, t3, t4, t5, t6, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(t3.support());
                result.extend(t3.support());
                result.extend(t4.support());
                result.extend(t5.support());
                result.extend(t6.support());
            }
        }

        result
    }

    fn act(&self, ctx: &TypeContext, i: &Identifier, f: Formula) -> Result<Self, TypeError> {
        fn act_formula(
            ctx: &TypeContext,
            o: &Formula,
            i: &Identifier,
            f: Formula,
        ) -> Result<Option<Formula>, TypeError> {
            if o.support().contains(i) {
                Ok(Some(o.act(ctx, i, f)?))
            } else {
                Ok(None)
            }
        }

        fn act_system(
            ctx: &TypeContext,
            o: &System<Term>,
            i: &Identifier,
            f: Formula,
        ) -> Result<Option<System<Term>>, TypeError> {
            if o.support().contains(i) {
                Ok(Some(o.act(ctx, i, f)?))
            } else {
                Ok(None)
            }
        }

        match self.as_ref() {
            Term::Pi(u, m) => {
                let new_u = u.act(ctx, i, f)?;
                if Rc::ptr_eq(u, &new_u) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Pi(new_u, m.clone())))
                }
            }
            Term::App(a, b, _) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_b = b.act(ctx, i, f)?;
                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(b, &new_b) {
                    Ok(self.clone())
                } else {
                    app(ctx, &new_a, &new_b)
                }
            }
            Term::Lam(x, t, u, m) => {
                let new_t = t.act(ctx, i, f.clone())?;
                let in_body_ctx =
                    ctx.with_term(x, &Rc::new(Term::Var(*x, Mod::Precise)), &new_t);
                let new_u = u.act(&in_body_ctx, i, f)?;

                if Rc::ptr_eq(t, &new_t) && Rc::ptr_eq(u, &new_u) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Lam(*x, new_t, new_u, m.clone())))
                }
            }
            Term::Sigma(t, m) => {
                let new_t = t.act(ctx, i, f)?;
                if Rc::ptr_eq(t, &new_t) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Sigma(new_t, m.clone())))
                }
            }
            Term::Pair(fst, snd, m) => {
                let new_fst = fst.act(ctx, i, f.clone())?;
                let new_snd = snd.act(ctx, i, f)?;
                if Rc::ptr_eq(fst, &new_fst) && Rc::ptr_eq(snd, &new_snd) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Pair(new_fst, new_snd, m.clone())))
                }
            }
            Term::Fst(v, _) => {
                let new_v = v.act(ctx, i, f)?;
                if Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(get_first(&new_v))
                }
            }
            Term::Snd(v, _) => {
                let new_v = v.act(ctx, i, f)?;
                if Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(get_second(&new_v))
                }
            }
            Term::Con(c, a, m) => {
                let mut changed = false;
                let new_a = a
                    .iter()
                    .map(|x| {
                        let new_x = x.act(ctx, i, f.clone())?;
                        if !Rc::ptr_eq(x, &new_x) {
                            changed = true;
                        }
                        Ok(new_x)
                    })
                    .collect::<Result<Vec<_>, TypeError>>()?;

                if !changed {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Con(*c, new_a, m.clone())))
                }
            }
            Term::PCon(c, t, vs, phis, m) => {
                let new_t = t.act(ctx, i, f.clone())?;
                let mut changed = !Rc::ptr_eq(t, &new_t);

                let new_vs = vs
                    .iter()
                    .map(|x| {
                        let new_x = x.act(ctx, i, f.clone())?;
                        if !Rc::ptr_eq(x, &new_x) {
                            changed = true;
                        }
                        Ok(new_x)
                    })
                    .collect::<Result<Vec<_>, TypeError>>()?;
                let new_phis = phis
                    .iter()
                    .map(|x| {
                        if x.support().contains(i) {
                            let new_x = x.act(ctx, i, f.clone())?;
                            changed = true;
                            Ok(new_x)
                        } else {
                            Ok(x.clone())
                        }
                    })
                    .collect::<Result<Vec<_>, TypeError>>()?;

                if !changed {
                    Ok(self.clone())
                } else {
                    pcon(ctx, c, &new_t, new_vs, new_phis, m.clone())
                }
            }
            Term::Split(c, t, b, m) => {
                let new_t = t.act(ctx, i, f)?;
                if Rc::ptr_eq(t, &new_t) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Split(*c, new_t, b.clone(), m.clone())))
                }
            }
            Term::PathP(a, u, v, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_u = u.act(ctx, i, f.clone())?;
                let new_v = v.act(ctx, i, f)?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(u, &new_u) && Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::PathP(new_a, new_u, new_v, m.clone())))
                }
            }
            Term::PLam(j, v, m) => {
                if j == i {
                    Ok(self.clone())
                } else {
                    let sphi = v.support();
                    sphi.contains(j); 
                    let new_v = v.act(ctx, i, f)?;
                    if Rc::ptr_eq(v, &new_v) {
                        Ok(self.clone())
                    } else {
                        Ok(Rc::new(Term::PLam(*j, new_v, m.clone())))
                    }
                }
            }
            Term::AppFormula(b, c, _) => {
                let new_b = b.act(ctx, i, f.clone())?;
                let new_c = act_formula(ctx, c, i, f.clone())?;

                if Rc::ptr_eq(b, &new_b) && new_c.is_none() {
                    Ok(self.clone())
                } else {
                    app_formula(ctx, &new_b, new_c.unwrap_or(c.clone()))
                }
            }
            Term::Comp(a, v, ts, _) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_v = v.act(ctx, i, f.clone())?;

                let new_ts = act_system(ctx, ts, i, f.clone())?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(v, &new_v) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    comp_line(ctx, &new_a, &new_v, new_ts.unwrap_or(ts.clone()))
                }
            }
            Term::HComp(a, u, us, _) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_u = u.act(ctx, i, f.clone())?;

                let new_us = act_system(ctx, us, i, f)?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(u, &new_u) && new_us.is_none() {
                    Ok(self.clone())
                } else {
                    hcomp(ctx, &new_a, &new_u, new_us.unwrap_or(us.clone()))
                }
            }
            Term::Glue(a, ts, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_ts = act_system(ctx, ts, i, f)?;

                if Rc::ptr_eq(a, &new_a) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    Ok(glue(&new_a, new_ts.unwrap_or(ts.clone()), m.clone()))
                }
            }
            Term::GlueElem(a, ts, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_ts = act_system(ctx, ts, i, f)?;
                if Rc::ptr_eq(a, &new_a) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    Ok(glue_elem(&new_a, new_ts.unwrap_or(ts.clone()), m.clone()))
                }
            }
            Term::UnGlueElem(a, ts, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_ts = act_system(ctx, ts, i, f)?;

                if Rc::ptr_eq(a, &new_a) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    unglue_elem(ctx, &new_a, new_ts.unwrap_or(ts.clone()), m.clone())
                }
            }
            Term::UnGlueElemU(a, b, ts, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_b = b.act(ctx, i, f.clone())?;
                let new_ts = act_system(ctx, ts, i, f)?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(b, &new_b) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    unglue_u(ctx, &new_a, &new_b, new_ts.unwrap_or(ts.clone()), m.clone())
                }
            }
            Term::Id(a, u, v, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_u = u.act(ctx, i, f.clone())?;
                let new_v = v.act(ctx, i, f.clone())?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(u, &new_u) && Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Id(new_a, new_u, new_v, m.clone())))
                }
            }
            Term::IdPair(u, us, m) => {
                let new_u = u.act(ctx, i, f.clone())?;
                let new_us = act_system(ctx, us, i, f)?;

                if Rc::ptr_eq(u, &new_u) && new_us.is_none() {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::IdPair(
                        new_u,
                        new_us.unwrap_or(us.clone()),
                        m.clone(),
                    )))
                }
            }
            Term::IdJ(a, u, c, d, x, p, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_u = u.act(ctx, i, f.clone())?;
                let new_c = c.act(ctx, i, f.clone())?;
                let new_d = d.act(ctx, i, f.clone())?;
                let new_x = x.act(ctx, i, f.clone())?;
                let new_p = p.act(ctx, i, f.clone())?;

                if Rc::ptr_eq(a, &new_a)
                    && Rc::ptr_eq(u, &new_u)
                    && Rc::ptr_eq(c, &new_c)
                    && Rc::ptr_eq(d, &new_d)
                    && Rc::ptr_eq(x, &new_x)
                    && Rc::ptr_eq(p, &new_p)
                {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::IdJ(
                        new_a,
                        new_u,
                        new_c,
                        new_d,
                        new_x,
                        new_p,
                        m.clone(),
                    )))
                }
            }
            Term::U
            | Term::Var(_, _)
            | Term::Sum(_, _, _)
            | Term::HSum(_, _, _)
            | Term::Undef(_, _)
            | Term::Hole => Ok(self.clone()),
            _ => panic!("not value"),
        }
    }
    fn swap(&self, from: &Identifier, to: &Identifier) -> Self {
        match self.as_ref() {
            Term::U => Rc::new(Term::U),
            Term::Pi(u, m) => Rc::new(Term::Pi(u.swap(from, to), m.clone())),
            Term::App(a, b, m) => Rc::new(Term::App(a.swap(from, to), b.swap(from, to), m.clone())),
            Term::Lam(x, t, u, m) => Rc::new(Term::Lam(
                *x,
                t.swap(from, to),
                u.swap(from, to),
                m.clone(),
            )),
            Term::Sigma(t, m) => Rc::new(Term::Sigma(t.swap(from, to), m.clone())),
            Term::Pair(fst, snd, m) => Rc::new(Term::Pair(
                fst.swap(from, to),
                snd.swap(from, to),
                m.clone(),
            )),
            Term::Fst(v, m) => Rc::new(Term::Fst(v.swap(from, to), m.clone())),
            Term::Snd(v, m) => Rc::new(Term::Snd(v.swap(from, to), m.clone())),
            Term::Con(c, a, m) => Rc::new(Term::Con(
                *c,
                a.iter().map(|x| x.swap(from, to)).collect(),
                m.clone(),
            )),
            Term::PCon(c, t, vs, phis, m) => Rc::new(Term::PCon(
                *c,
                t.swap(from, to),
                vs.iter().map(|x| x.swap(from, to)).collect(),
                phis.iter().map(|x| x.swap(from, to)).collect(),
                m.clone(),
            )),
            Term::Split(c, t, bs, m) => Rc::new(Term::Split(
                *c,
                t.swap(from, to),
                bs.clone(),
                m.clone(),
            )),
            Term::PathP(a, u, v, m) => Rc::new(Term::PathP(
                a.swap(from, to),
                u.swap(from, to),
                v.swap(from, to),
                m.clone(),
            )),
            Term::PLam(j, v, m) => {
                let k = if j == from {
                    to
                } else if j == to {
                    from
                } else {
                    j
                };
                Rc::new(Term::PLam(
                    *k,
                    v.swap(j, k).swap(from, to),
                    m.clone(),
                ))
            }
            Term::AppFormula(b, c, m) => Rc::new(Term::AppFormula(
                b.swap(from, to),
                c.swap(from, to),
                m.clone(),
            )),
            Term::Comp(a, v, ts, m) => Rc::new(Term::Comp(
                a.swap(from, to),
                v.swap(from, to),
                ts.swap(from, to),
                m.clone(),
            )),
            Term::HComp(a, u, us, m) => Rc::new(Term::HComp(
                a.swap(from, to),
                u.swap(from, to),
                us.swap(from, to),
                m.clone(),
            )),
            Term::Glue(a, ts, m) => {
                Rc::new(Term::Glue(a.swap(from, to), ts.swap(from, to), m.clone()))
            }
            Term::GlueElem(a, ts, m) => Rc::new(Term::GlueElem(
                a.swap(from, to),
                ts.swap(from, to),
                m.clone(),
            )),
            Term::UnGlueElem(a, ts, m) => Rc::new(Term::UnGlueElem(
                a.swap(from, to),
                ts.swap(from, to),
                m.clone(),
            )),
            Term::UnGlueElemU(a, b, ts, m) => Rc::new(Term::UnGlueElemU(
                a.swap(from, to),
                b.swap(from, to),
                ts.swap(from, to),
                m.clone(),
            )),
            Term::Id(a, u, v, m) => Rc::new(Term::Id(
                a.swap(from, to),
                u.swap(from, to),
                v.swap(from, to),
                m.clone(),
            )),
            Term::IdPair(u, us, m) => {
                Rc::new(Term::IdPair(u.swap(from, to), us.swap(from, to), m.clone()))
            }
            Term::IdJ(a, u, c, d, x, p, m) => Rc::new(Term::IdJ(
                a.swap(from, to),
                u.swap(from, to),
                c.swap(from, to),
                d.swap(from, to),
                x.swap(from, to),
                p.swap(from, to),
                m.clone(),
            )),
            Term::Var(_, _) => self.clone(),
            Term::Sum(_, _, _) => self.clone(),
            Term::HSum(_, _, _) => self.clone(),
            Term::Undef(_, _) => self.clone(),
            Term::Hole => self.clone(),
            _ => panic!("not value"),
        }
    }
}

impl Nominal for System<Term> {
    fn support(&self) -> Vec<Identifier> {
        let mut result = vec![];
        for (k, v) in self.iter() {
            result.extend(k.binds.keys());
            result.extend(v.support());
        }
        result
    }

    fn act(&self, ctx: &TypeContext, i: &Identifier, phi: Formula) -> Result<Self, TypeError> {
        let mut result = HashMap::new();
        for (alpha, u) in self.iter() {
            if let Some(d) = alpha.binds.get(i) {
                let mut beta = alpha.clone();
                beta.binds.remove(i);

                let s = inv_formula(phi.clone().face(ctx, &beta)?, d.clone());
                for delta in s {
                    let mut delta_ = delta.clone();
                    delta_.binds.remove(i);
                    let db = delta.meet(&beta);
                    let t = u.clone().face(ctx, &delta_)?;
                    result.insert(db, t);
                }
            } else {
                result.insert(
                    alpha.clone(),
                    u.act(ctx, i, phi.clone().face(ctx, alpha)?)?,
                );
            }
        }
        Ok(System::from(result))
    }

    fn swap(&self, from: &Identifier, to: &Identifier) -> Self {
        self.iter()
            .map(|(alpha, t_alpha)| {
                let beta = Face {
                    binds: alpha
                        .binds
                        .iter()
                        .map(|(n, d)| {
                            let k = if n == from {
                                to
                            } else if n == to {
                                from
                            } else {
                                n
                            };
                            (*k, d.clone())
                        })
                        .collect(),
                };
                (beta, t_alpha.swap(from, to))
            })
            .collect()
    }
}

impl Nominal for Formula {
    fn support(&self) -> Vec<Identifier> {
        fn inner(f: &Formula, acc: &mut Vec<Identifier>) {
            match f {
                Formula::Dir(_) => {}
                Formula::Atom(i) => acc.push(*i),
                Formula::NegAtom(i) => acc.push(*i),
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
        let mut result = vec![];
        inner(self, &mut result);
        result
    }

    fn act(&self, ctx: &TypeContext, i: &Identifier, phi: Formula) -> Result<Self, TypeError> {
        match self {
            Formula::Dir(d) => Ok(Formula::Dir(d.clone())),
            Formula::Atom(j) => {
                if i == j {
                    Ok(phi)
                } else {
                    Ok(Formula::Atom(*j))
                }
            }
            Formula::NegAtom(j) => {
                if i == j {
                    Ok(phi.negate())
                } else {
                    Ok(Formula::NegAtom(*j))
                }
            }
            Formula::And(psi1, psi2) => Ok(psi1
                .as_ref()
                .act(ctx, i, phi.clone())?
                .and(&psi2.as_ref().act(ctx, i, phi.clone())?)),
            Formula::Or(psi1, psi2) => Ok(psi1
                .as_ref()
                .act(ctx, i, phi.clone())?
                .or(&psi2.as_ref().act(ctx, i, phi.clone())?)),
        }
    }

    fn swap(&self, from: &Identifier, to: &Identifier) -> Self {
        match self {
            Formula::Dir(d) => Formula::Dir(d.clone()),
            Formula::Atom(j) => {
                let k = if j == from {
                    to
                } else if j == to {
                    from
                } else {
                    j
                };
                Formula::Atom(*k)
            }
            Formula::NegAtom(j) => {
                let k = if j == from {
                    to
                } else if j == to {
                    from
                } else {
                    j
                };
                Formula::NegAtom(*k)
            }
            Formula::And(psi1, psi2) => psi1
                .as_ref()
                .swap(from, to)
                .and(&psi2.as_ref().swap(from, to)),
            Formula::Or(psi1, psi2) => psi1
                .as_ref()
                .swap(from, to)
                .or(&psi2.as_ref().swap(from, to)),
        }
    }
}

pub trait Facing: Sized {
    fn face(&self, ctx: &TypeContext, face: &Face) -> Result<Self, TypeError>;
}

impl<A: Nominal + Clone> Facing for A {
    fn face(&self, ctx: &TypeContext, face: &Face) -> Result<A, TypeError> {
        face.binds.iter().fold(Ok(self.clone()), |a, (i, d)| {
            a?.act(ctx, i, Formula::Dir(d.clone()))
        })
    }
}

pub fn conj<A: Nominal>(
    ctx: &TypeContext,
    a: &A,
    i: &Identifier,
    j: &Identifier,
) -> Result<A, TypeError> {
    a.act(
        ctx,
        i,
        Formula::And(
            Box::new(Formula::Atom(*i)),
            Box::new(Formula::Atom(*j)),
        ),
    )
}

pub fn disj<A: Nominal>(
    ctx: &TypeContext,
    a: &A,
    i: &Identifier,
    j: &Identifier,
) -> Result<A, TypeError> {
    a.act(
        ctx,
        i,
        Formula::Or(
            Box::new(Formula::Atom(*i)),
            Box::new(Formula::Atom(*j)),
        ),
    )
}

pub fn sym<A: Nominal>(ctx: &TypeContext, a: &A, i: &Identifier) -> Result<A, TypeError> {
    a.act(ctx, i, Formula::NegAtom(*i))
}

pub fn border<A, B: Clone>(
    ctx: &TypeContext,
    value: &Rc<A>,
    shape: &System<B>,
) -> Result<System<A>, TypeError>
where
    Rc<A>: Facing,
{
    shape
        .iter()
        .map(|(f, _)| Ok((f.clone(), value.face(ctx, f)?)))
        .collect::<Result<_, TypeError>>()
}
