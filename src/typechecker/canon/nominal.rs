use crate::ctt::term::{Closure, Face, Formula, Identifier, System};
use crate::precise::term::Value;
use crate::typechecker::canon::app::{app, app_formula};
use crate::typechecker::canon::comp::{comp_line, comp_univ, hcomp, idj};
use crate::typechecker::canon::eval::{get_first, get_second, inv_formula, pcon};
use crate::typechecker::canon::glue::{glue, glue_elem, unglue_elem, unglue_u};
use crate::typechecker::context::{Entry, TypeContext};
use crate::typechecker::error::TypeError;
use std::collections::HashMap;
use std::rc::Rc;

pub trait Nominal: Sized {
    fn support(&self) -> Vec<Identifier>;

    fn act(&self, ctx: &TypeContext, i: &Identifier, f: Formula) -> Result<Self, TypeError>;

    fn swap(&self, from: &Identifier, to: &Identifier) -> Self;
}

impl Nominal for Closure {
    fn support(&self) -> Vec<Identifier> {
        let mut res = vec![];
        self.term_binds.iter().for_each(|(_, e)| {
            res.extend(e.value.support());
        });
        res
    }

    fn act(&self, ctx: &TypeContext, i: &Identifier, f: Formula) -> Result<Self, TypeError> {
        let term_binds = self
            .term_binds
            .iter()
            .map(|(k, v)| {
                Ok((
                    *k,
                    Entry {
                        tpe: v.tpe.act(ctx, i, f.clone())?,
                        value: v.value.act(ctx, i, f.clone())?,
                    },
                ))
            })
            .collect::<Result<_, TypeError>>()?;
        let formula_binds = self
            .formula_binds
            .iter()
            .map(|(k, v)| Ok((*k, v.act(ctx, i, f.clone())?)))
            .collect::<Result<_, TypeError>>()?;

        Ok(Closure {
            term_binds,
            formula_binds,
            face: self.face.clone(),
        })
    }

    fn swap(&self, from: &Identifier, to: &Identifier) -> Self {
        let term_binds = self
            .term_binds
            .iter()
            .map(|(k, v)| {
                (
                    *k,
                    Entry {
                        tpe: v.tpe.swap(from, to),
                        value: v.value.swap(from, to),
                    },
                )
            })
            .collect();
        let formula_binds = self
            .formula_binds
            .iter()
            .map(|(k, v)| (*k, v.swap(from, to)))
            .collect();

        Closure {
            term_binds,
            formula_binds,
            face: self.face.clone(),
        }
    }
}

impl Nominal for Rc<Value> {
    fn support(&self) -> Vec<Identifier> {
        let mut result = Vec::new();
        match self.as_ref() {
            Value::Stuck(_, c, _) => result.extend(c.support()),
            Value::Pi(a, t, _) => {
                result.extend(a.support());
                result.extend(t.support());
            }
            Value::App(t1, t2, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
            }
            Value::Var(_, _) => (),
            Value::U => (),
            Value::Sigma(a, t, _) => {
                result.extend(a.support());
                result.extend(t.support());
            }
            Value::Pair(t1, t2, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
            }
            Value::Fst(t, _) => result.extend(t.support()),
            Value::Snd(t, _) => result.extend(t.support()),
            Value::Con(_, ts, _) => {
                for t in ts {
                    result.extend(t.support());
                }
            }
            Value::PCon(_, t, ts, is, _) => {
                result.extend(t.support());
                for t in ts {
                    result.extend(t.support());
                }
                for i in is {
                    result.extend(i.support());
                }
            }
            Value::PathP(t1, t2, t3, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(t3.support());
            }
            Value::PLam(n, t, _) => result.extend(t.support().iter().filter(|x| x != &n)),
            Value::AppFormula(t, f, _) => {
                result.extend(t.support());
                result.extend(f.support())
            }
            Value::Comp(t1, t2, system, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(system.support());
            }
            Value::CompU(t, system, _) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Value::HComp(t1, t2, system, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(system.support());
            }
            Value::Glue(t, system, _) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Value::GlueElem(t, system, _) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Value::UnGlueElem(t, system, _) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Value::UnGlueElemU(t, b, system, _) => {
                result.extend(t.support());
                result.extend(b.support());
                result.extend(system.support());
            }
            Value::Id(t1, t2, t3, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(t3.support());
            }
            Value::IdPair(t, system, _) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Value::IdJ(t1, t2, t3, t4, t5, t6, _) => {
                result.extend(t1.support());
                result.extend(t2.support());
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
            o: &System<Value>,
            i: &Identifier,
            f: Formula,
        ) -> Result<Option<System<Value>>, TypeError> {
            if o.support().contains(i) {
                Ok(Some(o.act(ctx, i, f)?))
            } else {
                Ok(None)
            }
        }

        match self.as_ref() {
            Value::Stuck(t, c, m) => Ok(Rc::new(Value::Stuck(
                t.clone(),
                c.act(ctx, i, f)?,
                m.clone(),
            ))),
            Value::Pi(t, u, m) => {
                let new_t = t.act(ctx, i, f.clone())?;
                let new_u = u.act(ctx, i, f)?;
                if Rc::ptr_eq(t, &new_t) && Rc::ptr_eq(u, &new_u) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Value::Pi(new_t, new_u, m.clone())))
                }
            }
            Value::App(a, b, _) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_b = b.act(ctx, i, f)?;
                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(b, &new_b) {
                    Ok(self.clone())
                } else {
                    app(ctx, &new_a, &new_b)
                }
            }
            Value::Sigma(a, t, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_t = t.act(ctx, i, f)?;
                if Rc::ptr_eq(t, &new_t) && Rc::ptr_eq(a, &new_a) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Value::Sigma(new_a, new_t, m.clone())))
                }
            }
            Value::Pair(fst, snd, m) => {
                let new_fst = fst.act(ctx, i, f.clone())?;
                let new_snd = snd.act(ctx, i, f)?;
                if Rc::ptr_eq(fst, &new_fst) && Rc::ptr_eq(snd, &new_snd) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Value::Pair(new_fst, new_snd, m.clone())))
                }
            }
            Value::Fst(v, _) => {
                let new_v = v.act(ctx, i, f)?;
                if Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(get_first(&new_v))
                }
            }
            Value::Snd(v, _) => {
                let new_v = v.act(ctx, i, f)?;
                if Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(get_second(&new_v))
                }
            }
            Value::Con(c, a, m) => {
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
                    Ok(Rc::new(Value::Con(*c, new_a, m.clone())))
                }
            }
            Value::PCon(c, t, vs, phis, m) => {
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
            Value::PathP(a, u, v, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_u = u.act(ctx, i, f.clone())?;
                let new_v = v.act(ctx, i, f)?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(u, &new_u) && Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Value::PathP(new_a, new_u, new_v, m.clone())))
                }
            }
            Value::PLam(j, v, m) => {
                if j == i {
                    Ok(self.clone())
                } else {
                    let sphi = self.support();
                    if !sphi.contains(j) {
                        let new_v = v.act(ctx, i, f)?;
                        if Rc::ptr_eq(v, &new_v) {
                            Ok(self.clone())
                        } else {
                            Ok(Rc::new(Value::PLam(*j, new_v, m.clone())))
                        }
                    } else {
                        let k = ctx.fresh();
                        Ok(Rc::new(Value::PLam(
                            k,
                            v.swap(j, &k).act(ctx, i, f)?,
                            m.clone(),
                        )))
                    }
                }
            }
            Value::AppFormula(b, c, _) => {
                let new_b = b.act(ctx, i, f.clone())?;
                let new_c = act_formula(ctx, c, i, f.clone())?;

                if Rc::ptr_eq(b, &new_b) && new_c.is_none() {
                    Ok(self.clone())
                } else {
                    app_formula(ctx, &new_b, new_c.unwrap_or(c.clone()))
                }
            }
            Value::Comp(a, v, ts, _) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_v = v.act(ctx, i, f.clone())?;

                let new_ts = act_system(ctx, ts, i, f.clone())?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(v, &new_v) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    comp_line(ctx, &new_a, &new_v, new_ts.unwrap_or(ts.clone()))
                }
            }
            Value::CompU(v, ts, _) => {
                let new_v = v.act(ctx, i, f.clone())?;

                let new_ts = act_system(ctx, ts, i, f.clone())?;

                if Rc::ptr_eq(v, &new_v) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    comp_univ(ctx, &new_v, new_ts.unwrap_or(ts.clone()))
                }
            }
            Value::HComp(a, u, us, _) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_u = u.act(ctx, i, f.clone())?;

                let new_us = act_system(ctx, us, i, f)?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(u, &new_u) && new_us.is_none() {
                    Ok(self.clone())
                } else {
                    hcomp(ctx, &new_a, &new_u, new_us.unwrap_or(us.clone()))
                }
            }
            Value::Glue(a, ts, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_ts = act_system(ctx, ts, i, f)?;

                if Rc::ptr_eq(a, &new_a) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    Ok(glue(&new_a, new_ts.unwrap_or(ts.clone()), m.clone()))
                }
            }
            Value::GlueElem(a, ts, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_ts = act_system(ctx, ts, i, f)?;
                if Rc::ptr_eq(a, &new_a) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    Ok(glue_elem(&new_a, new_ts.unwrap_or(ts.clone()), m.clone()))
                }
            }
            Value::UnGlueElem(a, ts, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_ts = act_system(ctx, ts, i, f)?;

                if Rc::ptr_eq(a, &new_a) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    unglue_elem(ctx, &new_a, new_ts.unwrap_or(ts.clone()), m.clone())
                }
            }
            Value::UnGlueElemU(a, b, ts, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_b = b.act(ctx, i, f.clone())?;
                let new_ts = act_system(ctx, ts, i, f)?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(b, &new_b) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    unglue_u(ctx, &new_a, &new_b, new_ts.unwrap_or(ts.clone()), m.clone())
                }
            }
            Value::Id(a, u, v, m) => {
                let new_a = a.act(ctx, i, f.clone())?;
                let new_u = u.act(ctx, i, f.clone())?;
                let new_v = v.act(ctx, i, f.clone())?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(u, &new_u) && Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Value::Id(new_a, new_u, new_v, m.clone())))
                }
            }
            Value::IdPair(u, us, m) => {
                let new_u = u.act(ctx, i, f.clone())?;
                let new_us = act_system(ctx, us, i, f)?;

                if Rc::ptr_eq(u, &new_u) && new_us.is_none() {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Value::IdPair(
                        new_u,
                        new_us.unwrap_or(us.clone()),
                        m.clone(),
                    )))
                }
            }
            Value::IdJ(a, u, c, d, x, p, m) => {
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
                    idj(ctx, &new_a, &new_u, &new_c, &new_d, &new_x, &new_p)
                }
            }
            Value::U | Value::Var(_, _) => Ok(self.clone()),
        }
    }
    fn swap(&self, from: &Identifier, to: &Identifier) -> Self {
        match self.as_ref() {
            Value::U => Rc::new(Value::U),
            Value::Pi(t, u, m) => Rc::new(Value::Pi(t.swap(from, to), u.swap(from, to), m.clone())),
            Value::App(a, b, m) => {
                Rc::new(Value::App(a.swap(from, to), b.swap(from, to), m.clone()))
            }
            Value::Sigma(a, t, m) => {
                Rc::new(Value::Sigma(a.swap(from, to), t.swap(from, to), m.clone()))
            }
            Value::Pair(fst, snd, m) => Rc::new(Value::Pair(
                fst.swap(from, to),
                snd.swap(from, to),
                m.clone(),
            )),
            Value::Fst(v, m) => Rc::new(Value::Fst(v.swap(from, to), m.clone())),
            Value::Snd(v, m) => Rc::new(Value::Snd(v.swap(from, to), m.clone())),
            Value::Con(c, a, m) => Rc::new(Value::Con(
                *c,
                a.iter().map(|x| x.swap(from, to)).collect(),
                m.clone(),
            )),
            Value::PCon(c, t, vs, phis, m) => Rc::new(Value::PCon(
                *c,
                t.swap(from, to),
                vs.iter().map(|x| x.swap(from, to)).collect(),
                phis.iter().map(|x| x.swap(from, to)).collect(),
                m.clone(),
            )),
            Value::PathP(a, u, v, m) => Rc::new(Value::PathP(
                a.swap(from, to),
                u.swap(from, to),
                v.swap(from, to),
                m.clone(),
            )),
            Value::PLam(j, v, m) => {
                let k = if j == from {
                    to
                } else if j == to {
                    from
                } else {
                    j
                };
                Rc::new(Value::PLam(*k, v.swap(j, k).swap(from, to), m.clone()))
            }
            Value::AppFormula(b, c, m) => Rc::new(Value::AppFormula(
                b.swap(from, to),
                c.swap(from, to),
                m.clone(),
            )),
            Value::Comp(a, v, ts, m) => Rc::new(Value::Comp(
                a.swap(from, to),
                v.swap(from, to),
                ts.swap(from, to),
                m.clone(),
            )),
            Value::CompU(v, ts, m) => {
                Rc::new(Value::CompU(v.swap(from, to), ts.swap(from, to), m.clone()))
            }
            Value::HComp(a, u, us, m) => Rc::new(Value::HComp(
                a.swap(from, to),
                u.swap(from, to),
                us.swap(from, to),
                m.clone(),
            )),
            Value::Glue(a, ts, m) => {
                Rc::new(Value::Glue(a.swap(from, to), ts.swap(from, to), m.clone()))
            }
            Value::GlueElem(a, ts, m) => Rc::new(Value::GlueElem(
                a.swap(from, to),
                ts.swap(from, to),
                m.clone(),
            )),
            Value::UnGlueElem(a, ts, m) => Rc::new(Value::UnGlueElem(
                a.swap(from, to),
                ts.swap(from, to),
                m.clone(),
            )),
            Value::UnGlueElemU(a, b, ts, m) => Rc::new(Value::UnGlueElemU(
                a.swap(from, to),
                b.swap(from, to),
                ts.swap(from, to),
                m.clone(),
            )),
            Value::Id(a, u, v, m) => Rc::new(Value::Id(
                a.swap(from, to),
                u.swap(from, to),
                v.swap(from, to),
                m.clone(),
            )),
            Value::IdPair(u, us, m) => Rc::new(Value::IdPair(
                u.swap(from, to),
                us.swap(from, to),
                m.clone(),
            )),
            Value::IdJ(a, u, c, d, x, p, m) => Rc::new(Value::IdJ(
                a.swap(from, to),
                u.swap(from, to),
                c.swap(from, to),
                d.swap(from, to),
                x.swap(from, to),
                p.swap(from, to),
                m.clone(),
            )),
            Value::Stuck(t, c, m) => Rc::new(Value::Stuck(t.clone(), c.swap(from, to), m.clone())),
            Value::Var(_, _) => self.clone(),
        }
    }
}

impl<A> Nominal for System<A>
where
    Rc<A>: Nominal,
    A: Clone,
{
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
                result.insert(alpha.clone(), u.act(ctx, i, phi.clone().face(ctx, alpha)?)?);
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
        Formula::And(Box::new(Formula::Atom(*i)), Box::new(Formula::Atom(*j))),
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
        Formula::Or(Box::new(Formula::Atom(*i)), Box::new(Formula::Atom(*j))),
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
