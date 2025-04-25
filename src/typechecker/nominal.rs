use std::backtrace::Backtrace;
use crate::ctt::term::{Branch, Face, Formula, Identifier, System, Term};
use crate::typechecker::context::TypeContext;
use crate::typechecker::error::TypeError;
use crate::typechecker::eval::{
    app, app_formula, comp_line, get_first, get_second, glue, glue_elem, hcomp, inv_formula, pcon,
    unglue, unglue_elem, unglue_u, Facing,
};
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

pub trait Nominal: Sized {
    fn support(&self) -> Vec<Identifier>;

    fn act(&self, ctx: TypeContext, i: &Identifier, f: Formula) -> Result<Self, TypeError>;

    fn swap(&self, from: &Identifier, to: &Identifier) -> Self;
}

impl Nominal for Rc<Term> {
    fn support(&self) -> Vec<Identifier> {
        let mut result = Vec::new();
        match self.as_ref() {
            Term::Pi(t) => result.extend(t.support()),
            Term::App(t1, t2) => {
                result.extend(t1.support());
                result.extend(t2.support());
            }
            Term::Lam(_, t1, t2) => {
                result.extend(t1.support());
                result.extend(t2.support());
            }
            Term::Where(t, _) => result.extend(t.support()),
            Term::Var(_) => (),
            Term::U => (),
            Term::Sigma(t) => result.extend(t.support()),
            Term::Pair(t1, t2) => {
                result.extend(t1.support());
                result.extend(t2.support());
            }
            Term::Fst(t) => result.extend(t.support()),
            Term::Snd(t) => result.extend(t.support()),
            Term::Con(_, ts) => {
                for t in ts {
                    result.extend(t.support());
                }
            }
            Term::PCon(_, t, ts, is) => {
                result.extend(t.support());
                for t in ts {
                    result.extend(t.support());
                }
                for i in is {
                    result.extend(i.support());
                }
            }
            Term::Split(_, t, branches) => {
                result.extend(t.support());
                for branch in branches {
                    match branch {
                        Branch::OBranch(_, _, b) => result.extend(b.support()),
                        Branch::PBranch(_, _, _, b) => result.extend(b.support()),
                    }
                }
            }
            Term::Sum(_, _) => (),
            Term::HSum(_, _) => (),
            Term::Undef(t) => result.extend(t.support()),
            Term::Hole => (),
            Term::PathP(t1, t2, t3) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(t3.support());
            }
            Term::PLam(n, t) => result.extend(t.support().iter().filter(|x| x != &n)),
            Term::AppFormula(t, f) => {
                result.extend(t.support());
                result.extend(f.support())
            }
            Term::Comp(t1, t2, system) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(system.support());
            }
            Term::Fill(t1, t2, system) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(system.support());
            }
            Term::HComp(t1, t2, system) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(system.support());
            }
            Term::Glue(t, system) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Term::GlueElem(t, system) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Term::UnGlueElem(t, system) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Term::UnGlueElemU(t, b, system) => {
                result.extend(t.support());
                result.extend(b.support());
                result.extend(system.support());
            }
            Term::Id(t1, t2, t3) => {
                result.extend(t1.support());
                result.extend(t2.support());
                result.extend(t3.support());
            }
            Term::IdPair(t, system) => {
                result.extend(t.support());
                result.extend(system.support());
            }
            Term::IdJ(t1, t2, t3, t4, t5, t6) => {
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

    fn act(&self, ctx: TypeContext, i: &Identifier, f: Formula) -> Result<Self, TypeError> {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);

        let x = COUNTER.fetch_add(1, Ordering::SeqCst);
        // if x % 10000 == 0 {
        //     println!("{x}: act {:?} {:?} {:?}", self, i, f);
        //     if x == 8849712 {
        //         println!("{}", Backtrace::capture());
        //     }
        // }
        fn act_formula(
            ctx: TypeContext,
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
            ctx: TypeContext,
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
            Term::Pi(u) => {
                let new_u = u.act(ctx.clone(), i, f)?;
                if Rc::ptr_eq(u, &new_u) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Pi(new_u)))
                }
            }
            Term::App(a, b) => {
                let new_a = a.act(ctx.clone(), i, f.clone())?;
                let new_b = b.act(ctx.clone(), i, f)?;
                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(b, &new_b) {
                    Ok(self.clone())
                } else {
                    app(ctx.clone(), new_a, new_b)
                }
            }
            Term::Lam(x, t, u) => {
                let new_t = t.act(ctx.clone(), i, f.clone())?;
                let in_body_ctx = ctx.with_term(x, &Rc::new(Term::Var(x.clone())), &new_t);
                let new_u = u.act(in_body_ctx.clone(), i, f)?;

                if Rc::ptr_eq(t, &new_t) && Rc::ptr_eq(u, &new_u) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Lam(x.clone(), new_t, new_u)))
                }
            }
            Term::Sigma(t) => {
                let new_t = t.act(ctx.clone(), i, f)?;
                if Rc::ptr_eq(t, &new_t) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Sigma(new_t)))
                }
            }
            Term::Pair(fst, snd) => {
                let new_fst = fst.act(ctx.clone(), i, f.clone())?;
                let new_snd = snd.act(ctx.clone(), i, f)?;
                if Rc::ptr_eq(fst, &new_fst) && Rc::ptr_eq(snd, &new_snd) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Pair(new_fst, new_snd)))
                }
            }
            Term::Fst(v) => {
                let new_v = v.act(ctx.clone(), i, f)?;
                if Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(get_first(new_v))
                }
            }
            Term::Snd(v) => {
                let new_v = v.act(ctx.clone(), i, f)?;
                if Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(get_second(new_v))
                }
            }
            Term::Con(c, a) => {
                let mut changed = false;
                let new_a = a
                    .iter()
                    .map(|x| {
                        let new_x = x.act(ctx.clone(), i, f.clone())?;
                        if !Rc::ptr_eq(x, &new_x) {
                            changed = true;
                        }
                        Ok(new_x)
                    })
                    .collect::<Result<Vec<_>, TypeError>>()?;

                if !changed {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Con(c.clone(), new_a)))
                }
            }
            Term::PCon(c, t, vs, phis) => {
                let new_t = t.act(ctx.clone(), i, f.clone())?;
                let mut changed = !Rc::ptr_eq(t, &new_t);

                let new_vs = vs
                    .iter()
                    .map(|x| {
                        let new_x = x.act(ctx.clone(), i, f.clone())?;
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
                            let new_x = x.act(ctx.clone(), i, f.clone())?;
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
                    pcon(ctx.clone(), c, new_t, new_vs, new_phis)
                }
            }
            Term::Split(c, t, b) => {
                let new_t = t.act(ctx, i, f)?;
                if Rc::ptr_eq(t, &new_t) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Split(c.clone(), new_t, b.clone())))
                }
            }
            Term::PathP(a, u, v) => {
                let new_a = a.act(ctx.clone(), i, f.clone())?;
                let new_u = u.act(ctx.clone(), i, f.clone())?;
                let new_v = v.act(ctx.clone(), i, f)?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(u, &new_u) && Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::PathP(new_a, new_u, new_v)))
                }
            }
            Term::PLam(j, v) => {
                if j == i {
                    Ok(self.clone())
                } else {
                    let sphi = v.support();
                    if !sphi.contains(j) {

                    } else {

                    }
                    let new_v = v.act(ctx.clone(), i, f)?;
                    if Rc::ptr_eq(v, &new_v) {
                        Ok(self.clone())
                    } else {
                        Ok(Rc::new(Term::PLam(j.clone(), new_v)))
                    }
                }
            }
            Term::AppFormula(b, c) => {
                let new_b = b.act(ctx.clone(), i, f.clone())?;
                let new_c = act_formula(ctx.clone(), c, i, f.clone())?;

                if Rc::ptr_eq(b, &new_b) && new_c.is_none() {
                    Ok(self.clone())
                } else {
                    app_formula(ctx.clone(), new_b, new_c.unwrap_or(c.clone()))
                }
            }
            Term::Comp(a, v, ts) => {
                let new_a = a.act(ctx.clone(), i, f.clone())?;
                let new_v = v.act(ctx.clone(), i, f.clone())?;

                let new_ts = act_system(ctx.clone(), ts, i, f.clone())?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(v, &new_v) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    comp_line(ctx.clone(), new_a, new_v, new_ts.unwrap_or(ts.clone()))
                }
            }
            Term::HComp(a, u, us) => {
                let new_a = a.act(ctx.clone(), i, f.clone())?;
                let new_u = u.act(ctx.clone(), i, f.clone())?;

                let new_us = act_system(ctx.clone(), us, i, f)?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(u, &new_u) && new_us.is_none() {
                    Ok(self.clone())
                } else {
                    hcomp(ctx.clone(), new_a, new_u, new_us.unwrap_or(us.clone()))
                }
            }
            Term::Glue(a, ts) => {
                let new_a = a.act(ctx.clone(), i, f.clone())?;
                let new_ts = act_system(ctx.clone(), ts, i, f)?;

                if Rc::ptr_eq(a, &new_a) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    Ok(glue(new_a, new_ts.unwrap_or(ts.clone())))
                }
            }
            Term::GlueElem(a, ts) => {
                let new_a = a.act(ctx.clone(), i, f.clone())?;
                let new_ts = act_system(ctx.clone(), ts, i, f)?;
                if Rc::ptr_eq(a, &new_a) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    Ok(glue_elem(new_a, new_ts.unwrap_or(ts.clone())))
                }
            }
            Term::UnGlueElem(a, ts) => {
                let new_a = a.act(ctx.clone(), i, f.clone())?;
                let new_ts = act_system(ctx.clone(), ts, i, f)?;

                if Rc::ptr_eq(a, &new_a) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    unglue_elem(ctx.clone(), new_a, new_ts.unwrap_or(ts.clone()))
                }
            }
            Term::UnGlueElemU(a, b, ts) => {
                let new_a = a.act(ctx.clone(), i, f.clone())?;
                let new_b = b.act(ctx.clone(), i, f.clone())?;
                let new_ts = act_system(ctx.clone(), ts, i, f)?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(b, &new_b) && new_ts.is_none() {
                    Ok(self.clone())
                } else {
                    unglue_u(ctx.clone(), new_a, new_b, new_ts.unwrap_or(ts.clone()))
                }
            }
            Term::Id(a, u, v) => {
                let new_a = a.act(ctx.clone(), i, f.clone())?;
                let new_u = u.act(ctx.clone(), i, f.clone())?;
                let new_v = v.act(ctx.clone(), i, f.clone())?;

                if Rc::ptr_eq(a, &new_a) && Rc::ptr_eq(u, &new_u) && Rc::ptr_eq(v, &new_v) {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::Id(new_a, new_u, new_v)))
                }
            }
            Term::IdPair(u, us) => {
                let new_u = u.act(ctx.clone(), i, f.clone())?;
                let new_us = act_system(ctx.clone(), us, i, f)?;

                if Rc::ptr_eq(u, &new_u) && new_us.is_none() {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::IdPair(new_u, new_us.unwrap_or(us.clone()))))
                }
            }
            Term::IdJ(a, u, c, d, x, p) => {
                let new_a = a.act(ctx.clone(), i, f.clone())?;
                let new_u = u.act(ctx.clone(), i, f.clone())?;
                let new_c = c.act(ctx.clone(), i, f.clone())?;
                let new_d = d.act(ctx.clone(), i, f.clone())?;
                let new_x = x.act(ctx.clone(), i, f.clone())?;
                let new_p = p.act(ctx.clone(), i, f.clone())?;

                if Rc::ptr_eq(&a, &new_a)
                    && Rc::ptr_eq(&u, &new_u)
                    && Rc::ptr_eq(&c, &new_c)
                    && Rc::ptr_eq(&d, &new_d)
                    && Rc::ptr_eq(&x, &new_x)
                    && Rc::ptr_eq(&p, &new_p)
                {
                    Ok(self.clone())
                } else {
                    Ok(Rc::new(Term::IdJ(new_a, new_u, new_c, new_d, new_x, new_p)))
                }
            }
            Term::U | Term::Var(_) | Term::Sum(_, _) | Term::HSum(_, _) | Term::Undef(_) | Term::Hole => {
                Ok(self.clone())
            }
            _ => panic!("not value"),
        }
    }
    fn swap(&self, from: &Identifier, to: &Identifier) -> Self {
        match self.as_ref() {
            Term::U => Rc::new(Term::U),
            Term::Pi(u) => Rc::new(Term::Pi(u.swap(from, to))),
            Term::App(a, b) => Rc::new(Term::App(a.swap(from, to), b.swap(from, to))),
            Term::Lam(x, t, u) => Rc::new(Term::Lam(x.clone(), t.swap(from, to), u.swap(from, to))),
            Term::Sigma(t) => Rc::new(Term::Sigma(t.swap(from, to))),
            Term::Pair(fst, snd) => Rc::new(Term::Pair(fst.swap(from, to), snd.swap(from, to))),
            Term::Fst(v) => Rc::new(Term::Fst(v.swap(from, to))),
            Term::Snd(v) => Rc::new(Term::Snd(v.swap(from, to))),
            Term::Con(c, a) => Rc::new(Term::Con(
                c.clone(),
                a.iter().map(|x| x.swap(from, to)).collect(),
            )),
            Term::PCon(c, t, vs, phis) => Rc::new(Term::PCon(
                c.clone(),
                t.swap(from, to),
                vs.iter().map(|x| x.swap(from, to)).collect(),
                phis.iter().map(|x| x.swap(from, to)).collect(),
            )),
            Term::Split(c, t, bs) => {
                // bs.iter().map(|b| match b {
                //     Branch::OBranch(n, c, t) => {
                //
                //     }
                //     Branch::PBranch(n, c, i, t) => {}
                // })
                Rc::new(Term::Split(c.clone(), t.swap(from, to), bs.clone()))
            }
            Term::PathP(a, u, v) => Rc::new(Term::PathP(
                a.swap(from, to),
                u.swap(from, to),
                v.swap(from, to),
            )),
            Term::PLam(j, v) => {
                let k = if j == from {
                    to
                } else if j == to {
                    from
                } else {
                    j
                };
                Rc::new(Term::PLam(k.clone(), v.swap(j, &k).swap(from, to)))
            }
            Term::AppFormula(b, c) => Rc::new(Term::AppFormula(b.swap(from, to), c.swap(from, to))),
            Term::Comp(a, v, ts) => Rc::new(Term::Comp(
                a.swap(from, to),
                v.swap(from, to),
                ts.swap(from, to),
            )),
            Term::HComp(a, u, us) => Rc::new(Term::HComp(
                a.swap(from, to),
                u.swap(from, to),
                us.swap(from, to),
            )),
            Term::Glue(a, ts) => Rc::new(Term::Glue(a.swap(from, to), ts.swap(from, to))),
            Term::GlueElem(a, ts) => Rc::new(Term::GlueElem(a.swap(from, to), ts.swap(from, to))),
            Term::UnGlueElem(a, ts) => {
                Rc::new(Term::UnGlueElem(a.swap(from, to), ts.swap(from, to)))
            }
            Term::UnGlueElemU(a, b, ts) => Rc::new(Term::UnGlueElemU(
                a.swap(from, to),
                b.swap(from, to),
                ts.swap(from, to),
            )),
            Term::Id(a, u, v) => Rc::new(Term::Id(
                a.swap(from, to),
                u.swap(from, to),
                v.swap(from, to),
            )),
            Term::IdPair(u, us) => Rc::new(Term::IdPair(u.swap(from, to), us.swap(from, to))),
            Term::IdJ(a, u, c, d, x, p) => Rc::new(Term::IdJ(
                a.swap(from, to),
                u.swap(from, to),
                c.swap(from, to),
                d.swap(from, to),
                x.swap(from, to),
                p.swap(from, to),
            )),
            Term::Var(_) => self.clone(),
            Term::Sum(_, _) => self.clone(),
            Term::HSum(_, _) => self.clone(),
            Term::Undef(_) => self.clone(),
            Term::Hole => self.clone(),
            _ => panic!("not value"),
        }
    }
}

impl Nominal for System<Term> {
    fn support(&self) -> Vec<Identifier> {
        let mut result = vec![];
        for (k, v) in &self.binds {
            result.extend(k.binds.keys());
            result.extend(v.support());
        }
        result
    }

    fn act(&self, ctx: TypeContext, i: &Identifier, phi: Formula) -> Result<Self, TypeError> {
        let mut result = System {
            binds: HashMap::new(),
        };
        for (alpha, u) in self.binds.iter() {
            if let Some(d) = alpha.binds.get(i) {
                let mut beta = alpha.clone();
                beta.binds.remove(i);

                let s = inv_formula(phi.clone().face(ctx.clone(), &beta)?, d.clone());
                for delta in s {
                    let mut delta_ = delta.clone();
                    delta_.binds.remove(i);
                    let db = delta.meet(&beta);
                    let t = u.clone().face(ctx.clone(), &delta_)?;
                    result.binds.insert(db, t);
                }
            } else {
                result.binds.insert(
                    alpha.clone(),
                    u.act(ctx.clone(), i, phi.clone().face(ctx.clone(), &alpha)?)?,
                );
            }
        }
        Ok(result)
    }

    fn swap(&self, from: &Identifier, to: &Identifier) -> Self {
        System {
            binds: self
                .binds
                .iter()
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
                                (k.clone(), d.clone())
                            })
                            .collect(),
                    };
                    (beta, t_alpha.swap(from, to))
                })
                .collect(),
        }
    }
}

impl Nominal for Formula {
    fn support(&self) -> Vec<Identifier> {
        fn inner(f: &Formula, acc: &mut Vec<Identifier>) {
            match f {
                Formula::Dir(_) => {}
                Formula::Atom(i) => acc.push(i.clone()),
                Formula::NegAtom(i) => acc.push(i.clone()),
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

    fn act(&self, ctx: TypeContext, i: &Identifier, phi: Formula) -> Result<Self, TypeError> {
        match self {
            Formula::Dir(d) => Ok(Formula::Dir(d.clone())),
            Formula::Atom(j) => {
                if i == j {
                    Ok(phi)
                } else {
                    Ok(Formula::Atom(j.clone()))
                }
            }
            Formula::NegAtom(j) => {
                if i == j {
                    Ok(phi.negate())
                } else {
                    Ok(Formula::NegAtom(j.clone()))
                }
            }
            Formula::And(psi1, psi2) => Ok(psi1
                .as_ref()
                .act(ctx.clone(), i, phi.clone())?
                .and(&psi2.as_ref().act(ctx.clone(), i, phi.clone())?)),
            Formula::Or(psi1, psi2) => Ok(psi1
                .as_ref()
                .act(ctx.clone(), i, phi.clone())?
                .or(&psi2.as_ref().act(ctx.clone(), i, phi.clone())?)),
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
                Formula::Atom(k.clone())
            }
            Formula::NegAtom(j) => {
                let k = if j == from {
                    to
                } else if j == to {
                    from
                } else {
                    j
                };
                Formula::NegAtom(k.clone())
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
