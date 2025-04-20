use crate::ctt::term::{Branch, Face, Formula, Identifier, System, Term};
use crate::typechecker::context::TypeContext;
use crate::typechecker::error::TypeError;
use crate::typechecker::eval::{
    app, app_formula, comp_line, get_first, get_second, glue, glue_elem, hcomp, inv_formula, pcon,
    unglue_elem, Facing,
};
use std::collections::HashMap;
use std::rc::Rc;

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
        let sphi = f.support();
        match self.as_ref() {
            _ if !self.support().contains(i) => Ok(self.clone()),
            Term::U => Ok(Rc::new(Term::U)),
            Term::Pi(u) => Ok(Rc::new(Term::Pi(u.act(ctx.clone(), i, f)?))),
            Term::App(a, b) => app(
                ctx.clone(),
                a.act(ctx.clone(), i, f.clone())?,
                b.act(ctx.clone(), i, f)?,
            ),
            Term::Lam(x, t, u) => {
                let in_body_ctx = ctx.with_term(x, &Rc::new(Term::Var(x.clone())), t);
                Ok(Rc::new(Term::Lam(
                    x.clone(),
                    t.act(ctx.clone(), i, f.clone())?,
                    u.act(in_body_ctx.clone(), i, f)?,
                )))
            }

            Term::Sigma(t) => Ok(Rc::new(Term::Sigma(t.act(ctx.clone(), i, f)?))),
            Term::Pair(fst, snd) => Ok(Rc::new(Term::Pair(
                fst.act(ctx.clone(), i, f.clone())?,
                snd.act(ctx.clone(), i, f)?,
            ))),
            Term::Fst(v) => Ok(get_first(v.act(ctx.clone(), i, f)?)),
            Term::Snd(v) => Ok(get_second(v.act(ctx.clone(), i, f)?)),
            Term::Con(c, a) => Ok(Rc::new(Term::Con(
                c.clone(),
                a.iter()
                    .map(|x| x.act(ctx.clone(), i, f.clone()))
                    .collect::<Result<_, TypeError>>()?,
            ))),
            Term::PCon(c, t, vs, phis) => pcon(
                ctx.clone(),
                c,
                t.act(ctx.clone(), i, f.clone())?,
                vs.iter()
                    .map(|x| x.act(ctx.clone(), i, f.clone()))
                    .collect::<Result<_, TypeError>>()?,
                phis.iter()
                    .map(|x| x.act(ctx.clone(), i, f.clone()))
                    .collect::<Result<_, TypeError>>()?,
            ),
            Term::Split(c, t, b) => Ok(Rc::new(Term::Split(
                c.clone(),
                t.act(ctx, i, f)?,
                b.clone(),
            ))),
            Term::PathP(a, u, v) => Ok(Rc::new(Term::PathP(
                a.act(ctx.clone(), i, f.clone())?,
                u.act(ctx.clone(), i, f.clone())?,
                v.act(ctx.clone(), i, f)?,
            ))),
            Term::PLam(j, v) => {
                if j == i {
                    Ok(self.clone())
                } else if sphi.contains(j) {
                    Ok(Rc::new(Term::PLam(j.clone(), v.act(ctx.clone(), i, f)?)))
                } else {
                    let k = ctx.fresh();
                    let in_body_ctx = ctx.with_formula(&k, Formula::Atom(k));
                    Ok(Rc::new(Term::PLam(
                        k.clone(),
                        v.swap(j, &k).act(in_body_ctx, i, f)?,
                    )))
                }
            }
            Term::AppFormula(b, c) => app_formula(
                ctx.clone(),
                b.act(ctx.clone(), i, f.clone())?,
                c.act(ctx.clone(), i, f.clone())?,
            ),
            Term::Comp(a, v, ts) => comp_line(
                ctx.clone(),
                a.act(ctx.clone(), i, f.clone())?,
                v.act(ctx.clone(), i, f.clone())?,
                ts.act(ctx.clone(), i, f.clone())?,
            ),
            Term::HComp(a, u, us) => hcomp(
                ctx.clone(),
                a.act(ctx.clone(), i, f.clone())?,
                u.act(ctx.clone(), i, f.clone())?,
                us.act(ctx.clone(), i, f.clone())?,
            ),
            Term::Glue(a, ts) => Ok(glue(
                a.act(ctx.clone(), i, f.clone())?,
                ts.act(ctx.clone(), i, f.clone())?,
            )),
            Term::GlueElem(a, ts) => Ok(glue_elem(
                a.act(ctx.clone(), i, f.clone())?,
                ts.act(ctx.clone(), i, f.clone())?,
            )),
            Term::UnGlueElem(a, ts) => unglue_elem(
                ctx.clone(),
                a.act(ctx.clone(), i, f.clone())?,
                ts.act(ctx.clone(), i, f.clone())?,
            ),
            Term::Id(a, u, v) => Ok(Rc::new(Term::Id(
                a.act(ctx.clone(), i, f.clone())?,
                u.act(ctx.clone(), i, f.clone())?,
                v.act(ctx.clone(), i, f.clone())?,
            ))),
            Term::IdPair(u, us) => Ok(Rc::new(Term::IdPair(
                u.act(ctx.clone(), i, f.clone())?,
                us.act(ctx.clone(), i, f.clone())?,
            ))),
            Term::IdJ(a, u, c, d, x, p) => Ok(Rc::new(Term::IdJ(
                a.act(ctx.clone(), i, f.clone())?,
                u.act(ctx.clone(), i, f.clone())?,
                c.act(ctx.clone(), i, f.clone())?,
                d.act(ctx.clone(), i, f.clone())?,
                x.act(ctx.clone(), i, f.clone())?,
                p.act(ctx.clone(), i, f.clone())?,
            ))),
            Term::Var(_) => Ok(self.clone()),
            Term::Sum(_, _) => Ok(self.clone()),
            Term::HSum(_, _) => Ok(self.clone()),
            Term::Undef(_) => Ok(self.clone()),
            Term::Hole => Ok(self.clone()),
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
            Term::Split(c, t, b) => Rc::new(Term::Split(c.clone(), t.swap(from, to), b.clone())),
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
