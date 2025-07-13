use crate::ctt::formula::Formula;
use crate::ctt::system::{Face, System};
use crate::ctt::term::Closure;
use crate::ctt::Identifier;
use crate::precise::term::Value;
use crate::typechecker::canon::app::{app, app_formula};
use crate::typechecker::canon::comp::{comp_line, comp_univ, hcomp, idj};
use crate::typechecker::canon::eval::{get_first, get_second, inv_formula, pcon};
use crate::typechecker::canon::glue::{glue, glue_elem, unglue_elem, unglue_u};
use crate::typechecker::context::{Entry, EntryValueState, TypeContext};
use crate::typechecker::error::TypeError;
use std::collections::HashMap;
use std::rc::Rc;

pub trait Nominal: Sized {
    fn sups_for_act(&self, i: &Identifier) -> bool;

    fn sups_for_swap(&self, i: &Identifier) -> bool;

    fn act(&self, ctx: &TypeContext, i: &Identifier, f: Formula) -> Result<Self, TypeError>;

    fn swap(&self, from: &Identifier, to: &Identifier) -> Self;
}

pub fn act_closure(
    ctx: &TypeContext,
    c: &Closure,
    i: &Identifier,
    f: Formula,
) -> Result<Option<Closure>, TypeError> {
    let mut updated = false;

    let mut term_binds = c.term_binds.clone();
    for (k, v) in &c.term_binds {
        let mut entry_update = false;
        let acted_value = match v.value() {
            EntryValueState::Cached(value) => {
                let acted = value.act(ctx, i, f.clone())?;
                if !Rc::ptr_eq(&acted, &value) {
                    entry_update = true;
                }
                EntryValueState::Cached(acted)
            }
            EntryValueState::Lazy(term) => EntryValueState::Lazy(term),
        };
        if entry_update {
            updated = true;
            term_binds = term_binds.insert(*k, Entry::new_state(acted_value));
        }
    }
    let mut type_binds = c.type_binds.clone();
    for (k, v) in &c.type_binds {
        let mut entry_update = false;
        let acted_value = match v.value() {
            EntryValueState::Cached(value) => {
                let acted = value.act(ctx, i, f.clone())?;
                if !Rc::ptr_eq(&acted, &value) {
                    entry_update = true;
                }
                EntryValueState::Cached(acted)
            }
            EntryValueState::Lazy(term) => EntryValueState::Lazy(term),
        };
        if entry_update {
            updated = true;
            type_binds = type_binds.insert(*k, Entry::new_state(acted_value));
        }
    }
    let mut formula_binds = c.formula_binds.clone();
    for (k, v) in &c.formula_binds {
        let acted_v = v.act(ctx, i, f.clone())?;
        if &acted_v != v {
            updated = true;
            formula_binds = formula_binds.insert(*k, acted_v);
        }
    }

    if updated {
        Ok(Some(Closure {
            shadowed: c.shadowed.clone(),
            term_binds,
            type_binds,
            formula_binds,
        }))
    } else {
        Ok(None)
    }
}

fn swap_closure(c: &Closure, from: &Identifier, to: &Identifier) -> Option<Closure> {
    let mut updated = false;

    let mut term_binds = c.term_binds.clone();
    for (k, v) in &c.term_binds {
        let mut entry_update = false;
        let swapped_value = match v.value() {
            EntryValueState::Cached(value) => {
                let swapped = value.swap(from, to);
                if !Rc::ptr_eq(&swapped, &value) {
                    entry_update = true;
                }
                EntryValueState::Cached(swapped)
            }
            EntryValueState::Lazy(term) => EntryValueState::Lazy(term),
        };
        if entry_update {
            updated = true;
            term_binds = term_binds.insert(*k, Entry::new_state(swapped_value));
        }
    }
    let mut type_binds = c.type_binds.clone();
    for (k, v) in &c.type_binds {
        let mut entry_update = false;
        let swapped_value = match v.value() {
            EntryValueState::Cached(value) => {
                let swapped = value.swap(from, to);
                if !Rc::ptr_eq(&swapped, &value) {
                    entry_update = true;
                }
                EntryValueState::Cached(swapped)
            }
            EntryValueState::Lazy(term) => EntryValueState::Lazy(term),
        };
        if entry_update {
            updated = true;
            type_binds = type_binds.insert(*k, Entry::new_state(swapped_value));
        }
    }
    let mut formula_binds = c.formula_binds.clone();
    for (k, v) in &c.formula_binds {
        let acted_v = v.swap(from, to);
        if &acted_v != v {
            updated = true;
            formula_binds = formula_binds.insert(*k, acted_v);
        }
    }

    if updated {
        Some(Closure {
            shadowed: c.shadowed.clone(),
            term_binds,
            type_binds,
            formula_binds,
        })
    } else {
        None
    }
}

impl Nominal for Rc<Value> {
    fn sups_for_act(&self, i: &Identifier) -> bool {
        match self.as_ref() {
            Value::Stuck(_, c, _) => {
                fn closure_sups(c: &Closure, i: &Identifier) -> bool {
                    for (_, e) in &c.term_binds {
                        match e.value() {
                            EntryValueState::Cached(v) => {
                                if v.sups_for_act(i) {
                                    return true;
                                }
                            }
                            _ => (),
                        }
                    }
                    for (_, e) in &c.type_binds {
                        match e.value() {
                            EntryValueState::Cached(v) => {
                                if v.sups_for_act(i) {
                                    return true;
                                }
                            }
                            _ => (),
                        }
                    }
                    for (_, f) in &c.formula_binds {
                        if f.sups_for_act(i) {
                            return true;
                        }
                    }
                    false
                }
                closure_sups(c, i)
            }
            Value::Pi(a, t, _) => a.sups_for_act(i) || t.sups_for_act(i),
            Value::App(t1, t2, _) => t1.sups_for_act(i) || t2.sups_for_act(i),
            Value::Var(_, t, _) => t.sups_for_act(i),
            Value::U => false,
            Value::Sigma(a, t, _) => a.sups_for_act(i) || t.sups_for_act(i),
            Value::Pair(t1, t2, _) => t1.sups_for_act(i) || t2.sups_for_act(i),
            Value::Fst(t, _) => t.sups_for_act(i),
            Value::Snd(t, _) => t.sups_for_act(i),
            Value::Con(_, ts, _) => ts.iter().any(|v| v.sups_for_act(i)),
            Value::PCon(_, t, ts, is, _) => {
                t.sups_for_act(i)
                    || ts.iter().any(|v| v.sups_for_act(i))
                    || is.iter().any(|f| f.sups_for_act(i))
            }
            Value::PathP(t1, t2, t3, _) => {
                t1.sups_for_act(i) || t2.sups_for_act(i) || t3.sups_for_act(i)
            }
            Value::PLam(n, t, _) => n != i && t.sups_for_act(i),
            Value::AppFormula(t, f, _) => t.sups_for_act(i) || f.sups_for_act(i),
            Value::Comp(t1, t2, system, _) => {
                t1.sups_for_act(i) || t2.sups_for_act(i) || system.sups_for_act(i)
            }
            Value::CompU(t, system, _) => t.sups_for_act(i) || system.sups_for_act(i),
            Value::HComp(t1, t2, system, _) => {
                t1.sups_for_act(i) || t2.sups_for_act(i) || system.sups_for_act(i)
            }
            Value::Glue(t, system, _) => t.sups_for_act(i) || system.sups_for_act(i),
            Value::GlueElem(t, system, _) => t.sups_for_act(i) || system.sups_for_act(i),
            Value::UnGlueElem(t, system, _) => t.sups_for_act(i) || system.sups_for_act(i),
            Value::UnGlueElemU(t, b, system, _) => {
                t.sups_for_act(i) || b.sups_for_act(i) || system.sups_for_act(i)
            }
            Value::Id(t1, t2, t3, _) => {
                t1.sups_for_act(i) || t2.sups_for_act(i) || t3.sups_for_act(i)
            }
            Value::IdPair(t, system, _) => t.sups_for_act(i) || system.sups_for_act(i),

            Value::IdJ(t1, t2, t3, t4, t5, t6, _) => {
                t1.sups_for_act(i)
                    || t2.sups_for_act(i)
                    || t3.sups_for_act(i)
                    || t4.sups_for_act(i)
                    || t5.sups_for_act(i)
                    || t6.sups_for_act(i)
            }
        }
    }

    fn sups_for_swap(&self, i: &Identifier) -> bool {
        match self.as_ref() {
            Value::PLam(j, v, _) => j == i || v.sups_for_swap(i),
            Value::Stuck(_, c, _) => {
                fn closure_sups(c: &Closure, i: &Identifier) -> bool {
                    for (_, e) in &c.term_binds {
                        match e.value() {
                            EntryValueState::Cached(v) => {
                                if v.sups_for_swap(i) {
                                    return true;
                                }
                            }
                            _ => (),
                        }
                    }
                    for (_, e) in &c.type_binds {
                        match e.value() {
                            EntryValueState::Cached(v) => {
                                if v.sups_for_swap(i) {
                                    return true;
                                }
                            }
                            _ => (),
                        }
                    }
                    for (_, f) in &c.formula_binds {
                        if f.sups_for_swap(i) {
                            return true;
                        }
                    }
                    false
                }
                closure_sups(c, i)
            }
            Value::Pi(a, t, _) => a.sups_for_swap(i) || t.sups_for_swap(i),
            Value::App(t1, t2, _) => t1.sups_for_swap(i) || t2.sups_for_swap(i),
            Value::Var(_, t, _) => t.sups_for_swap(i),
            Value::U => false,
            Value::Sigma(a, t, _) => a.sups_for_swap(i) || t.sups_for_swap(i),
            Value::Pair(t1, t2, _) => t1.sups_for_swap(i) || t2.sups_for_swap(i),
            Value::Fst(t, _) => t.sups_for_swap(i),
            Value::Snd(t, _) => t.sups_for_swap(i),
            Value::Con(_, ts, _) => ts.iter().any(|v| v.sups_for_swap(i)),
            Value::PCon(_, t, ts, is, _) => {
                t.sups_for_swap(i)
                    || ts.iter().any(|v| v.sups_for_swap(i))
                    || is.iter().any(|f| f.sups_for_swap(i))
            }
            Value::PathP(t1, t2, t3, _) => {
                t1.sups_for_swap(i) || t2.sups_for_swap(i) || t3.sups_for_swap(i)
            }
            Value::AppFormula(t, f, _) => t.sups_for_swap(i) || f.sups_for_swap(i),
            Value::Comp(t1, t2, system, _) => {
                t1.sups_for_swap(i) || t2.sups_for_swap(i) || system.sups_for_swap(i)
            }
            Value::CompU(t, system, _) => t.sups_for_swap(i) || system.sups_for_swap(i),
            Value::HComp(t1, t2, system, _) => {
                t1.sups_for_swap(i) || t2.sups_for_swap(i) || system.sups_for_swap(i)
            }
            Value::Glue(t, system, _) => t.sups_for_swap(i) || system.sups_for_swap(i),
            Value::GlueElem(t, system, _) => t.sups_for_swap(i) || system.sups_for_swap(i),
            Value::UnGlueElem(t, system, _) => t.sups_for_swap(i) || system.sups_for_swap(i),
            Value::UnGlueElemU(t, b, system, _) => {
                t.sups_for_swap(i) || b.sups_for_swap(i) || system.sups_for_swap(i)
            }
            Value::Id(t1, t2, t3, _) => {
                t1.sups_for_swap(i) || t2.sups_for_swap(i) || t3.sups_for_swap(i)
            }
            Value::IdPair(t, system, _) => t.sups_for_swap(i) || system.sups_for_swap(i),

            Value::IdJ(t1, t2, t3, t4, t5, t6, _) => {
                t1.sups_for_swap(i)
                    || t2.sups_for_swap(i)
                    || t3.sups_for_swap(i)
                    || t4.sups_for_swap(i)
                    || t5.sups_for_swap(i)
                    || t6.sups_for_swap(i)
            }
        }
    }

    fn act(&self, ctx: &TypeContext, i: &Identifier, f: Formula) -> Result<Self, TypeError> {
        fn act_formula(
            ctx: &TypeContext,
            o: &Formula,
            i: &Identifier,
            f: Formula,
        ) -> Result<Option<Formula>, TypeError> {
            if o.sups_for_act(i) {
                Ok(Some(o.act(ctx, i, f)?))
            } else {
                Ok(None)
            }
        }

        fn act_system(
            ctx: &TypeContext,
            o: &System<Rc<Value>>,
            i: &Identifier,
            f: Formula,
        ) -> Result<Option<System<Rc<Value>>>, TypeError> {
            if o.sups_for_act(i) {
                Ok(Some(o.act(ctx, i, f)?))
            } else {
                Ok(None)
            }
        }

        let res = match self.as_ref() {
            Value::Stuck(t, c, m) => {
                if let Some(new_c) = act_closure(ctx, c, i, f)? {
                    Ok(Rc::new(Value::Stuck(t.clone(), new_c, m.clone())))
                } else {
                    Ok(self.clone())
                }
            }
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
                        if x.sups_for_act(i) {
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
                    if !f.sups_for_act(j) {
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
            Value::Var(n, t, m) => {
                let new_t = t.act(ctx, i, f)?;
                if Rc::ptr_eq(t, &new_t) {
                    Ok(self.clone())
                } else {
                    Ok(Value::var(*n, &new_t, m.clone()))
                }
            }
            Value::U => Ok(self.clone()),
        }?;
        Ok(res)
    }

    fn swap(&self, from: &Identifier, to: &Identifier) -> Self {
        fn swap_formula(o: &Formula, from: &Identifier, to: &Identifier) -> Option<Formula> {
            if o.sups_for_swap(from) || o.sups_for_swap(to) {
                Some(o.swap(from, to))
            } else {
                None
            }
        }

        fn swap_system(
            o: &System<Rc<Value>>,
            from: &Identifier,
            to: &Identifier,
        ) -> Option<System<Rc<Value>>> {
            if o.sups_for_swap(from) || o.sups_for_swap(to) {
                Some(o.swap(from, to))
            } else {
                None
            }
        }

        match self.as_ref() {
            Value::U => self.clone(),
            Value::Var(n, t, m) => {
                let new_t = t.swap(from, to);
                if Rc::ptr_eq(t, &new_t) {
                    self.clone()
                } else {
                    Value::var(*n, &new_t, m.clone())
                }
            }
            Value::Pi(t, u, m) => {
                let new_t = t.swap(from, to);
                let new_u = u.swap(from, to);
                if Rc::ptr_eq(&new_t, t) && Rc::ptr_eq(&new_u, u) {
                    self.clone()
                } else {
                    Rc::new(Value::Pi(new_t, new_u, m.clone()))
                }
            }
            Value::App(a, b, m) => {
                let new_a = a.swap(from, to);
                let new_b = b.swap(from, to);
                if Rc::ptr_eq(&new_a, a) && Rc::ptr_eq(&new_b, b) {
                    self.clone()
                } else {
                    Rc::new(Value::App(new_a, new_b, m.clone()))
                }
            }
            Value::Sigma(a, t, m) => {
                let new_a = a.swap(from, to);
                let new_t = t.swap(from, to);
                if Rc::ptr_eq(&new_a, a) && Rc::ptr_eq(&new_t, t) {
                    self.clone()
                } else {
                    Rc::new(Value::Sigma(new_a, new_t, m.clone()))
                }
            }
            Value::Pair(fst, snd, m) => {
                let new_fst = fst.swap(from, to);
                let new_snd = snd.swap(from, to);
                if Rc::ptr_eq(&new_fst, fst) && Rc::ptr_eq(&new_snd, snd) {
                    self.clone()
                } else {
                    Rc::new(Value::Pair(new_fst, new_snd, m.clone()))
                }
            }
            Value::Fst(v, m) => {
                let new_v = v.swap(from, to);
                if Rc::ptr_eq(&new_v, v) {
                    self.clone()
                } else {
                    Rc::new(Value::Fst(new_v, m.clone()))
                }
            }
            Value::Snd(v, m) => {
                let new_v = v.swap(from, to);
                if Rc::ptr_eq(&new_v, v) {
                    self.clone()
                } else {
                    Rc::new(Value::Snd(new_v, m.clone()))
                }
            }
            Value::Con(c, a, m) => {
                let mut changed = false;
                let new_a: Vec<_> = a
                    .iter()
                    .map(|x| {
                        let new_x = x.swap(from, to);
                        if !Rc::ptr_eq(&new_x, x) {
                            changed = true;
                        }
                        new_x
                    })
                    .collect();

                if !changed {
                    self.clone()
                } else {
                    Rc::new(Value::Con(*c, new_a, m.clone()))
                }
            }
            Value::PCon(c, t, vs, phis, m) => {
                let new_t = t.swap(from, to);
                let mut vs_changed = false;
                let new_vs: Vec<_> = vs
                    .iter()
                    .map(|x| {
                        let new_x = x.swap(from, to);
                        if !Rc::ptr_eq(&new_x, x) {
                            vs_changed = true;
                        }
                        new_x
                    })
                    .collect();

                let mut phis_changed = false;
                let new_phis: Vec<_> = phis
                    .iter()
                    .map(|x| {
                        if x.sups_for_swap(from) || x.sups_for_swap(to) {
                            let new_x = x.swap(from, to);
                            phis_changed = true;
                            new_x
                        } else {
                            x.clone()
                        }
                    })
                    .collect();

                if Rc::ptr_eq(&new_t, t) && !vs_changed && !phis_changed {
                    self.clone()
                } else {
                    Rc::new(Value::PCon(*c, new_t, new_vs, new_phis, m.clone()))
                }
            }
            Value::PathP(a, u, v, m) => {
                let new_a = a.swap(from, to);
                let new_u = u.swap(from, to);
                let new_v = v.swap(from, to);
                if Rc::ptr_eq(&new_a, a) && Rc::ptr_eq(&new_u, u) && Rc::ptr_eq(&new_v, v) {
                    self.clone()
                } else {
                    Rc::new(Value::PathP(new_a, new_u, new_v, m.clone()))
                }
            }
            Value::PLam(j, v, m) => {
                let k = if j == from {
                    to
                } else if j == to {
                    from
                } else {
                    j
                };

                if k == j {
                    let new_v = v.swap(from, to);
                    if Rc::ptr_eq(&new_v, v) {
                        self.clone()
                    } else {
                        Rc::new(Value::PLam(*j, new_v, m.clone()))
                    }
                } else {
                    let new_v = v.swap(from, to);
                    Rc::new(Value::PLam(*k, new_v, m.clone()))
                }
            }
            Value::AppFormula(b, c, m) => {
                let new_b = b.swap(from, to);
                let new_c = swap_formula(c, from, to);
                if Rc::ptr_eq(&new_b, b) && new_c.is_none() {
                    self.clone()
                } else {
                    Rc::new(Value::AppFormula(
                        new_b,
                        new_c.unwrap_or(c.clone()),
                        m.clone(),
                    ))
                }
            }
            Value::Comp(a, v, ts, m) => {
                let new_a = a.swap(from, to);
                let new_v = v.swap(from, to);
                let new_ts = swap_system(ts, from, to);
                if Rc::ptr_eq(&new_a, a) && Rc::ptr_eq(&new_v, v) && new_ts.is_none() {
                    self.clone()
                } else {
                    Rc::new(Value::Comp(
                        new_a,
                        new_v,
                        new_ts.unwrap_or(ts.clone()),
                        m.clone(),
                    ))
                }
            }
            Value::CompU(v, ts, m) => {
                let new_v = v.swap(from, to);
                let new_ts = swap_system(ts, from, to);
                if Rc::ptr_eq(&new_v, v) && new_ts.is_none() {
                    self.clone()
                } else {
                    Rc::new(Value::CompU(new_v, new_ts.unwrap_or(ts.clone()), m.clone()))
                }
            }
            Value::HComp(a, u, us, m) => {
                let new_a = a.swap(from, to);
                let new_u = u.swap(from, to);
                let new_us = swap_system(us, from, to);
                if Rc::ptr_eq(&new_a, a) && Rc::ptr_eq(&new_u, u) && new_us.is_none() {
                    self.clone()
                } else {
                    Rc::new(Value::HComp(
                        new_a,
                        new_u,
                        new_us.unwrap_or(us.clone()),
                        m.clone(),
                    ))
                }
            }
            Value::Glue(a, ts, m) => {
                let new_a = a.swap(from, to);
                let new_ts = swap_system(ts, from, to);
                if Rc::ptr_eq(&new_a, a) && new_ts.is_none() {
                    self.clone()
                } else {
                    Rc::new(Value::Glue(new_a, new_ts.unwrap_or(ts.clone()), m.clone()))
                }
            }
            Value::GlueElem(a, ts, m) => {
                let new_a = a.swap(from, to);
                let new_ts = swap_system(ts, from, to);
                if Rc::ptr_eq(&new_a, a) && new_ts.is_none() {
                    self.clone()
                } else {
                    Rc::new(Value::GlueElem(
                        new_a,
                        new_ts.unwrap_or(ts.clone()),
                        m.clone(),
                    ))
                }
            }
            Value::UnGlueElem(a, ts, m) => {
                let new_a = a.swap(from, to);
                let new_ts = swap_system(ts, from, to);
                if Rc::ptr_eq(&new_a, a) && new_ts.is_none() {
                    self.clone()
                } else {
                    Rc::new(Value::UnGlueElem(
                        new_a,
                        new_ts.unwrap_or(ts.clone()),
                        m.clone(),
                    ))
                }
            }
            Value::UnGlueElemU(a, b, ts, m) => {
                let new_a = a.swap(from, to);
                let new_b = b.swap(from, to);
                let new_ts = swap_system(ts, from, to);
                if Rc::ptr_eq(&new_a, a) && Rc::ptr_eq(&new_b, b) && new_ts.is_none() {
                    self.clone()
                } else {
                    Rc::new(Value::UnGlueElemU(
                        new_a,
                        new_b,
                        new_ts.unwrap_or(ts.clone()),
                        m.clone(),
                    ))
                }
            }
            Value::Id(a, u, v, m) => {
                let new_a = a.swap(from, to);
                let new_u = u.swap(from, to);
                let new_v = v.swap(from, to);
                if Rc::ptr_eq(&new_a, a) && Rc::ptr_eq(&new_u, u) && Rc::ptr_eq(&new_v, v) {
                    self.clone()
                } else {
                    Rc::new(Value::Id(new_a, new_u, new_v, m.clone()))
                }
            }
            Value::IdPair(u, us, m) => {
                let new_u = u.swap(from, to);
                let new_us = swap_system(us, from, to);
                if Rc::ptr_eq(&new_u, u) && new_us.is_none() {
                    self.clone()
                } else {
                    Rc::new(Value::IdPair(
                        new_u,
                        new_us.unwrap_or(us.clone()),
                        m.clone(),
                    ))
                }
            }
            Value::IdJ(a, u, c, d, x, p, m) => {
                let new_a = a.swap(from, to);
                let new_u = u.swap(from, to);
                let new_c = c.swap(from, to);
                let new_d = d.swap(from, to);
                let new_x = x.swap(from, to);
                let new_p = p.swap(from, to);
                if Rc::ptr_eq(&new_a, a)
                    && Rc::ptr_eq(&new_u, u)
                    && Rc::ptr_eq(&new_c, c)
                    && Rc::ptr_eq(&new_d, d)
                    && Rc::ptr_eq(&new_x, x)
                    && Rc::ptr_eq(&new_p, p)
                {
                    self.clone()
                } else {
                    Rc::new(Value::IdJ(
                        new_a,
                        new_u,
                        new_c,
                        new_d,
                        new_x,
                        new_p,
                        m.clone(),
                    ))
                }
            }
            Value::Stuck(t, c, m) => {
                if let Some(new_c) = swap_closure(c, from, to) {
                    Rc::new(Value::Stuck(t.clone(), new_c, m.clone()))
                } else {
                    self.clone()
                }
            }
        }
    }
}

impl<A> Nominal for System<A>
where
    A: Nominal,
    A: Clone,
{
    fn sups_for_act(&self, i: &Identifier) -> bool {
        for (k, v) in self.iter() {
            if k.binds.contains_key(i) || v.sups_for_act(i) {
                return true;
            }
        }
        return false;
    }

    fn sups_for_swap(&self, i: &Identifier) -> bool {
        for (k, v) in self.iter() {
            if k.binds.contains_key(i) || v.sups_for_swap(i) {
                return true;
            }
        }
        return false;
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
                    let t = u.face(ctx, &delta_)?;
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
    fn sups_for_act(&self, i: &Identifier) -> bool {
        match self {
            Formula::Dir(_) => false,
            Formula::Atom(identifier) => identifier == i,
            Formula::NegAtom(identifier) => identifier == i,
            Formula::And(lhs, rhs) => lhs.sups_for_act(i) || rhs.sups_for_act(i),
            Formula::Or(lhs, rhs) => lhs.sups_for_act(i) || rhs.sups_for_act(i),
        }
    }

    fn sups_for_swap(&self, i: &Identifier) -> bool {
        match self {
            Formula::Dir(_) => false,
            Formula::Atom(identifier) => identifier == i,
            Formula::NegAtom(identifier) => identifier == i,
            Formula::And(lhs, rhs) => lhs.sups_for_swap(i) || rhs.sups_for_swap(i),
            Formula::Or(lhs, rhs) => lhs.sups_for_swap(i) || rhs.sups_for_swap(i),
        }
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

pub fn border<A: Clone, B: Clone>(
    ctx: &TypeContext,
    value: &A,
    shape: &System<B>,
) -> Result<System<A>, TypeError>
where
    A: Facing,
{
    shape
        .iter()
        .map(|(f, _)| Ok((f.clone(), value.face(ctx, f)?)))
        .collect::<Result<_, TypeError>>()
}

mod tests {
    use std::collections::HashMap;

    use crate::{
        ctt::{formula::Dir, system::Face, system::System, Identifier},
        precise::term::{Mod, Value},
        typechecker::{canon::nominal::Nominal, context::TypeContext},
    };

    use super::disj;

    #[test]
    fn act_system() {
        let s = System::from(HashMap::from([(
            Face::cond(&Identifier(0), Dir::One),
            Value::u(),
        )]));
        let k = disj(&TypeContext::empty(), &s, &Identifier(4), &Identifier(1));
        println!("k {:?}", k);
    }

    #[test]
    fn swap_with_plam() {
        let v = Value::comp_u(
            &Value::plam(Identifier(0), &Value::u(), Mod::Precise),
            System::from(HashMap::from([(
                Face::cond(&Identifier(2), Dir::Zero),
                Value::u(),
            )])),
            Mod::Precise,
        );

        Value::plam(Identifier(0), &Value::u(), Mod::Precise);
        let res = v.swap(&Identifier(2), &Identifier(1));
        println!("res {:?}", res);
    }
}
