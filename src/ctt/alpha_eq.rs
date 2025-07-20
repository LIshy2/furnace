use std::{cell::RefCell, collections::HashSet, rc::Rc, slice::SliceIndex};

use rpds::HashTrieMap;

use std::fmt::Debug;

use crate::{
    ctt::{
        formula::Formula,
        system::{Face, System},
        term::{Branch, Closure, DeclarationSet, Label, Telescope, Term, Value},
        Identifier,
    },
    typechecker::context::EntryValueState,
};

#[derive(Clone)]
pub struct AlphaContext {
    left_binds: HashTrieMap<Identifier, usize>,
    left_binds_inv: HashTrieMap<usize, Identifier>,
    right_binds: HashTrieMap<Identifier, usize>,
    right_binds_inv: HashTrieMap<usize, Identifier>,
    counter: Rc<RefCell<usize>>,
}

impl AlphaContext {
    pub fn new() -> AlphaContext {
        AlphaContext {
            left_binds: Default::default(),
            left_binds_inv: Default::default(),
            right_binds: Default::default(),
            right_binds_inv: Default::default(),
            counter: Default::default(),
        }
    }

    fn bind(&self, l: &Identifier, r: &Identifier) -> AlphaContext {
        let mut borrow = self.counter.borrow_mut();
        let res = *borrow;
        *borrow += 1;
        AlphaContext {
            left_binds: self.left_binds.insert(*l, res),
            left_binds_inv: self.left_binds_inv.insert(res, *l),
            right_binds: self.right_binds.insert(*r, res),
            right_binds_inv: self.right_binds_inv.insert(res, *r),
            counter: self.counter.clone(),
        }
    }

    fn is_eq(&self, l: &Identifier, r: &Identifier) -> bool {
        if !self.left_binds.contains_key(l) {
            l == r
        } else {
            self.left_binds[l] == self.right_binds[r]
        }
    }

    fn right_paired(&self, l: &Identifier) -> Identifier {
        if self.left_binds.contains_key(l) {
            self.right_binds_inv[&self.left_binds[l]]
        } else {
            *l
        }
    }

    fn left_paired(&self, r: &Identifier) -> Identifier {
        self.left_binds_inv[&self.right_binds[r]]
    }
}

impl Default for AlphaContext {
    fn default() -> Self {
        Self::new()
    }
}

pub trait AlphaEq {
    fn eq(ctx: &AlphaContext, lhs: &Self, rhs: &Self) -> bool;
}

impl<T: AlphaEq> AlphaEq for Rc<T> {
    fn eq(ctx: &AlphaContext, lhs: &Self, rhs: &Self) -> bool {
        AlphaEq::eq(ctx, lhs.as_ref(), rhs.as_ref())
    }
}

impl<T: AlphaEq> AlphaEq for Box<T> {
    fn eq(ctx: &AlphaContext, lhs: &Self, rhs: &Self) -> bool {
        AlphaEq::eq(ctx, lhs.as_ref(), rhs.as_ref())
    }
}

impl<T: AlphaEq> AlphaEq for Vec<T> {
    fn eq(ctx: &AlphaContext, lhs: &Self, rhs: &Self) -> bool {
        lhs.len() == rhs.len() && lhs.iter().zip(rhs).all(|(a, b)| AlphaEq::eq(ctx, a, b))
    }
}

impl AlphaEq for Closure {
    fn eq(ctx: &AlphaContext, lhs: &Self, rhs: &Self) -> bool {
        if lhs.term_binds.keys().collect::<HashSet<_>>()
            != rhs.term_binds.keys().collect::<HashSet<_>>()
        {
            return false;
        }
        if lhs.type_binds.keys().collect::<HashSet<_>>()
            != rhs.type_binds.keys().collect::<HashSet<_>>()
        {
            return false;
        }
        if lhs.formula_binds.keys().collect::<HashSet<_>>()
            != rhs.formula_binds.keys().collect::<HashSet<_>>()
        {
            return false;
        }
        for (k, lv) in &lhs.term_binds {
            let rv = &rhs.term_binds[k];
            match (lv.value(), rv.value()) {
                (EntryValueState::Lazy(term1), EntryValueState::Lazy(term2)) => {
                    if !AlphaEq::eq(ctx, &term1, &term2) {
                        return false;
                    }
                }
                (EntryValueState::Cached(value1), EntryValueState::Cached(value2)) => {
                    if !AlphaEq::eq(ctx, &value1, &value2) {
                        return false;
                    }
                }
                _ => {
                    return false;
                }
            }
        }
        for (k, lv) in &lhs.type_binds {
            let rv = &rhs.type_binds[k];
            match (lv.value(), rv.value()) {
                (EntryValueState::Lazy(term1), EntryValueState::Lazy(term2)) => {
                    if term1 != term2 {
                        return false;
                    }
                }
                (EntryValueState::Cached(value1), EntryValueState::Cached(value2)) => {
                    if !AlphaEq::eq(ctx, &value1, &value2) {
                        return false;
                    }
                }
                _ => {
                    return false;
                }
            }
        }
        for (k, lv) in &lhs.formula_binds {
            let rv = &rhs.formula_binds[&ctx.right_paired(k)];
            if !AlphaEq::eq(ctx, lv, rv) {
                return false;
            }
        }
        true
    }
}

impl AlphaEq for Formula {
    fn eq(ctx: &AlphaContext, lhs: &Self, rhs: &Self) -> bool {
        match (lhs, rhs) {
            (Formula::Dir(dir1), Formula::Dir(dir2)) => dir1 == dir2,
            (Formula::Atom(id1), Formula::Atom(id2)) => ctx.is_eq(id1, id2),
            (Formula::NegAtom(id1), Formula::NegAtom(id2)) => ctx.is_eq(id1, id2),
            (Formula::And(lf1, lf2), Formula::And(rf1, rf2)) => {
                AlphaEq::eq(ctx, lf1.as_ref(), rf1.as_ref())
                    && AlphaEq::eq(ctx, lf2.as_ref(), rf2.as_ref())
            }
            (Formula::Or(lf1, lf2), Formula::Or(rf1, rf2)) => {
                AlphaEq::eq(ctx, lf1.as_ref(), rf1.as_ref())
                    && AlphaEq::eq(ctx, lf2.as_ref(), rf2.as_ref())
            }
            _ => false,
        }
    }
}

impl<A: AlphaEq> AlphaEq for System<A> {
    fn eq(ctx: &AlphaContext, lhs: &Self, rhs: &Self) -> bool {
        if lhs.len() != rhs.len() {
            return false;
        }
        for (k1, v1) in lhs.iter() {
            let k2 = Face {
                binds: k1
                    .binds
                    .iter()
                    .map(|(i, d)| (ctx.right_paired(i), *d))
                    .collect(),
            };
            if let Some(v2) = rhs.get(&k2) {
                if !AlphaEq::eq(ctx, v1, v2) {
                    return false;
                }
            } else {
                return false;
            }
        }
        true
    }
}

impl<A: AlphaEq> AlphaEq for Telescope<A> {
    fn eq(ctx: &AlphaContext, lhs: &Self, rhs: &Self) -> bool {
        let mut ctx = ctx.clone();
        for ((x1, tpe1), (x2, tpe2)) in lhs.variables.iter().zip(&rhs.variables) {
            if !AlphaEq::eq(&ctx, tpe1, tpe2) {
                return false;
            }
            ctx = ctx.bind(x1, x2);
        }
        true
    }
}

impl<M> AlphaEq for Term<M> {
    fn eq(ctx: &AlphaContext, lhs: &Self, rhs: &Self) -> bool {
        match (lhs, rhs) {
            (Term::Pi(a, _), Term::Pi(b, _)) => AlphaEq::eq(ctx, a, b),
            (Term::App(f1, a1, _), Term::App(f2, a2, _)) => {
                AlphaEq::eq(ctx, f1, f2) && AlphaEq::eq(ctx, a1, a2)
            }
            (Term::Lam(id1, ty1, body1, _), Term::Lam(id2, ty2, body2, _)) => {
                let new_ctx = ctx.bind(id1, id2);
                AlphaEq::eq(ctx, ty1, ty2) && AlphaEq::eq(&new_ctx, body1, body2)
            }
            (Term::Where(t1, ds1, _), Term::Where(t2, ds2, _)) => {
                AlphaEq::eq(ctx, t1, t2) && {
                    match (ds1, ds2) {
                        (DeclarationSet::Mutual(decls1), DeclarationSet::Mutual(decls2)) => {
                            decls1.len() == decls2.len()
                                && decls1.iter().zip(decls2).all(|(d1, d2)| {
                                    d1.name == d2.name
                                        && AlphaEq::eq(ctx, &d1.body, &d2.body)
                                        && AlphaEq::eq(ctx, &d1.tpe, &d2.tpe)
                                })
                        }
                        (DeclarationSet::Opaque(id1), DeclarationSet::Opaque(id2)) => id1 == id2,
                        (DeclarationSet::Transparent(id1), DeclarationSet::Transparent(id2)) => {
                            id1 == id2
                        }
                        (DeclarationSet::TransparentAll, DeclarationSet::TransparentAll) => true,
                        _ => false,
                    }
                }
            }
            (Term::Var(id1, _), Term::Var(id2, _)) => ctx.is_eq(id1, id2),
            (Term::U, Term::U) => true,
            (Term::Sigma(a, _), Term::Sigma(b, _)) => AlphaEq::eq(ctx, a, b),
            (Term::Pair(a1, b1, _), Term::Pair(a2, b2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, b1, b2)
            }
            (Term::Fst(p1, _), Term::Fst(p2, _)) => AlphaEq::eq(ctx, p1, p2),
            (Term::Snd(p1, _), Term::Snd(p2, _)) => AlphaEq::eq(ctx, p1, p2),
            (Term::Con(id1, args1, _), Term::Con(id2, args2, _)) => {
                id1 == id2 && AlphaEq::eq(ctx, args1, args2)
            }
            (Term::PCon(id1, ty1, args1, form1, _), Term::PCon(id2, ty2, args2, form2, _)) => {
                id1 == id2
                    && AlphaEq::eq(ctx, ty1, ty2)
                    && AlphaEq::eq(ctx, args1, args2)
                    && AlphaEq::eq(ctx, form1, form2)
            }
            (Term::Split(_, t1, br1, _), Term::Split(_, t2, br2, _)) => {
                AlphaEq::eq(ctx, t1, t2)
                    && br1.len() == br2.len()
                    && br1.iter().zip(br2).all(|bs| match bs {
                        (
                            Branch::OBranch(id1, args1, body1),
                            Branch::OBranch(id2, args2, body2),
                        ) => {
                            id1 == id2 && args1.len() == args2.len() && {
                                let new_ctx = args1
                                    .iter()
                                    .zip(args2)
                                    .fold(ctx.clone(), |acc, (id1, id2)| acc.bind(id1, id2));
                                AlphaEq::eq(&new_ctx, body1, body2)
                            }
                        }
                        (
                            Branch::PBranch(id1, args1, ints1, body1),
                            Branch::PBranch(id2, args2, ints2, body2),
                        ) => {
                            id1 == id2
                                && args1.len() == args2.len()
                                && ints1.len() == ints2.len()
                                && {
                                    let arg_ctx = args1
                                        .iter()
                                        .zip(args2)
                                        .fold(ctx.clone(), |acc, (id1, id2)| acc.bind(id1, id2));
                                    let new_ctx = ints1
                                        .iter()
                                        .zip(ints2)
                                        .fold(arg_ctx, |acc, (id1, id2)| acc.bind(id1, id2));
                                    AlphaEq::eq(&new_ctx, body1, body2)
                                }
                        }
                        _ => false,
                    })
            }
            (Term::Sum(id1, labels1, _), Term::Sum(id2, labels2, _)) => {
                id1 == id2
                    && labels1.iter().zip(labels2).all(|ls| match ls {
                        (Label::OLabel(id1, tele1), Label::OLabel(id2, tele2)) => {
                            id1 == id2 && AlphaEq::eq(ctx, tele1, tele2)
                        }
                        (
                            Label::PLabel(id1, tele1, ints1, sys1),
                            Label::PLabel(id2, tele2, ints2, sys2),
                        ) => {
                            id1 == id2
                                && AlphaEq::eq(ctx, tele1, tele2)
                                && ints1.len() == ints2.len()
                                && {
                                    let new_ctx = ints1
                                        .iter()
                                        .zip(ints2)
                                        .fold(ctx.clone(), |acc, (id1, id2)| acc.bind(id1, id2));
                                    AlphaEq::eq(&new_ctx, sys1, sys2)
                                }
                        }
                        _ => false,
                    })
            }
            (Term::HSum(id1, labels1, _), Term::HSum(id2, labels2, _)) => {
                id1 == id2
                    && labels1.iter().zip(labels2).all(|ls| match ls {
                        (Label::OLabel(id1, tele1), Label::OLabel(id2, tele2)) => {
                            id1 == id2 && AlphaEq::eq(ctx, tele1, tele2)
                        }
                        (
                            Label::PLabel(id1, tele1, ints1, sys1),
                            Label::PLabel(id2, tele2, ints2, sys2),
                        ) => {
                            id1 == id2
                                && AlphaEq::eq(ctx, tele1, tele2)
                                && ints1.len() == ints2.len()
                                && {
                                    let new_ctx = ints1
                                        .iter()
                                        .zip(ints2)
                                        .fold(ctx.clone(), |acc, (id1, id2)| acc.bind(id1, id2));
                                    AlphaEq::eq(&new_ctx, sys1, sys2)
                                }
                        }
                        _ => false,
                    })
            }
            (Term::Undef(t1, _), Term::Undef(t2, _)) => AlphaEq::eq(ctx, t1, t2),
            (Term::Hole, Term::Hole) => true,
            (Term::PathP(a1, b1, c1, _), Term::PathP(a2, b2, c2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, b1, b2) && AlphaEq::eq(ctx, c1, c2)
            }
            (Term::PLam(id1, t1, _), Term::PLam(id2, t2, _)) => {
                let new_ctx = ctx.bind(id1, id2);
                AlphaEq::eq(&new_ctx, t1, t2)
            }
            (Term::AppFormula(t1, f1, _), Term::AppFormula(t2, f2, _)) => {
                AlphaEq::eq(ctx, t1, t2) && AlphaEq::eq(ctx, f1, f2)
            }
            (Term::Comp(t1, u1, sys1, _), Term::Comp(t2, u2, sys2, _)) => {
                AlphaEq::eq(ctx, t1, t2) && AlphaEq::eq(ctx, u1, u2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Term::Fill(t1, u1, sys1, _), Term::Fill(t2, u2, sys2, _)) => {
                AlphaEq::eq(ctx, t1, t2) && AlphaEq::eq(ctx, u1, u2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Term::HComp(t1, u1, sys1, _), Term::HComp(t2, u2, sys2, _)) => {
                AlphaEq::eq(ctx, t1, t2) && AlphaEq::eq(ctx, u1, u2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Term::Glue(t1, sys1, _), Term::Glue(t2, sys2, _)) => {
                AlphaEq::eq(ctx, t1, t2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Term::GlueElem(t1, sys1, _), Term::GlueElem(t2, sys2, _)) => {
                AlphaEq::eq(ctx, t1, t2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Term::UnGlueElem(t1, sys1, _), Term::UnGlueElem(t2, sys2, _)) => {
                AlphaEq::eq(ctx, t1, t2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Term::Id(a1, b1, c1, _), Term::Id(a2, b2, c2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, b1, b2) && AlphaEq::eq(ctx, c1, c2)
            }
            (Term::IdPair(t1, sys1, _), Term::IdPair(t2, sys2, _)) => {
                AlphaEq::eq(ctx, t1, t2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Term::IdJ(a1, b1, c1, d1, e1, f1, _), Term::IdJ(a2, b2, c2, d2, e2, f2, _)) => {
                AlphaEq::eq(ctx, a1, a2)
                    && AlphaEq::eq(ctx, b1, b2)
                    && AlphaEq::eq(ctx, c1, c2)
                    && AlphaEq::eq(ctx, d1, d2)
                    && AlphaEq::eq(ctx, e1, e2)
                    && AlphaEq::eq(ctx, f1, f2)
            }
            _ => false,
        }
    }
}

impl<M> AlphaEq for Value<M> {
    fn eq(ctx: &AlphaContext, lhs: &Self, rhs: &Self) -> bool {
        match (lhs, rhs) {
            (Value::Stuck(t1, c1, _), Value::Stuck(t2, c2, _)) => {
                AlphaEq::eq(ctx, t1, t2) && AlphaEq::eq(ctx, c1, c2)
            }
            (Value::Pi(t1, a1, _), Value::Pi(t2, a2, _)) => {
                AlphaEq::eq(ctx, t1, t2) && AlphaEq::eq(ctx, a1, a2)
            }
            (Value::App(f1, arg1, _), Value::App(f2, arg2, _)) => {
                AlphaEq::eq(ctx, f1, f2) && AlphaEq::eq(ctx, arg1, arg2)
            }
            (Value::Var(n1, t1, _), Value::Var(n2, t2, _)) => {
                ctx.is_eq(n1, n2) && AlphaEq::eq(ctx, t1, t2)
            }
            (Value::U, Value::U) => true,
            (Value::Sigma(t1, a1, _), Value::Sigma(t2, a2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, t1, t2)
            }
            (Value::Pair(a1, b1, _), Value::Pair(a2, b2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, b1, b2)
            }
            (Value::Fst(p1, _), Value::Fst(p2, _)) => AlphaEq::eq(ctx, p1, p2),
            (Value::Snd(p1, _), Value::Snd(p2, _)) => AlphaEq::eq(ctx, p1, p2),
            (Value::Con(n1, args1, _), Value::Con(n2, args2, _)) => {
                n1 == n2 && AlphaEq::eq(ctx, args1, args2)
            }
            (Value::PCon(n1, ty1, args1, faces1, _), Value::PCon(n2, ty2, args2, faces2, _)) => {
                n1 == n2
                    && AlphaEq::eq(ctx, ty1, ty2)
                    && AlphaEq::eq(ctx, args1, args2)
                    && AlphaEq::eq(ctx, faces1, faces2)
            }
            (Value::PathP(a1, b1, ty1, _), Value::PathP(a2, b2, ty2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, b1, b2) && AlphaEq::eq(ctx, ty1, ty2)
            }
            (Value::PLam(n1, b1, _), Value::PLam(n2, b2, _)) => {
                let new_ctx = ctx.bind(n1, n2);
                AlphaEq::eq(&new_ctx, b1, b2)
            }
            (Value::AppFormula(f1, form1, _), Value::AppFormula(f2, form2, _)) => {
                AlphaEq::eq(ctx, f1, f2) && AlphaEq::eq(ctx, form1, form2)
            }
            (Value::Comp(a1, b1, sys1, _), Value::Comp(a2, b2, sys2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, b1, b2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Value::CompU(a1, sys1, _), Value::CompU(a2, sys2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Value::HComp(a1, b1, sys1, _), Value::HComp(a2, b2, sys2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, b1, b2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Value::Glue(a1, sys1, _), Value::Glue(a2, sys2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Value::GlueElem(a1, sys1, _), Value::GlueElem(a2, sys2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Value::UnGlueElem(a1, sys1, _), Value::UnGlueElem(a2, sys2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Value::UnGlueElemU(a1, b1, sys1, _), Value::UnGlueElemU(a2, b2, sys2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, b1, b2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Value::Id(a1, x1, y1, _), Value::Id(a2, x2, y2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, x1, x2) && AlphaEq::eq(ctx, y1, y2)
            }
            (Value::IdPair(a1, sys1, _), Value::IdPair(a2, sys2, _)) => {
                AlphaEq::eq(ctx, a1, a2) && AlphaEq::eq(ctx, sys1, sys2)
            }
            (Value::IdJ(a1, x1, y1, p1, m1, c1, _), Value::IdJ(a2, x2, y2, p2, m2, c2, _)) => {
                AlphaEq::eq(ctx, a1, a2)
                    && AlphaEq::eq(ctx, x1, x2)
                    && AlphaEq::eq(ctx, y1, y2)
                    && AlphaEq::eq(ctx, p1, p2)
                    && AlphaEq::eq(ctx, m1, m2)
                    && AlphaEq::eq(ctx, c1, c2)
            }
            _ => false,
        }
    }
}
