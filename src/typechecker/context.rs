use crate::ctt::term::{Branch, Closure, DeclarationSet, Face, Formula, Identifier, Label, System};
use crate::precise::term::{Mod, Term, Value};
use crate::typechecker::canon::eval::eval;
use crate::typechecker::canon::heat::PathIndex;
use crate::typechecker::error::TypeError;
use rpds::{HashTrieMap, HashTrieSet};
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::Debug;
use std::rc::Rc;

use super::canon::nominal::Facing;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub tpe: Rc<Value>,
    pub value: Rc<Value>,
}

#[derive(Clone)]
pub enum TypeContext {
    Clear {
        term_binds: HashTrieMap<Identifier, Entry>,
        shadowed: HashTrieSet<Identifier>,
        formula_binds: HashTrieMap<Identifier, Formula>,
        counter: Rc<RefCell<usize>>,
        path_index: Rc<RefCell<PathIndex>>,
        is_compact: bool,
        notifier: Option<Rc<dyn ProgressNotifier>>,
    },
    Faced {
        ctx: Box<TypeContext>,
        cache: Rc<RefCell<HashTrieMap<Identifier, Entry>>>,
        face: Face,
    },
}

impl TypeContext {
    pub fn empty() -> TypeContext {
        TypeContext::Clear {
            term_binds: HashTrieMap::new(),
            shadowed: HashTrieSet::new(),
            formula_binds: HashTrieMap::new(),
            counter: Rc::new(RefCell::new(99999)),
            path_index: Rc::new(RefCell::new(PathIndex::new())),
            is_compact: true,
            notifier: None,
        }
    }

    pub fn new(notifier: Rc<dyn ProgressNotifier>) -> TypeContext {
        TypeContext::Clear {
            term_binds: HashTrieMap::new(),
            shadowed: HashTrieSet::new(),
            formula_binds: HashTrieMap::new(),
            counter: Rc::new(RefCell::new(99999)),
            path_index: Rc::new(RefCell::new(PathIndex::new())),
            is_compact: true,
            notifier: Some(notifier),
        }
    }

    pub fn opaque(&self, name: Identifier) -> TypeContext {
        match self {
            TypeContext::Clear {
                term_binds,
                shadowed,
                formula_binds,
                counter,
                path_index,
                is_compact,
                notifier,
            } => TypeContext::Clear {
                term_binds: term_binds.clone(),
                shadowed: shadowed.insert(name),
                formula_binds: formula_binds.clone(),
                counter: counter.clone(),
                path_index: path_index.clone(),
                is_compact: *is_compact,
                notifier: notifier.clone(),
            },
            TypeContext::Faced { ctx, cache, face } => TypeContext::Faced {
                ctx: Box::new(ctx.opaque(name)),
                cache: Rc::new(RefCell::new(cache.borrow().remove(&name))),
                face: face.clone(),
            },
        }
    }

    pub fn transparent(&self, name: Identifier) -> TypeContext {
        match self {
            TypeContext::Clear {
                term_binds,
                shadowed,
                formula_binds,
                counter,
                path_index,
                is_compact,
                notifier,
            } => TypeContext::Clear {
                term_binds: term_binds.clone(),
                shadowed: shadowed.remove(&name),
                formula_binds: formula_binds.clone(),
                counter: counter.clone(),
                path_index: path_index.clone(),
                is_compact: *is_compact,
                notifier: notifier.clone(),
            },
            TypeContext::Faced { ctx, cache, face } => TypeContext::Faced {
                ctx: Box::new(ctx.transparent(name)),
                cache: Rc::new(RefCell::new(cache.borrow().remove(&name))),
                face: face.clone(),
            },
        }
    }

    pub fn transparent_all(&self) -> TypeContext {
        match self {
            TypeContext::Clear {
                term_binds,
                formula_binds,
                counter,
                path_index,
                is_compact,
                notifier,
                ..
            } => TypeContext::Clear {
                term_binds: term_binds.clone(),
                shadowed: HashTrieSet::new(),
                formula_binds: formula_binds.clone(),
                counter: counter.clone(),
                path_index: path_index.clone(),
                is_compact: *is_compact,
                notifier: notifier.clone(),
            },
            TypeContext::Faced { ctx, face, .. } => TypeContext::Faced {
                ctx: Box::new(ctx.transparent_all()),
                cache: Rc::new(RefCell::new(HashTrieMap::new())),
                face: face.clone(),
            },
        }
    }

    pub fn fresh(&self) -> Identifier {
        match self {
            TypeContext::Clear { counter, .. } => {
                let res = *counter.borrow_mut();
                *counter.borrow_mut() += 1;
                Identifier(res)
            }
            TypeContext::Faced { ctx, .. } => ctx.fresh(),
        }
    }

    pub fn lookup_term(&self, name: &Identifier) -> Option<Entry> {
        match self {
            TypeContext::Clear {
                term_binds,
                shadowed,
                ..
            } => {
                let e = term_binds.get(name).cloned()?;
                let new_entry = Entry {
                    tpe: e.tpe,
                    value: if shadowed.contains(name) {
                        Value::var(*name, Mod::Precise)
                    } else {
                        e.value
                    },
                };
                Some(new_entry)
            }
            TypeContext::Faced { ctx, cache, face } => {
                let cache_entry = { cache.borrow().get(name).cloned() };
                if let Some(e) = cache_entry {
                    Some(e)
                } else {
                    let e = ctx.lookup_term(name)?;
                    let faced_e = Entry {
                        tpe: e.tpe.face(self, face).unwrap(),
                        value: e.value.face(self, face).unwrap(),
                    };
                    cache.replace_with(|c| c.insert(*name, faced_e.clone()));
                    Some(faced_e)
                }
            }
        }
    }

    pub fn lookup_formula(&self, name: &Identifier) -> Option<Formula> {
        match self {
            TypeContext::Clear { formula_binds, .. } => {
                let f = formula_binds.get(name).cloned()?;
                Some(f)
            }
            TypeContext::Faced { ctx, face, .. } => {
                Some(ctx.lookup_formula(name)?.face(self, face).unwrap())
            }
        }
    }

    // fn analyze_hsum(&self, hsum: &Rc<Term>) {
    //     if let Term::HSum(_, labels, ..) = hsum.as_ref() {
    //         for label in labels {
    //             if let Label::PLabel(_, _, is, sys) = label {
    //                 if is.len() == 1 && sys.len() == 2 {
    //                     let endpoints = sys.values().collect::<Vec<_>>();
    //                     self.path_index.borrow_mut().add(endpoints[0], endpoints[1]);
    //                 }
    //             }
    //         }
    //     }
    // }

    pub fn with_term(&self, name: &Identifier, value: &Rc<Value>, tpe: &Rc<Value>) -> TypeContext {
        match self {
            TypeContext::Clear {
                term_binds,
                shadowed,
                formula_binds,
                counter,
                path_index,
                is_compact,
                notifier,
            } => TypeContext::Clear {
                term_binds: term_binds.insert(
                    *name,
                    Entry {
                        value: value.clone(),
                        tpe: tpe.clone(),
                    },
                ),
                shadowed: shadowed.clone(),
                formula_binds: formula_binds.clone(),
                counter: counter.clone(),
                path_index: path_index.clone(),
                is_compact: *is_compact,
                notifier: notifier.clone(),
            },
            TypeContext::Faced { ctx, cache, face } => TypeContext::Faced {
                ctx: Box::new(ctx.with_term(name, value, tpe)),
                cache: Rc::new(RefCell::new(cache.borrow().clone())),
                face: face.clone(),
            },
        }
    }

    pub fn with_face(&self, face: &Face) -> Result<TypeContext, TypeError> {
        let res = face.binds.iter().fold(self.clone(), |acc, (k, v)| {
            acc.with_formula(k, Formula::Dir(v.clone()))
        });
        Ok(TypeContext::Faced {
            ctx: Box::new(res),
            cache: Rc::new(RefCell::new(HashTrieMap::new())),
            face: face.clone(),
        })
    }

    pub fn with_formula(&self, name: &Identifier, formula: Formula) -> TypeContext {
        match self {
            TypeContext::Clear {
                term_binds,
                shadowed,
                formula_binds,
                counter,
                path_index,
                is_compact,
                notifier,
            } => TypeContext::Clear {
                term_binds: term_binds.clone(),
                shadowed: shadowed.clone(),
                formula_binds: formula_binds.insert(*name, formula),
                counter: counter.clone(),
                path_index: path_index.clone(),
                is_compact: *is_compact,
                notifier: notifier.clone(),
            },
            TypeContext::Faced { ctx, cache, face } => TypeContext::Faced {
                ctx: Box::new(ctx.with_formula(name, formula)),
                cache: Rc::new(RefCell::new(cache.borrow().clone())),
                face: face.clone(),
            },
        }
    }

    pub fn with_decl_set(&self, decls: &DeclarationSet<Term>) -> Result<TypeContext, TypeError> {
        let mut new_ctx = self.clone();
        if let DeclarationSet::Mutual(decls) = decls {
            for decl in decls {
                let tpe = eval(&new_ctx, &decl.tpe)?;
                let rec_ctx = new_ctx.with_term(
                    &decl.name,
                    &Value::stuck(
                        decl.body.as_ref().clone(),
                        new_ctx.closure_rec(&decl.body, &decl.name),
                        Mod::Precise,
                    ),
                    &tpe,
                );
                new_ctx = new_ctx.with_term(&decl.name, &eval(&rec_ctx, &decl.body)?, &tpe);
            }
        } else {
            todo!();
        }
        Ok(new_ctx)
    }

    pub fn closure(&self, t: &Rc<Term>) -> Closure {
        match self {
            TypeContext::Clear {
                term_binds,
                formula_binds,
                ..
            } => {
                let (free_vars, free_fs) = free_vars(t);
                let term_binds = free_vars
                    .iter()
                    .map(|v| {
                        (
                            *v,
                            term_binds
                                .get(v)
                                .unwrap_or_else(|| panic!("unfound var {:?}", v))
                                .clone(),
                        )
                    })
                    .collect();
                let formula_binds = free_fs
                    .iter()
                    .map(|v| (*v, formula_binds[v].clone()))
                    .collect();
                Closure {
                    term_binds,
                    formula_binds,
                    face: Face::eps(),
                }
            }
            TypeContext::Faced { ctx, face, .. } => {
                let mut closure = ctx.closure(t);
                closure.face = closure.face.meet(face);
                closure
            }
        }
    }

    pub fn closure_rec(&self, t: &Rc<Term>, name: &Identifier) -> Closure {
        match self {
            TypeContext::Clear {
                term_binds,
                formula_binds,
                ..
            } => {
                let (mut free_vars, free_fs) = free_vars(t);
                free_vars.remove(name);
                let term_binds = free_vars
                    .iter()
                    .map(|v| {
                        (
                            *v,
                            term_binds
                                .get(v)
                                .unwrap_or_else(|| panic!("unfound var {:?}", v))
                                .clone(),
                        )
                    })
                    .collect();
                let formula_binds = free_fs
                    .iter()
                    .map(|v| (*v, formula_binds[v].clone()))
                    .collect();
                Closure {
                    term_binds,
                    formula_binds,
                    face: Face::eps(),
                }
            }
            TypeContext::Faced { ctx, face, .. } => {
                let mut closure = ctx.closure(t);
                closure.face = closure.face.meet(face);
                closure
            }
        }
    }

    pub fn in_closure(&self, c: &Closure) -> TypeContext {
        match self {
            TypeContext::Clear {
                term_binds,
                shadowed,
                formula_binds,
                counter,
                path_index,
                is_compact,
                notifier,
            } => {
                let term_binds = c
                    .term_binds
                    .iter()
                    .fold(term_binds.clone(), |acc, (k, v)| acc.insert(*k, v.clone()));
                let formula_binds = c
                    .formula_binds
                    .iter()
                    .fold(formula_binds.clone(), |acc, (k, v)| {
                        acc.insert(*k, v.clone())
                    });

                TypeContext::Clear {
                    term_binds,
                    shadowed: shadowed.clone(),
                    formula_binds,
                    counter: counter.clone(),
                    path_index: path_index.clone(),
                    is_compact: *is_compact,
                    notifier: notifier.clone(),
                }
            }
            TypeContext::Faced { ctx, cache, face } => {
                if !c.face.compatible(face) {
                    panic!("AAAA");
                }
                let bcache = { cache.borrow().clone() };
                TypeContext::Faced {
                    ctx: Box::new(ctx.in_closure(c)),
                    cache: Rc::new(RefCell::new(bcache)),
                    face: face.clone(),
                }
            }
        }
    }

    fn notifier(&self) -> Option<Rc<dyn ProgressNotifier>> {
        match self {
            TypeContext::Clear { notifier, .. } => notifier.clone(),
            TypeContext::Faced { ctx, .. } => ctx.notifier(),
        }
    }

    pub fn uncompacted(&self) -> TypeContext {
        self.clone()
        // TypeContext {
        //     term_binds: self.term_binds.clone(),
        //     shadowed: self.shadowed.clone(),
        //     formula_binds: self.formula_binds.clone(),
        //     face: self.face.clone(),
        //     counter: self.counter.clone(),
        //     path_index: self.path_index.clone(),
        //     is_compact: false,
        //     notifier: self.notifier.clone(),
        // }
    }

    pub fn compact(&self, t: &Rc<Value>) -> Rc<Value> {
        t.clone()
        // if !self.is_compact {
        //     t.clone()
        // } else {
        //     let res = self.path_index.borrow_mut().compact(t);
        //     res
        // }
    }
}

pub trait ProgressNotifier {
    fn decl_check_started(&self, decl_name: &Identifier);

    fn decl_check_finished(&self, decl_name: &Identifier);
}

impl ProgressNotifier for TypeContext {
    fn decl_check_started(&self, decl_name: &Identifier) {
        if let Some(notifier) = &self.notifier() {
            notifier.decl_check_started(decl_name);
        }
    }

    fn decl_check_finished(&self, decl_name: &Identifier) {
        if let Some(notifier) = &self.notifier() {
            notifier.decl_check_finished(decl_name);
        }
    }
}

pub fn free_vars(term: &Term) -> (HashSet<Identifier>, HashSet<Identifier>) {
    let mut fv = HashSet::new();
    let mut fi = HashSet::new();
    free_vars_helper(term, &mut fv, &mut fi, &HashSet::new(), &HashSet::new());
    (fv, fi)
}

fn free_vars_helper(
    term: &Term,
    free_vars: &mut HashSet<Identifier>,
    free_is: &mut HashSet<Identifier>,
    bound_vars: &HashSet<Identifier>,
    bound_is: &HashSet<Identifier>,
) {
    match term {
        Term::Var(id, _) => {
            if !bound_vars.contains(id) {
                free_vars.insert(*id);
            }
        }
        Term::Lam(param, tpe, body, _) => {
            free_vars_helper(tpe, free_vars, free_is, bound_vars, bound_is);
            let mut new_bound = bound_vars.clone();
            new_bound.insert(*param);
            free_vars_helper(body, free_vars, free_is, &new_bound, bound_is);
        }
        Term::Pi(lam, _) | Term::Sigma(lam, _) => {
            free_vars_helper(lam, free_vars, free_is, bound_vars, bound_is);
        }
        Term::App(f, arg, _) => {
            free_vars_helper(f, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(arg, free_vars, free_is, bound_vars, bound_is);
        }
        Term::Where(t, decls, _) => {
            let mut new_bound = bound_vars.clone();
            match decls {
                DeclarationSet::Mutual(declarations) => {
                    for decl in declarations {
                        new_bound.insert(decl.name);
                        free_vars_helper(&decl.body, free_vars, free_is, &new_bound, bound_is);
                        free_vars_helper(&decl.tpe, free_vars, free_is, &new_bound, bound_is);
                    }
                }
                DeclarationSet::Opaque(name) => {
                    new_bound.insert(*name);
                }
                DeclarationSet::Transparent(_) => {}
                DeclarationSet::TransparentAll => {}
            }
            free_vars_helper(t, free_vars, free_is, &new_bound, bound_is);
        }
        Term::Split(_, t, brs, _) => {
            for br in brs {
                match br {
                    Branch::OBranch(_, args, e) => {
                        let mut new_bound = bound_vars.clone();
                        for a in args {
                            new_bound.insert(*a);
                        }
                        free_vars_helper(e, free_vars, free_is, &new_bound, bound_is);
                    }
                    Branch::PBranch(_, args, is, e) => {
                        let mut new_bound_vars = bound_vars.clone();
                        let mut new_bound_is = bound_is.clone();
                        for a in args {
                            new_bound_vars.insert(*a);
                        }
                        for i in is {
                            new_bound_is.insert(*i);
                        }
                        free_vars_helper(e, free_vars, free_is, &new_bound_vars, &new_bound_is);
                    }
                }
            }
            free_vars_helper(t, free_vars, free_is, bound_vars, bound_is);
        }
        Term::Sum(_, labs, _) | Term::HSum(_, labs, _) => {
            for lab in labs {
                match lab {
                    Label::OLabel(_, tele) => {
                        let args = &tele.variables;
                        let mut new_bound = bound_vars.clone();
                        for (name, tpe) in args {
                            free_vars_helper(tpe, free_vars, free_is, &new_bound, bound_is);
                            new_bound.insert(*name);
                        }
                    }
                    Label::PLabel(_, tele, is, sys) => {
                        let args = &tele.variables;
                        let mut new_bound_vars = bound_vars.clone();
                        let mut new_bound_is = bound_is.clone();
                        for (name, tpe) in args {
                            free_vars_helper(
                                tpe,
                                free_vars,
                                free_is,
                                &new_bound_vars,
                                &new_bound_is,
                            );
                            new_bound_vars.insert(*name);
                        }
                        for i in is {
                            new_bound_is.insert(*i);
                        }
                        free_vars_system(sys, free_vars, free_is, &new_bound_vars, &new_bound_is);
                    }
                }
            }
        }
        Term::Pair(a, b, _) => {
            free_vars_helper(a, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(b, free_vars, free_is, bound_vars, bound_is);
        }
        Term::Fst(t, _) | Term::Snd(t, _) => {
            free_vars_helper(t, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(t, free_vars, free_is, bound_vars, bound_is);
        }
        Term::PCon(_, tpe, args, fs, _) => {
            free_vars_helper(tpe, free_vars, free_is, bound_vars, bound_is);
            for arg in args {
                free_vars_helper(arg, free_vars, free_is, bound_vars, bound_is);
            }
            for f in fs {
                free_is_formula(f, free_vars, free_is, bound_vars, bound_is);
            }
        }
        Term::Con(_, args, _) => {
            for arg in args {
                free_vars_helper(arg, free_vars, free_is, bound_vars, bound_is);
            }
        }
        Term::PathP(a, b, ty, _) => {
            free_vars_helper(a, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(b, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(ty, free_vars, free_is, bound_vars, bound_is);
        }
        Term::Comp(a, b, sys, _) | Term::Fill(a, b, sys, _) | Term::HComp(a, b, sys, _) => {
            free_vars_helper(a, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(b, free_vars, free_is, bound_vars, bound_is);
            free_vars_system(sys, free_vars, free_is, bound_vars, bound_is);
        }
        Term::PLam(param, body, _) => {
            let mut new_bound_is = bound_is.clone();
            new_bound_is.insert(*param);
            free_vars_helper(body, free_vars, free_is, bound_vars, &new_bound_is);
        }
        Term::AppFormula(t, f, _) => {
            free_vars_helper(t, free_vars, free_is, bound_vars, bound_is);
            free_is_formula(f, free_vars, free_is, bound_vars, bound_is);
        }
        Term::Glue(t, sys, _) | Term::GlueElem(t, sys, _) | Term::UnGlueElem(t, sys, _) => {
            free_vars_helper(t, free_vars, free_is, bound_vars, bound_is);
            free_vars_system(sys, free_vars, free_is, bound_vars, bound_is);
        }
        Term::Undef(t, _) => {
            free_vars_helper(t, free_vars, free_is, bound_vars, bound_is);
        }
        Term::Id(a, b, ty, _) => {
            free_vars_helper(a, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(b, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(ty, free_vars, free_is, bound_vars, bound_is);
        }
        Term::IdPair(a, sys, _) => {
            free_vars_helper(a, free_vars, free_is, bound_vars, bound_is);
            free_vars_system(sys, free_vars, free_is, bound_vars, bound_is);
        }
        Term::IdJ(a, b, c, d, e, f, _) => {
            free_vars_helper(a, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(b, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(c, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(d, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(e, free_vars, free_is, bound_vars, bound_is);
            free_vars_helper(f, free_vars, free_is, bound_vars, bound_is);
        }
        Term::U | Term::Hole => {}
    }
}

fn free_vars_system(
    sys: &System<Term>,
    free_vars: &mut HashSet<Identifier>,
    free_is: &mut HashSet<Identifier>,
    bound_vars: &HashSet<Identifier>,
    bound_is: &HashSet<Identifier>,
) {
    for (k, v) in sys.iter() {
        for i in k.binds.keys() {
            if !bound_is.contains(i) {
                free_is.insert(*i);
            }
        }
        free_vars_helper(v, free_vars, free_is, bound_vars, bound_is);
    }
}

fn free_is_formula(
    f: &Formula,
    free_vars: &mut HashSet<Identifier>,
    free_is: &mut HashSet<Identifier>,
    bound_vars: &HashSet<Identifier>,
    bound_is: &HashSet<Identifier>,
) {
    match f {
        Formula::Dir(_) => {}
        Formula::Atom(i) => {
            if !bound_is.contains(i) {
                free_is.insert(*i);
            }
        }
        Formula::NegAtom(i) => {
            if !bound_is.contains(i) {
                free_is.insert(*i);
            }
        }
        Formula::And(lhs, rhs) => {
            free_is_formula(lhs, free_vars, free_is, bound_vars, bound_is);
            free_is_formula(rhs, free_vars, free_is, bound_vars, bound_is);
        }
        Formula::Or(lhs, rhs) => {
            free_is_formula(lhs, free_vars, free_is, bound_vars, bound_is);
            free_is_formula(rhs, free_vars, free_is, bound_vars, bound_is);
        }
    }
}
