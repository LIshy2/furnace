use crate::ctt::term::{Branch, Closure, DeclarationSet, Face, Formula, Identifier, Label, System};
use crate::precise::term::{Mod, Term, Value};
use crate::typechecker::canon::eval::eval;
use crate::typechecker::canon::heat::PathIndex;
use crate::typechecker::error::TypeError;
use rpds::{HashTrieMap, HashTrieSet};
use std::backtrace::Backtrace;
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::Debug;
use std::rc::Rc;
use tracing::trace_span;

use super::canon::eval::eval_system;
use super::canon::nominal::{act_closure, Facing};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntryValueState {
    Lazy(Rc<Term>, Closure),
    Cached(Rc<Value>),
}

#[derive(Clone)]
pub enum EntryInner {
    Frozen {
        value: EntryValueState,
    },
    Faced {
        ctx: TypeContext,
        inner: Rc<RefCell<EntryInner>>,
        face: Face,
    },
}

impl Debug for EntryInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Frozen { value } => f.debug_struct("Frozen").field("value", value).finish(),
            Self::Faced { inner, face, .. } => f
                .debug_struct("Faced")
                .field("inner", inner)
                .field("face", face)
                .finish(),
        }
    }
}

impl PartialEq for EntryInner {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Frozen { value: l_value }, Self::Frozen { value: r_value }) => {
                l_value == r_value
            }
            (
                Self::Faced {
                    ctx: l_ctx,
                    inner: l_inner,
                    face: l_face,
                },
                Self::Faced {
                    ctx: r_ctx,
                    inner: r_inner,
                    face: r_face,
                },
            ) => {
                l_inner == r_inner
                    && l_face == r_face
                    && l_ctx.term_binds == r_ctx.term_binds
                    && l_ctx.formula_binds == r_ctx.formula_binds
            }
            _ => false,
        }
    }
}

impl Eq for EntryInner {}

impl EntryInner {
    pub fn value(&mut self) -> EntryValueState {
        match self {
            EntryInner::Frozen { value, .. } => value.clone(),
            EntryInner::Faced { ctx, face, inner } => {
                let value = {
                    let mut inner = inner.borrow_mut();
                    match inner.value() {
                        EntryValueState::Cached(value) => {
                            EntryValueState::Cached(value.face(ctx, face).unwrap())
                        }
                        EntryValueState::Lazy(term, c) => {
                            let mut new_closure = None;
                            for (i, d) in &face.binds {
                                new_closure = act_closure(
                                    ctx,
                                    new_closure.as_ref().unwrap_or(&c),
                                    i,
                                    Formula::Dir(d.clone()),
                                )
                                .unwrap();
                            }
                            EntryValueState::Lazy(term, new_closure.unwrap_or(c))
                        }
                    }
                };
                let new_inner = EntryInner::Frozen {
                    value: value.clone(),
                };
                *self = new_inner;
                value
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Entry {
    inner: Rc<RefCell<EntryInner>>,
}

impl Entry {
    pub fn new(value: &Rc<Value>) -> Entry {
        Entry {
            inner: Rc::new(RefCell::new(EntryInner::Frozen {
                value: EntryValueState::Cached(value.clone()),
            })),
        }
    }
    pub fn lazy(ctx: &TypeContext, name: &Identifier, value: &Rc<Term>) -> Entry {
        Entry {
            inner: Rc::new(RefCell::new(EntryInner::Frozen {
                value: EntryValueState::Lazy(value.clone(), ctx.closure_rec(value, name)),
            })),
        }
    }

    pub fn new_state(state: EntryValueState) -> Entry {
        Entry {
            inner: Rc::new(RefCell::new(EntryInner::Frozen { value: state })),
        }
    }

    pub fn value(&self) -> EntryValueState {
        self.inner.borrow_mut().value()
    }

    pub fn face(&self, ctx: TypeContext, face: &Face) -> Entry {
        Entry {
            inner: Rc::new(RefCell::new(EntryInner::Faced {
                ctx: ctx,
                inner: self.inner.clone(),
                face: face.clone(),
            })),
        }
    }
}

#[derive(Clone)]
pub struct TypeContext {
    term_binds: HashTrieMap<Identifier, Entry>,
    type_binds: HashTrieMap<Identifier, Entry>,
    shadowed: HashTrieSet<Identifier>,
    formula_binds: HashTrieMap<Identifier, Formula>,
    counter: Rc<RefCell<usize>>,
    path_index: Rc<RefCell<PathIndex>>,
    is_compact: bool,
    notifier: Option<Rc<dyn ProgressNotifier>>,
}

impl TypeContext {
    pub fn empty() -> TypeContext {
        TypeContext {
            term_binds: HashTrieMap::new(),
            type_binds: HashTrieMap::new(),
            shadowed: HashTrieSet::new(),
            formula_binds: HashTrieMap::new(),
            counter: Rc::new(RefCell::new(99999)),
            path_index: Rc::new(RefCell::new(PathIndex::new())),
            is_compact: true,
            notifier: None,
        }
    }

    pub fn new(notifier: Rc<dyn ProgressNotifier>) -> TypeContext {
        TypeContext {
            term_binds: HashTrieMap::new(),
            type_binds: HashTrieMap::new(),
            shadowed: HashTrieSet::new(),
            formula_binds: HashTrieMap::new(),
            counter: Rc::new(RefCell::new(99999)),
            path_index: Rc::new(RefCell::new(PathIndex::new())),
            is_compact: true,
            notifier: Some(notifier),
        }
    }

    pub fn opaque(&self, name: Identifier) -> TypeContext {
        TypeContext {
            term_binds: self.term_binds.clone(),
            type_binds: self.type_binds.clone(),
            shadowed: self.shadowed.insert(name),
            formula_binds: self.formula_binds.clone(),
            counter: self.counter.clone(),
            path_index: self.path_index.clone(),
            is_compact: self.is_compact,
            notifier: self.notifier.clone(),
        }
    }

    pub fn transparent(&self, name: Identifier) -> TypeContext {
        TypeContext {
            term_binds: self.term_binds.clone(),
            type_binds: self.type_binds.clone(),
            shadowed: self.shadowed.remove(&name),
            formula_binds: self.formula_binds.clone(),
            counter: self.counter.clone(),
            path_index: self.path_index.clone(),
            is_compact: self.is_compact,
            notifier: self.notifier.clone(),
        }
    }

    pub fn transparent_all(&self) -> TypeContext {
        TypeContext {
            term_binds: self.term_binds.clone(),
            type_binds: self.type_binds.clone(),
            shadowed: HashTrieSet::new(),
            formula_binds: self.formula_binds.clone(),
            counter: self.counter.clone(),
            path_index: self.path_index.clone(),
            is_compact: self.is_compact,
            notifier: self.notifier.clone(),
        }
    }

    pub fn fresh(&self) -> Identifier {
        let res = *self.counter.borrow_mut();
        // if res == 133159 {
        //     println!("133159");
        //     println!("{}", Backtrace::capture());
        // }
        // if res == 135308 {
        //     println!("135308");
        //     println!("{}", Backtrace::capture());
        // }
        *self.counter.borrow_mut() += 1;
        Identifier(res)
    }

    // #[instrument(skip(self))]
    pub fn lookup_tpe(&self, name: &Identifier) -> Option<Rc<Value>> {
        let e = self.type_binds.get(name).cloned()?;
        match e.value() {
            EntryValueState::Lazy(term, c) => {
                let rec_ctx = self.in_closure(&c).with_term(
                    &name,
                    &Value::stuck(
                        term.as_ref().clone(),
                        self.in_closure(&c).closure_rec(&term, name),
                        Mod::Precise,
                    ),
                );
                let check_span = trace_span!("def_eval", def = ?name);
                let _enter = check_span.enter();
                let value = eval(&rec_ctx, &term).unwrap();
                drop(_enter);
                Some(value)
            }
            EntryValueState::Cached(value) => Some(value),
        }
    }

    // #[instrument(skip(self))]
    pub fn lookup_value(&self, name: &Identifier) -> Option<Rc<Value>> {
        let value = if self.shadowed.contains(name) {
            Value::var(*name, Mod::Precise)
        } else {
            let e = self.term_binds.get(name).cloned()?;
            match e.value() {
                EntryValueState::Lazy(term, c) => {
                    let rec_ctx = self.in_closure(&c).with_term(
                        &name,
                        &Value::stuck(
                            term.as_ref().clone(),
                            self.in_closure(&c).closure_rec(&term, name),
                            Mod::Precise,
                        ),
                    );
                    let check_span = trace_span!("def_eval", def = ?name);
                    let _enter = check_span.enter();
                    let value = eval(&rec_ctx, &term).unwrap();
                    drop(_enter);
                    value
                }
                EntryValueState::Cached(value) => value,
            }
        };
        Some(value)
    }

    pub fn lookup_formula(&self, name: &Identifier) -> Option<Formula> {
        let f = self.formula_binds.get(name).cloned()?;
        Some(f)
    }

    fn analyze_hsum(&self, hsum: &Term) {
        if let Term::HSum(_, labels, ..) = hsum {
            for label in labels {
                if let Label::PLabel(_, t, is, sys) = label {
                    if t.variables.len() == 0 && is.len() == 1 && sys.len() == 2 {
                        let sys_ctx = self.with_formula(&is[0], Formula::Atom(is[0]));
                        let sys = eval_system(&sys_ctx, sys).unwrap();
                        let endpoints = sys.values().collect::<Vec<_>>();
                        self.path_index.borrow_mut().add(endpoints[0], endpoints[1]);
                    }
                }
            }
        }
    }

    pub fn with_term(&self, name: &Identifier, value: &Rc<Value>) -> TypeContext {
        if let Value::Stuck(t, _, _) = value.as_ref() {
            self.analyze_hsum(t);
        }
        TypeContext {
            term_binds: self.term_binds.insert(*name, Entry::new(value)),
            type_binds: self.type_binds.clone(),
            shadowed: self.shadowed.clone(),
            formula_binds: self.formula_binds.clone(),
            counter: self.counter.clone(),
            path_index: self.path_index.clone(),
            is_compact: self.is_compact,
            notifier: self.notifier.clone(),
        }
    }

    pub fn with_tpe(&self, name: &Identifier, tpe: &Rc<Value>) -> TypeContext {
        if let Value::Stuck(t, _, _) = tpe.as_ref() {
            self.analyze_hsum(t);
        }
        TypeContext {
            term_binds: self.term_binds.clone(),
            type_binds: self.type_binds.insert(*name, Entry::new(tpe)),
            shadowed: self.shadowed.clone(),
            formula_binds: self.formula_binds.clone(),
            counter: self.counter.clone(),
            path_index: self.path_index.clone(),
            is_compact: self.is_compact,
            notifier: self.notifier.clone(),
        }
    }

    pub fn with_lazy_term(
        &self,
        name: &Identifier,
        value: &Rc<Term>,
        tpe: &Rc<Term>,
    ) -> TypeContext {
        self.analyze_hsum(value.as_ref());
        TypeContext {
            term_binds: self
                .term_binds
                .insert(*name, Entry::lazy(self, name, value)),
            type_binds: self.type_binds.insert(*name, Entry::lazy(self, name, tpe)),
            shadowed: self.shadowed.clone(),
            formula_binds: self.formula_binds.clone(),
            counter: self.counter.clone(),
            path_index: self.path_index.clone(),
            is_compact: self.is_compact,
            notifier: self.notifier.clone(),
        }
    }

    pub fn with_face(&self, face: &Face) -> Result<TypeContext, TypeError> {
        let mut acc = face.binds.iter().fold(self.clone(), |acc, (k, v)| {
            acc.with_formula(k, Formula::Dir(v.clone()))
        });
        acc.formula_binds = acc
            .formula_binds
            .iter()
            .map(|(k, v)| (*k, v.face(&acc, face).unwrap()))
            .collect();
        acc.term_binds = acc
            .term_binds
            .iter()
            .map(|(k, v)| (*k, v.face(acc.clone(), face)))
            .collect();
        acc.type_binds = acc
            .type_binds
            .iter()
            .map(|(k, v)| (*k, v.face(acc.clone(), face)))
            .collect();
        Ok(acc)
    }

    pub fn with_formula(&self, name: &Identifier, formula: Formula) -> TypeContext {
        TypeContext {
            term_binds: self.term_binds.clone(),
            type_binds: self.type_binds.clone(),
            shadowed: self.shadowed.clone(),
            formula_binds: self.formula_binds.insert(*name, formula),
            counter: self.counter.clone(),
            path_index: self.path_index.clone(),
            is_compact: self.is_compact,
            notifier: self.notifier.clone(),
        }
    }

    pub fn with_decl_set(&self, decls: &DeclarationSet<Term>) -> Result<TypeContext, TypeError> {
        let mut new_ctx = self.clone();
        if let DeclarationSet::Mutual(decls) = decls {
            for decl in decls {
                new_ctx = new_ctx.with_lazy_term(&decl.name, &decl.body, &decl.tpe);
            }
        } else {
            todo!();
        }
        Ok(new_ctx)
    }

    pub fn closure(&self, t: &Rc<Term>) -> Closure {
        let (free_vars, free_fs) = free_vars(&t);
        let term_binds = free_vars
            .iter()
            .map(|v| {
                (
                    v.clone(),
                    self.term_binds
                        .get(v)
                        .expect(&format!("unfound var {:?}", v))
                        .clone(),
                )
            })
            .collect();
        let type_binds = free_vars
            .iter()
            .filter_map(|v| Some((v.clone(), self.type_binds.get(v)?.clone())))
            .collect();
        let shadowed = free_vars
            .into_iter()
            .filter(|n| self.shadowed.contains(n))
            .collect();
        let formula_binds = free_fs
            .iter()
            .map(|v| (v.clone(), self.formula_binds[v].clone()))
            .collect();
        Closure {
            shadowed,
            term_binds,
            type_binds,
            formula_binds,
        }
    }

    pub fn closure_rec(&self, t: &Rc<Term>, name: &Identifier) -> Closure {
        let (mut free_vars, free_fs) = free_vars(&t);
        free_vars.remove(name);
        let term_binds = free_vars
            .iter()
            .map(|v| {
                (
                    v.clone(),
                    self.term_binds
                        .get(v)
                        .expect(&format!("unfound var {:?}", v))
                        .clone(),
                )
            })
            .collect();
        let type_binds = free_vars
            .iter()
            .filter_map(|v| Some((v.clone(), self.type_binds.get(v)?.clone())))
            .collect();
        let shadowed = free_vars
            .into_iter()
            .filter(|n| self.shadowed.contains(n))
            .collect();
        let formula_binds = free_fs
            .iter()
            .map(|v| (v.clone(), self.formula_binds[v].clone()))
            .collect();
        Closure {
            term_binds,
            type_binds,
            shadowed,
            formula_binds,
        }
    }

    pub fn closure_mutuals(&self, t: &Rc<Term>, names: &[Identifier]) -> Closure {
        println!("mutuals {:?}", names);
        let (mut free_vars, free_fs) = free_vars(&t);
        for name in names {
            free_vars.remove(name);
        }
        let term_binds = free_vars
            .iter()
            .map(|v| {
                (
                    v.clone(),
                    self.term_binds
                        .get(v)
                        .expect(&format!("unfound var {:?}", v))
                        .clone(),
                )
            })
            .collect();
        let type_binds = free_vars
            .iter()
            .filter_map(|v| Some((v.clone(), self.type_binds.get(v)?.clone())))
            .collect();
        let shadowed = free_vars
            .into_iter()
            .filter(|n| self.shadowed.contains(n))
            .collect();
        let formula_binds = free_fs
            .iter()
            .map(|v| (v.clone(), self.formula_binds[v].clone()))
            .collect();
        Closure {
            term_binds,
            type_binds,
            shadowed,
            formula_binds,
        }
    }

    pub fn in_closure(&self, c: &Closure) -> TypeContext {
        let term_binds = c
            .term_binds
            .iter()
            .fold(self.term_binds.clone(), |acc, (k, v)| {
                acc.insert(*k, v.clone())
            });
        let type_binds = c
            .type_binds
            .iter()
            .fold(self.type_binds.clone(), |acc, (k, v)| {
                acc.insert(*k, v.clone())
            });
        let formula_binds = c
            .formula_binds
            .iter()
            .fold(self.formula_binds.clone(), |acc, (k, v)| {
                acc.insert(*k, v.clone())
            });
        let mut shadowed = self.shadowed.clone();

        for n in c.shadowed.iter() {
            shadowed = shadowed.insert(*n);
        }
        TypeContext {
            term_binds,
            type_binds,
            shadowed,
            formula_binds,
            counter: self.counter.clone(),
            path_index: self.path_index.clone(),
            is_compact: self.is_compact,
            notifier: self.notifier.clone(),
        }
    }

    pub fn uncompacted(&self) -> TypeContext {
        TypeContext {
            term_binds: self.term_binds.clone(),
            type_binds: self.type_binds.clone(),
            shadowed: self.shadowed.clone(),
            formula_binds: self.formula_binds.clone(),
            counter: self.counter.clone(),
            path_index: self.path_index.clone(),
            is_compact: false,
            notifier: self.notifier.clone(),
        }
    }

    pub fn compact(&self, t: &Rc<Value>) -> Rc<Value> {
        if !self.is_compact {
            t.clone()
        } else {
            let res = self.path_index.borrow_mut().compact(t);
            res
        }
    }
}

pub trait ProgressNotifier {
    fn decl_check_started(&self, decl_name: &Identifier);

    fn decl_check_finished(&self, decl_name: &Identifier);
}

impl ProgressNotifier for TypeContext {
    fn decl_check_started(&self, decl_name: &Identifier) {
        if let Some(notifier) = &self.notifier {
            notifier.decl_check_started(decl_name);
        }
    }

    fn decl_check_finished(&self, decl_name: &Identifier) {
        if let Some(notifier) = &self.notifier {
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
                free_vars.insert(id.clone());
            }
        }
        Term::Lam(param, tpe, body, _) => {
            free_vars_helper(tpe, free_vars, free_is, &bound_vars, bound_is);
            let mut new_bound = bound_vars.clone();
            new_bound.insert(param.clone());
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
                    }
                    for decl in declarations {
                        free_vars_helper(&decl.body, free_vars, free_is, &new_bound, bound_is);
                        free_vars_helper(&decl.tpe, free_vars, free_is, &new_bound, bound_is);
                    }
                }
                DeclarationSet::Opaque(_) => {}
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
                            free_vars_helper(&tpe, free_vars, free_is, &new_bound, bound_is);
                            new_bound.insert(*name);
                        }
                    }
                    Label::PLabel(_, tele, is, sys) => {
                        let args = &tele.variables;
                        let mut new_bound_vars = bound_vars.clone();
                        let mut new_bound_is = bound_is.clone();
                        for (name, tpe) in args {
                            free_vars_helper(
                                &tpe,
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
            new_bound_is.insert(param.clone());
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
        for (i, _) in &k.binds {
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
