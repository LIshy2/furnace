use crate::ctt::term::{DeclarationSet, Face, Formula, Identifier, Label};
use crate::precise::term::Term;
use crate::typechecker::canon::eval::{eval, eval_system};
use crate::typechecker::canon::heat::PathIndex;
use crate::typechecker::error::TypeError;
use rpds::HashTrieMap;
use std::cell::RefCell;
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

use super::canon::nominal::Facing;

#[derive(Clone, Debug)]
pub struct Entry {
    pub tpe: Rc<Term>,
    pub value: Rc<Term>,
}

#[derive(Clone)]
pub struct TypeContext {
    term_binds: HashTrieMap<Identifier, Entry>,
    formula_binds: HashTrieMap<Identifier, Formula>,
    face: Face,
    counter: Rc<RefCell<usize>>,
    path_index: Rc<RefCell<PathIndex>>,
    is_compact: bool,
    notifier: Rc<dyn ProgressNotifier>,
}

impl Debug for TypeContext {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (name, e) in self.term_binds.iter() {
            name.fmt(f)?;
            write!(f, " - ")?;
            e.value.fmt(f)?;
            write!(f, ": ")?;
            e.tpe.fmt(f)?;
            write!(f, "\n")?;
        }
        write!(f, "INTERVALS\n")?;
        for (name, e) in self.formula_binds.iter() {
            name.fmt(f)?;
            write!(f, " - ")?;
            e.fmt(f)?;
            write!(f, "\n")?;
        }
        Ok(())
    }
}

impl TypeContext {
    pub fn new(notifier: Rc<dyn ProgressNotifier>) -> TypeContext {
        TypeContext {
            term_binds: HashTrieMap::new(),
            formula_binds: HashTrieMap::new(),
            face: Face::eps(),
            counter: Rc::new(RefCell::new(99999)),
            path_index: Rc::new(RefCell::new(PathIndex::new())),
            is_compact: true,
            notifier,
        }
    }

    pub fn fresh(&self) -> Identifier {
        let res = *self.counter.borrow_mut();
        *self.counter.borrow_mut() += 1;
        Identifier(res)
    }

    pub fn lookup_term(&self, name: &Identifier) -> Option<Entry> {
        let e = self.term_binds.get(name).map(|x| x.clone())?;
        let new_entry = Entry {
            tpe: e.tpe.face(self, &self.face).unwrap(),
            value: e.value.face(self, &self.face).unwrap(),
        };
        Some(new_entry)
    }

    pub fn lookup_formula(&self, name: &Identifier) -> Option<Formula> {
        let f = self.formula_binds.get(name).map(|x| x.clone())?;
        Some(f.face(self, &self.face).unwrap())
    }

    fn analyze_hsum(&self, hsum: &Rc<Term>) {
        match hsum.as_ref() {
            Term::HSum(_, labels, ..) => {
                for label in labels {
                    match label {
                        Label::PLabel(_, _, is, sys) => {
                            if is.len() == 1 {
                                if sys.len() == 2 {
                                    let endpoints = sys.values().collect::<Vec<_>>();
                                    self.path_index
                                        .borrow_mut()
                                        .add(&endpoints[0], &endpoints[1]);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => (),
        }
    }

    pub fn with_term(&self, name: &Identifier, value: &Rc<Term>, tpe: &Rc<Term>) -> TypeContext {
        self.analyze_hsum(value);
        TypeContext {
            term_binds: self.term_binds.insert(
                name.clone(),
                Entry {
                    value: value.clone(),
                    tpe: tpe.clone(),
                },
            ),
            formula_binds: self.formula_binds.clone(),
            face: self.face.clone(),
            counter: self.counter.clone(),
            path_index: self.path_index.clone(),
            is_compact: self.is_compact,
            notifier: self.notifier.clone(),
        }
    }

    pub fn with_face(&self, face: &Face) -> Result<TypeContext, TypeError> {
        let mut res = face.binds.iter().fold(self.clone(), |acc, (k, v)| {
            acc.with_formula(k, Formula::Dir(v.clone()))
        });
        res.face = self.face.meet(face);
        Ok(res)
    }

    pub fn uncompacted(&self) -> TypeContext {
        TypeContext {
            term_binds: self.term_binds.clone(),
            formula_binds: self.formula_binds.clone(),
            face: self.face.clone(),
            counter: self.counter.clone(),
            path_index: self.path_index.clone(),
            is_compact: false,
            notifier: self.notifier.clone(),
        }
    }

    pub fn with_formula(&self, name: &Identifier, formula: Formula) -> TypeContext {
        TypeContext {
            term_binds: self.term_binds.clone(),
            formula_binds: self.formula_binds.insert(name.clone(), formula),
            counter: self.counter.clone(),
            face: self.face.clone(),
            path_index: self.path_index.clone(),
            is_compact: self.is_compact,
            notifier: self.notifier.clone(),
        }
    }

    pub fn with_decl_set(&self, decls: &DeclarationSet<Term>) -> Result<TypeContext, TypeError> {
        let mut new_ctx = self.clone();
        match decls {
            DeclarationSet::Mutual(decls) => {
                for decl in decls {
                    new_ctx = new_ctx.with_term(
                        &decl.name,
                        &eval(&new_ctx, &decl.body)?,
                        &eval(&new_ctx, &decl.tpe)?,
                    );
                }
            }
            _ => (),
        }
        Ok(new_ctx)
    }

    pub fn compact(&self, t: &Rc<Term>) -> Rc<Term> {
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
        self.notifier.decl_check_started(decl_name);
    }

    fn decl_check_finished(&self, decl_name: &Identifier) {
        self.notifier.decl_check_finished(decl_name);
    }
}
