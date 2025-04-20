use std::backtrace::Backtrace;
use crate::ctt::term::{DeclarationSet, Dir, Face, Formula, Identifier, System, Term};
use crate::typechecker::error::TypeError;
use crate::typechecker::eval::{eval, Facing};
use rpds::HashTrieMap;
use std::cell::RefCell;
use std::fmt::{Debug, Formatter};
use std::ops::Add;
use std::rc::Rc;
use std::sync::atomic::AtomicUsize;
use std::time::{Instant, SystemTime};

#[derive(Clone, Debug)]
pub struct Entry {
    pub tpe: Rc<Term>,
    pub value: Rc<Term>,
}

#[derive(Clone)]
pub struct TypeContext {
    term_binds: HashTrieMap<Identifier, Entry>,
    formula_binds: HashTrieMap<Identifier, Formula>,
    counter: Rc<RefCell<usize>>,
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
    pub fn new() -> TypeContext {
        TypeContext {
            term_binds: HashTrieMap::new(),
            formula_binds: HashTrieMap::new(),
            counter: Rc::new(RefCell::new(99999)),
        }
    }

    pub fn fresh(&self) -> Identifier {
        let res = *self.counter.borrow_mut();
        *self.counter.borrow_mut() += 1;
        res
    }

    pub fn lookup_term(&self, name: &Identifier) -> Option<Entry> {
        self.term_binds.get(name).map(|x| x.clone())
    }

    pub fn lookup_formula(&self, name: &Identifier) -> Option<Formula> {
        self.formula_binds.get(name).map(|x| x.clone())
    }

    pub fn with_term(&self, name: &Identifier, value: &Rc<Term>, tpe: &Rc<Term>) -> TypeContext {
        TypeContext {
            term_binds: self.term_binds.insert(
                name.clone(),
                Entry {
                    value: value.clone(),
                    tpe: tpe.clone(),
                },
            ),
            formula_binds: self.formula_binds.clone(),
            counter: self.counter.clone(),
        }
    }

    pub fn with_face(&self, face: &Face) -> Result<TypeContext, TypeError> {
        let mut res = face.binds.iter().fold(self.clone(), |acc, (k, v)| {
            acc.with_formula(k, Formula::Dir(v.clone()))
        });
        // let keys = self.term_binds.keys();
        // for k in keys {
        //     let mut v = res.term_binds[k].clone();
        //     v.value = v.value.clone().face(res.clone(), face)?;
        //     v.tpe = v.tpe.clone().face(res.clone(), face)?;
        //     res.term_binds = res.term_binds.insert(k.clone(), v);
        // }
        Ok(res)
    }

    pub fn with_formula(&self, name: &Identifier, formula: Formula) -> TypeContext {
        TypeContext {
            term_binds: self.term_binds.clone(),
            formula_binds: self.formula_binds.insert(name.clone(), formula),
            counter: self.counter.clone(),
        }
    }

    pub fn with_decl_set(&self, decls: &DeclarationSet) -> Result<TypeContext, TypeError> {
        let mut new_ctx = self.clone();
        match decls {
            DeclarationSet::Mutual(decls) => {
                for decl in decls {
                    new_ctx = new_ctx.with_term(
                        &decl.name,
                        &eval(new_ctx.clone(), decl.body.as_ref())?,
                        &eval(new_ctx.clone(), decl.tpe.as_ref())?,
                    );
                }
            }
            _ => (),
        }
        Ok(new_ctx)
    }
}
