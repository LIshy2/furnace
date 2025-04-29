use crate::ctt::term;
use crate::parser::ast::AIdent;
use crate::resolver::error::ResolveError;
use crate::resolver::error::ResolveError::{UnresolvedName, UnresolvedVar};
use rpds::HashTrieMap;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone)]
struct Generator {
    num: usize,
    dict: Vec<AIdent>
}

impl Generator {
    fn new() -> Generator {
        Generator {
            num: 0,
            dict: vec![],
        }
    }

    fn inc(&mut self, name: &AIdent) -> term::Identifier {
        let res = self.num;
        self.dict.push(name.clone());
        self.num += 1;
        term::Identifier(res)
    }
}

#[derive(Clone)]
enum SymbolKind {
    Variable,
    Constructor,
    PConstructor,
    Name,
}

#[derive(Clone)]
pub struct ResolveContext {
    binds: HashTrieMap<String, (SymbolKind, term::Identifier)>,
    counter: Rc<RefCell<Generator>>,
}

impl ResolveContext {
    pub fn new() -> ResolveContext {
        ResolveContext {
            binds: HashTrieMap::new(),
            counter: Rc::new(RefCell::new(Generator::new())),
        }
    }

    pub fn with_var(&self, name: String) -> ResolveContext {
        let id = self.counter.borrow_mut().inc(&name);
        ResolveContext {
            binds: self
                .binds
                .insert(name.to_string(), (SymbolKind::Variable, id)),
            counter: self.counter.clone(),
        }
    }

    pub fn with_vars<C: IntoIterator<Item = String>>(&self, names: C) -> ResolveContext {
        let mut ctx = self.clone();
        for name in names {
            ctx = ctx.with_var(name);
        }
        ctx
    }

    pub fn with_name(&self, name: String) -> ResolveContext {
        let id = self.counter.borrow_mut().inc(&name);

        ResolveContext {
            binds: self.binds.insert(name.to_string(), (SymbolKind::Name, id)),
            counter: self.counter.clone(),
        }
    }

    pub fn with_names<C: IntoIterator<Item = String>>(&self, names: C) -> ResolveContext {
        let mut ctx = self.clone();
        for name in names {
            ctx = ctx.with_name(name);
        }
        ctx
    }

    pub fn with_constructor(&self, name: String) -> ResolveContext {
        let id = self.counter.borrow_mut().inc(&name);
        ResolveContext {
            binds: self.binds.insert(name, (SymbolKind::Constructor, id)),
            counter: self.counter.clone(),
        }
    }

    pub fn with_pconstructor(&self, name: String) -> ResolveContext {
        let id = self.counter.borrow_mut().inc(&name);

        ResolveContext {
            binds: self.binds.insert(name, (SymbolKind::PConstructor, id)),
            counter: self.counter.clone(),
        }
    }

    pub fn except(&self, name: &str) -> ResolveContext {
        ResolveContext {
            binds: self.binds.remove(name),
            counter: self.counter.clone(),
        }
    }

    pub fn resolve_var(&self, ident: &str) -> Result<term::Term, ResolveError> {
        if let Some((kind, id)) = self.binds.get(ident) {
            match kind {
                SymbolKind::Variable => Ok(term::Term::Var(id.clone())),
                SymbolKind::Constructor => Ok(term::Term::Con(id.clone(), vec![])),
                SymbolKind::PConstructor | SymbolKind::Name => {
                    Err(UnresolvedVar(ident.to_string()))
                }
            }
        } else {
            Err(UnresolvedVar(ident.to_string()))
        }
    }

    pub fn resolve_identifier(&self, ident: &str) -> Result<term::Identifier, ResolveError> {
        if let Some((kind, id)) = self.binds.get(ident) {
            match kind {
                SymbolKind::Variable => Ok(id.clone()),
                SymbolKind::Constructor | SymbolKind::PConstructor => Ok(id.clone()),
                SymbolKind::Name => {
                    Err(UnresolvedVar(ident.to_string()))
                }
            }
        } else {
            Err(UnresolvedVar(ident.to_string()))
        }
    }

    pub fn resolve_name(&self, ident: &str) -> Result<term::Identifier, ResolveError> {
        if let Some((SymbolKind::Name, id)) = self.binds.get(ident) {
            Ok(id.clone())
        } else {
            Err(UnresolvedName(ident.to_string()))
        }
    }
}

pub trait Demangler {
    fn demangle(&self, id: &term::Identifier) -> AIdent;
}

impl Demangler for ResolveContext {
    fn demangle(&self, id: &term::Identifier) -> AIdent {
        self.counter.borrow().dict[id.0].clone()
    }
}
