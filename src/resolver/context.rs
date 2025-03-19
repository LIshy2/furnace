use crate::term;

use crate::resolver::error::ResolveError;
use crate::resolver::error::ResolveError::{UnresolvedName, UnresolvedVar};
use rpds::HashTrieMap;

#[derive(Clone)]
enum SymbolKind {
    Variable,
    Constructor,
    PConstructor,
    Name,
}

#[derive(Clone)]
pub struct ResolveContext {
    binds: HashTrieMap<String, SymbolKind>,
}

impl ResolveContext {
    pub fn new() -> ResolveContext {
        ResolveContext {
            binds: HashTrieMap::new(),
        }
    }

    pub fn with_var(&self, name: String) -> ResolveContext {
        ResolveContext {
            binds: self.binds.insert(name.to_string(), SymbolKind::Variable),
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
        ResolveContext {
            binds: self.binds.insert(name.to_string(), SymbolKind::Name),
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
        ResolveContext {
            binds: self.binds.insert(name, SymbolKind::Constructor),
        }
    }

    pub fn with_pconstructor(&self, name: String) -> ResolveContext {
        ResolveContext {
            binds: self.binds.insert(name, SymbolKind::PConstructor),
        }
    }

    pub fn except(&self, name: &str) -> ResolveContext {
        ResolveContext {
            binds: self.binds.remove(name),
        }
    }

    pub fn resolve_var(&self, ident: &str) -> Result<term::Term, ResolveError> {
        if let Some(kind) = self.binds.get(ident) {
            match kind {
                SymbolKind::Variable => Ok(term::Term::Var(ident.to_string())),
                SymbolKind::Constructor => Ok(term::Term::Con(ident.to_string(), vec![])),
                SymbolKind::PConstructor | SymbolKind::Name => {
                    Err(UnresolvedVar(ident.to_string()))
                }
            }
        } else {
            Err(UnresolvedVar(ident.to_string()))
        }
    }
    pub fn resolve_name(&self, ident: &str) -> Result<term::Identifier, ResolveError> {
        if let Some(SymbolKind::Name) = self.binds.get(ident) {
            Ok(ident.to_string())
        } else {
            Err(UnresolvedName(ident.to_string()))
        }
    }
}
