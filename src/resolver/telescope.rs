use crate::ctt::term;
use crate::ctt::term::Identifier;
use crate::parser::ast;
use crate::parser::ast::AIdent;
use crate::resolver::context::ResolveContext;
use crate::resolver::error::ResolveError;
use crate::resolver::term::resolve_term;
use std::rc::Rc;

#[derive(Clone)]
pub struct Telescope {
    scopes: Vec<(Vec<Identifier>, Rc<term::Term<()>>)>,
    ctx: ResolveContext,
}

impl Telescope {
    pub fn from_tele<V: IntoIterator<Item = ast::Tele>>(
        ctx: ResolveContext,
        tele: V,
    ) -> Result<Telescope, ResolveError> {
        let mut ctx = ctx;
        let scopes = tele
            .into_iter()
            .map(|scope| {
                let param_tpe = resolve_term(ctx.clone(), *scope.tpe)?;
                for var in &scope.ids {
                    ctx = ctx.with_var(var.clone());
                }
                Ok((
                    scope
                        .ids
                        .iter()
                        .map(|x| ctx.resolve_identifier(x))
                        .collect::<Result<_, ResolveError>>()?,
                    param_tpe,
                ))
            })
            .collect::<Result<_, _>>()?;
        Ok(Telescope { scopes, ctx })
    }

    pub fn from_ptele<V: IntoIterator<Item = ast::PTele>>(
        ctx: ResolveContext,
        tele: V,
    ) -> Result<Telescope, ResolveError> {
        fn split_ids(apps: ast::Term) -> Vec<AIdent> {
            match apps {
                ast::Term::App(right, id) => match *id {
                    ast::Term::Var(name) => {
                        let mut prefix = split_ids(*right);
                        prefix.push(name);
                        prefix
                    }
                    _ => panic!("TODO"),
                },
                ast::Term::Var(name) => vec![name],
                _ => panic!("TODO"),
            }
        }
        Telescope::from_tele(
            ctx,
            tele.into_iter().map(|pscope| ast::Tele {
                ids: split_ids(*pscope.id),
                tpe: pscope.tpe,
            }),
        )
    }

    pub(crate) fn context(&self) -> ResolveContext {
        self.ctx.clone()
    }

    fn through<R>(
        self,
        result: impl FnOnce(ResolveContext) -> Result<R, ResolveError>,
        layer: &impl Fn(&Identifier, &term::Term<()>, R) -> Result<R, ResolveError>,
    ) -> Result<R, ResolveError> {
        self.scopes
            .iter()
            .rfold(result(self.ctx.clone()), |acc, (ids, tpe)| {
                ids.iter().rfold(acc, |acc, var| layer(var, tpe, acc?))
            })
    }

    pub fn lambda<B: FnOnce(ResolveContext) -> Result<Rc<term::Term<()>>, ResolveError>>(
        self,
        body: B,
    ) -> Result<Rc<term::Term<()>>, ResolveError> {
        self.through(|ctx| body(ctx), &|name, tpe, body| {
            let tpe = Rc::new(tpe.clone());
            Ok(Rc::new(term::Term::Lam(
                name.clone(),
                tpe.clone(),
                body,
                (),
            )))
        })
    }

    pub fn pi<R: FnOnce(ResolveContext) -> Result<Rc<term::Term<()>>, ResolveError>>(
        self,
        result_type: R,
    ) -> Result<Rc<term::Term<()>>, ResolveError> {
        self.through(|ctx| result_type(ctx), &|name, tpe, result_type| {
            let tpe = Rc::new(tpe.clone());
            Ok(Rc::new(term::Term::Pi(
                Rc::new(term::Term::Lam(name.clone(), tpe, result_type, ())),
                (),
            )))
        })
    }

    pub fn sigma<R: FnOnce(ResolveContext) -> Result<Rc<term::Term<()>>, ResolveError>>(
        self,
        result_type: R,
    ) -> Result<Rc<term::Term<()>>, ResolveError> {
        self.through(|ctx| result_type(ctx), &|name, tpe, result_type| {
            let tpe = Rc::new(tpe.clone());
            Ok(Rc::new(term::Term::Sigma(
                Rc::new(term::Term::Lam(name.clone(), tpe, result_type, ())),
                (),
            )))
        })
    }

    pub fn resolve(self) -> (term::Telescope<term::Term<()>>, ResolveContext) {
        let scope = term::Telescope {
            variables: self
                .scopes
                .into_iter()
                .flat_map(|(ids, tpe)| ids.into_iter().map(move |id| (id, tpe.clone())))
                .collect(),
        };
        (scope, self.ctx)
    }
}
