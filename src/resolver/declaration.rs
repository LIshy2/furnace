use super::context::ResolveContext;
use super::error::ResolveError;
use super::telescope::Telescope;
use super::term::{resolve_branch, resolve_label, resolve_term};
use std::rc::Rc;

use crate::ctt::term;
use crate::ctt::term::DeclarationSet;
use crate::parser::ast;
use crate::parser::ast::AIdent;

fn resolve_data(
    ctx: ResolveContext,
    name: AIdent,
    tele: Vec<ast::Tele>,
    labels: Vec<ast::Label>,
    force_h: bool,
) -> Result<DeclarationSet, ResolveError> {
    let telescope = Telescope::from_tele(ctx.clone(), tele)?;
    let ctx = telescope.context();


    let name = ctx.resolve_identifier(&name)?;

    let labels = labels
        .into_iter()
        .map(|l| resolve_label(ctx.clone(), l))
        .collect::<Result<Vec<term::Label>, ResolveError>>()?;
    let is_h = force_h
        || labels.iter().any(|l| match l {
            term::Label::OLabel(_, _) => false,
            term::Label::PLabel(_, _, _, _) => true,
        });
    let body = if is_h {
        term::Term::HSum(name, labels)
    } else {
        term::Term::Sum(name, labels)
    };

    let body = telescope.clone().lambda(|_| Ok(Rc::new(body)))?;
    let tpe = telescope.pi(|_| Ok(Rc::new(term::Term::U)))?;
    Ok(DeclarationSet::Mutual(vec![term::Declaration {
        name,
        tpe,
        body,
    }]))
}

fn data_context(ctx: ResolveContext, name: String, labels: &[ast::Label]) -> ResolveContext {
    let new_ctx = labels
        .iter()
        .fold(ctx.with_var(name), |ctx, label| match label {
            ast::Label::OLabel(name, _) => ctx.with_constructor(name.clone()),
            ast::Label::PLabel(name, _, _, _) => ctx.with_pconstructor(name.clone()),
        });
    new_ctx
}

fn resolve_declaration(
    ctx: ResolveContext,
    decl: ast::Decl,
) -> Result<(DeclarationSet, ResolveContext), ResolveError> {
    match decl {
        ast::Decl::Mutual(decls) => {
            let ctx = decls.iter().fold(ctx, |ctx, d| match d {
                ast::Decl::Def(name, _, _, _) => ctx.with_var(name.clone()),
                ast::Decl::Data(name, _, labels) => data_context(ctx, name.clone(), labels),
                ast::Decl::HData(name, _, labels) => data_context(ctx, name.clone(), labels),
                ast::Decl::Split(name, _, _, _) => ctx.with_var(name.clone()),
                ast::Decl::Undef(name, _, _) => ctx.with_var(name.clone()),
                ast::Decl::Mutual(_) => ctx,
                ast::Decl::Opaque(name) => ctx.with_var(name.clone()),
                ast::Decl::Transparent(name) => ctx.with_var(name.clone()),
                ast::Decl::TransparentAll => ctx,
            });
            let mut mutual = Vec::new();
            for decl in decls {
                if let (DeclarationSet::Mutual(mut decls), _) =
                    resolve_declaration(ctx.clone(), decl)?
                {
                    mutual.append(&mut decls);
                } else {
                    Err(ResolveError::UnsupportedDeclaration)?
                }
            }
            Ok((DeclarationSet::Mutual(mutual), ctx))
        }
        ast::Decl::Opaque(decl) => {
            Ok((DeclarationSet::Opaque(ctx.resolve_identifier(&decl)?), ctx))
        }
        ast::Decl::Transparent(decl) => Ok((
            DeclarationSet::Transparent(ctx.resolve_identifier(&decl)?),
            ctx,
        )),
        ast::Decl::TransparentAll => Ok((DeclarationSet::TransparentAll, ctx)),
        ast::Decl::Def(name, tele, tpe, body) => {
            let ctx = ctx.with_var(name.clone());
            let telescope = Telescope::from_tele(ctx.clone(), tele.into_iter())?;
            let body = telescope
                .clone()
                .lambda(|ctx| resolve_term(ctx.clone(), *body))?;

            let tpe = telescope.pi(|ctx| resolve_term(ctx, *tpe))?;

            Ok((
                DeclarationSet::Mutual(vec![term::Declaration {
                    name: ctx.resolve_identifier(&name)?,
                    tpe,
                    body,
                }]),
                ctx,
            ))
        }
        ast::Decl::Data(name, tele, labels) => {
            let ctx = data_context(ctx.clone(), name.clone(), &labels);
            Ok((resolve_data(ctx.clone(), name, tele, labels, false)?, ctx))
        }
        ast::Decl::HData(name, tele, labels) => {
            let ctx = data_context(ctx.clone(), name.clone(), &labels);
            Ok((resolve_data(ctx.clone(), name, tele, labels, true)?, ctx))
        }
        ast::Decl::Split(name, tele, tpe, branches) => {
            let ctx = ctx.with_var(name.clone());
            let name = ctx.resolve_identifier(&name)?;
            let telescope = Telescope::from_tele(ctx.clone(), tele)?;
            let splitted_tpe = resolve_term(telescope.context(), *tpe)?;
            let tpe = telescope.clone().pi(|ctx| Ok(splitted_tpe.clone()))?;
            let body = telescope.lambda(|ctx| {
                let branches = branches
                    .into_iter()
                    .map(|b| resolve_branch(ctx.clone(), b))
                    .collect::<Result<Vec<term::Branch>, ResolveError>>()?;
                Ok(Rc::new(term::Term::Split(name, splitted_tpe, branches)))
            })?;
            Ok((
                DeclarationSet::Mutual(vec![term::Declaration { name, tpe, body }]),
                ctx,
            ))
        }
        ast::Decl::Undef(name, tele, tpe) => {
            let telescope = Telescope::from_tele(ctx.clone(), tele)?;
            let tpe = telescope.pi(|ctx| resolve_term(ctx, *tpe))?;
            let def_ctx = ctx.with_var(name.clone());
            let name = def_ctx.resolve_identifier(&name)?;
            let declaration_set = DeclarationSet::Mutual(vec![term::Declaration {
                name,
                tpe: tpe.clone(),
                body: Rc::new(term::Term::Undef(tpe)),
            }]);
            Ok((declaration_set, def_ctx))
        }
    }
}

pub fn resolve_declarations(
    mut ctx: ResolveContext,
    decls: Vec<ast::Decl>,
) -> Result<(Vec<DeclarationSet>, ResolveContext), ResolveError> {
    let declaration_sets = decls
        .into_iter()
        .map(|decl| {
            let (decl, new_ctx) = resolve_declaration(ctx.clone(), decl)?;
            ctx = new_ctx;
            Ok(decl)
        })
        .collect::<Result<Vec<DeclarationSet>, ResolveError>>()?;
    Ok((declaration_sets, ctx))
}
