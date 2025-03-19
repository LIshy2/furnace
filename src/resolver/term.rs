use super::context::ResolveContext;
use super::declaration::resolve_declarations;
use super::telescope::Telescope;
use std::collections::HashMap;

use crate::parser::ast;
use crate::resolver::error::ResolveError;
use crate::term::{Branch, DeclarationSet, Dir, Face, Formula, Label, System, Term};

fn where_chain(decls: Vec<DeclarationSet>, head: Box<Term>) -> Box<Term> {
    decls
        .into_iter()
        .rfold(head, |acc, decl| Box::new(Term::Where(acc, decl)))
}

fn unique_id() -> String {
    chrono::offset::Local::now().timestamp_micros().to_string()
}

fn open_app(t: ast::Term) -> (Box<ast::Term>, Vec<ast::Term>) {
    match t {
        ast::Term::App(f, arg) => {
            let (fun, mut args) = open_app(*f);
            args.push(*arg);
            (fun, args)
        }
        u => (Box::new(u), vec![]),
    }
}

fn is_pcon_app(t: &ast::Term) -> bool {
    match t {
        ast::Term::AppFormula(u, _) => is_pcon_app(u.as_ref()),
        u => {
            fn in_app_check(t: &ast::Term) -> bool {
                match t {
                    ast::Term::App(f, _) => in_app_check(f),
                    ast::Term::PCon(_, _) => true,
                    _ => false,
                }
            }
            in_app_check(u)
        }
    }
}

fn open_formula_app(t: ast::Term) -> (Box<ast::Term>, Vec<ast::Term>, Vec<ast::Formula>) {
    fn inner(t: ast::Term) -> (Box<ast::Term>, Vec<ast::Term>, Vec<ast::Formula>) {
        match t {
            ast::Term::AppFormula(u, phi) => {
                let (a, b, mut c) = open_formula_app(*u);
                c.push(*phi);
                (a, b, c)
            }
            u => {
                let (a, b) = open_app(u);
                (a, b, vec![])
            }
        }
    }
    let (a, b, mut c) = inner(t);
    c.reverse();
    (a, b, c)
}

pub fn resolve_term(ctx: ResolveContext, term: ast::Term) -> Result<Box<Term>, ResolveError> {
    match term {
        ast::Term::Var(name) => {
            ctx.resolve_var(&name)?;
            Ok(Box::new(Term::Var(name)))
        }
        ast::Term::Where(expr, decls) => {
            let (decls, ctx) = resolve_declarations(ctx, decls)?;
            Ok(where_chain(decls, resolve_term(ctx, *expr)?))
        }
        ast::Term::Let(decls, expr) => {
            let (decls, ctx) = resolve_declarations(ctx, decls)?;
            Ok(where_chain(decls, resolve_term(ctx, *expr)?))
        }
        ast::Term::Lam(tele, body) => {
            Telescope::from_ptele(ctx, tele)?.lambda(|ctx| resolve_term(ctx, *body))
        }
        ast::Term::PLam(names, body) => {
            let ctx = names
                .iter()
                .fold(ctx, |ctx, name| ctx.with_name(name.clone()));
            let body = resolve_term(ctx, *body)?;
            Ok(names
                .into_iter()
                .rfold(body, |acc, name| Box::new(Term::PLam(name, acc))))
        }
        ast::Term::Split(obj, branches) => {
            let branches = branches
                .into_iter()
                .map(|b| resolve_branch(ctx.clone(), b))
                .collect::<Result<_, _>>()?;
            Ok(Box::new(Term::Split(
                unique_id(),
                resolve_term(ctx, *obj)?,
                branches,
            )))
        }
        ast::Term::Fun(arg, result) => Ok(Box::new(Term::Pi(Box::new(Term::Lam(
            "_".to_string(),
            resolve_term(ctx.clone(), *arg)?,
            resolve_term(ctx, *result)?,
        ))))),
        ast::Term::Pi(args, result) => {
            Telescope::from_ptele(ctx, args)?.lambda(|ctx| resolve_term(ctx, *result))
        }
        ast::Term::Sigma(fst, scd) => {
            Telescope::from_ptele(ctx, fst)?.sigma(|ctx| resolve_term(ctx, *scd))
        }
        app @ ast::Term::AppFormula(_, _) => {
            let is_pcon = is_pcon_app(&app);
            if is_pcon {
                let (x, xs, phis) = open_formula_app(app);
                let ast::Term::PCon(name, arg) = *x else {
                    panic!("wrong pcon");
                };
                Ok(Box::new(Term::PCon(
                    name,
                    resolve_term(ctx.clone(), *arg)?,
                    xs.into_iter()
                        .map(|t| Ok(*resolve_term(ctx.clone(), t)?))
                        .collect::<Result<_, ResolveError>>()?,
                    phis.into_iter()
                        .map(|f| resolve_formula(ctx.clone(), f))
                        .collect::<Result<_, ResolveError>>()?,
                )))
            } else {
                let ast::Term::AppFormula(t, phi) = app else {
                    panic!("not app formula");
                };
                Ok(Box::new(Term::AppFormula(
                    resolve_term(ctx.clone(), *t)?,
                    resolve_formula(ctx, *phi)?,
                )))
            }
        }
        ast::Term::App(f, a) => {
            let (fun, args) = open_app(ast::Term::App(f, a));
            let fun = resolve_term(ctx.clone(), *fun)?;
            let mut args = args
                .into_iter()
                .map(|a| Ok(*resolve_term(ctx.clone(), a)?))
                .collect::<Result<_, ResolveError>>()?;
            match *fun {
                Term::Con(label, mut add_args) => {
                    add_args.append(&mut args);
                    Ok(Box::new(Term::Con(label, add_args)))
                }
                _ => Ok(args
                    .into_iter()
                    .fold(fun, |acc, arg| Box::new(Term::App(acc, Box::new(arg))))),
            }
        }
        ast::Term::Fst(pair) => Ok(Box::new(Term::Fst(resolve_term(ctx, *pair)?))),
        ast::Term::Snd(pair) => Ok(Box::new(Term::Snd(resolve_term(ctx, *pair)?))),
        ast::Term::Pair(fst, mut scd) => {
            let last = resolve_term(ctx.clone(), *scd.pop().unwrap())?;
            let paired = scd.into_iter().rfold(Ok(last), |acc, t| {
                let head = resolve_term(ctx.clone(), *t)?;
                Ok(Box::new(Term::Pair(head, acc?)))
            })?;
            Ok(Box::new(Term::Pair(resolve_term(ctx, *fst)?, paired)))
        }
        ast::Term::PathP(a, u, v) => Ok(Box::new(Term::PathP(
            resolve_term(ctx.clone(), *a)?,
            resolve_term(ctx.clone(), *u)?,
            resolve_term(ctx, *v)?,
        ))),
        ast::Term::Comp(u, v, ts) => Ok(Box::new(Term::Comp(
            resolve_term(ctx.clone(), *u)?,
            resolve_term(ctx.clone(), *v)?,
            resolve_system(ctx, ts)?,
        ))),
        ast::Term::HComp(u, v, ts) => Ok(Box::new(Term::HComp(
            resolve_term(ctx.clone(), *u)?,
            resolve_term(ctx.clone(), *v)?,
            resolve_system(ctx, ts)?,
        ))),
        ast::Term::Trans(u, v) => Ok(Box::new(Term::Comp(
            resolve_term(ctx.clone(), *u)?,
            resolve_term(ctx, *v)?,
            System::empty(),
        ))),
        ast::Term::Fill(u, v, ts) => Ok(Box::new(Term::Fill(
            resolve_term(ctx.clone(), *u)?,
            resolve_term(ctx.clone(), *v)?,
            resolve_system(ctx, ts)?,
        ))),
        ast::Term::Glue(u, ts) => Ok(Box::new(Term::Glue(
            resolve_term(ctx.clone(), *u)?,
            resolve_system(ctx, ts)?,
        ))),
        ast::Term::GlueElem(u, ts) => Ok(Box::new(Term::GlueElem(
            resolve_term(ctx.clone(), *u)?,
            resolve_system(ctx, ts)?,
        ))),
        ast::Term::UnGlueElem(u, ts) => Ok(Box::new(Term::UnGlueElem(
            resolve_term(ctx.clone(), *u)?,
            resolve_system(ctx, ts)?,
        ))),
        ast::Term::Id(a, u, v) => Ok(Box::new(Term::Id(
            resolve_term(ctx.clone(), *a)?,
            resolve_term(ctx.clone(), *u)?,
            resolve_term(ctx.clone(), *v)?,
        ))),
        ast::Term::IdPair(u, ts) => Ok(Box::new(Term::IdPair(
            resolve_term(ctx.clone(), *u)?,
            resolve_system(ctx, ts)?,
        ))),
        ast::Term::IdJ(a, t, c, d, x, p) => Ok(Box::new(Term::IdJ(
            resolve_term(ctx.clone(), *a)?,
            resolve_term(ctx.clone(), *t)?,
            resolve_term(ctx.clone(), *c)?,
            resolve_term(ctx.clone(), *d)?,
            resolve_term(ctx.clone(), *x)?,
            resolve_term(ctx.clone(), *p)?,
        ))),
        ast::Term::U => Ok(Box::new(Term::U)),
        ast::Term::Hole => Ok(Box::new(Term::Hole)),
        _ => panic!(""),
    }
}

fn resolve_formula(ctx: ResolveContext, formula: ast::Formula) -> Result<Formula, ResolveError> {
    match formula {
        ast::Formula::Dir(ast::Dir::Zero) => Ok(Formula::Dir(Dir::Zero)),
        ast::Formula::Dir(ast::Dir::One) => Ok(Formula::Dir(Dir::One)),
        ast::Formula::Atom(name) => {
            ctx.resolve_name(&name)?;
            Ok(Formula::Atom(name))
        }
        ast::Formula::Neg(formula) => {
            fn negate_formula(formula: Formula) -> Formula {
                match formula {
                    Formula::Dir(Dir::Zero) => Formula::Dir(Dir::One),
                    Formula::Dir(Dir::One) => Formula::Dir(Dir::Zero),
                    Formula::Atom(name) => Formula::NegAtom(name),
                    Formula::NegAtom(name) => Formula::Atom(name),
                    Formula::And(lhs, rhs) => Formula::Or(
                        Box::new(negate_formula(*lhs)),
                        Box::new(negate_formula(*rhs)),
                    ),
                    Formula::Or(lhs, rhs) => Formula::And(
                        Box::new(negate_formula(*lhs)),
                        Box::new(negate_formula(*rhs)),
                    ),
                }
            }
            Ok(negate_formula(resolve_formula(ctx, *formula)?))
        }
        ast::Formula::And(lhs, rhs) => match (*lhs, *rhs) {
            (_, ast::Formula::Dir(ast::Dir::Zero)) => Ok(Formula::Dir(Dir::Zero)),
            (ast::Formula::Dir(ast::Dir::Zero), _) => Ok(Formula::Dir(Dir::Zero)),
            (l, ast::Formula::Dir(ast::Dir::One)) => resolve_formula(ctx, l),
            (ast::Formula::Dir(ast::Dir::One), r) => resolve_formula(ctx, r),
            (l, r) => Ok(Formula::And(
                Box::new(resolve_formula(ctx.clone(), l)?),
                Box::new(resolve_formula(ctx.clone(), r)?),
            )),
        },
        ast::Formula::Or(lhs, rhs) => match (*lhs, *rhs) {
            (_, ast::Formula::Dir(ast::Dir::One)) => Ok(Formula::Dir(Dir::One)),
            (ast::Formula::Dir(ast::Dir::One), _) => Ok(Formula::Dir(Dir::One)),
            (l, ast::Formula::Dir(ast::Dir::Zero)) => resolve_formula(ctx, l),
            (ast::Formula::Dir(ast::Dir::Zero), r) => resolve_formula(ctx, r),
            (l, r) => Ok(Formula::Or(
                Box::new(resolve_formula(ctx.clone(), l)?),
                Box::new(resolve_formula(ctx.clone(), r)?),
            )),
        },
    }
}

pub fn resolve_label(
    octx: ResolveContext,
    pctx: ResolveContext,
    label: ast::Label,
) -> Result<Label, ResolveError> {
    match label {
        ast::Label::OLabel(name, tele) => {
            let (telescope, _) = Telescope::from_tele(octx, tele)?.resolve();
            Ok(Label::OLabel(name, telescope))
        }
        ast::Label::PLabel(name, tele, intervals, system) => {
            let (telescope, ctx) = Telescope::from_tele(pctx.except(&name), tele)?.resolve();
            let system_ctx = ctx.with_names(intervals.clone());
            Ok(Label::PLabel(
                name,
                telescope,
                intervals,
                resolve_system(system_ctx, system)?,
            ))
        }
    }
}

pub fn resolve_branch(ctx: ResolveContext, branch: ast::Branch) -> Result<Branch, ResolveError> {
    match branch {
        ast::Branch::OBranch(name, params, body) => {
            let ctx = ctx.with_vars(params.clone());
            Ok(Branch::OBranch(name, params, resolve_term(ctx, *body)?))
        }
        ast::Branch::PBranch(name, params, intervals, body) => {
            let ctx = ctx.with_vars(params.clone()).with_names(intervals.clone());
            Ok(Branch::PBranch(
                name,
                params,
                intervals,
                resolve_term(ctx, *body)?,
            ))
        }
    }
}

fn resolve_system(ctx: ResolveContext, system: ast::System) -> Result<System<Term>, ResolveError> {
    let ast::System(sides) = system;
    Ok(System {
        binds: sides
            .into_iter()
            .map(|side| {
                let faces = side
                    .faces
                    .into_iter()
                    .map(|f| {
                        ctx.resolve_name(&f.id)?;
                        Ok(match f.dir {
                            ast::Dir::Zero => (f.id, Dir::Zero),
                            ast::Dir::One => (f.id, Dir::One),
                        })
                    })
                    .collect::<Result<HashMap<String, Dir>, ResolveError>>()?;
                Ok((Face { binds: faces }, resolve_term(ctx.clone(), *side.exp)?))
            })
            .collect::<Result<HashMap<Face, Box<Term>>, ResolveError>>()?,
    })
}
