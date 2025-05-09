use crate::ctt::term::{Face, System};
use crate::precise::term::{Mod, Term};
use crate::typechecker::context::TypeContext;
use crate::typechecker::error::TypeError;
use std::rc::Rc;

use super::app::app;
use super::comp::eq_fun;
use super::eval::{equiv_dom, equiv_fun};

pub fn glue(v: &Rc<Term>, system: System<Term>, m: Mod) -> Rc<Term> {
    if let Some(result) = system.get(&Face::eps()) {
        equiv_dom(result)
    } else {
        Term::glue(v, system, m)
    }
}

pub fn glue_elem(v: &Rc<Term>, system: System<Term>, m: Mod) -> Rc<Term> {
    if let Some(result) = system.get(&Face::eps()) {
        result.clone()
    } else {
        Term::glue_elem(v, system, m)
    }
}

pub fn unglue_u(
    ctx: &TypeContext,
    w: &Rc<Term>,
    b: &Rc<Term>,
    es: System<Term>,
    m: Mod,
) -> Result<Rc<Term>, TypeError> {
    if let Some(result) = es.get(&Face::eps()) {
        eq_fun(ctx, result, w)
    } else {
        match w.as_ref() {
            Term::GlueElem(v, _, _) => Ok(v.clone()),
            _ => Ok(Term::unglue_elem_u(w, b, es, m)),
        }
    }
}

pub fn unglue(
    ctx: &TypeContext,
    v: &Rc<Term>,
    system: System<Term>,
) -> Result<Rc<Term>, TypeError> {
    if let Some(result) = system.get(&Face::eps()) {
        app(ctx, &equiv_fun(result), v)
    } else {
        match v.as_ref() {
            Term::GlueElem(v, _, _) => Ok(v.clone()),
            _ => panic!("AAAA"),
        }
    }
}

pub fn unglue_elem(
    ctx: &TypeContext,
    v: &Rc<Term>,
    system: System<Term>,
    m: Mod,
) -> Result<Rc<Term>, TypeError> {
    if let Some(result) = system.get(&Face::eps()) {
        app(ctx, &equiv_fun(result), v)
    } else {
        match v.as_ref() {
            Term::GlueElem(v, _, _) => Ok(v.clone()),
            _ => Ok(Term::unglue_elem(v, system, m)),
        }
    }
}
