use crate::ctt::system::{Face, System};
use crate::precise::term::{Mod, Value};
use crate::typechecker::context::TypeContext;
use crate::typechecker::error::{ErrorCause, TypeError};
use std::rc::Rc;

use super::app::app;
use super::comp::eq_fun;
use super::eval::{equiv_dom, equiv_fun};

pub fn glue(v: &Rc<Value>, system: System<Rc<Value>>, m: Mod) -> Rc<Value> {
    if let Some(result) = system.get(&Face::eps()) {
        equiv_dom(result)
    } else {
        Value::glue(v, system, m)
    }
}

pub fn glue_elem(v: &Rc<Value>, system: System<Rc<Value>>, m: Mod) -> Rc<Value> {
    if let Some(result) = system.get(&Face::eps()) {
        result.clone()
    } else {
        Value::glue_elem(v, system, m)
    }
}

pub fn unglue_u(
    ctx: &TypeContext,
    w: &Rc<Value>,
    b: &Rc<Value>,
    es: System<Rc<Value>>,
    m: Mod,
) -> Result<Rc<Value>, TypeError> {
    if let Some(result) = es.get(&Face::eps()) {
        eq_fun(ctx, result, w)
    } else {
        match w.as_ref() {
            Value::GlueElem(v, _, _) => Ok(v.clone()),
            _ => Ok(Value::unglue_elem_u(w, b, es, m)),
        }
    }
}

pub fn unglue(
    ctx: &TypeContext,
    v: &Rc<Value>,
    system: System<Rc<Value>>,
) -> Result<Rc<Value>, TypeError> {
    if let Some(result) = system.get(&Face::eps()) {
        app(ctx, &equiv_fun(result), v)
    } else {
        match v.as_ref() {
            Value::GlueElem(v, _, _) => Ok(v.clone()),
            _ => Err(ErrorCause::ExpectedGlue(v.clone()))?,
        }
    }
}

pub fn unglue_elem(
    ctx: &TypeContext,
    v: &Rc<Value>,
    system: System<Rc<Value>>,
    m: Mod,
) -> Result<Rc<Value>, TypeError> {
    if let Some(result) = system.get(&Face::eps()) {
        app(ctx, &equiv_fun(result), v)
    } else {
        match v.as_ref() {
            Value::GlueElem(v, _, _) => Ok(v.clone()),
            _ => Ok(Value::unglue_elem(v, system, m)),
        }
    }
}
