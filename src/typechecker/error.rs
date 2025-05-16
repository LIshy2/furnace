use crate::ctt::term::{Identifier, System};
use crate::precise::term::{Term, Value};
use std::backtrace::Backtrace;
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum ErrorCause {
    UnexpectedTypeInfered {
        term: Rc<Term>,
        expected: Rc<Value>,
        infered: Rc<Value>,
    },
    ExpectedDataType(Rc<Value>),
    ExpectedSigma(Rc<Value>),
    UnEqInIdSystem(Rc<Value>, Rc<Value>),
    UnknownTermName(Identifier),
    Hole,
    UnknownNameInSystem,
    UnknownInterval,
    MissingBranch,
    WrongPathEnd((Rc<Value>, Rc<Value>), (Rc<Value>, Rc<Value>)),
    UneqInHSumSplit(System<Value>, System<Value>),
}

pub struct TypeError {
    cause: ErrorCause,
    trace: Backtrace,
}

impl From<ErrorCause> for TypeError {
    fn from(value: ErrorCause) -> Self {
        TypeError {
            cause: value,
            trace: Backtrace::capture(),
        }
    }
}

impl Debug for TypeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.cause.fmt(f)?;
        std::fmt::Display::fmt(&self.trace, f)
    }
}

impl Display for TypeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Oh no, something bad went down")
    }
}

impl Error for TypeError {}
