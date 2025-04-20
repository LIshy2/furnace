use std::backtrace::Backtrace;
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};
use crate::ctt::term::Identifier;

#[derive(Clone, Debug)]
pub enum ErrorCause {
    UnknownTermName(Identifier),
    Hole,
    UnknownNameInSystem,
    UnknownInterval,
    MissingBranch,
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
