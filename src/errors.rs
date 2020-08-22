use std::error::Error;
use std::fmt;
use std::io;

pub type ReplResult<T> = Result<T, ReplError>;

#[derive(Debug)]
pub enum ReplError {
    IOError(io::Error),
    TokenisationError(String, Position),
    ParsingError(String, Position),
    EvaluationError(String, Position),
    InternalError(String, Position),
}

impl Error for ReplError {}

impl ReplError {
    pub fn get_position(&self) -> Option<Position> {
        match self {
            ReplError::InternalError(_, pos) => Some(*pos),
            ReplError::EvaluationError(_, pos) => Some(*pos),
            ReplError::ParsingError(_, pos) => Some(*pos),
            ReplError::TokenisationError(_, pos) => Some(*pos),
            ReplError::IOError(_) => None,
        }
    }
}

impl fmt::Display for ReplError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ReplError::IOError(e) => write!(f, "REPL IO error: {}.", e),
            ReplError::TokenisationError(msg, span) => {
                write!(f, "REPL tokenisation error: {} at {}.)", msg, span)
            }
            ReplError::ParsingError(msg, span) => {
                write!(f, "RERPL parsing error: {} at {}.", msg, span)
            }
            ReplError::EvaluationError(msg, span) => {
                write!(f, "REPL evaluation error: {} at {}.", msg, span)
            }
            ReplError::InternalError(msg, span) => write!(
                f,
                "REPL internal error: {} at {}. This is a bug!",
                msg, span
            ),
        }
    }
}

impl From<io::Error> for ReplError {
    fn from(e: io::Error) -> Self {
        ReplError::IOError(e)
    }
}

#[derive(Debug, Eq, Clone, Copy, PartialEq)]
pub enum Position {
    Span(usize, usize),
    Point(usize),
    Unknown,
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Position::Span(begin, end) => write!(f, "{} — {}", begin, end),
            Position::Point(point) => write!(f, "{}", point),
            Position::Unknown => write!(f, "unknown position"),
        }
    }
}
