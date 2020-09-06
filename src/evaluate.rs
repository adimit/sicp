use crate::errors::{Position, ReplError, ReplResult};
use std::fmt;

use crate::syntax::{AstReducer, Expression, AST};

#[derive(Debug, Eq, PartialEq)]
pub enum Command {
    Quit,
}

impl fmt::Display for Command {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Command::Quit => write!(fmt, "QUIT"),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum EvaluationResult {
    Symbol(String),
    Int(i64),
    Command(Command),
}

struct EvaluationReducer<'a> {
    ast: &'a AST,
}

impl EvaluationReducer<'_> {
    fn new(ast: &AST) -> EvaluationReducer {
        EvaluationReducer { ast }
    }
}

impl AstReducer for EvaluationReducer<'_> {
    type Product = EvaluationResult;

    fn reduce_int(&self, n: i64) -> ReplResult<Self::Product> {
        Ok(EvaluationResult::Int(n))
    }

    fn reduce_symbol(&self, sym: &str) -> ReplResult<Self::Product> {
        Ok(EvaluationResult::Symbol(sym.into()))
    }

    fn reduce_application<'a>(
        &self,
        head: &Expression,
        args: impl Iterator<Item = &'a Expression>,
    ) -> ReplResult<Self::Product> {
        let funhead = self.ast.reduce_expr(head, self)?;
        match funhead {
            EvaluationResult::Symbol(sym) if sym == "+" => {
                let funargs = args
                    .map(|arg| {
                        let eval = self.ast.reduce_expr(arg, self)?;
                        match eval {
                            EvaluationResult::Int(num) => Ok(num),
                            _ => Err(ReplError::EvaluationError(
                                format!("Wrong type argument {}", eval),
                                arg.span.into(),
                            )),
                        }
                    })
                    .collect::<ReplResult<Vec<i64>>>()?;
                Ok(EvaluationResult::Int(funargs.iter().sum()))
            }
            EvaluationResult::Symbol(_) => Err(ReplError::EvaluationError(
                format!("Unknown function {}", funhead),
                head.span.into(),
            )),
            _ => Err(ReplError::EvaluationError(
                format!("Invalid function head {}", funhead),
                head.span.into(),
            )),
        }
    }
}

impl fmt::Display for EvaluationResult {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EvaluationResult::Symbol(sym) => write!(fmt, "Sym({})", sym),
            EvaluationResult::Int(int) => write!(fmt, "Int({})", int),
            EvaluationResult::Command(cmd) => write!(fmt, "Cmd({})", cmd),
        }
    }
}

pub fn evaluate_ast(ast: &AST) -> ReplResult<EvaluationResult> {
    let reducer = EvaluationReducer::new(ast);
    let mut results = ast.reduce(&reducer)?;

    results.pop().ok_or(ReplError::InternalError(
        String::from("No results to evaluate!"),
        Position::Unknown,
    ))
}
