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

#[derive(Clone, Debug, PartialEq)]
pub enum Number {
    Int(i32),
    Float(f64),
}

impl From<i32> for Number {
    fn from(i: i32) -> Self {
        Number::Int(i)
    }
}

impl From<f64> for Number {
    fn from(f: f64) -> Self {
        Number::Float(f)
    }
}

impl std::iter::Sum for Number {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Number::Int(0), |acc, num| match num {
            Number::Int(int_num) => match acc {
                Number::Int(int_acc) => Number::Int(int_acc + int_num),
                Number::Float(float_acc) => Number::Float(float_acc + f64::from(int_num)),
            },
            Number::Float(float_num) => match acc {
                Number::Int(int_acc) => Number::Float(f64::from(int_acc) + float_num),
                Number::Float(float_acc) => Number::Float(float_acc + float_num),
            },
        })
    }
}

impl fmt::Display for Number {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Number::Int(int) => write!(fmt, "Int({})", int),
            Number::Float(float) => write!(fmt, "Float({})", float),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum EvaluationResult {
    Symbol(String),
    Number(Number),
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

    fn reduce_int(&self, n: i32) -> ReplResult<Self::Product> {
        Ok(EvaluationResult::Number(Number::Int(n)))
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
                            EvaluationResult::Number(num) => Ok(num),
                            _ => Err(ReplError::EvaluationError(
                                format!("Wrong type argument {}", eval),
                                arg.span.into(),
                            )),
                        }
                    })
                    .collect::<ReplResult<Vec<Number>>>()?;
                Ok(EvaluationResult::Number(funargs.iter().cloned().sum()))
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
            EvaluationResult::Number(num) => write!(fmt, "Int({})", num),
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
