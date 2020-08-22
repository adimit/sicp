use crate::errors::{Position, ReplError, ReplResult};
use std::fmt;

use crate::syntax::{Expression, ExpressionData, AST};
use crate::tokenisation::Span;

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

impl fmt::Display for EvaluationResult {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EvaluationResult::Symbol(sym) => write!(fmt, "Sym({})", sym),
            EvaluationResult::Int(int) => write!(fmt, "Int({})", int),
            EvaluationResult::Command(cmd) => write!(fmt, "Cmd({})", cmd),
        }
    }
}

fn evaluate_expr(expr: &Expression, ast: &AST) -> ReplResult<EvaluationResult> {
    match &expr.content {
        ExpressionData::Symbol(sym) => Ok(EvaluationResult::Symbol(sym.to_string())),
        ExpressionData::Int(int) => Ok(EvaluationResult::Int(*int)),
        ExpressionData::Application(nodeid, args) => {
            let head = ast.get_node_result(*nodeid)?;
            let evaluated_head = evaluate_expr(head, ast)?;
            let evaluated_args = args
                .iter()
                .map(|arg| {
                    let arg_expr = ast.get_node_result(*arg)?;
                    evaluate_expr(arg_expr, ast).map(|e| (e, arg_expr.span))
                })
                .collect::<ReplResult<Vec<(EvaluationResult, Span)>>>()?;

            match &evaluated_head {
                EvaluationResult::Symbol(sym) if sym == "+" => {
                    let numbers = evaluated_args
                        .iter()
                        .map(|arg| match arg {
                            (EvaluationResult::Int(number), _) => Ok(*number),
                            (evaluated_arg, span) => Err(ReplError::EvaluationError(
                                format!(
                                    "Wrong type argument {} for function head {}",
                                    evaluated_arg, evaluated_head
                                ),
                                Position::from(*span),
                            )),
                        })
                        .collect::<ReplResult<Vec<i64>>>()?;
                    Ok(EvaluationResult::Int(numbers.iter().sum()))
                }
                _ => Err(ReplError::EvaluationError(
                    format!("Invalid function head expression {}", evaluated_head,),
                    Position::from(head.span),
                )),
            }
        }
    }
}

pub fn evaluate_ast(ast: &AST) -> ReplResult<EvaluationResult> {
    let forest = ast.get_roots();
    let mut results = forest
        .iter()
        .map(|nodeid| {
            let node = ast.get_node_result(*nodeid)?;
            evaluate_expr(node, &ast)
        })
        .collect::<ReplResult<Vec<EvaluationResult>>>()?;

    results.pop().ok_or(ReplError::InternalError(
        String::from("No results to evaluate!"),
        Position::Unknown,
    ))
}
