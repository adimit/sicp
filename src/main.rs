use std::fmt;
use std::io;
use std::{
    error::Error,
    io::{stdout, Write},
};

#[derive(Debug)]
enum ReplError {
    IOError(io::Error),
    TokenisationError(String),
    ParsingError(String),
    EvaluationError(String),
}

impl Error for ReplError {}

impl fmt::Display for ReplError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ReplError::IOError(e) => write!(f, "REPL IO error: {}", e)?,
            ReplError::TokenisationError(msg) => write!(f, "REPL tokenisation error: {}", msg)?,
            ReplError::ParsingError(msg) => write!(f, "RERPL parsing error: {}", msg)?,
            ReplError::EvaluationError(msg) => write!(f, "REPL evaluation error: {}", msg)?,
        }
        Ok(())
    }
}

impl From<io::Error> for ReplError {
    fn from(e: io::Error) -> Self {
        ReplError::IOError(e)
    }
}

enum Token {
    Number(i64),
    Symbol(String),
}

enum Input {
    Line(String),
    EOF,
}

#[derive(Debug, Eq, PartialEq)]
enum Command {
    Quit,
}

#[derive(Debug, Eq, PartialEq)]
enum EvaluationResult {
    Expression(Expression),
    Command(Command),
}

#[derive(Debug, Eq, PartialEq)]
enum Expression {
    String(String),
    Int(i64),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::String(s) => {
                write!(f, "{}", s)?;
            }
            Expression::Int(i) => {
                write!(f, "{}", i)?;
            }
        }
        Ok(())
    }
}

fn tokenise(string: &str) -> Result<Vec<Token>, ReplError> {
    Ok(string
        .split(" ")
        .map(|token| {
            token
                .parse::<i64>()
                .map_or(Token::Symbol(String::from(token)), |number| {
                    Token::Number(number)
                })
        })
        .collect())
}

fn read() -> Result<Input, ReplError> {
    print!("λ> ");
    stdout().flush()?;

    let mut input = String::new();
    let bytes_read = io::stdin().read_line(&mut input)?;

    if bytes_read == 0 {
        return Ok(Input::EOF);
    };

    Ok(Input::Line(String::from(
        input.strip_suffix("\n").unwrap_or(&input),
    )))
}

fn evaluate_tokens(tokens: Vec<Token>) -> Result<EvaluationResult, ReplError> {
    tokens
        .get(0)
        .map(|token| match token {
            Token::Number(num) => EvaluationResult::Expression(Expression::Int(*num)),
            Token::Symbol(sym) => EvaluationResult::Expression(Expression::String(sym.clone())),
        })
        .map_or(
            Err(ReplError::EvaluationError(String::from(
                "No tokens to evaluate",
            ))),
            |result| Ok(result),
        )
}

fn eval(input: Input) -> Result<EvaluationResult, ReplError> {
    match input {
        Input::Line(string) => {
            let tokens = tokenise(&string)?;
            evaluate_tokens(tokens)
        }
        Input::EOF => Ok(EvaluationResult::Command(Command::Quit)),
    }
}

fn repl() -> Result<EvaluationResult, ReplError> {
    let input = read()?;
    let output = eval(input)?;
    Ok(output)
}

fn main() {
    loop {
        let output = repl();
        match output {
            Ok(result) => match result {
                EvaluationResult::Expression(e) => {
                    println!("{}", e);
                }
                EvaluationResult::Command(c) => match c {
                    Command::Quit => {
                        println!("\nBye!");
                        break;
                    }
                },
            },
            Err(e) => {
                println!("Encountered an error:\n{}", e);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evaluates_simple_expressions() {
        assert_eq!(
            eval(Input::Line(String::from("123"))).unwrap(),
            EvaluationResult::Expression(Expression::Int(123))
        )
    }
}
