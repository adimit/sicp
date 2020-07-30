// steps:
// read input (possible failure)
// tokenise (possible lexing failure)
// parse (possible parsing failure, e.g. unbalanced parens)
// optimise?
// evaluate (possible evaluation failure, e.g. no definition)
// print

// tasks:
// - wrap all return types in result type where needed
// - decide which errors get thrown where
// - add error handling in print

use std::fmt;
use std::io;
use std::{error::Error, io::{stdout, Write}};

#[derive(Debug)]
enum ReplError {
    IOError(io::Error),
    TokenisationError(String),
    ParsingError(String),
    EvaluationError(String)
}

impl Error for ReplError {}

impl fmt::Display for ReplError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ReplError::IOError(e) => { write!(f, "REPL IO error: {}", e)? }
            ReplError::TokenisationError(msg) => { write!(f, "REPL tokenisation error: {}", msg)? }
            ReplError::ParsingError(msg) => { write!(f, "RERPL parsing error: {}", msg)? }
            ReplError::EvaluationError(msg) => {write!(f, "REPL evaluation error: {}", msg)? }
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
}

enum Input {
    Line(String),
    EOF,
}

enum Command {
    Quit,
}

enum EvaluationResult {
    Expression(Expression),
    Command(Command),
}

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

fn read() -> Result<Input, ReplError> {
    print!("λ> ");
    stdout().flush()?;

    let mut input = String::new();
    let line = io::stdin().read_line(&mut input)?;

    Ok(match line {
        0 => Input::EOF,
        _ => Input::Line(String::from(input.strip_suffix("\n").unwrap_or(&input))),
    })
}

fn eval(input: Input) -> Result<EvaluationResult, ReplError> {
    Ok(match input {
        Input::Line(string) => EvaluationResult::Expression(Expression::String(string)),
        Input::EOF => EvaluationResult::Command(Command::Quit),
    })
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
            Ok(result) => {
                match result {
                    EvaluationResult::Expression(e) => {
                        println!("{}", e);
                    }
                    EvaluationResult::Command(c) => {
                        match c {
                            Command::Quit => {
                                println!("\nBye!");
                                break;
                            }
                        }
                    }
                }
            }
            Err(e) => {
                println!("Encountered an error:\n{}", e);
            }
        }
    }
}
