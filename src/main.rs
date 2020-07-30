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
use std::io::{stdout, Write};

enum Token {
    Number(i64),
}

enum Input {
    Line(Token),
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

fn read() -> Input {
    print!("λ> ");
    stdout().flush().expect("Failed to flush stdout.");

    let mut input = String::new();

    match io::stdin().read_line(&mut input) {
        Ok(0) => Input::EOF,
        Ok(_) => match input.strip_suffix("\n") {
            Some(s) => Input::Line(Token::Number(1)),
            None => Input::Line(Token::Number(1)),
        },
        Err(e) => panic!("Could not read from stdin: {}", e),
    }
}

fn eval(input: Input) -> EvaluationResult {
    match input {
        Input::Line(token) => EvaluationResult::Expression(Expression::Int(match token {
            Token::Number(n) => n,
        })),
        Input::EOF => EvaluationResult::Command(Command::Quit),
    }
}

fn main() {
    loop {
        let input = read();
        let output = eval(input);
        match output {
            EvaluationResult::Expression(e) => {
                println!("{}", e);
            }
            EvaluationResult::Command(c) => match c {
                Command::Quit => {
                    println!("\nBye!");
                    break;
                }
            },
        }
    }
}
