use std::io;
use std::io::{stdout, Write};
use std::fmt;

enum Command {
    Quit
}

enum EvaluationResult {
    Expression(Expression),
    Command(Command)
}

enum Expression {
    String(String)
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::String(s) => { write!(f, "{}", s)?; }
        }
        Ok(())
    }
}

fn read() -> String {
    print!("λ> ");
    stdout().flush().expect("Failed to flush stdout.");

    let mut input = String::new();

    io::stdin()
        .read_line(&mut input)
        .expect("Failed to read a line of input.");

    match input.strip_suffix("\n") {
        Some(s) => {String::from(s)}
        None => {input}
    }
}

fn eval(input: String) -> EvaluationResult {
    EvaluationResult::Expression(Expression::String(input))
}

fn main() {
    loop {
        let input = read();
        let output = eval(input);
        match output {
            EvaluationResult::Expression(e) => {
                println!("{}", e);
            }
            EvaluationResult::Command(c) => {
                match c {
                    Command::Quit => {
                        break;
                    }
                }
            }
        }
    }
}
