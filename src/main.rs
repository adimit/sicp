use std::io;
use std::io::{stdout, Write};
use std::fmt;

enum Input {
    Line(String),
    EOF
}

enum Command {
    Quit
}

enum EvaluationResult {
    Expression(Expression),
    Command(Command)
}

enum Expression {
    String(String),
    Int(i64),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::String(s) => { write!(f, "{}", s)?; }
            Expression::Int(i) => { write!(f, "{}", i)?; }
        }
        Ok(())
    }
}

fn read() -> Input {
    print!("λ> ");
    stdout().flush().expect("Failed to flush stdout.");

    let mut input = String::new();

    match io::stdin().read_line(&mut input) {
        Ok(0) => { Input::EOF }
        Ok(_) => {
            match input.strip_suffix("\n") {
                Some(s) => {Input::Line(String::from(s))}
                None => {Input::Line(input)}
            }
        }
        Err(e) => {
            panic!("Could not read from stdin: {}", e)
        }
    }
}

fn eval(input: Input) -> EvaluationResult {
    match input {
        Input::Line(line) => {
            EvaluationResult::Expression(Expression::String(line))
        }
        Input::EOF => {
            EvaluationResult::Command(Command::Quit)
        }
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
            EvaluationResult::Command(c) => {
                match c {
                    Command::Quit => {
                        println!("Bye!");
                        break;
                    }
                }
            }
        }
    }
}
