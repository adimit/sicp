use std::io;
use std::io::{stdout, Write};
use std::fmt;

enum Expression {
    StringExpr(String)
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::StringExpr(s) => { write!(f, "{}", s)?; }
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

fn eval(input: String) -> Expression {
    Expression::StringExpr(input)
}

fn main() {
    loop {
        let input = read();
        let output = eval(input);
        println!("{}", output);
    }
}
