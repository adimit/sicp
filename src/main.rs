use sicp::{
    errors::{Position, ReplResult},
    evaluate::{evaluate_ast, Command, EvaluationResult},
    syntax::parse_tokens,
    tokenisation::tokenise,
};
use std::io;
use std::io::{stdout, Write};

enum Input {
    Line(String),
    EOF,
}

fn read() -> ReplResult<Input> {
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

fn eval(input: Input) -> ReplResult<EvaluationResult> {
    match input {
        Input::Line(string) => {
            let tokens = tokenise(&string)?;
            let ast = parse_tokens(tokens)?;
            evaluate_ast(&ast)
        }
        Input::EOF => Ok(EvaluationResult::Command(Command::Quit)),
    }
}

fn repl() -> ReplResult<EvaluationResult> {
    let input = read()?;
    eval(input)
}

fn main() {
    loop {
        let output = repl();
        match output {
            Ok(result) => match result {
                EvaluationResult::Symbol(sym) => {
                    println!("{}", sym);
                }
                EvaluationResult::Number(num) => {
                    println!("{}", num);
                }
                EvaluationResult::Command(c) => match c {
                    Command::Quit => {
                        println!("\nBye!");
                        break;
                    }
                },
            },
            Err(e) => match e.get_position() {
                Some(Position::Span(begin, end)) => println!(
                    "{}^{}\n{}",
                    " ".repeat(3 + begin),
                    "-".repeat(end - begin),
                    e
                ),
                Some(Position::Point(point)) => println!("{}^\n{}", " ".repeat(3 + point), e),
                _ => println!("Encountered an error:\n{}", e),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sicp::evaluate::Number;

    #[test]
    fn evaluates_primitive_expressions() {
        assert_eq!(
            test_eval("123").unwrap(),
            EvaluationResult::Number(Number::Int(123))
        );
    }
    fn test_eval(input: &str) -> ReplResult<EvaluationResult> {
        eval(Input::Line(input.to_string()))
    }

    #[test]
    fn evaluates_addition_expression() {
        assert_eq!(
            test_eval("(+ 1 2)").unwrap(),
            EvaluationResult::Number(Number::Int(3))
        );
    }

    #[test]
    fn evaluates_nested_addition_expression() {
        assert_eq!(
            test_eval("(+ 1 (+ 2 3) 4 5)").unwrap(),
            EvaluationResult::Number(Number::Int(15))
        );
    }

    #[test]
    fn error_on_unknown_function() {
        let r = test_eval("(foo)");
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().get_position().unwrap(), Position::Span(1, 3));
    }

    #[test]
    fn error_on_wrong_type_argument_for_sum() {
        let r = test_eval("(+ foo)");
        assert!(r.is_err());
        let position = r.unwrap_err().get_position().unwrap();
        assert_eq!(position, Position::Span(3, 5))
    }

    #[test]
    fn sum_of_no_numbers_is_zero() {
        assert_eq!(
            test_eval("(+)").unwrap(),
            EvaluationResult::Number(Number::Int(0))
        );
    }

    #[test]
    fn sum_of_float_and_int_is_float() {
        assert_eq!(
            test_eval("(+ 1 1.0)").unwrap(),
            EvaluationResult::Number(Number::Float(2.0))
        )
    }
}
