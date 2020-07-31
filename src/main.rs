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

#[derive(Debug, Eq, PartialEq)]
enum Token {
    OpenParen,
    ClosedParen,
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

#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Clone)]
struct TakeWhilePeeking<I, P> {
    iterator: I,
    empty: bool,
    predicate: P
}

impl<I: Iterator, P> Iterator for TakeWhilePeeking<&mut std::iter::Peekable<I>, P> where P: FnMut(&I::Item) -> bool {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.empty {
            None
        } else {
            let peeked = self.iterator.peek()?;
            if (self.predicate)(peeked) {
                self.iterator.next()
            } else {
                self.empty = true;
                None
            }
        }
    }
}

fn take_while_peeking<I: std::iter::Iterator, P: FnMut(&I::Item) -> bool>(
    i: &mut std::iter::Peekable<I>, p: P
) -> TakeWhilePeeking<&mut std::iter::Peekable<I>, P> {
    TakeWhilePeeking {
        iterator: i,
        empty: false,
        predicate: p
    }
}

fn parse_digits(chars:&mut std::iter::Peekable<std::str::Chars>) -> Result<i64, ReplError> {
    let string: String = take_while_peeking(chars, |c| { c.is_digit(10) }).collect();
    string.parse().map_err(|err| { ReplError::TokenisationError(format!("Error parsing string: {}", err)) })
}

fn parse_symbol(chars:&mut std::iter::Peekable<std::str::Chars>) -> Result<String, ReplError> {
    Ok(take_while_peeking(chars, |c| { !c.is_whitespace() }).collect())
}

fn expect_one_of(chars: &mut std::iter::Peekable<std::str::Chars>, next: Vec<char>) -> Result<(), ReplError> {
    match chars.peek() {
        Some(c) if next.contains(c) => Ok(()),
        Some(c) => Err(ReplError::TokenisationError(format!("Unexpected {}. Expected one of {}.", c, render_alternatives(next)))),
        None => Err(ReplError::TokenisationError(format!("Unexpected end of string. Expected one of {}", render_alternatives(next))))
    }
}

fn expect_end_of_string(chars: &mut std::iter::Peekable<std::str::Chars>) -> Result<(), ReplError> {
    match chars.peek() {
        Some(c) => Err(ReplError::TokenisationError(format!("Unexpected {}. Expected end of string.", c))),
        None => Ok(())
    }
}

fn render_alternatives(v: Vec<char>) -> String {
    v.iter().map(|c| { format!("`{}`", c) }).collect::<Vec<String>>().join(", ")
}

fn tokenise(string: &str) -> Result<Vec<Token>, ReplError> {
    let mut chars = string.chars().peekable();
    let mut tokens: Vec<Token> = Vec::new();

    loop {
        match chars.peek() {
            Some('(') => { chars.next(); tokens.push(Token::OpenParen) },
            Some(')') => { chars.next(); tokens.push(Token::ClosedParen) },
            Some(x) if x.is_whitespace() => { chars.next(); },
            Some(x) if x.is_digit(10) => {
                let number = parse_digits(&mut chars)?;
                tokens.push(Token::Number(number));
                expect_one_of(&mut chars, vec![' ', '(', ')'])
                    .or(expect_end_of_string(&mut chars))?
            },
            Some(_) => {
                let symbol = parse_symbol(&mut chars)?;
                tokens.push(Token::Symbol(symbol));
            },
            None => { break; }
        }
    }

    Ok(tokens)
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
            Token::OpenParen => { EvaluationResult::Expression(Expression::String(String::from("(")))}
            Token::ClosedParen => { EvaluationResult::Expression(Expression::String(String::from(")")))}
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
    fn take_while_peeking_leaves_last_element_intact() {
        let mut iter = [1,2,3].iter().cloned().peekable();
        let f: Vec<u8> = take_while_peeking(&mut iter, |n| { *n < 3}).collect();
        assert_eq!(f, vec!(1,2));
        assert_eq!(iter.next(), Some(3));
    }

    #[test]
    fn parse_digits_parses_number() {
        let mut chars = "123".chars().peekable();
        assert_eq!(parse_digits(&mut chars).unwrap(), 123)
    }

    #[test]
    fn expect_one_of_passes_on_correct_character() {
        let mut iter = "ab".chars().peekable();
        assert!(expect_one_of(&mut iter, vec!('b', 'c')).is_err());
        iter.next();
        assert!(expect_one_of(&mut iter, vec!('b', 'c')).is_ok());
    }

    #[test]
    fn evaluates_primitive_expressions() {
        assert_eq!(
            eval(Input::Line(String::from("123"))).unwrap(),
            EvaluationResult::Expression(Expression::Int(123))
        )
    }

    #[test]
    fn tokenises_expressions() {
        let result = tokenise("(foo bar 123)").unwrap();
        assert_eq!(result, [Token::OpenParen, Token::Symbol(String::from("foo")), Token::Symbol(String::from("bar")), Token::Number(123), Token::ClosedParen]);
    }

    #[test]
    fn evaluates_addition_expression() {
        assert_eq!(
            eval(Input::Line(String::from("(+ 1 2)"))).unwrap(),
            EvaluationResult::Expression(Expression::Int(3))
        )
    }
}
