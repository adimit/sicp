#![feature(peekable_next_if)]

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
struct Span {
    begin: usize,
    end: usize,
}

#[derive(Debug, Eq, PartialEq)]
struct Token {
    content: TokenData,
    span: Span,
}

impl Token {
    fn create(begin: usize, end: usize, content: TokenData) -> Self {
        Token {
            span: Span { begin, end },
            content,
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
enum TokenData {
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

type Tape<'a> = std::iter::Peekable<std::iter::Enumerate<std::str::Chars<'a>>>;

fn tokenise(string: &str) -> Result<Vec<Token>, ReplError> {
    let mut chars = string.chars().enumerate().peekable();
    let mut tokens = Vec::new();
    while let Some(token) = parse_a_token(&mut chars) {
        tokens.push(token);
    }

    match chars.peek() {
        Some((pos, c)) => Err(ReplError::TokenisationError(format!(
            "Unrecognised input `{}` at position {}.",
            c, pos
        ))),
        None => Ok(tokens),
    }
}

fn parse_a_token(tape: &mut Tape) -> Option<Token> {
    parse_whitespace(tape);
    let r = parse_open_paren(tape)
        .or_else(|| parse_closed_paren(tape))
        .or_else(|| parse_symbol(tape));
    parse_whitespace(tape);
    r
}

fn parse_open_paren(tape: &mut Tape) -> Option<Token> {
    tape.next_if(|(_, c)| *c == '(')
        .map(|(pos, _)| Token::create(pos, pos, TokenData::OpenParen))
}

fn parse_closed_paren(tape: &mut Tape) -> Option<Token> {
    tape.next_if(|(_, c)| *c == ')')
        .map(|(pos, _)| Token::create(pos, pos, TokenData::ClosedParen))
}

fn parse_whitespace(tape: &mut Tape) -> Option<()> {
    tape.next_if(|(_, c)| c.is_whitespace()).map(|(_, _)| ())
}

fn parse_symbol(tape: &mut Tape) -> Option<Token> {
    let mut string = String::new();
    let mut lastpos = 0;
    while let Some((pos, c)) = tape.next_if(|(_, c)| !(c.is_whitespace() || *c == '(' || *c == ')'))
    {
        string.push(c);
        lastpos = pos;
    }

    if string.len() > 0 {
        let start: usize = lastpos - (string.len() - 1);
        match string.parse::<i64>() {
            Ok(num) => Some(Token::create(start, lastpos, TokenData::Number(num))),
            Err(_) => Some(Token::create(start, lastpos, TokenData::Symbol(string))),
        }
    } else {
        None
    }
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
        .map(|token| match &token.content {
            TokenData::Number(num) => EvaluationResult::Expression(Expression::Int(*num)),
            TokenData::Symbol(sym) => EvaluationResult::Expression(Expression::String(sym.clone())),
            TokenData::OpenParen => {
                EvaluationResult::Expression(Expression::String(String::from("(")))
            }
            TokenData::ClosedParen => {
                EvaluationResult::Expression(Expression::String(String::from(")")))
            }
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
    fn evaluates_primitive_expressions() {
        assert_eq!(
            eval(Input::Line(String::from("123"))).unwrap(),
            EvaluationResult::Expression(Expression::Int(123))
        )
    }

    #[test]
    fn tokenises_expressions() {
        let result = tokenise("(foo bar 123)").unwrap();
        assert_eq!(
            result,
            [
                Token {
                    span: Span { begin: 0, end: 0 },
                    content: TokenData::OpenParen
                },
                Token {
                    span: Span { begin: 1, end: 3 },
                    content: TokenData::Symbol("foo".to_string())
                },
                Token {
                    span: Span { begin: 5, end: 7 },
                    content: TokenData::Symbol("bar".to_string())
                },
                Token {
                    span: Span { begin: 9, end: 11 },
                    content: TokenData::Number(123)
                },
                Token {
                    span: Span { begin: 12, end: 12 },
                    content: TokenData::ClosedParen
                },
            ]
        )
    }

    #[test]
    fn evaluates_addition_expression() {
        assert_eq!(
            eval(Input::Line(String::from("(+ 1 2)"))).unwrap(),
            EvaluationResult::Expression(Expression::Int(3))
        )
    }
}
