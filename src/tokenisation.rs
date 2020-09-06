use crate::errors::{Position, ReplError, ReplResult};
use std::fmt;

#[derive(Debug, Eq, Clone, Copy, PartialEq)]
pub struct Span {
    pub begin: usize,
    pub end: usize,
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.begin, self.end)
    }
}

impl Span {
    pub fn new(begin: usize, end: usize) -> Span {
        Span { begin, end }
    }
}

impl From<Span> for Position {
    fn from(span: Span) -> Self {
        Position::Span(span.begin, span.end)
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct Token {
    pub content: TokenData,
    pub span: Span,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{} ({})]", self.content, self.span)
    }
}

impl fmt::Display for TokenData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenData::OpenParen => write!(f, "("),
            TokenData::ClosedParen => write!(f, "("),
            TokenData::Number(n) => write!(f, "num:{}", n),
            TokenData::Symbol(s) => write!(f, "sym:{}", s),
        }
    }
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
pub enum TokenData {
    OpenParen,
    ClosedParen,
    Number(i32),
    Symbol(String),
}

type Tape<'a> = std::iter::Peekable<std::iter::Enumerate<std::str::Chars<'a>>>;

pub fn tokenise(string: &str) -> ReplResult<Vec<Token>> {
    let mut chars = string.chars().enumerate().peekable();
    let mut tokens = Vec::new();
    while let Some(token) = parse_a_token(&mut chars) {
        tokens.push(token);
    }

    match chars.peek() {
        Some((pos, c)) => Err(ReplError::TokenisationError(
            format!("Unrecognised input `{}`", c),
            Position::Point(*pos),
        )),
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
        match string.parse::<i32>() {
            Ok(num) => Some(Token::create(start, lastpos, TokenData::Number(num))),
            Err(_) => Some(Token::create(start, lastpos, TokenData::Symbol(string))),
        }
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenises_expressions() {
        let result = tokenise("(foo bar 123)").unwrap();
        assert_eq!(
            result,
            [
                Token {
                    span: Span::new(0, 0),
                    content: TokenData::OpenParen
                },
                Token {
                    span: Span::new(1, 3),
                    content: TokenData::Symbol("foo".to_string())
                },
                Token {
                    span: Span::new(5, 7),
                    content: TokenData::Symbol("bar".to_string())
                },
                Token {
                    span: Span::new(9, 11),
                    content: TokenData::Number(123)
                },
                Token {
                    span: Span::new(12, 12),
                    content: TokenData::ClosedParen
                },
            ]
        )
    }
}
