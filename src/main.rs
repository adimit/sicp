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

#[derive(Debug, Eq, Clone, Copy, PartialEq)]
struct Span {
    begin: usize,
    end: usize,
}

#[derive(Debug, Eq, PartialEq)]
struct Token {
    content: TokenData,
    span: Span,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
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

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
struct NodeId(usize);

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Expression {
    span: Span,
    id: NodeId,
    content: ExpressionData,
}

#[derive(Debug, Eq, PartialEq)]
enum ExpressionData {
    Symbol(String),
    Int(i64),
    Application(NodeId, Vec<NodeId>),
}

type ReplResult<T> = Result<T, ReplError>;

// hand-rolled arena allocator. Static, no content mutability
struct AST {
    nodes: Vec<NodeId>,
    roots: Vec<NodeId>,
}

impl AST {
    fn new() -> Self {
        AST {
            nodes: Vec::new(),
            roots: Vec::new(),
        }
    }

    fn new_expression(&mut self, span: Span, content: ExpressionData) -> NodeId {
        todo!()
    }

    fn new_application<'a, I: IntoIterator<Item = &'a NodeId>>(
        &mut self,
        head: NodeId,
        args: I,
    ) -> ReplResult<NodeId> {
        // check out that the given node ids exist
        // while checking the references, get the spans
        todo!()
    }

    fn get_node(&self, id: NodeId) -> Option<&Expression> {
        todo!()
    }

    fn add_root(&self, id: NodeId) -> ReplResult<()> {
        todo!()
    }

    fn get_roots<'a, I: Iterator<Item = &'a Expression>>(&self) -> I {
        todo!()
    }
}

#[cfg(test)]
mod ast_tests {
    #[test]
    fn insert_an_expression() {}

    #[test]
    fn insert_application_without_args() {
        // check spans
    }

    #[test]
    fn insert_application_with_args() {
        // check spans
    }

    #[test]
    fn insert_application_with_wrong_funhead_nodeid() {}

    #[test]
    fn insert_application_with_wrong_args_nodeid() {}

    #[test]
    fn add_root_nodes() {}

    #[test]
    fn add_root_nodes_with_wrong_node_id() {}
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let content = &self.content;
        match content {
            ExpressionData::Symbol(s) => {
                write!(f, "{}", s)?;
            }
            ExpressionData::Int(i) => {
                write!(f, "{}", i)?;
            }
            ExpressionData::Application(head, tail) => {
                write!(f, "({}", head)?;
                for expr in tail.iter() {
                    write!(f, " {}", expr.to_string())?;
                }
                write!(f, ")")?;
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

fn to_result<T, E>(option: Option<T>, error: E) -> Result<T, E> {
    match option {
        Some(content) => Ok(content),
        None => Err(error),
    }
}

// Recursive ast building function. Each invocation covers one level
// of depth, successive recurvise calls increase depth.
fn build_ast<'a, I: Iterator<Item = &'a Token>>(
    tit: &mut I,
    ast: &mut AST,
    depth: usize,
) -> Result<Vec<NodeId>, ReplError> where
{
    let mut forest = Vec::new();

    while let Some(token) = tit.next() {
        let expr = match &token.content {
            TokenData::Number(number) => {
                Ok(ast.new_expression(token.span, ExpressionData::Int(*number)))
            }
            TokenData::Symbol(s) => {
                Ok(ast.new_expression(token.span, ExpressionData::Symbol(String::from(s))))
            }

            TokenData::OpenParen => {
                let content = build_ast(tit, ast, depth + 1)?;
                if content.len() < 1 {
                    Err(ReplError::ParsingError(format!(
                        "Empty function application, at {}",
                        token
                    )))
                } else {
                    // since we know there's some content, we can
                    // assume there's an element 0, and a last element.
                    let funhead = content[0];
                    let rest = &content[1..];
                    ast.new_application(funhead, rest)
                }
            }
            TokenData::ClosedParen => match depth {
                0 => Err(ReplError::ParsingError(format!(
                    "Unbalanced parentheses. Unexpected `)` at {}.",
                    token.span.begin
                ))),
                _ => return Ok(forest), // hop out of the loop and return forest as is
            },
        }?;
        forest.push(expr);
    }
    // End of input has been reached. If we're not at depth == 0,
    // somebody forgot to balance their paretheses.
    if depth == 0 {
        // Add all the nodes from depth = 0 to the root node pool
        let _units = forest
            .iter()
            .map(|node| ast.add_root(*node))
            .collect::<Result<Vec<()>, ReplError>>()?;
        Ok(forest)
    } else {
        Err(ReplError::ParsingError(format!(
            "Expected {} closing parentheses at end of input.",
            depth
        )))
    }
}

fn evaluate_tokens<'a>(tokens: Vec<Token>) -> Result<EvaluationResult, ReplError> {
    let mut tit = tokens.iter();
    let mut ast: AST = AST::new();

    let _forest = build_ast(&mut tit, &mut ast, 0);

    todo!("Like, implement AST generation *and* evaluation. Hop hop!")
}

fn eval<'a>(input: Input) -> Result<EvaluationResult, ReplError> {
    match input {
        Input::Line(string) => {
            let tokens = tokenise(&string)?;
            evaluate_tokens(tokens)
        }
        Input::EOF => Ok(EvaluationResult::Command(Command::Quit)),
    }
}

fn repl<'a>() -> Result<EvaluationResult, ReplError> {
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
        if let EvaluationResult::Expression(expr) = eval(Input::Line(String::from("123"))).unwrap()
        {
            assert_eq!(expr.span, Span { begin: 0, end: 2 });
            assert_eq!(expr.content, ExpressionData::Int(123));
        } else {
            panic!("Wrong evaluation result");
        }
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
        if let EvaluationResult::Expression(expr) =
            eval(Input::Line(String::from("(+ 1 2)"))).unwrap()
        {
            assert_eq!(expr.content, ExpressionData::Int(3))
        } else {
            panic!("Wrong evaluation result");
        }
    }
}
