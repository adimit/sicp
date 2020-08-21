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
        write!(
            f,
            "[{} ({}, {})]",
            self.content, self.span.begin, self.span.end
        )
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

impl fmt::Display for Command {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Command::Quit => write!(fmt, "QUIT"),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
enum EvaluationResult {
    Symbol(String),
    Int(i64),
    Command(Command),
}

impl fmt::Display for EvaluationResult {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EvaluationResult::Symbol(sym) => write!(fmt, "Sym({})", sym),
            EvaluationResult::Int(int) => write!(fmt, "Int({})", int),
            EvaluationResult::Command(cmd) => write!(fmt, "Cmd({})", cmd),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
struct NodeId(usize);

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let NodeId(num) = self;
        write!(f, "node:{}", num)
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
    nodes: Vec<Expression>,
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
        let id = NodeId(self.nodes.len());
        let expr = Expression { span, content, id };
        self.nodes.push(expr);
        id
    }

    fn new_application<'a, I: IntoIterator<Item = NodeId>>(
        &mut self,
        head: NodeId,
        args: I,
    ) -> ReplResult<NodeId> {
        // check out that the given node ids exist
        // while checking the references, get the spans
        let head_expr = self
            .get_node(head)
            .ok_or(ReplError::ParsingError(format!("Unknown node {}", head)))?;
        let tail = args.into_iter().collect::<Vec<NodeId>>();
        let mut max_span = head_expr.span.end;
        tail.iter()
            .map(|node| {
                let expr = self.get_node(*node).ok_or(ReplError::ParsingError(format!(
                    "Unknown node {}",
                    head_expr
                )))?;
                max_span = std::cmp::max(max_span, expr.span.end);
                Ok(expr)
            })
            .collect::<Result<Vec<&Expression>, ReplError>>()?;
        let id = NodeId(self.nodes.len());
        let expr = Expression {
            span: Span {
                begin: head_expr.span.begin,
                end: max_span,
            },
            id,
            content: ExpressionData::Application(head, tail),
        };
        self.nodes.push(expr);
        Ok(id)
    }

    fn get_node(&self, id: NodeId) -> Option<&Expression> {
        let NodeId(n) = id;
        self.nodes.get(n)
    }

    fn add_root(&mut self, id: NodeId) -> ReplResult<()> {
        self.get_node(id)
            .ok_or(ReplError::ParsingError(format!("Unknown node {}", id)))?;
        self.roots.push(id);
        Ok(())
    }
}

#[cfg(test)]
mod ast_tests {
    use super::*;

    fn span(begin: usize, end: usize) -> Span {
        Span { begin, end }
    }

    #[test]
    fn insert_an_expression() {
        let mut ast = AST::new();
        let expr = ExpressionData::Int(1);
        let id = ast.new_expression(span(0, 0), expr);
        assert!(ast.get_node(id).is_some());
    }

    #[test]
    fn insert_application_without_args() {
        let mut ast = AST::new();
        let expr = ExpressionData::Symbol("foo".to_string());
        let id = ast.new_expression(span(0, 1), expr);
        let ap = ast.new_application(id, vec![]).unwrap();
        let ap_expr = ast.get_node(ap).unwrap();
        assert_eq!(ap_expr.span, span(0, 1));

        if let ExpressionData::Application(head, tail) = &ap_expr.content {
            assert_eq!(*head, id);
            assert_eq!(tail.len(), 0);
        } else {
            panic!("Wrong expression data");
        }
    }

    #[test]
    fn insert_application_with_args() {
        let mut ast = AST::new();
        let expr = ExpressionData::Symbol("foo".to_string());
        let expr_1 = ExpressionData::Symbol("bar".to_string());
        let expr_2 = ExpressionData::Symbol("baz".to_string());
        let head_id = ast.new_expression(span(0, 2), expr);
        let args_1 = ast.new_expression(span(3, 5), expr_1);
        let args_2 = ast.new_expression(span(6, 8), expr_2);

        let ap = ast.new_application(head_id, vec![args_1, args_2]).unwrap();
        let ap_expr = ast.get_node(ap).unwrap();

        assert_eq!(ap_expr.span, span(0, 8));

        if let ExpressionData::Application(head, tail) = &ap_expr.content {
            assert_eq!(*head, head_id);
            assert_eq!(tail, &[args_1, args_2]);
        } else {
            panic!("Wrong expression data");
        }
    }

    #[test]
    fn insert_application_with_wrong_funhead_nodeid() {
        let mut ast = AST::new();
        let result = ast.new_application(NodeId(0), vec![]);
        assert!(result.is_err());
    }

    #[test]
    fn insert_application_with_wrong_args_nodeid() {
        let mut ast = AST::new();
        let expr = ExpressionData::Symbol("foo".to_string());
        let head = ast.new_expression(span(0, 0), expr);
        let result = ast.new_application(head, vec![NodeId(99)]);
        assert!(result.is_err());
    }

    #[test]
    fn add_root_nodes() {
        let mut ast = AST::new();
        let expr = ExpressionData::Symbol("foo".to_string());
        let head = ast.new_expression(span(0, 0), expr);
        let ap = ast.new_application(head, vec![]).unwrap();
        let root_added = ast.add_root(ap);
        assert!(root_added.is_ok());

        assert_eq!(ast.roots, vec!(ap));
    }

    #[test]
    fn add_root_nodes_with_wrong_node_id() {
        let mut ast = AST::new();
        let result = ast.add_root(NodeId(99));
        assert!(result.is_err());
    }
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
                    let mut args = content.iter().cloned();
                    args.next();
                    ast.new_application(content[0], args)
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
            .collect::<Result<Vec<()>, ReplError>>();
        Ok(forest)
    } else {
        Err(ReplError::ParsingError(format!(
            "Expected {} closing parentheses at end of input.",
            depth
        )))
    }
}

fn evaluate_expr<'a>(expr: &'a Expression, ast: &AST) -> ReplResult<EvaluationResult> {
    match &expr.content {
        ExpressionData::Symbol(sym) => Ok(EvaluationResult::Symbol(sym.to_string())),
        ExpressionData::Int(int) => Ok(EvaluationResult::Int(*int)),
        ExpressionData::Application(nodeid, args) => {
            let head = ast
                .get_node(*nodeid)
                .ok_or(ReplError::EvaluationError(format!(
                    "Unknown node id {}.",
                    nodeid
                )))?;
            let evaluated_head = evaluate_expr(head, ast)?;
            let evaluated_args = args
                .iter()
                .map(|arg| {
                    let arg_expr =
                        ast.get_node(*arg)
                            .ok_or(ReplError::EvaluationError(format!(
                                "Unknown node id {}.",
                                arg
                            )))?;
                    evaluate_expr(arg_expr, ast)
                })
                .collect::<ReplResult<Vec<EvaluationResult>>>()?;

            match evaluated_head {
                EvaluationResult::Symbol(sym) if sym == "+" => {
                    let numbers = evaluated_args
                        .iter()
                        .map(|arg| match arg {
                            EvaluationResult::Int(number) => Ok(*number),
                            _ => Err(ReplError::EvaluationError(format!(
                                "Wrong type argument {}.",
                                arg
                            ))),
                        })
                        .collect::<ReplResult<Vec<i64>>>()?;
                    Ok(EvaluationResult::Int(numbers.iter().sum()))
                }
                _ => Err(ReplError::EvaluationError(format!(
                    "Invalid function head expression {} at {}-{}.",
                    evaluated_head, head.span.begin, head.span.end
                ))),
            }
        }
    }
}

fn evaluate_tokens<'a>(tokens: Vec<Token>) -> Result<EvaluationResult, ReplError> {
    let mut tit = tokens.iter();
    let mut ast: AST = AST::new();

    let forest = build_ast(&mut tit, &mut ast, 0)?;

    let mut results = forest
        .iter()
        .map(|nodeid| match ast.get_node(*nodeid) {
            Some(tree) => evaluate_expr(tree, &ast),
            None => Err(ReplError::EvaluationError(format!(
                "Unkonwn node id {}.",
                *nodeid
            ))),
        })
        .collect::<ReplResult<Vec<EvaluationResult>>>()?;

    results
        .pop()
        .ok_or(ReplError::EvaluationError("No results!".to_string()))
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
                EvaluationResult::Symbol(sym) => {
                    println!("{}", sym);
                }
                EvaluationResult::Int(int) => {
                    println!("{}", int);
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
        assert_eq!(test_eval("123").unwrap(), EvaluationResult::Int(123));
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
    fn test_eval(input: &str) -> ReplResult<EvaluationResult> {
        eval(Input::Line(input.to_string()))
    }

    #[test]
    fn evaluates_addition_expression() {
        assert_eq!(test_eval("(+ 1 2)").unwrap(), EvaluationResult::Int(3));
    }

    #[test]
    fn evaluates_nested_addition_expression() {
        assert_eq!(
            test_eval("(+ 1 (+ 2 3) 4 5)").unwrap(),
            EvaluationResult::Int(15)
        );
    }

    #[test]
    fn error_on_unknown_function() {
        assert!(test_eval("(foo)").is_err())
    }

    #[test]
    fn error_on_wrong_type_argument_for_sum() {
        assert!(test_eval("(+ foo)").is_err())
    }

    #[test]
    fn sum_of_no_numbers_is_zero() {
        assert_eq!(test_eval("(+)").unwrap(), EvaluationResult::Int(0));
    }
}
