use crate::errors::{Position, ReplError, ReplResult};
use crate::tokenisation::{Span, Token, TokenData};
use std::fmt;

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
struct NodeId(usize);

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let NodeId(num) = self;
        write!(f, "node:{}", num)
    }
}

#[derive(Debug, PartialEq)]
pub struct Expression {
    pub span: Span,
    id: NodeId,
    content: ExpressionData,
}

#[derive(Debug, PartialEq)]
enum ExpressionData {
    Symbol(String),
    Int(i32),
    Float(f64),
    Application(NodeId, Vec<NodeId>),
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
            ExpressionData::Float(float) => {
                write!(f, "{}", float)?;
            }
        }
        Ok(())
    }
}

// hand-rolled arena allocator. Static, no content mutability
pub struct AST {
    nodes: Vec<Expression>,
    roots: Vec<NodeId>,
}

pub trait AstReducer {
    type Product;

    fn reduce_int(&self, n: i32) -> ReplResult<Self::Product>;

    fn reduce_symbol(&self, sym: &str) -> ReplResult<Self::Product>;

    fn reduce_application<'a>(
        &self,
        head: &Expression,
        args: impl Iterator<Item = &'a Expression>,
    ) -> ReplResult<Self::Product>;
}

impl AST {
    fn new() -> Self {
        AST {
            nodes: Vec::new(),
            roots: Vec::new(),
        }
    }

    pub fn reduce<P>(&self, reducer: &impl AstReducer<Product = P>) -> ReplResult<Vec<P>> {
        let roots = self
            .get_roots()
            .iter()
            .map(|nodeid| self.get_node_result(*nodeid))
            .collect::<ReplResult<Vec<&Expression>>>()?;
        roots
            .iter()
            .map(|expr| self.reduce_expr(expr, reducer))
            .collect()
    }

    pub fn reduce_expr<P>(
        &self,
        expr: &Expression,
        reducer: &impl AstReducer<Product = P>,
    ) -> ReplResult<P> {
        match &expr.content {
            ExpressionData::Symbol(sym) => reducer.reduce_symbol(sym),
            ExpressionData::Int(num) => reducer.reduce_int(*num),
            ExpressionData::Application(head_id, tail_ids) => {
                let head = self.get_node_result(*head_id)?;
                let args = tail_ids
                    .iter()
                    .map(|node_id| self.get_node_result(*node_id))
                    .collect::<ReplResult<Vec<&Expression>>>()?;

                reducer.reduce_application(head, args.iter().cloned())
            }
            ExpressionData::Float(float) => todo!(),
        }
    }

    fn new_expression(&mut self, span: Span, content: ExpressionData) -> NodeId {
        let id = NodeId(self.nodes.len());
        let expr = Expression { span, content, id };
        self.nodes.push(expr);
        id
    }

    fn new_application(
        &mut self,
        head: NodeId,
        args: impl IntoIterator<Item = NodeId>,
    ) -> ReplResult<NodeId> {
        // check out that the given node ids exist
        // while checking the references, get the spans
        let head_expr = self.get_node_result(head)?;
        let tail = args.into_iter().collect::<Vec<NodeId>>();
        let mut max_span = head_expr.span.end;
        tail.iter()
            .map(|node| {
                let expr = self.get_node_result(*node)?;
                max_span = std::cmp::max(max_span, expr.span.end);
                Ok(expr)
            })
            .collect::<ReplResult<Vec<&Expression>>>()?;
        let id = NodeId(self.nodes.len());
        let expr = Expression {
            span: Span::new(head_expr.span.begin, max_span),
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

    fn get_node_result(&self, id: NodeId) -> ReplResult<&Expression> {
        self.get_node(id).ok_or(ReplError::InternalError(
            format!("Unknown node id {}", id),
            Position::Unknown,
        ))
    }

    fn add_root(&mut self, id: NodeId) -> ReplResult<()> {
        self.get_node_result(id)?;
        self.roots.push(id);
        Ok(())
    }

    fn get_roots(&self) -> Vec<NodeId> {
        self.roots.clone()
    }
}

// Recursive ast building function. Each invocation covers one level
// of depth, successive recurvise calls increase depth.
fn build_ast<'a, I: Iterator<Item = &'a Token>>(
    tit: &mut I,
    ast: &mut AST,
    depth: usize,
) -> ReplResult<Vec<NodeId>> {
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
                    Err(ReplError::ParsingError(
                        format!("Empty function application {}", token.content),
                        Position::from(token.span),
                    ))
                } else {
                    // since we know there's some content, we can
                    // assume there's an element 0, and a last element.
                    let mut args = content.iter().cloned();
                    args.next();
                    ast.new_application(content[0], args)
                }
            }
            TokenData::ClosedParen => match depth {
                0 => Err(ReplError::ParsingError(
                    format!("Unbalanced parentheses. Unexpected `)`",),
                    Position::from(token.span),
                )),
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
            .collect::<ReplResult<Vec<()>>>();
        Ok(forest)
    } else {
        Err(ReplError::ParsingError(
            format!("Expected {} closing parentheses at end of input.", depth),
            Position::Unknown,
        ))
    }
}

pub fn parse_tokens(tokens: Vec<Token>) -> ReplResult<AST> {
    let mut tit = tokens.iter();
    let mut ast: AST = AST::new();

    build_ast(&mut tit, &mut ast, 0)?;
    Ok(ast)
}

#[cfg(test)]
mod ast_tests {
    use super::*;

    #[test]
    fn insert_an_expression() {
        let mut ast = AST::new();
        let expr = ExpressionData::Int(1);
        let id = ast.new_expression(Span::new(0, 0), expr);
        assert!(ast.get_node(id).is_some());
    }

    #[test]
    fn insert_application_without_args() {
        let mut ast = AST::new();
        let expr = ExpressionData::Symbol("foo".to_string());
        let id = ast.new_expression(Span::new(0, 1), expr);
        let ap = ast.new_application(id, vec![]).unwrap();
        let ap_expr = ast.get_node(ap).unwrap();
        assert_eq!(ap_expr.span, Span::new(0, 1));

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
        let head_id = ast.new_expression(Span::new(0, 2), expr);
        let args_1 = ast.new_expression(Span::new(3, 5), expr_1);
        let args_2 = ast.new_expression(Span::new(6, 8), expr_2);

        let ap = ast.new_application(head_id, vec![args_1, args_2]).unwrap();
        let ap_expr = ast.get_node(ap).unwrap();

        assert_eq!(ap_expr.span, Span::new(0, 8));

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
        let head = ast.new_expression(Span::new(0, 0), expr);
        let result = ast.new_application(head, vec![NodeId(99)]);
        assert!(result.is_err());
    }

    #[test]
    fn add_root_nodes() {
        let mut ast = AST::new();
        let expr = ExpressionData::Symbol("foo".to_string());
        let head = ast.new_expression(Span::new(0, 0), expr);
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
