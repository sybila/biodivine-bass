use crate::condition_expression::ConditionExpression;
use crate::statement::Statement;

/// Tokens for parsing condition expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Number(usize),
    Identifier(String),
    LeftParen,
    RightParen,
    Comma,
}

/// Tokenize a condition expression string.
fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();

    while let Some(&ch) = chars.peek() {
        match ch {
            ch if ch.is_whitespace() => {
                chars.next();
            }
            '(' => {
                tokens.push(Token::LeftParen);
                chars.next();
            }
            ')' => {
                tokens.push(Token::RightParen);
                chars.next();
            }
            ',' => {
                tokens.push(Token::Comma);
                chars.next();
            }
            '0'..='9' => {
                let mut num_str = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch.is_ascii_digit() {
                        num_str.push(ch);
                        chars.next();
                    } else {
                        break;
                    }
                }
                let num = num_str
                    .parse::<usize>()
                    .map_err(|_| format!("Invalid number: {}", num_str))?;
                tokens.push(Token::Number(num));
            }
            'a'..='z' | 'A'..='Z' | '_' => {
                let mut ident = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch.is_alphanumeric() || ch == '_' {
                        ident.push(ch);
                        chars.next();
                    } else {
                        break;
                    }
                }
                tokens.push(Token::Identifier(ident));
            }
            _ => {
                return Err(format!("Unexpected character: {}", ch));
            }
        }
    }

    Ok(tokens)
}

/// Parser for condition expressions.
struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens,
            position: 0,
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }

    fn next(&mut self) -> Option<Token> {
        if self.position < self.tokens.len() {
            let token = self.tokens[self.position].clone();
            self.position += 1;
            Some(token)
        } else {
            None
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), String> {
        match self.next() {
            Some(token) if token == expected => Ok(()),
            Some(token) => Err(format!("Expected {:?}, found {:?}", expected, token)),
            None => Err(format!("Expected {:?}, found end of input", expected)),
        }
    }

    fn parse_expression(&mut self) -> Result<ConditionExpression, String> {
        match self.peek() {
            Some(Token::Number(n)) => {
                let n = *n;
                self.next();
                Ok(ConditionExpression::statement(Statement::from(n)))
            }
            Some(Token::Identifier(ident)) => {
                let ident = ident.clone();
                self.next();

                match ident.as_str() {
                    "c" => {
                        // Constant: c(v) or c(f)
                        self.expect(Token::LeftParen)?;
                        match self.next() {
                            Some(Token::Identifier(val)) if val == "v" => {
                                self.expect(Token::RightParen)?;
                                Ok(ConditionExpression::constant(true))
                            }
                            Some(Token::Identifier(val)) if val == "f" => {
                                self.expect(Token::RightParen)?;
                                Ok(ConditionExpression::constant(false))
                            }
                            Some(token) => Err(format!(
                                "Expected 'v' or 'f' in constant, found {:?}",
                                token
                            )),
                            None => Err("Unexpected end of input in constant".to_string()),
                        }
                    }
                    "neg" => {
                        // Negation: neg(expr)
                        self.expect(Token::LeftParen)?;
                        let expr = self.parse_expression()?;
                        self.expect(Token::RightParen)?;
                        Ok(ConditionExpression::negation(expr))
                    }
                    "and" => {
                        // AND: and(expr1, expr2, ...)
                        self.expect(Token::LeftParen)?;
                        let operands = self.parse_operands()?;
                        self.expect(Token::RightParen)?;
                        Ok(ConditionExpression::and(&operands))
                    }
                    "or" => {
                        // OR: or(expr1, expr2, ...)
                        self.expect(Token::LeftParen)?;
                        let operands = self.parse_operands()?;
                        self.expect(Token::RightParen)?;
                        Ok(ConditionExpression::or(&operands))
                    }
                    "xor" => {
                        // XOR: xor(expr1, expr2)
                        self.expect(Token::LeftParen)?;
                        let left = self.parse_expression()?;
                        self.expect(Token::Comma)?;
                        let right = self.parse_expression()?;
                        self.expect(Token::RightParen)?;
                        Ok(ConditionExpression::exclusive_or(left, right))
                    }
                    "imp" => {
                        // Implication: imp(expr1, expr2)
                        self.expect(Token::LeftParen)?;
                        let left = self.parse_expression()?;
                        self.expect(Token::Comma)?;
                        let right = self.parse_expression()?;
                        self.expect(Token::RightParen)?;
                        Ok(ConditionExpression::implication(left, right))
                    }
                    "iff" => {
                        // Equivalence: iff(expr1, expr2)
                        self.expect(Token::LeftParen)?;
                        let left = self.parse_expression()?;
                        self.expect(Token::Comma)?;
                        let right = self.parse_expression()?;
                        self.expect(Token::RightParen)?;
                        Ok(ConditionExpression::equivalence(left, right))
                    }
                    _ => Err(format!("Unknown identifier: {}", ident)),
                }
            }
            Some(token) => Err(format!("Unexpected token: {:?}", token)),
            None => Err("Unexpected end of input".to_string()),
        }
    }

    fn parse_operands(&mut self) -> Result<Vec<ConditionExpression>, String> {
        let mut operands = Vec::new();

        // Parse first operand
        operands.push(self.parse_expression()?);

        // Parse remaining operands
        while let Some(Token::Comma) = self.peek() {
            self.next(); // consume comma
            operands.push(self.parse_expression()?);
        }

        Ok(operands)
    }
}

/// Parse a condition expression from a string.
///
/// Supports the following syntax:
/// - `42` - Statement reference
/// - `c(v)` - Constant true (verum)
/// - `c(f)` - Constant false (falsum)
/// - `neg(expr)` - Negation
/// - `and(expr1, expr2, ...)` - Logical AND
/// - `or(expr1, expr2, ...)` - Logical OR
/// - `xor(expr1, expr2)` - Exclusive OR
/// - `imp(expr1, expr2)` - Implication
/// - `iff(expr1, expr2)` - Equivalence
pub fn parse(input: &str) -> Result<ConditionExpression, String> {
    let tokens = tokenize(input)?;
    let mut parser = Parser::new(tokens);
    let expr = parser.parse_expression()?;

    // Ensure we've consumed all tokens
    if parser.position < parser.tokens.len() {
        return Err(format!(
            "Unexpected tokens after expression: {:?}",
            &parser.tokens[parser.position..]
        ));
    }

    Ok(expr)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tokenizer tests

    #[test]
    fn test_tokenize_number() {
        let tokens = tokenize("42").unwrap();
        assert_eq!(tokens, vec![Token::Number(42)]);
    }

    #[test]
    fn test_tokenize_identifier() {
        let tokens = tokenize("neg").unwrap();
        assert_eq!(tokens, vec![Token::Identifier("neg".to_string())]);
    }

    #[test]
    fn test_tokenize_parentheses() {
        let tokens = tokenize("(())").unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::LeftParen,
                Token::LeftParen,
                Token::RightParen,
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn test_tokenize_comma() {
        let tokens = tokenize(",").unwrap();
        assert_eq!(tokens, vec![Token::Comma]);
    }

    #[test]
    fn test_tokenize_complex_expression() {
        let tokens = tokenize("and(neg(1), 42)").unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::Identifier("and".to_string()),
                Token::LeftParen,
                Token::Identifier("neg".to_string()),
                Token::LeftParen,
                Token::Number(1),
                Token::RightParen,
                Token::Comma,
                Token::Number(42),
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn test_tokenize_with_whitespace() {
        let tokens = tokenize("  and  ( 1 ,  2 )  ").unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::Identifier("and".to_string()),
                Token::LeftParen,
                Token::Number(1),
                Token::Comma,
                Token::Number(2),
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn test_tokenize_invalid_character() {
        let result = tokenize("and(1@2)");
        assert!(result.is_err());
    }

    // Parser tests

    #[test]
    fn test_parse_statement_number() {
        let expr = parse("42").unwrap();
        assert!(expr.is_statement());
        assert_eq!(expr.as_statement(), Some(Statement::from(42)));
    }

    #[test]
    fn test_parse_constant_true() {
        let expr = parse("c(v)").unwrap();
        assert!(expr.is_constant());
        assert_eq!(expr.as_constant(), Some(true));
    }

    #[test]
    fn test_parse_constant_false() {
        let expr = parse("c(f)").unwrap();
        assert!(expr.is_constant());
        assert_eq!(expr.as_constant(), Some(false));
    }

    #[test]
    fn test_parse_negation() {
        let expr = parse("neg(42)").unwrap();
        assert!(expr.is_negation());
        let operand = expr.as_negation().unwrap();
        assert!(operand.is_statement());
        assert_eq!(operand.as_statement(), Some(Statement::from(42)));
    }

    #[test]
    fn test_parse_and_two_operands() {
        let expr = parse("and(1, 2)").unwrap();
        assert!(expr.is_and());
        let operands = expr.as_and().unwrap();
        assert_eq!(operands.len(), 2);
        assert!(operands[0].is_statement());
        assert!(operands[1].is_statement());
    }

    #[test]
    fn test_parse_and_three_operands() {
        let expr = parse("and(1, 2, 3)").unwrap();
        assert!(expr.is_and());
        let operands = expr.as_and().unwrap();
        assert_eq!(operands.len(), 3);
    }

    #[test]
    fn test_parse_or_two_operands() {
        let expr = parse("or(10, 20)").unwrap();
        assert!(expr.is_or());
        let operands = expr.as_or().unwrap();
        assert_eq!(operands.len(), 2);
    }

    #[test]
    fn test_parse_xor() {
        let expr = parse("xor(5, 6)").unwrap();
        assert!(expr.is_exclusive_or());
        let (left, right) = expr.as_exclusive_or().unwrap();
        assert!(left.is_statement());
        assert!(right.is_statement());
    }

    #[test]
    fn test_parse_implication() {
        let expr = parse("imp(1, 2)").unwrap();
        assert!(expr.is_implication());
        let (left, right) = expr.as_implication().unwrap();
        assert!(left.is_statement());
        assert!(right.is_statement());
    }

    #[test]
    fn test_parse_equivalence() {
        let expr = parse("iff(3, 4)").unwrap();
        assert!(expr.is_equivalence());
        let (left, right) = expr.as_equivalence().unwrap();
        assert!(left.is_statement());
        assert!(right.is_statement());
    }

    #[test]
    fn test_parse_nested_expression() {
        // or(neg(1), 7)
        let expr = parse("or(neg(1), 7)").unwrap();
        assert!(expr.is_or());
        let operands = expr.as_or().unwrap();
        assert_eq!(operands.len(), 2);
        assert!(operands[0].is_negation());
        assert!(operands[1].is_statement());
    }

    #[test]
    fn test_parse_deeply_nested_expression() {
        // and(or(7, neg(6)), 2)
        let expr = parse("and(or(7, neg(6)), 2)").unwrap();
        assert!(expr.is_and());
        let operands = expr.as_and().unwrap();
        assert_eq!(operands.len(), 2);

        assert!(operands[0].is_or());
        let or_operands = operands[0].as_or().unwrap();
        assert_eq!(or_operands.len(), 2);
        assert!(or_operands[0].is_statement());
        assert!(or_operands[1].is_negation());

        assert!(operands[1].is_statement());
    }

    #[test]
    fn test_parse_complex_from_test_file() {
        // From test file: and(or(7,neg(6)),2)
        let expr = parse("and(or(7,neg(6)),2)").unwrap();
        assert!(expr.is_and());
    }

    #[test]
    fn test_parse_with_whitespace() {
        let expr = parse("  and  ( 1 ,  2 )  ").unwrap();
        assert!(expr.is_and());
        let operands = expr.as_and().unwrap();
        assert_eq!(operands.len(), 2);
    }

    #[test]
    fn test_parse_empty_string_fails() {
        let result = parse("");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_unknown_identifier_fails() {
        let result = parse("unknown(1)");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_incomplete_expression_fails() {
        let result = parse("and(1");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_extra_tokens_fails() {
        let result = parse("1 2");
        assert!(result.is_err());
    }

    // Test parsing real examples from test files

    #[test]
    fn test_parse_real_example_1() {
        // ac(8,or(neg(1),7))
        let expr = parse("or(neg(1),7)").unwrap();
        assert!(expr.is_or());
        let operands = expr.as_or().unwrap();
        assert_eq!(operands.len(), 2);
        assert!(operands[0].is_negation());
        assert!(operands[1].is_statement());
    }

    #[test]
    fn test_parse_real_example_2() {
        // ac(3,and(or(7,neg(6)),2))
        let expr = parse("and(or(7,neg(6)),2)").unwrap();
        assert!(expr.is_and());
    }

    #[test]
    fn test_parse_real_example_3() {
        // ac(10,and(neg(2),6))
        let expr = parse("and(neg(2),6)").unwrap();
        assert!(expr.is_and());
        let operands = expr.as_and().unwrap();
        assert_eq!(operands.len(), 2);
    }

    #[test]
    fn test_parse_real_example_4() {
        // ac(2,and(neg(9),neg(6)))
        let expr = parse("and(neg(9),neg(6))").unwrap();
        assert!(expr.is_and());
        let operands = expr.as_and().unwrap();
        assert_eq!(operands.len(), 2);
        assert!(operands[0].is_negation());
        assert!(operands[1].is_negation());
    }

    #[test]
    fn test_parse_real_example_5() {
        // Very complex nested example from test files
        let expr = parse(
            "and(and(and(or(and(or(4,neg(1)),neg(and(4,neg(1)))),6),neg(and(and(or(4,neg(1)),neg(and(4,neg(1)))),6))),7),5)",
        )
        .unwrap();
        assert!(expr.is_and());
    }

    #[test]
    fn test_parse_constant_with_wrong_token() {
        // Test: c(x) where x is not v or f
        let result = parse("c(x)");
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .contains("Expected 'v' or 'f' in constant")
        );
    }

    #[test]
    fn test_parse_constant_with_number() {
        // Test: c(42) - number instead of v/f
        let result = parse("c(42)");
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .contains("Expected 'v' or 'f' in constant")
        );
    }

    #[test]
    fn test_parse_constant_incomplete() {
        // Test: c( with no closing
        let result = parse("c(");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unexpected end of input"));
    }

    #[test]
    fn test_parse_expression_starting_with_unexpected_token() {
        // Test expression starting with a token that's not a number or identifier
        let tokens = vec![Token::LeftParen, Token::Number(1), Token::RightParen];
        let mut parser = Parser::new(tokens);
        let result = parser.parse_expression();
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unexpected token"));
    }

    #[test]
    fn test_parse_wrong_closing_paren() {
        // Test: and(1,2] - wrong bracket type
        let result = parse("and(1,2");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Expected"));
    }

    #[test]
    fn test_expect_method_wrong_token() {
        // Test the expect method when it gets the wrong token
        let tokens = vec![Token::LeftParen, Token::Number(1)];
        let mut parser = Parser::new(tokens);
        parser.next(); // consume LeftParen
        let result = parser.expect(Token::RightParen);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.contains("Expected"));
        assert!(err.contains("found"));
    }
}
