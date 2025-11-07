use crate::condition_expression::ConditionExpression;
use std::fmt::Write;

/// Format a condition expression to a string.
///
/// Uses the following syntax:
/// - `42` - Statement reference
/// - `c(v)` - Constant true (verum)
/// - `c(f)` - Constant false (falsum)
/// - `neg(expr)` - Negation
/// - `and(expr1, expr2, ...)` - Logical AND
/// - `or(expr1, expr2, ...)` - Logical OR
/// - `xor(expr1, expr2)` - Exclusive OR
/// - `imp(expr1, expr2)` - Implication
/// - `iff(expr1, expr2)` - Equivalence
pub fn write(expr: &ConditionExpression) -> String {
    let mut result = String::new();
    write_to(&mut result, expr).expect("Writing to String should never fail");
    result
}

/// Write a condition expression to a formatter.
fn write_to(f: &mut impl Write, expr: &ConditionExpression) -> std::fmt::Result {
    if let Some(value) = expr.as_constant() {
        // Constant: c(v) or c(f)
        if value {
            write!(f, "c(v)")
        } else {
            write!(f, "c(f)")
        }
    } else if let Some(statement) = expr.as_statement() {
        // Statement reference: just the number
        write!(f, "{}", usize::from(statement))
    } else if let Some(operand) = expr.as_negation() {
        // Negation: neg(expr)
        write!(f, "neg(")?;
        write_to(f, operand)?;
        write!(f, ")")
    } else if let Some(operands) = expr.as_and() {
        // AND: and(expr1, expr2, ...)
        write!(f, "and(")?;
        write_operands(f, operands)?;
        write!(f, ")")
    } else if let Some(operands) = expr.as_or() {
        // OR: or(expr1, expr2, ...)
        write!(f, "or(")?;
        write_operands(f, operands)?;
        write!(f, ")")
    } else if let Some((left, right)) = expr.as_exclusive_or() {
        // XOR: xor(left, right)
        write!(f, "xor(")?;
        write_to(f, left)?;
        write!(f, ",")?;
        write_to(f, right)?;
        write!(f, ")")
    } else if let Some((left, right)) = expr.as_implication() {
        // Implication: imp(left, right)
        write!(f, "imp(")?;
        write_to(f, left)?;
        write!(f, ",")?;
        write_to(f, right)?;
        write!(f, ")")
    } else if let Some((left, right)) = expr.as_equivalence() {
        // Equivalence: iff(left, right)
        write!(f, "iff(")?;
        write_to(f, left)?;
        write!(f, ",")?;
        write_to(f, right)?;
        write!(f, ")")
    } else {
        // This should never happen if all variants are covered
        unreachable!("All ConditionExpression variants should be handled")
    }
}

/// Write multiple operands separated by commas.
fn write_operands(f: &mut impl Write, operands: &[ConditionExpression]) -> std::fmt::Result {
    for (i, operand) in operands.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        write_to(f, operand)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::statement::Statement;

    #[test]
    fn test_write_constant_true() {
        let expr = ConditionExpression::constant(true);
        assert_eq!(write(&expr), "c(v)");
    }

    #[test]
    fn test_write_constant_false() {
        let expr = ConditionExpression::constant(false);
        assert_eq!(write(&expr), "c(f)");
    }

    #[test]
    fn test_write_statement() {
        let expr = ConditionExpression::statement(Statement::from(42));
        assert_eq!(write(&expr), "42");
    }

    #[test]
    fn test_write_negation() {
        let expr =
            ConditionExpression::negation(ConditionExpression::statement(Statement::from(5)));
        assert_eq!(write(&expr), "neg(5)");
    }

    #[test]
    fn test_write_and_two_operands() {
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
        ]);
        assert_eq!(write(&expr), "and(1,2)");
    }

    #[test]
    fn test_write_and_three_operands() {
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
            ConditionExpression::statement(Statement::from(3)),
        ]);
        assert_eq!(write(&expr), "and(1,2,3)");
    }

    #[test]
    fn test_write_or_two_operands() {
        let expr = ConditionExpression::or(&[
            ConditionExpression::statement(Statement::from(10)),
            ConditionExpression::statement(Statement::from(20)),
        ]);
        assert_eq!(write(&expr), "or(10,20)");
    }

    #[test]
    fn test_write_xor() {
        let expr = ConditionExpression::exclusive_or(
            ConditionExpression::statement(Statement::from(5)),
            ConditionExpression::statement(Statement::from(6)),
        );
        assert_eq!(write(&expr), "xor(5,6)");
    }

    #[test]
    fn test_write_implication() {
        let expr = ConditionExpression::implication(
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
        );
        assert_eq!(write(&expr), "imp(1,2)");
    }

    #[test]
    fn test_write_equivalence() {
        let expr = ConditionExpression::equivalence(
            ConditionExpression::statement(Statement::from(3)),
            ConditionExpression::statement(Statement::from(4)),
        );
        assert_eq!(write(&expr), "iff(3,4)");
    }

    #[test]
    fn test_write_nested_expression() {
        // or(neg(1), 7)
        let expr = ConditionExpression::or(&[
            ConditionExpression::negation(ConditionExpression::statement(Statement::from(1))),
            ConditionExpression::statement(Statement::from(7)),
        ]);
        assert_eq!(write(&expr), "or(neg(1),7)");
    }

    #[test]
    fn test_write_deeply_nested_expression() {
        // and(or(7, neg(6)), 2)
        let expr = ConditionExpression::and(&[
            ConditionExpression::or(&[
                ConditionExpression::statement(Statement::from(7)),
                ConditionExpression::negation(ConditionExpression::statement(Statement::from(6))),
            ]),
            ConditionExpression::statement(Statement::from(2)),
        ]);
        assert_eq!(write(&expr), "and(or(7,neg(6)),2)");
    }

    #[test]
    fn test_write_complex_expression() {
        // and(neg(2), 6)
        let expr = ConditionExpression::and(&[
            ConditionExpression::negation(ConditionExpression::statement(Statement::from(2))),
            ConditionExpression::statement(Statement::from(6)),
        ]);
        assert_eq!(write(&expr), "and(neg(2),6)");
    }

    #[test]
    fn test_write_multiple_negations() {
        // and(neg(9), neg(6))
        let expr = ConditionExpression::and(&[
            ConditionExpression::negation(ConditionExpression::statement(Statement::from(9))),
            ConditionExpression::negation(ConditionExpression::statement(Statement::from(6))),
        ]);
        assert_eq!(write(&expr), "and(neg(9),neg(6))");
    }

    #[test]
    fn test_write_very_complex_expression() {
        // From test files: and(and(and(9,neg(7)),or(neg(10),neg(1))),or(4,6))
        let expr = ConditionExpression::and(&[
            ConditionExpression::and(&[
                ConditionExpression::and(&[
                    ConditionExpression::statement(Statement::from(9)),
                    ConditionExpression::negation(ConditionExpression::statement(Statement::from(
                        7,
                    ))),
                ]),
                ConditionExpression::or(&[
                    ConditionExpression::negation(ConditionExpression::statement(Statement::from(
                        10,
                    ))),
                    ConditionExpression::negation(ConditionExpression::statement(Statement::from(
                        1,
                    ))),
                ]),
            ]),
            ConditionExpression::or(&[
                ConditionExpression::statement(Statement::from(4)),
                ConditionExpression::statement(Statement::from(6)),
            ]),
        ]);
        assert_eq!(
            write(&expr),
            "and(and(and(9,neg(7)),or(neg(10),neg(1))),or(4,6))"
        );
    }

    // Round-trip tests: parse -> write -> parse should give equivalent expressions

    #[test]
    fn test_roundtrip_simple_statement() {
        let input = "42";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_statement());
        assert_eq!(reparsed.as_statement(), Some(Statement::from(42)));
    }

    #[test]
    fn test_roundtrip_constant_true() {
        let input = "c(v)";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_constant());
        assert_eq!(reparsed.as_constant(), Some(true));
    }

    #[test]
    fn test_roundtrip_constant_false() {
        let input = "c(f)";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_constant());
        assert_eq!(reparsed.as_constant(), Some(false));
    }

    #[test]
    fn test_roundtrip_negation() {
        let input = "neg(42)";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_negation());
    }

    #[test]
    fn test_roundtrip_and() {
        let input = "and(1,2,3)";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_and());
        assert_eq!(reparsed.as_and().unwrap().len(), 3);
    }

    #[test]
    fn test_roundtrip_or() {
        let input = "or(10,20)";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_or());
    }

    #[test]
    fn test_roundtrip_xor() {
        let input = "xor(5,6)";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_exclusive_or());
    }

    #[test]
    fn test_roundtrip_implication() {
        let input = "imp(1,2)";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_implication());
    }

    #[test]
    fn test_roundtrip_equivalence() {
        let input = "iff(3,4)";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_equivalence());
    }

    #[test]
    fn test_roundtrip_nested_expression() {
        let input = "or(neg(1),7)";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_or());
    }

    #[test]
    fn test_roundtrip_deeply_nested_expression() {
        let input = "and(or(7,neg(6)),2)";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_and());
    }

    #[test]
    fn test_roundtrip_complex_from_test_files() {
        let input = "and(and(and(9,neg(7)),or(neg(10),neg(1))),or(4,6))";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, input);
        assert!(reparsed.is_and());
    }

    #[test]
    fn test_roundtrip_with_whitespace() {
        // Parser removes whitespace, so the written form won't have it
        let input = "and( 1 , 2 )";
        let parsed = ConditionExpression::parse(input).unwrap();
        let written = write(&parsed);
        let reparsed = ConditionExpression::parse(&written).unwrap();

        assert_eq!(written, "and(1,2)");
        assert!(reparsed.is_and());
    }
}
