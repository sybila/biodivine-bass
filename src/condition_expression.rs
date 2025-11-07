use crate::statement::Statement;
use std::sync::Arc;

/// Represents a single Boolean expression over [`Statement`] references. It can be parsed
/// and written into the `.adf` text format.
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct ConditionExpression(Arc<ConditionExpressionNode>);

/// Internal enum data structure of [`ConditionExpression`].
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
enum ConditionExpressionNode {
    Constant(bool),
    Statement(Statement),
    Negation(ConditionExpression),
    And(Vec<ConditionExpression>),
    Or(Vec<ConditionExpression>),
    Implication(ConditionExpression, ConditionExpression),
    Equivalence(ConditionExpression, ConditionExpression),
    ExclusiveOr(ConditionExpression, ConditionExpression),
}

impl ConditionExpression {
    // Constructors

    /// Create a constant boolean condition.
    pub fn constant(value: bool) -> Self {
        ConditionExpression(Arc::new(ConditionExpressionNode::Constant(value)))
    }

    /// Create a condition referencing a statement.
    pub fn statement(statement: Statement) -> Self {
        ConditionExpression(Arc::new(ConditionExpressionNode::Statement(statement)))
    }

    /// Create a negation condition.
    pub fn negation(operand: ConditionExpression) -> Self {
        ConditionExpression(Arc::new(ConditionExpressionNode::Negation(operand)))
    }

    /// Create a logical AND condition.
    pub fn and(operands: &[ConditionExpression]) -> Self {
        ConditionExpression(Arc::new(ConditionExpressionNode::And(operands.to_vec())))
    }

    /// Create a logical OR condition.
    pub fn or(operands: &[ConditionExpression]) -> Self {
        ConditionExpression(Arc::new(ConditionExpressionNode::Or(operands.to_vec())))
    }

    /// Create an implication condition (left -> right).
    pub fn implication(left: ConditionExpression, right: ConditionExpression) -> Self {
        ConditionExpression(Arc::new(ConditionExpressionNode::Implication(left, right)))
    }

    /// Create an equivalence condition (left <-> right).
    pub fn equivalence(left: ConditionExpression, right: ConditionExpression) -> Self {
        ConditionExpression(Arc::new(ConditionExpressionNode::Equivalence(left, right)))
    }

    /// Create an exclusive OR condition (left XOR right).
    pub fn exclusive_or(left: ConditionExpression, right: ConditionExpression) -> Self {
        ConditionExpression(Arc::new(ConditionExpressionNode::ExclusiveOr(left, right)))
    }

    // Type checking methods

    /// Check if this condition is a constant.
    pub fn is_constant(&self) -> bool {
        matches!(*self.0, ConditionExpressionNode::Constant(_))
    }

    /// Check if this condition is a statement reference.
    pub fn is_statement(&self) -> bool {
        matches!(*self.0, ConditionExpressionNode::Statement(_))
    }

    /// Check if this condition is a negation.
    pub fn is_negation(&self) -> bool {
        matches!(*self.0, ConditionExpressionNode::Negation(_))
    }

    /// Check if this condition is an AND.
    pub fn is_and(&self) -> bool {
        matches!(*self.0, ConditionExpressionNode::And(_))
    }

    /// Check if this condition is an OR.
    pub fn is_or(&self) -> bool {
        matches!(*self.0, ConditionExpressionNode::Or(_))
    }

    /// Check if this condition is an implication.
    pub fn is_implication(&self) -> bool {
        matches!(*self.0, ConditionExpressionNode::Implication(_, _))
    }

    /// Check if this condition is an equivalence.
    pub fn is_equivalence(&self) -> bool {
        matches!(*self.0, ConditionExpressionNode::Equivalence(_, _))
    }

    /// Check if this condition is an exclusive OR.
    pub fn is_exclusive_or(&self) -> bool {
        matches!(*self.0, ConditionExpressionNode::ExclusiveOr(_, _))
    }

    // Access methods

    /// Get the boolean value if this is a constant condition.
    pub fn as_constant(&self) -> Option<bool> {
        match *self.0 {
            ConditionExpressionNode::Constant(value) => Some(value),
            _ => None,
        }
    }

    /// Get the statement if this is a statement condition.
    pub fn as_statement(&self) -> Option<Statement> {
        match *self.0 {
            ConditionExpressionNode::Statement(statement) => Some(statement),
            _ => None,
        }
    }

    /// Get the operand if this is a negation condition.
    pub fn as_negation(&self) -> Option<&ConditionExpression> {
        match &*self.0 {
            ConditionExpressionNode::Negation(operand) => Some(operand),
            _ => None,
        }
    }

    /// Get the operands if this is an AND condition.
    pub fn as_and(&self) -> Option<&[ConditionExpression]> {
        match &*self.0 {
            ConditionExpressionNode::And(operands) => Some(operands),
            _ => None,
        }
    }

    /// Get the operands if this is an OR condition.
    pub fn as_or(&self) -> Option<&[ConditionExpression]> {
        match &*self.0 {
            ConditionExpressionNode::Or(operands) => Some(operands),
            _ => None,
        }
    }

    /// Get the left and right operands if this is an implication condition.
    pub fn as_implication(&self) -> Option<(&ConditionExpression, &ConditionExpression)> {
        match &*self.0 {
            ConditionExpressionNode::Implication(left, right) => Some((left, right)),
            _ => None,
        }
    }

    /// Get the left and right operands if this is an equivalence condition.
    pub fn as_equivalence(&self) -> Option<(&ConditionExpression, &ConditionExpression)> {
        match &*self.0 {
            ConditionExpressionNode::Equivalence(left, right) => Some((left, right)),
            _ => None,
        }
    }

    /// Get the left and right operands if this is an exclusive OR condition.
    pub fn as_exclusive_or(&self) -> Option<(&ConditionExpression, &ConditionExpression)> {
        match &*self.0 {
            ConditionExpressionNode::ExclusiveOr(left, right) => Some((left, right)),
            _ => None,
        }
    }
}

impl ConditionExpression {
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
    pub fn parse(input: &str) -> Result<Self, String> {
        crate::condition_expression_parser::parse(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constant_constructor_and_accessors() {
        let cond_true = ConditionExpression::constant(true);
        assert!(cond_true.is_constant());
        assert_eq!(cond_true.as_constant(), Some(true));
        assert!(!cond_true.is_statement());
        assert!(!cond_true.is_and());

        let cond_false = ConditionExpression::constant(false);
        assert!(cond_false.is_constant());
        assert_eq!(cond_false.as_constant(), Some(false));
    }

    #[test]
    fn test_statement_constructor_and_accessors() {
        let stmt = Statement::from(42);
        let cond = ConditionExpression::statement(stmt);

        assert!(cond.is_statement());
        assert_eq!(cond.as_statement(), Some(stmt));
        assert!(!cond.is_constant());
        assert!(!cond.is_and());
    }

    #[test]
    fn test_negation_constructor_and_accessors() {
        let inner = ConditionExpression::statement(Statement::from(5));
        let cond = ConditionExpression::negation(inner.clone());

        assert!(cond.is_negation());
        assert!(cond.as_negation().is_some());
        let operand = cond.as_negation().unwrap();
        assert!(operand.is_statement());
        assert_eq!(operand.as_statement(), Some(Statement::from(5)));
        assert!(!cond.is_constant());
        assert!(!cond.is_and());
    }

    #[test]
    fn test_and_constructor_and_accessors() {
        let operands = vec![
            ConditionExpression::constant(true),
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::constant(false),
        ];
        let cond = ConditionExpression::and(&operands);

        assert!(cond.is_and());
        assert!(cond.as_and().is_some());
        assert_eq!(cond.as_and().unwrap().len(), 3);
        assert!(!cond.is_or());
        assert!(!cond.is_constant());
    }

    #[test]
    fn test_or_constructor_and_accessors() {
        let operands = vec![
            ConditionExpression::constant(true),
            ConditionExpression::statement(Statement::from(2)),
        ];
        let cond = ConditionExpression::or(&operands);

        assert!(cond.is_or());
        assert!(cond.as_or().is_some());
        assert_eq!(cond.as_or().unwrap().len(), 2);
        assert!(!cond.is_and());
        assert!(!cond.is_constant());
    }

    #[test]
    fn test_implication_constructor_and_accessors() {
        let left = ConditionExpression::constant(true);
        let right = ConditionExpression::statement(Statement::from(5));
        let cond = ConditionExpression::implication(left.clone(), right.clone());

        assert!(cond.is_implication());
        assert!(cond.as_implication().is_some());

        let (l, r) = cond.as_implication().unwrap();
        assert!(l.is_constant());
        assert!(r.is_statement());
        assert!(!cond.is_equivalence());
        assert!(!cond.is_exclusive_or());
    }

    #[test]
    fn test_equivalence_constructor_and_accessors() {
        let left = ConditionExpression::statement(Statement::from(10));
        let right = ConditionExpression::statement(Statement::from(20));
        let cond = ConditionExpression::equivalence(left.clone(), right.clone());

        assert!(cond.is_equivalence());
        assert!(cond.as_equivalence().is_some());

        let (l, r) = cond.as_equivalence().unwrap();
        assert!(l.is_statement());
        assert!(r.is_statement());
        assert!(!cond.is_implication());
        assert!(!cond.is_exclusive_or());
    }

    #[test]
    fn test_exclusive_or_constructor_and_accessors() {
        let left = ConditionExpression::constant(false);
        let right = ConditionExpression::statement(Statement::from(3));
        let cond = ConditionExpression::exclusive_or(left.clone(), right.clone());

        assert!(cond.is_exclusive_or());
        assert!(cond.as_exclusive_or().is_some());

        let (l, r) = cond.as_exclusive_or().unwrap();
        assert!(l.is_constant());
        assert!(r.is_statement());
        assert!(!cond.is_implication());
        assert!(!cond.is_equivalence());
    }

    #[test]
    fn test_nested_expressions() {
        // Create: (s1 AND s2) OR (s3 -> s4)
        let s1 = ConditionExpression::statement(Statement::from(1));
        let s2 = ConditionExpression::statement(Statement::from(2));
        let s3 = ConditionExpression::statement(Statement::from(3));
        let s4 = ConditionExpression::statement(Statement::from(4));

        let and_expr = ConditionExpression::and(&[s1, s2]);
        let impl_expr = ConditionExpression::implication(s3, s4);
        let or_expr = ConditionExpression::or(&[and_expr.clone(), impl_expr.clone()]);

        assert!(or_expr.is_or());
        let operands = or_expr.as_or().unwrap();
        assert_eq!(operands.len(), 2);
        assert!(operands[0].is_and());
        assert!(operands[1].is_implication());
    }

    #[test]
    fn test_cloning() {
        let cond1 = ConditionExpression::statement(Statement::from(100));
        let cond2 = cond1.clone();

        assert!(cond1.is_statement());
        assert!(cond2.is_statement());
        assert_eq!(cond1.as_statement(), cond2.as_statement());
    }

    #[test]
    fn test_none_returns_for_wrong_type() {
        let cond = ConditionExpression::constant(true);

        assert!(cond.as_statement().is_none());
        assert!(cond.as_negation().is_none());
        assert!(cond.as_and().is_none());
        assert!(cond.as_or().is_none());
        assert!(cond.as_implication().is_none());
        assert!(cond.as_equivalence().is_none());
        assert!(cond.as_exclusive_or().is_none());
    }
}
