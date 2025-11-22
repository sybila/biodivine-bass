use crate::statement::Statement;
use std::fmt;
use std::sync::Arc;

/// Represents a single Boolean expression over [`Statement`] references. It can be parsed
/// and written into the `.adf` text format.
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct ConditionExpression(pub(crate) Arc<ConditionExpressionNode>);

/// Internal enum data structure of [`ConditionExpression`].
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum ConditionExpressionNode {
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
    pub fn as_statement(&self) -> Option<&Statement> {
        match &*self.0 {
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
    /// Obtain the underlying [`ConditionExpressionNode`] that stores the expression
    /// type and children.
    pub fn node(&self) -> &ConditionExpressionNode {
        self.0.as_ref()
    }

    /// Parse a condition expression from a string.
    ///
    /// Supports the following syntax:
    /// - `42` or `foo` - Statement reference (numeric or string label)
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

    /// Collect all statement references in this expression.
    /// Returns a sorted vector of all statements referenced in the expression.
    pub fn collect_statements(&self) -> Vec<Statement> {
        use std::collections::BTreeSet;
        let mut statements = BTreeSet::new();
        self.collect_statements_recursive(&mut statements);
        statements.into_iter().collect()
    }

    /// Helper method to recursively collect all statement references.
    fn collect_statements_recursive(&self, statements: &mut std::collections::BTreeSet<Statement>) {
        if let Some(stmt) = self.as_statement() {
            statements.insert(stmt.clone());
        } else if let Some(operand) = self.as_negation() {
            operand.collect_statements_recursive(statements);
        } else if let Some(operands) = self.as_and() {
            for operand in operands {
                operand.collect_statements_recursive(statements);
            }
        } else if let Some(operands) = self.as_or() {
            for operand in operands {
                operand.collect_statements_recursive(statements);
            }
        } else if let Some((left, right)) = self.as_implication() {
            left.collect_statements_recursive(statements);
            right.collect_statements_recursive(statements);
        } else if let Some((left, right)) = self.as_equivalence() {
            left.collect_statements_recursive(statements);
            right.collect_statements_recursive(statements);
        } else if let Some((left, right)) = self.as_exclusive_or() {
            left.collect_statements_recursive(statements);
            right.collect_statements_recursive(statements);
        }
        // Constants don't contain statements
    }

    /// Substitute multiple statements with condition expressions using a map.
    ///
    /// This method recursively traverses the expression tree and replaces every
    /// occurrence of statements in the map with their corresponding replacement expressions.
    /// This is more efficient than calling `substitute` multiple times.
    ///
    /// # Arguments
    ///
    /// * `substitutions` - A map from statements to their replacement expressions
    ///
    /// # Returns
    ///
    /// A new expression with all occurrences of statements in the map replaced.
    ///
    /// # Example
    ///
    /// ```
    /// # use biodivine_adf_solver::{ConditionExpression, Statement};
    /// # use std::collections::BTreeMap;
    /// let s1 = Statement::from(1);
    /// let s2 = Statement::from(2);
    /// let expr = ConditionExpression::and(&[
    ///     ConditionExpression::statement(s1.clone()),
    ///     ConditionExpression::statement(s2.clone()),
    /// ]);
    ///
    /// let mut subs = BTreeMap::new();
    /// subs.insert(s1.clone(), ConditionExpression::constant(true));
    /// subs.insert(s2.clone(), ConditionExpression::constant(false));
    /// let result = expr.substitute_many(&subs);
    ///
    /// // Result should be: and(c(v), c(f))
    /// assert_eq!(result.to_string(), "and(c(v),c(f))");
    /// ```
    pub fn substitute_many(
        &self,
        substitutions: &std::collections::BTreeMap<Statement, ConditionExpression>,
    ) -> Self {
        // Optimization: if map is empty, return self
        if substitutions.is_empty() {
            return self.clone();
        }

        match &*self.0 {
            ConditionExpressionNode::Constant(_) => self.clone(),
            ConditionExpressionNode::Statement(stmt) => substitutions
                .get(stmt)
                .cloned()
                .unwrap_or_else(|| self.clone()),
            ConditionExpressionNode::Negation(operand) => {
                ConditionExpression::negation(operand.substitute_many(substitutions))
            }
            ConditionExpressionNode::And(operands) => {
                let new_operands: Vec<_> = operands
                    .iter()
                    .map(|op| op.substitute_many(substitutions))
                    .collect();
                ConditionExpression::and(&new_operands)
            }
            ConditionExpressionNode::Or(operands) => {
                let new_operands: Vec<_> = operands
                    .iter()
                    .map(|op| op.substitute_many(substitutions))
                    .collect();
                ConditionExpression::or(&new_operands)
            }
            ConditionExpressionNode::Implication(left, right) => ConditionExpression::implication(
                left.substitute_many(substitutions),
                right.substitute_many(substitutions),
            ),
            ConditionExpressionNode::Equivalence(left, right) => ConditionExpression::equivalence(
                left.substitute_many(substitutions),
                right.substitute_many(substitutions),
            ),
            ConditionExpressionNode::ExclusiveOr(left, right) => ConditionExpression::exclusive_or(
                left.substitute_many(substitutions),
                right.substitute_many(substitutions),
            ),
        }
    }

    /// Substitute all occurrences of a statement with a condition expression.
    ///
    /// This method recursively traverses the expression tree and replaces every
    /// occurrence of the given statement with the provided replacement expression.
    ///
    /// # Arguments
    ///
    /// * `statement` - The statement to replace
    /// * `replacement` - The expression to substitute in place of the statement
    ///
    /// # Returns
    ///
    /// A new expression with all occurrences of `statement` replaced by `replacement`.
    ///
    /// # Example
    ///
    /// ```
    /// # use biodivine_adf_solver::{ConditionExpression, Statement};
    /// let s1 = Statement::from(1);
    /// let s2 = Statement::from(2);
    /// let expr = ConditionExpression::and(&[
    ///     ConditionExpression::statement(s1.clone()),
    ///     ConditionExpression::statement(s2.clone()),
    /// ]);
    ///
    /// let replacement = ConditionExpression::negation(
    ///     ConditionExpression::statement(Statement::from(3))
    /// );
    /// let result = expr.substitute(&s1, &replacement);
    ///
    /// // Result should be: and(neg(3), 2)
    /// assert_eq!(result.to_string(), "and(neg(3),2)");
    /// ```
    pub fn substitute(&self, statement: &Statement, replacement: &ConditionExpression) -> Self {
        match &*self.0 {
            ConditionExpressionNode::Constant(_) => self.clone(),
            ConditionExpressionNode::Statement(stmt) => {
                if stmt == statement {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            ConditionExpressionNode::Negation(operand) => {
                ConditionExpression::negation(operand.substitute(statement, replacement))
            }
            ConditionExpressionNode::And(operands) => {
                let new_operands: Vec<_> = operands
                    .iter()
                    .map(|op| op.substitute(statement, replacement))
                    .collect();
                ConditionExpression::and(&new_operands)
            }
            ConditionExpressionNode::Or(operands) => {
                let new_operands: Vec<_> = operands
                    .iter()
                    .map(|op| op.substitute(statement, replacement))
                    .collect();
                ConditionExpression::or(&new_operands)
            }
            ConditionExpressionNode::Implication(left, right) => ConditionExpression::implication(
                left.substitute(statement, replacement),
                right.substitute(statement, replacement),
            ),
            ConditionExpressionNode::Equivalence(left, right) => ConditionExpression::equivalence(
                left.substitute(statement, replacement),
                right.substitute(statement, replacement),
            ),
            ConditionExpressionNode::ExclusiveOr(left, right) => ConditionExpression::exclusive_or(
                left.substitute(statement, replacement),
                right.substitute(statement, replacement),
            ),
        }
    }

    /// Check if this expression contains any non-binary AND or OR operators.
    ///
    /// Returns `true` if the expression contains AND or OR operators with anything
    /// other than exactly 2 operands (0, 1, or 3+ operands).
    ///
    /// This is useful for determining if binarization is necessary.
    ///
    /// # Example
    ///
    /// ```
    /// # use biodivine_adf_solver::{ConditionExpression, Statement};
    /// let s1 = Statement::from(1);
    /// let s2 = Statement::from(2);
    /// let s3 = Statement::from(3);
    ///
    /// // Binary AND
    /// let expr1 = ConditionExpression::and(&[
    ///     ConditionExpression::statement(s1.clone()),
    ///     ConditionExpression::statement(s2.clone()),
    /// ]);
    /// assert!(!expr1.has_non_binary_operators());
    ///
    /// // Ternary AND
    /// let expr2 = ConditionExpression::and(&[
    ///     ConditionExpression::statement(s1),
    ///     ConditionExpression::statement(s2),
    ///     ConditionExpression::statement(s3),
    /// ]);
    /// assert!(expr2.has_non_binary_operators());
    /// ```
    pub fn has_non_binary_operators(&self) -> bool {
        match &*self.0 {
            ConditionExpressionNode::Constant(_) | ConditionExpressionNode::Statement(_) => false,
            ConditionExpressionNode::Negation(operand) => operand.has_non_binary_operators(),
            ConditionExpressionNode::And(operands) => {
                operands.len() != 2 || operands.iter().any(|op| op.has_non_binary_operators())
            }
            ConditionExpressionNode::Or(operands) => {
                operands.len() != 2 || operands.iter().any(|op| op.has_non_binary_operators())
            }
            ConditionExpressionNode::Implication(left, right) => {
                left.has_non_binary_operators() || right.has_non_binary_operators()
            }
            ConditionExpressionNode::Equivalence(left, right) => {
                left.has_non_binary_operators() || right.has_non_binary_operators()
            }
            ConditionExpressionNode::ExclusiveOr(left, right) => {
                left.has_non_binary_operators() || right.has_non_binary_operators()
            }
        }
    }

    /// Convert all n-ary AND and OR operators into binary operators.
    ///
    /// This method recursively transforms the expression tree so that all AND and OR
    /// operations have exactly two operands. N-ary operations are converted to
    /// left-associative binary operations:
    /// - `and(a, b, c)` becomes `and(and(a, b), c)`
    /// - `or(a, b, c, d)` becomes `or(or(or(a, b), c), d)`
    ///
    /// Operations with 0 or 1 operands are handled as follows:
    /// - `and()` becomes `c(v)` (true)
    /// - `and(a)` becomes `a`
    /// - `or()` becomes `c(f)` (false)
    /// - `or(a)` becomes `a`
    ///
    /// Other operators (negation, implication, equivalence, xor) are recursively processed
    /// but remain unchanged in their structure.
    ///
    /// # Returns
    ///
    /// A new expression with all AND/OR operators converted to binary form.
    ///
    /// # Example
    ///
    /// ```
    /// # use biodivine_adf_solver::{ConditionExpression, Statement};
    /// let s1 = Statement::from(1);
    /// let s2 = Statement::from(2);
    /// let s3 = Statement::from(3);
    ///
    /// // Create: and(1, 2, 3)
    /// let expr = ConditionExpression::and(&[
    ///     ConditionExpression::statement(s1),
    ///     ConditionExpression::statement(s2),
    ///     ConditionExpression::statement(s3),
    /// ]);
    ///
    /// let binarized = expr.binarize();
    ///
    /// // Result: and(and(1, 2), 3)
    /// assert_eq!(binarized.to_string(), "and(and(1,2),3)");
    /// ```
    pub fn binarize(&self) -> Self {
        match &*self.0 {
            ConditionExpressionNode::Constant(_) => self.clone(),
            ConditionExpressionNode::Statement(_) => self.clone(),
            ConditionExpressionNode::Negation(operand) => {
                ConditionExpression::negation(operand.binarize())
            }
            ConditionExpressionNode::And(operands) => {
                // Recursively binarize all operands first
                let binarized_operands: Vec<_> = operands.iter().map(|op| op.binarize()).collect();

                match binarized_operands.len() {
                    0 => ConditionExpression::constant(true), // Empty AND is true
                    1 => binarized_operands[0].clone(), // Single operand AND is the operand itself
                    _ => {
                        // Convert to left-associative binary: and(and(a, b), c)
                        let mut result = ConditionExpression::and(&[
                            binarized_operands[0].clone(),
                            binarized_operands[1].clone(),
                        ]);
                        for operand in &binarized_operands[2..] {
                            result = ConditionExpression::and(&[result, operand.clone()]);
                        }
                        result
                    }
                }
            }
            ConditionExpressionNode::Or(operands) => {
                // Recursively binarize all operands first
                let binarized_operands: Vec<_> = operands.iter().map(|op| op.binarize()).collect();

                match binarized_operands.len() {
                    0 => ConditionExpression::constant(false), // Empty OR is false
                    1 => binarized_operands[0].clone(), // Single operand OR is the operand itself
                    _ => {
                        // Convert to left-associative binary: or(or(a, b), c)
                        let mut result = ConditionExpression::or(&[
                            binarized_operands[0].clone(),
                            binarized_operands[1].clone(),
                        ]);
                        for operand in &binarized_operands[2..] {
                            result = ConditionExpression::or(&[result, operand.clone()]);
                        }
                        result
                    }
                }
            }
            ConditionExpressionNode::Implication(left, right) => {
                ConditionExpression::implication(left.binarize(), right.binarize())
            }
            ConditionExpressionNode::Equivalence(left, right) => {
                ConditionExpression::equivalence(left.binarize(), right.binarize())
            }
            ConditionExpressionNode::ExclusiveOr(left, right) => {
                ConditionExpression::exclusive_or(left.binarize(), right.binarize())
            }
        }
    }
}

impl TryFrom<&str> for ConditionExpression {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Self::parse(value)
    }
}

impl fmt::Display for ConditionExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", crate::condition_expression_writer::write(self))
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
        let cond = ConditionExpression::statement(stmt.clone());

        assert!(cond.is_statement());
        assert_eq!(cond.as_statement(), Some(&stmt));
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
        assert_eq!(operand.as_statement(), Some(&Statement::from(5)));
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

        // Test as_constant returning None on non-constant
        let stmt_cond = ConditionExpression::statement(Statement::from(1));
        assert!(stmt_cond.as_constant().is_none());
    }

    // Display trait tests

    #[test]
    fn test_display_constant_true() {
        let expr = ConditionExpression::constant(true);
        assert_eq!(format!("{}", expr), "c(v)");
        assert_eq!(expr.to_string(), "c(v)");
    }

    #[test]
    fn test_display_constant_false() {
        let expr = ConditionExpression::constant(false);
        assert_eq!(format!("{}", expr), "c(f)");
    }

    #[test]
    fn test_display_statement() {
        let expr = ConditionExpression::statement(Statement::from(42));
        assert_eq!(format!("{}", expr), "42");
    }

    #[test]
    fn test_display_negation() {
        let expr =
            ConditionExpression::negation(ConditionExpression::statement(Statement::from(5)));
        assert_eq!(format!("{}", expr), "neg(5)");
    }

    #[test]
    fn test_display_and() {
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
        ]);
        assert_eq!(format!("{}", expr), "and(1,2)");
    }

    #[test]
    fn test_display_nested() {
        let expr = ConditionExpression::or(&[
            ConditionExpression::negation(ConditionExpression::statement(Statement::from(1))),
            ConditionExpression::statement(Statement::from(7)),
        ]);
        assert_eq!(format!("{}", expr), "or(neg(1),7)");
    }

    #[test]
    fn test_display_parse_roundtrip() {
        // Parse an expression, convert to string, parse again - should be equivalent
        let original = "and(or(7,neg(6)),2)";
        let parsed = ConditionExpression::parse(original).unwrap();
        let displayed = format!("{}", parsed);
        let reparsed = ConditionExpression::parse(&displayed).unwrap();

        assert_eq!(displayed, original);
        assert_eq!(format!("{}", reparsed), original);
    }

    // TryFrom tests

    #[test]
    fn test_try_from_valid_expression() {
        use std::convert::TryFrom;

        let expr = ConditionExpression::try_from("and(1,2)").unwrap();
        assert!(expr.is_and());
        assert_eq!(expr.as_and().unwrap().len(), 2);
    }

    #[test]
    fn test_try_from_invalid_expression() {
        use std::convert::TryFrom;

        let result = ConditionExpression::try_from("invalid(1,2)");
        assert!(result.is_err());
    }

    #[test]
    fn test_try_from_roundtrip() {
        use std::convert::TryFrom;

        let input = "or(neg(1),7)";
        let expr = ConditionExpression::try_from(input).unwrap();
        let output = format!("{}", expr);
        assert_eq!(input, output);
    }

    // Tests for collect_statements
    #[test]
    fn test_collect_statements_constant() {
        let expr = ConditionExpression::constant(true);
        let stmts = expr.collect_statements();
        assert!(stmts.is_empty());
    }

    #[test]
    fn test_collect_statements_single_statement() {
        let s1 = Statement::from(42);
        let expr = ConditionExpression::statement(s1.clone());
        let stmts = expr.collect_statements();
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0], s1);
    }

    #[test]
    fn test_collect_statements_negation() {
        let s1 = Statement::from(1);
        let expr = ConditionExpression::negation(ConditionExpression::statement(s1.clone()));
        let stmts = expr.collect_statements();
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0], s1);
    }

    #[test]
    fn test_collect_statements_and() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
            ConditionExpression::statement(s3.clone()),
        ]);
        let stmts = expr.collect_statements();
        assert_eq!(stmts.len(), 3);
        assert!(stmts.contains(&s1));
        assert!(stmts.contains(&s2));
        assert!(stmts.contains(&s3));
    }

    #[test]
    fn test_collect_statements_nested() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let expr = ConditionExpression::or(&[
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::and(&[
                ConditionExpression::statement(s2.clone()),
                ConditionExpression::negation(ConditionExpression::statement(s3.clone())),
            ]),
        ]);
        let stmts = expr.collect_statements();
        assert_eq!(stmts.len(), 3);
        assert!(stmts.contains(&s1));
        assert!(stmts.contains(&s2));
        assert!(stmts.contains(&s3));
    }

    #[test]
    fn test_collect_statements_duplicates() {
        let s1 = Statement::from(1);
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s1.clone()),
        ]);
        let stmts = expr.collect_statements();
        // Should deduplicate
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0], s1);
    }

    #[test]
    fn test_collect_statements_implication() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let expr = ConditionExpression::implication(
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
        );
        let stmts = expr.collect_statements();
        assert_eq!(stmts.len(), 2);
        assert!(stmts.contains(&s1));
        assert!(stmts.contains(&s2));
    }

    #[test]
    fn test_collect_statements_equivalence() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let expr = ConditionExpression::equivalence(
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
        );
        let stmts = expr.collect_statements();
        assert_eq!(stmts.len(), 2);
        assert!(stmts.contains(&s1));
        assert!(stmts.contains(&s2));
    }

    #[test]
    fn test_collect_statements_xor() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let expr = ConditionExpression::exclusive_or(
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
        );
        let stmts = expr.collect_statements();
        assert_eq!(stmts.len(), 2);
        assert!(stmts.contains(&s1));
        assert!(stmts.contains(&s2));
    }

    #[test]
    fn test_collect_statements_sorted() {
        let s3 = Statement::from(3);
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        // Add in reverse order
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s3.clone()),
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
        ]);
        let stmts = expr.collect_statements();
        // Should be sorted
        assert_eq!(stmts.len(), 3);
        assert_eq!(stmts[0], s1);
        assert_eq!(stmts[1], s2);
        assert_eq!(stmts[2], s3);
    }

    // Tests for substitute

    #[test]
    fn test_substitute_constant_unchanged() {
        let expr = ConditionExpression::constant(true);
        let s1 = Statement::from(1);
        let replacement = ConditionExpression::constant(false);

        let result = expr.substitute(&s1, &replacement);
        assert_eq!(result, expr);
        assert!(result.is_constant());
        assert_eq!(result.as_constant(), Some(true));
    }

    #[test]
    fn test_substitute_statement_match() {
        let s1 = Statement::from(1);
        let expr = ConditionExpression::statement(s1.clone());
        let replacement = ConditionExpression::constant(true);

        let result = expr.substitute(&s1, &replacement);
        assert_eq!(result, replacement);
        assert!(result.is_constant());
    }

    #[test]
    fn test_substitute_statement_no_match() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let expr = ConditionExpression::statement(s1.clone());
        let replacement = ConditionExpression::constant(true);

        let result = expr.substitute(&s2, &replacement);
        assert_eq!(result, expr);
        assert!(result.is_statement());
        assert_eq!(result.as_statement(), Some(&s1));
    }

    #[test]
    fn test_substitute_negation() {
        let s1 = Statement::from(1);
        let expr = ConditionExpression::negation(ConditionExpression::statement(s1.clone()));
        let replacement = ConditionExpression::constant(true);

        let result = expr.substitute(&s1, &replacement);
        assert!(result.is_negation());
        let inner = result.as_negation().unwrap();
        assert!(inner.is_constant());
        assert_eq!(inner.as_constant(), Some(true));
    }

    #[test]
    fn test_substitute_and_simple() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
        ]);
        let replacement = ConditionExpression::constant(false);

        let result = expr.substitute(&s1, &replacement);
        assert!(result.is_and());
        let operands = result.as_and().unwrap();
        assert_eq!(operands.len(), 2);
        assert!(operands[0].is_constant());
        assert!(operands[1].is_statement());
        assert_eq!(operands[1].as_statement(), Some(&s2));
    }

    #[test]
    fn test_substitute_or_multiple_occurrences() {
        let s1 = Statement::from(1);
        let expr = ConditionExpression::or(&[
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s1.clone()),
        ]);
        let replacement = ConditionExpression::constant(true);

        let result = expr.substitute(&s1, &replacement);
        assert!(result.is_or());
        let operands = result.as_or().unwrap();
        assert_eq!(operands.len(), 2);
        assert!(operands[0].is_constant());
        assert!(operands[1].is_constant());
    }

    #[test]
    fn test_substitute_implication() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let expr = ConditionExpression::implication(
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
        );
        let replacement =
            ConditionExpression::negation(ConditionExpression::statement(Statement::from(3)));

        let result = expr.substitute(&s1, &replacement);
        assert!(result.is_implication());
        let (left, right) = result.as_implication().unwrap();
        assert!(left.is_negation());
        assert!(right.is_statement());
        assert_eq!(right.as_statement(), Some(&s2));
    }

    #[test]
    fn test_substitute_equivalence() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let expr = ConditionExpression::equivalence(
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
        );
        let replacement = ConditionExpression::constant(true);

        let result = expr.substitute(&s2, &replacement);
        assert!(result.is_equivalence());
        let (left, right) = result.as_equivalence().unwrap();
        assert!(left.is_statement());
        assert!(right.is_constant());
    }

    #[test]
    fn test_substitute_xor() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let expr = ConditionExpression::exclusive_or(
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
        );
        let replacement = ConditionExpression::constant(false);

        let result = expr.substitute(&s1, &replacement);
        assert!(result.is_exclusive_or());
        let (left, right) = result.as_exclusive_or().unwrap();
        assert!(left.is_constant());
        assert!(right.is_statement());
    }

    #[test]
    fn test_substitute_nested_complex() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // Create: and(or(1, 2), neg(1))
        let expr = ConditionExpression::and(&[
            ConditionExpression::or(&[
                ConditionExpression::statement(s1.clone()),
                ConditionExpression::statement(s2.clone()),
            ]),
            ConditionExpression::negation(ConditionExpression::statement(s1.clone())),
        ]);

        let replacement = ConditionExpression::statement(s3.clone());
        let result = expr.substitute(&s1, &replacement);

        // Result should be: and(or(3, 2), neg(3))
        assert_eq!(result.to_string(), "and(or(3,2),neg(3))");
    }

    #[test]
    fn test_substitute_with_complex_replacement() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
        ]);

        // Replace s1 with "or(s2, s3)"
        let replacement = ConditionExpression::or(&[
            ConditionExpression::statement(s2.clone()),
            ConditionExpression::statement(s3.clone()),
        ]);

        let result = expr.substitute(&s1, &replacement);

        // Result should be: and(or(2, 3), 2)
        assert_eq!(result.to_string(), "and(or(2,3),2)");
    }

    #[test]
    fn test_substitute_no_occurrences() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
        ]);

        let replacement = ConditionExpression::constant(true);
        let result = expr.substitute(&s3, &replacement);

        // Should be unchanged
        assert_eq!(result, expr);
        assert_eq!(result.to_string(), "and(1,2)");
    }

    #[test]
    fn test_substitute_chain() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        let expr = ConditionExpression::statement(s1.clone());

        // First substitution: 1 -> 2
        let result1 = expr.substitute(&s1, &ConditionExpression::statement(s2.clone()));
        assert_eq!(result1.to_string(), "2");

        // Second substitution: 2 -> 3
        let result2 = result1.substitute(&s2, &ConditionExpression::statement(s3.clone()));
        assert_eq!(result2.to_string(), "3");
    }

    // Tests for binarize

    #[test]
    fn test_binarize_constant() {
        let expr = ConditionExpression::constant(true);
        let result = expr.binarize();
        assert_eq!(result, expr);
        assert!(result.is_constant());
    }

    #[test]
    fn test_binarize_statement() {
        let s1 = Statement::from(1);
        let expr = ConditionExpression::statement(s1.clone());
        let result = expr.binarize();
        assert_eq!(result, expr);
        assert!(result.is_statement());
    }

    #[test]
    fn test_binarize_negation() {
        let s1 = Statement::from(1);
        let expr = ConditionExpression::negation(ConditionExpression::statement(s1));
        let result = expr.binarize();
        assert!(result.is_negation());
        assert_eq!(result.to_string(), "neg(1)");
    }

    #[test]
    fn test_binarize_and_empty() {
        let expr = ConditionExpression::and(&[]);
        let result = expr.binarize();
        assert!(result.is_constant());
        assert_eq!(result.as_constant(), Some(true));
    }

    #[test]
    fn test_binarize_and_single() {
        let s1 = Statement::from(1);
        let expr = ConditionExpression::and(&[ConditionExpression::statement(s1.clone())]);
        let result = expr.binarize();
        assert!(result.is_statement());
        assert_eq!(result.to_string(), "1");
    }

    #[test]
    fn test_binarize_and_two() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1),
            ConditionExpression::statement(s2),
        ]);
        let result = expr.binarize();
        assert!(result.is_and());
        assert_eq!(result.to_string(), "and(1,2)");
    }

    #[test]
    fn test_binarize_and_three() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1),
            ConditionExpression::statement(s2),
            ConditionExpression::statement(s3),
        ]);
        let result = expr.binarize();
        // Should be: and(and(1, 2), 3)
        assert_eq!(result.to_string(), "and(and(1,2),3)");
    }

    #[test]
    fn test_binarize_and_four() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let s4 = Statement::from(4);
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1),
            ConditionExpression::statement(s2),
            ConditionExpression::statement(s3),
            ConditionExpression::statement(s4),
        ]);
        let result = expr.binarize();
        // Should be: and(and(and(1, 2), 3), 4)
        assert_eq!(result.to_string(), "and(and(and(1,2),3),4)");
    }

    #[test]
    fn test_binarize_or_empty() {
        let expr = ConditionExpression::or(&[]);
        let result = expr.binarize();
        assert!(result.is_constant());
        assert_eq!(result.as_constant(), Some(false));
    }

    #[test]
    fn test_binarize_or_single() {
        let s1 = Statement::from(1);
        let expr = ConditionExpression::or(&[ConditionExpression::statement(s1.clone())]);
        let result = expr.binarize();
        assert!(result.is_statement());
        assert_eq!(result.to_string(), "1");
    }

    #[test]
    fn test_binarize_or_two() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let expr = ConditionExpression::or(&[
            ConditionExpression::statement(s1),
            ConditionExpression::statement(s2),
        ]);
        let result = expr.binarize();
        assert!(result.is_or());
        assert_eq!(result.to_string(), "or(1,2)");
    }

    #[test]
    fn test_binarize_or_three() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let expr = ConditionExpression::or(&[
            ConditionExpression::statement(s1),
            ConditionExpression::statement(s2),
            ConditionExpression::statement(s3),
        ]);
        let result = expr.binarize();
        // Should be: or(or(1, 2), 3)
        assert_eq!(result.to_string(), "or(or(1,2),3)");
    }

    #[test]
    fn test_binarize_or_five() {
        let expr = ConditionExpression::or(&[
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
            ConditionExpression::statement(Statement::from(3)),
            ConditionExpression::statement(Statement::from(4)),
            ConditionExpression::statement(Statement::from(5)),
        ]);
        let result = expr.binarize();
        // Should be: or(or(or(or(1, 2), 3), 4), 5)
        assert_eq!(result.to_string(), "or(or(or(or(1,2),3),4),5)");
    }

    #[test]
    fn test_binarize_nested_and_or() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let s4 = Statement::from(4);

        // Create: and(1, 2, or(3, 4))
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1),
            ConditionExpression::statement(s2),
            ConditionExpression::or(&[
                ConditionExpression::statement(s3),
                ConditionExpression::statement(s4),
            ]),
        ]);
        let result = expr.binarize();
        // Should be: and(and(1, 2), or(3, 4))
        assert_eq!(result.to_string(), "and(and(1,2),or(3,4))");
    }

    #[test]
    fn test_binarize_deeply_nested() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let s4 = Statement::from(4);

        // Create: and(or(1, 2, 3), 4)
        let expr = ConditionExpression::and(&[
            ConditionExpression::or(&[
                ConditionExpression::statement(s1),
                ConditionExpression::statement(s2),
                ConditionExpression::statement(s3),
            ]),
            ConditionExpression::statement(s4),
        ]);
        let result = expr.binarize();
        // Should be: and(or(or(1, 2), 3), 4)
        assert_eq!(result.to_string(), "and(or(or(1,2),3),4)");
    }

    #[test]
    fn test_binarize_with_negation() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // Create: and(neg(1), 2, 3)
        let expr = ConditionExpression::and(&[
            ConditionExpression::negation(ConditionExpression::statement(s1)),
            ConditionExpression::statement(s2),
            ConditionExpression::statement(s3),
        ]);
        let result = expr.binarize();
        // Should be: and(and(neg(1), 2), 3)
        assert_eq!(result.to_string(), "and(and(neg(1),2),3)");
    }

    #[test]
    fn test_binarize_implication() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // Create: imp(and(1, 2, 3), 1)
        let expr = ConditionExpression::implication(
            ConditionExpression::and(&[
                ConditionExpression::statement(s1.clone()),
                ConditionExpression::statement(s2),
                ConditionExpression::statement(s3),
            ]),
            ConditionExpression::statement(s1),
        );
        let result = expr.binarize();
        // Should binarize the and inside
        assert_eq!(result.to_string(), "imp(and(and(1,2),3),1)");
    }

    #[test]
    fn test_binarize_equivalence() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // Create: iff(or(1, 2, 3), 1)
        let expr = ConditionExpression::equivalence(
            ConditionExpression::or(&[
                ConditionExpression::statement(s1.clone()),
                ConditionExpression::statement(s2),
                ConditionExpression::statement(s3),
            ]),
            ConditionExpression::statement(s1),
        );
        let result = expr.binarize();
        // Should binarize the or inside
        assert_eq!(result.to_string(), "iff(or(or(1,2),3),1)");
    }

    #[test]
    fn test_binarize_xor() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // Create: xor(and(1, 2, 3), 1)
        let expr = ConditionExpression::exclusive_or(
            ConditionExpression::and(&[
                ConditionExpression::statement(s1.clone()),
                ConditionExpression::statement(s2),
                ConditionExpression::statement(s3),
            ]),
            ConditionExpression::statement(s1),
        );
        let result = expr.binarize();
        // Should binarize the and inside
        assert_eq!(result.to_string(), "xor(and(and(1,2),3),1)");
    }

    #[test]
    fn test_binarize_already_binary() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1),
            ConditionExpression::statement(s2),
        ]);
        let result = expr.binarize();
        // Should remain the same
        assert_eq!(result, expr);
    }

    #[test]
    fn test_binarize_complex_mixed() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let s4 = Statement::from(4);
        let s5 = Statement::from(5);

        // Create: or(and(1, 2, 3), and(4, 5))
        let expr = ConditionExpression::or(&[
            ConditionExpression::and(&[
                ConditionExpression::statement(s1),
                ConditionExpression::statement(s2),
                ConditionExpression::statement(s3),
            ]),
            ConditionExpression::and(&[
                ConditionExpression::statement(s4),
                ConditionExpression::statement(s5),
            ]),
        ]);
        let result = expr.binarize();
        // Should be: or(and(and(1, 2), 3), and(4, 5))
        assert_eq!(result.to_string(), "or(and(and(1,2),3),and(4,5))");
    }

    #[test]
    fn test_binarize_idempotent() {
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1),
            ConditionExpression::statement(s2),
            ConditionExpression::statement(s3),
        ]);
        let result1 = expr.binarize();
        let result2 = result1.binarize();
        // Binarizing a binarized expression should not change it
        assert_eq!(result1, result2);
    }

    // Tests for substitute_many

    #[test]
    fn test_substitute_many_empty_map() {
        use std::collections::BTreeMap;

        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
        ]);
        let subs = BTreeMap::new();
        let result = expr.substitute_many(&subs);
        assert_eq!(result, expr);
    }

    #[test]
    fn test_substitute_many_single() {
        use std::collections::BTreeMap;

        let s1 = Statement::from(1);
        let expr = ConditionExpression::statement(s1.clone());

        let mut subs = BTreeMap::new();
        subs.insert(s1, ConditionExpression::constant(true));

        let result = expr.substitute_many(&subs);
        assert!(result.is_constant());
        assert_eq!(result.as_constant(), Some(true));
    }

    #[test]
    fn test_substitute_many_multiple() {
        use std::collections::BTreeMap;

        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
            ConditionExpression::statement(s3.clone()),
        ]);

        let mut subs = BTreeMap::new();
        subs.insert(s1, ConditionExpression::constant(true));
        subs.insert(s2, ConditionExpression::constant(false));

        let result = expr.substitute_many(&subs);
        assert_eq!(result.to_string(), "and(c(v),c(f),3)");
    }

    #[test]
    fn test_substitute_many_nested() {
        use std::collections::BTreeMap;

        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        let expr = ConditionExpression::or(&[
            ConditionExpression::and(&[
                ConditionExpression::statement(s1.clone()),
                ConditionExpression::statement(s2.clone()),
            ]),
            ConditionExpression::negation(ConditionExpression::statement(s3.clone())),
        ]);

        let mut subs = BTreeMap::new();
        subs.insert(s1, ConditionExpression::statement(Statement::from(10)));
        subs.insert(s3, ConditionExpression::statement(Statement::from(30)));

        let result = expr.substitute_many(&subs);
        assert_eq!(result.to_string(), "or(and(10,2),neg(30))");
    }

    #[test]
    fn test_substitute_many_all_occurrences() {
        use std::collections::BTreeMap;

        let s1 = Statement::from(1);

        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s1.clone()),
        ]);

        let mut subs = BTreeMap::new();
        subs.insert(s1, ConditionExpression::constant(true));

        let result = expr.substitute_many(&subs);
        assert_eq!(result.to_string(), "and(c(v),c(v),c(v))");
    }

    #[test]
    fn test_substitute_many_complex_replacement() {
        use std::collections::BTreeMap;

        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1.clone()),
            ConditionExpression::statement(s2.clone()),
        ]);

        let mut subs = BTreeMap::new();
        subs.insert(
            s1,
            ConditionExpression::or(&[
                ConditionExpression::statement(Statement::from(3)),
                ConditionExpression::statement(Statement::from(4)),
            ]),
        );

        let result = expr.substitute_many(&subs);
        assert_eq!(result.to_string(), "and(or(3,4),2)");
    }

    #[test]
    fn test_substitute_many_no_match() {
        use std::collections::BTreeMap;

        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(s1),
            ConditionExpression::statement(s2),
        ]);

        let mut subs = BTreeMap::new();
        subs.insert(s3, ConditionExpression::constant(true));

        let result = expr.substitute_many(&subs);
        assert_eq!(result, expr);
    }

    #[test]
    fn test_substitute_many_all_operators() {
        use std::collections::BTreeMap;

        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        let expr = ConditionExpression::implication(
            ConditionExpression::equivalence(
                ConditionExpression::statement(s1.clone()),
                ConditionExpression::statement(s2.clone()),
            ),
            ConditionExpression::exclusive_or(
                ConditionExpression::statement(s1.clone()),
                ConditionExpression::statement(s2.clone()),
            ),
        );

        let mut subs = BTreeMap::new();
        subs.insert(s1, ConditionExpression::statement(Statement::from(10)));
        subs.insert(s2, ConditionExpression::statement(Statement::from(20)));

        let result = expr.substitute_many(&subs);
        assert_eq!(result.to_string(), "imp(iff(10,20),xor(10,20))");
    }

    // Tests for has_non_binary_operators

    #[test]
    fn test_has_non_binary_operators_constant() {
        let expr = ConditionExpression::constant(true);
        assert!(!expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_statement() {
        let expr = ConditionExpression::statement(Statement::from(1));
        assert!(!expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_negation_binary() {
        let expr = ConditionExpression::negation(ConditionExpression::and(&[
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
        ]));
        assert!(!expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_negation_non_binary() {
        let expr = ConditionExpression::negation(ConditionExpression::and(&[
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
            ConditionExpression::statement(Statement::from(3)),
        ]));
        assert!(expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_binary_and() {
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
        ]);
        assert!(!expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_ternary_and() {
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
            ConditionExpression::statement(Statement::from(3)),
        ]);
        assert!(expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_unary_and() {
        let expr = ConditionExpression::and(&[ConditionExpression::statement(Statement::from(1))]);
        assert!(expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_empty_and() {
        let expr = ConditionExpression::and(&[]);
        assert!(expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_binary_or() {
        let expr = ConditionExpression::or(&[
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
        ]);
        assert!(!expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_ternary_or() {
        let expr = ConditionExpression::or(&[
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
            ConditionExpression::statement(Statement::from(3)),
        ]);
        assert!(expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_implication_binary() {
        let expr = ConditionExpression::implication(
            ConditionExpression::and(&[
                ConditionExpression::statement(Statement::from(1)),
                ConditionExpression::statement(Statement::from(2)),
            ]),
            ConditionExpression::statement(Statement::from(3)),
        );
        assert!(!expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_implication_non_binary() {
        let expr = ConditionExpression::implication(
            ConditionExpression::and(&[
                ConditionExpression::statement(Statement::from(1)),
                ConditionExpression::statement(Statement::from(2)),
                ConditionExpression::statement(Statement::from(3)),
            ]),
            ConditionExpression::statement(Statement::from(4)),
        );
        assert!(expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_nested() {
        let expr = ConditionExpression::and(&[
            ConditionExpression::or(&[
                ConditionExpression::statement(Statement::from(1)),
                ConditionExpression::statement(Statement::from(2)),
            ]),
            ConditionExpression::statement(Statement::from(3)),
        ]);
        assert!(!expr.has_non_binary_operators());
    }

    #[test]
    fn test_has_non_binary_operators_deeply_nested_non_binary() {
        let expr = ConditionExpression::and(&[
            ConditionExpression::or(&[
                ConditionExpression::statement(Statement::from(1)),
                ConditionExpression::statement(Statement::from(2)),
                ConditionExpression::statement(Statement::from(3)),
            ]),
            ConditionExpression::statement(Statement::from(4)),
        ]);
        assert!(expr.has_non_binary_operators());
    }
}
