use crate::{ConditionExpression, AdfExpressions, Statement};
use cancel_this::{Cancellable, is_cancelled};
use ruddy::VariableId;
use ruddy::split::Bdd;
use std::collections::BTreeMap;
use std::ops::Index;

/// Maps every [`Statement`] to a single BDD [`VariableId`].
///
/// It is assumed that the BDD variables follow the natural ordering of the statements, but do not
/// necessarily need to use the exact same identifiers.
pub struct DirectMap {
    mapping: BTreeMap<Statement, VariableId>,
}

impl DirectMap {
    /// Create a new [`DirectMap`] from an ordered list of [`Statement`] objects.
    pub fn new(statements: &[Statement]) -> Self {
        let mapping = statements
            .iter()
            .map(|stmt| {
                let index = u32::try_from(stmt.into_index()).expect("Statement index out of range");
                (*stmt, VariableId::new(index << 2))
            })
            .collect();
        DirectMap { mapping }
    }

    /// Get the BDD [`VariableId`] for a [`Statement`].
    pub fn get(&self, statement: Statement) -> Option<VariableId> {
        self.mapping.get(&statement).copied()
    }

    /// Get ordered list of all [`Statement`] objects in the map.
    pub fn statements(&self) -> Vec<Statement> {
        self.mapping.keys().copied().collect()
    }

    /// Create a [`Bdd`] literal for the given [`Statement`].    
    pub fn get_literal(&self, statement: Statement, polarity: bool) -> Bdd {
        let var = self[&statement];
        Bdd::new_literal(var, polarity)
    }
}

impl Index<&Statement> for DirectMap {
    type Output = VariableId;

    fn index(&self, statement: &Statement) -> &Self::Output {
        self.mapping
            .get(statement)
            .expect("Statement not found in DirectMap")
    }
}

impl Index<Statement> for DirectMap {
    type Output = VariableId;

    fn index(&self, statement: Statement) -> &Self::Output {
        &self[&statement]
    }
}

/// Maps every [`Statement`] to two BDD [`VariableId`] objects, one for "positive" and one for
/// "negative" value of [`Statement`].
///
/// It is assumed that the BDD variables follow the natural ordering of the statements
/// (and positive < negative), but do not necessarily need to use the exact same identifiers.
pub struct DualMap {
    mapping: BTreeMap<Statement, (VariableId, VariableId)>,
}

impl DualMap {
    /// Create a new [`DualMap`] from an ordered list of [`Statement`] objects.
    /// For each statement, two consecutive variable IDs are allocated (positive, then negative).
    pub fn new(statements: &[Statement]) -> Self {
        let mapping = statements
            .iter()
            .map(|stmt| {
                let index = u32::try_from(stmt.into_index()).expect("Statement index out of range");
                let t_var = VariableId::new((index << 2) + 1);
                let f_var = VariableId::new((index << 2) + 2);
                (*stmt, (t_var, f_var))
            })
            .collect();
        DualMap { mapping }
    }

    /// Get the BDD [`VariableId`]s (positive, negative) for a [`Statement`].
    pub fn get(&self, statement: Statement) -> Option<(VariableId, VariableId)> {
        self.mapping.get(&statement).copied()
    }

    /// Get ordered list of all [`Statement`] objects in the map.
    pub fn statements(&self) -> Vec<Statement> {
        self.mapping.keys().copied().collect()
    }

    /// Create [`Bdd`] literals for both the positive and negative dual variables.
    ///
    /// Returns a tuple `(positive_literal, negative_literal)` where:
    /// - `positive_literal` is a [`Bdd`] representing the "can be true" variable
    /// - `negative_literal` is a [`Bdd`] representing the "can be false" variable
    pub fn get_literals(&self, statement: Statement) -> (Bdd, Bdd) {
        let (t_var, f_var) = self[&statement];
        (Bdd::new_literal(t_var, true), Bdd::new_literal(f_var, true))
    }

    /// Create a [`Bdd`] literal for the positive dual variable (can be true).
    pub fn get_positive_literal(&self, statement: Statement) -> Bdd {
        let (t_var, _) = self[&statement];
        Bdd::new_literal(t_var, true)
    }

    /// Create a [`Bdd`] literal for the negative dual variable (can be false).
    pub fn get_negative_literal(&self, statement: Statement) -> Bdd {
        let (_, f_var) = self[&statement];
        Bdd::new_literal(f_var, true)
    }
}

impl Index<&Statement> for DualMap {
    type Output = (VariableId, VariableId);

    fn index(&self, statement: &Statement) -> &Self::Output {
        self.mapping
            .get(statement)
            .expect("Statement not found in DualMap")
    }
}

impl Index<Statement> for DualMap {
    type Output = (VariableId, VariableId);

    fn index(&self, statement: Statement) -> &Self::Output {
        &self[&statement]
    }
}

/// Uses [`DirectMap`] to encode every condition of an ADF directly into a BDD.
///
/// Note that statements can exist in `var_map` that do not have corresponding conditions.
/// These are considered to be "free" statements.
pub struct DirectEncoding {
    var_map: DirectMap,
    conditions: BTreeMap<Statement, Bdd>,
}

impl DirectEncoding {
    /// Get the variable map.
    pub fn var_map(&self) -> &DirectMap {
        &self.var_map
    }

    /// Get the [`Bdd`] condition for a [`Statement`], if it exists.
    pub fn get_condition(&self, statement: Statement) -> Option<&Bdd> {
        self.conditions.get(&statement)
    }

    /// Get all statements that have conditions.
    pub fn conditional_statements(&self) -> impl Iterator<Item = &Statement> {
        self.conditions.keys()
    }
}

/// Uses [`DualMap`] to encode every condition of an ADF into two BDDs, one describing
/// all dual interpretations where the statement can become true, and one describing all dual
/// interpretations where the statement can become false.
///
/// Note that statements can exist in `var_map` that do not have corresponding conditions.
/// These are considered to be "free" statements.
///
/// Also note that for many applications, it is sufficient to encode "free" statements using
/// direct encoding. However, strictly speaking, this is not
pub struct DualEncoding {
    var_map: DualMap,
    conditions: BTreeMap<Statement, (Bdd, Bdd)>,
}

impl DualEncoding {
    /// Get the variable map.
    pub fn var_map(&self) -> &DualMap {
        &self.var_map
    }

    /// Get the [`Bdd`] conditions (can_be_true, can_be_false) for a [`Statement`], if they exist.
    pub fn get_condition(&self, statement: Statement) -> Option<(&Bdd, &Bdd)> {
        self.conditions.get(&statement).map(|(t, f)| (t, f))
    }

    /// Get all statements that have conditions.
    pub fn conditional_statements(&self) -> impl Iterator<Item = &Statement> {
        self.conditions.keys()
    }
}

/// A [`AdfBdds`] encodes an ADF symbolically using BDDs.
///
/// Internally, it uses two encodings, depending on use case. Direct encoding uses one [`Bdd`]
/// variable per statement, while dual encoding uses two.
pub struct AdfBdds {
    direct_encoding: DirectEncoding,
    dual_encoding: DualEncoding,
}

impl AdfBdds {
    /// Get the direct encoding of this ADF.
    pub fn direct_encoding(&self) -> &DirectEncoding {
        &self.direct_encoding
    }

    /// Get the dual encoding of this ADF.
    pub fn dual_encoding(&self) -> &DualEncoding {
        &self.dual_encoding
    }

    /// Try to create a SymbolicAdf from an ExpressionAdf.
    ///
    /// This operation is cancellable using the `cancel-this` crate. If cancelled,
    /// it will return an error.
    pub fn try_from_expressions(adf: &AdfExpressions) -> Cancellable<Self> {
        // Get all statements in sorted order
        let statements: Vec<Statement> = adf.statements().copied().collect();

        // Create variable maps
        let direct_map = DirectMap::new(&statements);
        let dual_map = DualMap::new(&statements);

        // Build direct encoding conditions
        let mut direct_conditions = BTreeMap::new();
        for (statement, condition) in adf.conditions() {
            is_cancelled!()?;
            let bdd = expression_to_bdd(condition, &direct_map)?;
            direct_conditions.insert(*statement, bdd);
        }

        // Build dual encoding conditions from direct encoding
        let mut dual_conditions = BTreeMap::new();
        for (statement, condition) in direct_conditions.iter() {
            is_cancelled!()?;
            let can_be_true = direct_to_dual_encoding(condition, &direct_map, &dual_map)?;
            let can_be_false = direct_to_dual_encoding(&condition.not(), &direct_map, &dual_map)?;
            dual_conditions.insert(*statement, (can_be_true, can_be_false));
        }

        Ok(AdfBdds {
            direct_encoding: DirectEncoding {
                var_map: direct_map,
                conditions: direct_conditions,
            },
            dual_encoding: DualEncoding {
                var_map: dual_map,
                conditions: dual_conditions,
            },
        })
    }
}

impl From<&AdfExpressions> for AdfBdds {
    fn from(adf: &AdfExpressions) -> Self {
        // Use the cancellable version, but panic if cancelled
        AdfBdds::try_from_expressions(adf)
            .expect("Conversion from ExpressionAdf to SymbolicAdf was cancelled")
    }
}

impl From<AdfExpressions> for AdfBdds {
    fn from(adf: AdfExpressions) -> Self {
        AdfBdds::from(&adf)
    }
}

/// Convert a ConditionExpression to a BDD using direct encoding.
///
/// This function is cancellable and will check for cancellation at each recursive step.
fn expression_to_bdd(expr: &ConditionExpression, var_map: &DirectMap) -> Cancellable<Bdd> {
    // Check for cancellation
    is_cancelled!()?;

    // Check for constant
    if let Some(value) = expr.as_constant() {
        return if value {
            Ok(Bdd::new_true())
        } else {
            Ok(Bdd::new_false())
        };
    }

    // Check for statement reference
    if let Some(stmt) = expr.as_statement() {
        return Ok(var_map.get_literal(stmt, true));
    }

    // Check for negation
    if let Some(operand) = expr.as_negation() {
        return Ok(expression_to_bdd(operand, var_map)?.not());
    }

    // Check for AND
    if let Some(operands) = expr.as_and() {
        let mut result = Bdd::new_true();
        for op in operands {
            result = result.and(&expression_to_bdd(op, var_map)?);
        }
        return Ok(result);
    }

    // Check for OR
    if let Some(operands) = expr.as_or() {
        let mut result = Bdd::new_false();
        for op in operands {
            result = result.or(&expression_to_bdd(op, var_map)?);
        }
        return Ok(result);
    }

    // Check for implication
    if let Some((left, right)) = expr.as_implication() {
        let left_bdd = expression_to_bdd(left, var_map)?;
        let right_bdd = expression_to_bdd(right, var_map)?;
        return Ok(left_bdd.not().or(&right_bdd));
    }

    // Check for equivalence
    if let Some((left, right)) = expr.as_equivalence() {
        let left_bdd = expression_to_bdd(left, var_map)?;
        let right_bdd = expression_to_bdd(right, var_map)?;
        return Ok(left_bdd.iff(&right_bdd));
    }

    // Check for exclusive OR
    if let Some((left, right)) = expr.as_exclusive_or() {
        let left_bdd = expression_to_bdd(left, var_map)?;
        let right_bdd = expression_to_bdd(right, var_map)?;
        return Ok(left_bdd.xor(&right_bdd));
    }

    panic!("Unknown expression type");
}

/// Convert a direct encoding BDD to a dual encoding BDD.
///
/// This applies the principle: for each state variable, we add constraints
/// (state_var => t_var) & (!state_var => f_var) and then existentially quantify state_var.
///
/// This function is cancellable and will check for cancellation at each iteration.
fn direct_to_dual_encoding(
    function: &Bdd,
    direct_map: &DirectMap,
    dual_map: &DualMap,
) -> Cancellable<Bdd> {
    // Get all statements in the direct map (in reverse order for efficiency)
    let statements = direct_map.statements();
    let mut result = function.clone();

    // Process variables in reverse order for efficiency
    for statement in statements.iter().rev() {
        // Check for cancellation at each iteration
        is_cancelled!()?;

        let direct_var = direct_map[statement];
        let (t_lit, f_lit) = dual_map.get_literals(*statement);

        // (direct_var => t_var) & (!direct_var => f_var)
        // This is equivalent to: (!direct_var | t_var) & (direct_var | f_var)
        let direct_implies_t = direct_map.get_literal(*statement, false).or(&t_lit);
        let not_direct_implies_f = direct_map.get_literal(*statement, true).or(&f_lit);
        let mapping_function = direct_implies_t.and(&not_direct_implies_f);

        // Apply constraint and existentially quantify the state variable
        result = result.and(&mapping_function).exists(&[direct_var]);
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_direct_map_creation() {
        let statements = vec![Statement::from(0), Statement::from(5), Statement::from(10)];
        let map = DirectMap::new(&statements);

        // Check that all statements are present
        assert_eq!(map.statements().len(), 3);
        assert!(map.statements().contains(&Statement::from(0)));
        assert!(map.statements().contains(&Statement::from(5)));
        assert!(map.statements().contains(&Statement::from(10)));
    }

    #[test]
    fn test_direct_map_get() {
        let statements = vec![Statement::from(0), Statement::from(5)];
        let map = DirectMap::new(&statements);

        // Check that we can retrieve variable IDs
        assert!(map.get(Statement::from(0)).is_some());
        assert!(map.get(Statement::from(5)).is_some());
        assert!(map.get(Statement::from(99)).is_none());

        // Variable IDs should be based on statement indices (shifted by 2)
        let var0 = map.get(Statement::from(0)).unwrap();
        let var5 = map.get(Statement::from(5)).unwrap();
        assert_eq!(u64::from(var0), 0 << 2);
        assert_eq!(u64::from(var5), 5 << 2);
    }

    #[test]
    fn test_direct_map_indexing() {
        let statements = vec![Statement::from(0), Statement::from(5)];
        let map = DirectMap::new(&statements);

        // Check indexing with reference
        let var0_ref = map[&Statement::from(0)];
        let var0_get = map.get(Statement::from(0)).unwrap();
        assert_eq!(var0_ref, var0_get);

        // Check indexing with value
        let var5_val = map[Statement::from(5)];
        let var5_get = map.get(Statement::from(5)).unwrap();
        assert_eq!(var5_val, var5_get);
    }

    #[test]
    #[should_panic(expected = "Statement not found in DirectMap")]
    fn test_direct_map_indexing_panic() {
        let statements = vec![Statement::from(0)];
        let map = DirectMap::new(&statements);
        let _ = map[Statement::from(99)];
    }

    #[test]
    fn test_direct_map_get_literal() {
        let statements = vec![Statement::from(0)];
        let map = DirectMap::new(&statements);

        let positive = map.get_literal(Statement::from(0), true);
        let negative = map.get_literal(Statement::from(0), false);

        // Both should be valid BDDs (not true or false constants)
        assert!(!positive.is_true());
        assert!(!positive.is_false());
        assert!(!negative.is_true());
        assert!(!negative.is_false());

        // They should be different
        assert!(!positive.structural_eq(&negative));
    }

    #[test]
    fn test_dual_map_creation() {
        let statements = vec![Statement::from(0), Statement::from(5), Statement::from(10)];
        let map = DualMap::new(&statements);

        // Check that all statements are present
        assert_eq!(map.statements().len(), 3);
        assert!(map.statements().contains(&Statement::from(0)));
        assert!(map.statements().contains(&Statement::from(5)));
        assert!(map.statements().contains(&Statement::from(10)));
    }

    #[test]
    fn test_dual_map_get() {
        let statements = vec![Statement::from(0), Statement::from(5)];
        let map = DualMap::new(&statements);

        // Check that we can retrieve variable ID pairs
        assert!(map.get(Statement::from(0)).is_some());
        assert!(map.get(Statement::from(5)).is_some());
        assert!(map.get(Statement::from(99)).is_none());

        // Variable IDs should be consecutive: (index << 2) + 1 and (index << 2) + 2
        let (t0, f0) = map.get(Statement::from(0)).unwrap();
        let (t5, f5) = map.get(Statement::from(5)).unwrap();

        assert_eq!(u64::from(t0), (0 << 2) + 1);
        assert_eq!(u64::from(f0), (0 << 2) + 2);
        assert_eq!(u64::from(t5), (5 << 2) + 1);
        assert_eq!(u64::from(f5), (5 << 2) + 2);
    }

    #[test]
    fn test_dual_map_indexing() {
        let statements = vec![Statement::from(0), Statement::from(5)];
        let map = DualMap::new(&statements);

        // Check indexing with reference
        let (t0_ref, f0_ref) = map[&Statement::from(0)];
        let (t0_get, f0_get) = map.get(Statement::from(0)).unwrap();
        assert_eq!(t0_ref, t0_get);
        assert_eq!(f0_ref, f0_get);

        // Check indexing with value
        let (t5_val, f5_val) = map[Statement::from(5)];
        let (t5_get, f5_get) = map.get(Statement::from(5)).unwrap();
        assert_eq!(t5_val, t5_get);
        assert_eq!(f5_val, f5_get);
    }

    #[test]
    #[should_panic(expected = "Statement not found in DualMap")]
    fn test_dual_map_indexing_panic() {
        let statements = vec![Statement::from(0)];
        let map = DualMap::new(&statements);
        let _ = map[Statement::from(99)];
    }

    #[test]
    fn test_dual_map_get_literals() {
        let statements = vec![Statement::from(0)];
        let map = DualMap::new(&statements);

        let (t_lit, f_lit) = map.get_literals(Statement::from(0));

        // Both should be valid BDDs (not true or false constants)
        assert!(!t_lit.is_true());
        assert!(!t_lit.is_false());
        assert!(!f_lit.is_true());
        assert!(!f_lit.is_false());

        // They should be different
        assert!(!t_lit.structural_eq(&f_lit));
    }

    #[test]
    fn test_dual_map_individual_literals() {
        let statements = vec![Statement::from(0)];
        let map = DualMap::new(&statements);

        let t_lit = map.get_positive_literal(Statement::from(0));
        let f_lit = map.get_negative_literal(Statement::from(0));
        let (t_both, f_both) = map.get_literals(Statement::from(0));

        // Individual methods should match get_literals
        assert!(t_lit.structural_eq(&t_both));
        assert!(f_lit.structural_eq(&f_both));
    }

    #[test]
    fn test_expression_to_bdd_constants() {
        let statements = vec![Statement::from(0)];
        let map = DirectMap::new(&statements);

        let true_expr = ConditionExpression::constant(true);
        let false_expr = ConditionExpression::constant(false);

        let true_bdd = expression_to_bdd(&true_expr, &map).unwrap();
        let false_bdd = expression_to_bdd(&false_expr, &map).unwrap();

        assert!(true_bdd.is_true());
        assert!(false_bdd.is_false());
    }

    #[test]
    fn test_expression_to_bdd_statement() {
        let statements = vec![Statement::from(0)];
        let map = DirectMap::new(&statements);

        let stmt_expr = ConditionExpression::statement(Statement::from(0));
        let stmt_bdd = expression_to_bdd(&stmt_expr, &map).unwrap();

        // Should not be a constant
        assert!(!stmt_bdd.is_true());
        assert!(!stmt_bdd.is_false());

        // Should be equivalent to the literal
        let expected = map.get_literal(Statement::from(0), true);
        assert!(stmt_bdd.structural_eq(&expected));
    }

    #[test]
    fn test_expression_to_bdd_negation() {
        let statements = vec![Statement::from(0)];
        let map = DirectMap::new(&statements);

        let stmt_expr = ConditionExpression::statement(Statement::from(0));
        let neg_expr = ConditionExpression::negation(stmt_expr);
        let neg_bdd = expression_to_bdd(&neg_expr, &map).unwrap();

        // Should not be a constant
        assert!(!neg_bdd.is_true());
        assert!(!neg_bdd.is_false());

        // Should be equivalent to negated literal
        let expected = map.get_literal(Statement::from(0), false);
        assert!(neg_bdd.structural_eq(&expected));
    }

    #[test]
    fn test_symbolic_adf_basic() {
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, 1).
            ac(1, c(v)).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        // Check direct encoding
        let direct = symbolic_adf.direct_encoding();
        assert_eq!(direct.conditional_statements().count(), 2);
        assert!(direct.get_condition(Statement::from(0)).is_some());
        assert!(direct.get_condition(Statement::from(1)).is_some());

        // Check dual encoding
        let dual = symbolic_adf.dual_encoding();
        assert_eq!(dual.conditional_statements().count(), 2);
        assert!(dual.get_condition(Statement::from(0)).is_some());
        assert!(dual.get_condition(Statement::from(1)).is_some());
    }

    #[test]
    fn test_direct_encoding_accessors() {
        let adf_str = r#"
            s(0).
            ac(0, c(v)).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        let direct = symbolic_adf.direct_encoding();

        // Test var_map accessor
        let var_map = direct.var_map();
        assert!(var_map.get(Statement::from(0)).is_some());

        // Test get_condition
        let condition = direct.get_condition(Statement::from(0));
        assert!(condition.is_some());
        assert!(condition.unwrap().is_true());

        // Test conditional_statements
        let statements: Vec<_> = direct.conditional_statements().copied().collect();
        assert_eq!(statements.len(), 1);
        assert_eq!(statements[0], Statement::from(0));
    }

    #[test]
    fn test_dual_encoding_accessors() {
        let adf_str = r#"
            s(0).
            ac(0, c(v)).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        let dual = symbolic_adf.dual_encoding();

        // Test var_map accessor
        let var_map = dual.var_map();
        assert!(var_map.get(Statement::from(0)).is_some());

        // Test get_condition
        let condition = dual.get_condition(Statement::from(0));
        assert!(condition.is_some());
        let (can_be_true, can_be_false) = condition.unwrap();

        // Both BDDs should exist (we don't make assumptions about their exact values
        // as they depend on the dual encoding transformation)
        assert!(can_be_true.node_count() > 0);
        assert!(can_be_false.node_count() > 0);

        // Test conditional_statements
        let statements: Vec<_> = dual.conditional_statements().copied().collect();
        assert_eq!(statements.len(), 1);
        assert_eq!(statements[0], Statement::from(0));
    }
}
