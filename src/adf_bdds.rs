use crate::{AdfExpressions, ConditionExpression, Statement};
use cancel_this::{Cancellable, is_cancelled};
use ruddy::VariableId;
use ruddy::split::Bdd;
use std::cmp::max;
use std::collections::{BTreeMap, BTreeSet};
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
            .enumerate()
            .map(|(index, stmt)| {
                let index = u32::try_from(index).expect("Statement index out of range");
                (stmt.clone(), VariableId::new(index << 2))
            })
            .collect();
        DirectMap { mapping }
    }

    /// Get the BDD [`VariableId`] for a [`Statement`].
    pub fn get(&self, statement: &Statement) -> Option<VariableId> {
        self.mapping.get(statement).copied()
    }

    /// Get all [`Statement`] objects in the map.
    ///
    /// The statements are returned in sorted order (by their index) because they are
    /// stored in a [`BTreeMap`].
    pub fn statements(&self) -> impl DoubleEndedIterator<Item = &Statement> + '_ {
        self.mapping.keys()
    }

    /// Create a [`Bdd`] literal for the given [`Statement`].    
    pub fn make_literal(&self, statement: &Statement, polarity: bool) -> Bdd {
        let var = self[statement];
        Bdd::new_literal(var, polarity)
    }

    /// Return the largest [`VariableId`] used in this encoding (or `0` if the encoding is empty).
    pub fn maximum_variable_id(&self) -> VariableId {
        self.mapping
            .values()
            .max()
            .copied()
            .unwrap_or(VariableId::new(0))
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
            .enumerate()
            .map(|(i, stmt)| {
                let index = u32::try_from(i).expect("Statement index out of range");
                let t_var = VariableId::new((index << 2) + 1);
                let f_var = VariableId::new((index << 2) + 2);
                (stmt.clone(), (t_var, f_var))
            })
            .collect();
        DualMap { mapping }
    }

    /// Get the BDD [`VariableId`]s (positive, negative) for a [`Statement`].
    pub fn get(&self, statement: &Statement) -> Option<(VariableId, VariableId)> {
        self.mapping.get(statement).copied()
    }

    /// Get all [`Statement`] objects in the map.
    ///
    /// The statements are returned in sorted order (by their index) because they are
    /// stored in a [`BTreeMap`].
    pub fn statements(&self) -> impl DoubleEndedIterator<Item = &Statement> + '_ {
        self.mapping.keys()
    }

    /// Create [`Bdd`] literals for both the positive and negative dual variables.
    ///
    /// Returns a tuple `(positive_literal, negative_literal)` where:
    /// - `positive_literal` is a [`Bdd`] representing the "can be true" variable
    /// - `negative_literal` is a [`Bdd`] representing the "can be false" variable
    pub fn make_literals(&self, statement: &Statement) -> (Bdd, Bdd) {
        let (t_var, f_var) = self[statement];
        (Bdd::new_literal(t_var, true), Bdd::new_literal(f_var, true))
    }

    /// Create a [`Bdd`] literal for the positive dual variable (can be true).
    pub fn make_positive_literal(&self, statement: &Statement) -> Bdd {
        let (t_var, _) = self[statement];
        Bdd::new_literal(t_var, true)
    }

    /// Create a [`Bdd`] literal for the negative dual variable (can be false).
    pub fn make_negative_literal(&self, statement: &Statement) -> Bdd {
        let (_, f_var) = self[statement];
        Bdd::new_literal(f_var, true)
    }

    /// Return the largest [`VariableId`] used in this encoding (or `0` if the encoding is empty).
    pub fn maximum_variable_id(&self) -> VariableId {
        self.mapping
            .values()
            .map(|(a, b)| max(a, b))
            .max()
            .copied()
            .unwrap_or(VariableId::new(0))
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
    pub fn get_condition(&self, statement: &Statement) -> Option<&Bdd> {
        self.conditions.get(statement)
    }

    /// Get all statements that have conditions.
    ///
    /// The statements are returned in sorted order (by their index) because they are
    /// stored in a [`BTreeMap`].
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
/// direct encoding. However, strictly speaking, this is not always sufficient if we want to
/// find solutions where a free statement is, well, free and other statements are fixed.
///
/// In dual encoding, each statement has two variables: positive (can be true) and negative
/// (can be false). The valuation where both variables are false is invalid (a statement must
/// be able to be either true or false). The `valid` BDD encodes the constraint that for every
/// statement, at least one of its dual variables must be true.
pub struct DualEncoding {
    var_map: DualMap,
    conditions: BTreeMap<Statement, (Bdd, Bdd)>,
    valid: Bdd,
}

impl DualEncoding {
    /// Get the variable map.
    pub fn var_map(&self) -> &DualMap {
        &self.var_map
    }

    /// Get the [`Bdd`] conditions (can_be_true, can_be_false) for a [`Statement`], if they exist.
    pub fn get_condition(&self, statement: &Statement) -> Option<(&Bdd, &Bdd)> {
        self.conditions.get(statement).map(|(t, f)| (t, f))
    }

    /// Get all statements that have conditions.
    ///
    /// The statements are returned in sorted order (by their index) because they are
    /// stored in a [`BTreeMap`].
    pub fn conditional_statements(&self) -> impl Iterator<Item = &Statement> {
        self.conditions.keys()
    }

    /// Get the [`Bdd`] representing all valid dual variable valuations.
    ///
    /// This BDD is true for valuations where, for every statement, at least one of its
    /// dual variables (positive or negative) is true. Valuations where both dual variables
    /// of any statement are false are excluded as invalid.
    pub fn valid(&self) -> &Bdd {
        &self.valid
    }
}

/// A [`AdfBdds`] encodes an ADF symbolically using BDDs.
///
/// Internally, it uses two encodings, depending on use case. Direct encoding uses one [`Bdd`]
/// variable per statement, while dual encoding uses two.
///
/// By default, the variables are ordered such that the direct variable is followed by the
/// two dual variables.
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

    /// Return the largest [`VariableId`] used in the internal encodings
    /// (or `0` if the ADF is empty).
    pub fn maximum_variable_id(&self) -> VariableId {
        max(
            self.direct_encoding.var_map().maximum_variable_id(),
            self.dual_encoding.var_map().maximum_variable_id(),
        )
    }

    /// Compute the number of valuations in a "directly encoded" BDD representation of the
    /// ADF statements.
    ///
    /// The given BDD can only use variables of the direct encoding.
    pub fn count_direct_valuations(&self, bdd: &Bdd) -> f64 {
        // Sanity check that the BDD is "valid".
        let used_variables = bdd.used_variables();
        let direct_variables = self
            .direct_encoding
            .var_map
            .mapping
            .values()
            .copied()
            .collect::<BTreeSet<_>>();
        assert!(used_variables.is_subset(&direct_variables));

        // Count the number of "unused variables" that we have in the BDD
        let statement_count = self.direct_encoding.var_map.mapping.len();

        if statement_count == 0 {
            // For empty ADFs, the result is trivial.
            return if bdd.is_false() { 0.0 } else { 1.0 };
        }

        // Each statement maps to 4 variables, which means (starting
        // from zero), the last variable is 4*x - 1.
        let max_var = VariableId::new_long((statement_count * 4 - 1) as u64).unwrap();
        let unused_vars = statement_count * 3;

        // Count valuations and normalize them based on unused variables.
        let count = bdd.count_satisfying_valuations(Some(max_var));

        count / 2.0f64.powf(unused_vars as f64)
    }

    /// Try to create a [`AdfBdds`] from an [`AdfExpressions`].
    ///
    /// This operation is cancellable using the `cancel-this` crate. If cancelled,
    /// it will return an error.
    ///
    /// # Panics
    ///
    /// Conversion fails if [`AdfExpressions`] contains missing statements.
    pub fn try_from_expressions(adf: &AdfExpressions) -> Cancellable<Self> {
        assert!(
            adf.find_missing_statements().is_empty(),
            "ADF contains missing statements."
        );
        // Get all statements in sorted order
        let statements: Vec<Statement> = adf.statements().cloned().collect();

        // Create variable maps
        let direct_map = DirectMap::new(&statements);
        let dual_map = DualMap::new(&statements);

        // Build direct encoding conditions
        let mut direct_conditions = BTreeMap::new();
        for (statement, condition) in adf.conditions() {
            is_cancelled!()?;
            let bdd = expression_to_bdd(condition, &direct_map)?;
            direct_conditions.insert(statement, bdd);
        }

        // Build dual encoding conditions from direct encoding
        let mut dual_conditions = BTreeMap::new();
        let mapping_function = direct_to_dual_map_function(&direct_map, &dual_map)?;
        for (statement, condition) in direct_conditions.iter() {
            let can_be_true = direct_to_dual_encoding(condition, &mapping_function, &direct_map);
            is_cancelled!()?;
            let can_be_false =
                direct_to_dual_encoding(&condition.not(), &mapping_function, &direct_map);
            is_cancelled!()?;

            dual_conditions.insert(statement.clone(), (can_be_true, can_be_false));
        }

        // Build the valid BDD for dual encoding
        // For each statement, at least one of (t_var, f_var) must be true
        let mut valid = Bdd::new_true();
        for statement in &statements {
            is_cancelled!()?;
            let (t_lit, f_lit) = dual_map.make_literals(statement);
            // At least one must be true: t_var OR f_var
            valid = valid.and(&t_lit.or(&f_lit));
        }

        Ok(AdfBdds {
            direct_encoding: DirectEncoding {
                var_map: direct_map,
                conditions: direct_conditions,
            },
            dual_encoding: DualEncoding {
                var_map: dual_map,
                conditions: dual_conditions,
                valid,
            },
        })
    }
}

impl From<&AdfExpressions> for AdfBdds {
    fn from(adf: &AdfExpressions) -> Self {
        // Use the cancellable version, but panic if cancelled
        AdfBdds::try_from_expressions(adf)
            .expect("Conversion from `AdfExpressions` to `AdfBdds` was cancelled")
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
    use crate::condition_expression::ConditionExpressionNode::{
        And, Constant, Equivalence, ExclusiveOr, Implication, Negation, Or, Statement,
    };

    // Check for cancellation
    is_cancelled!()?;

    match &*expr.0 {
        Constant(value) => {
            if *value {
                Ok(Bdd::new_true())
            } else {
                Ok(Bdd::new_false())
            }
        }
        Statement(stmt) => Ok(var_map.make_literal(stmt, true)),
        Negation(operand) => Ok(expression_to_bdd(operand, var_map)?.not()),
        And(operands) => {
            let mut result = Bdd::new_true();
            for op in operands {
                result = result.and(&expression_to_bdd(op, var_map)?);
            }
            Ok(result)
        }
        Or(operands) => {
            let mut result = Bdd::new_false();
            for op in operands {
                result = result.or(&expression_to_bdd(op, var_map)?);
            }
            Ok(result)
        }
        Implication(left, right) => {
            let left_bdd = expression_to_bdd(left, var_map)?;
            let right_bdd = expression_to_bdd(right, var_map)?;
            Ok(left_bdd.not().or(&right_bdd))
        }
        Equivalence(left, right) => {
            let left_bdd = expression_to_bdd(left, var_map)?;
            let right_bdd = expression_to_bdd(right, var_map)?;
            Ok(left_bdd.iff(&right_bdd))
        }
        ExclusiveOr(left, right) => {
            let left_bdd = expression_to_bdd(left, var_map)?;
            let right_bdd = expression_to_bdd(right, var_map)?;
            Ok(left_bdd.xor(&right_bdd))
        }
    }
}

/// Build a map function which connects each variable in the direct encoding
/// to the two of its dual counterparts.
///
/// Note that in theory, the ordering of BDD variables can be arbitrary, but the best
/// result is achieved if the three variables follow each other in the variable ordering.
fn direct_to_dual_map_function(direct_map: &DirectMap, dual_map: &DualMap) -> Cancellable<Bdd> {
    let mut mapping_function = Bdd::new_true();
    for statement in direct_map.statements().rev() {
        is_cancelled!()?;

        let (t_lit, f_lit) = dual_map.make_literals(statement);

        // (direct_var => t_var) & (!direct_var => f_var)
        // This is equivalent to: (!direct_var | t_var) & (direct_var | f_var)
        let direct_implies_t = direct_map.make_literal(statement, false).or(&t_lit);
        let not_direct_implies_f = direct_map.make_literal(statement, true).or(&f_lit);
        let var_mapping = direct_implies_t.and(&not_direct_implies_f);

        // Apply constraint and existentially quantify the state variable
        mapping_function = mapping_function.and(&var_mapping);
    }

    Ok(mapping_function)
}

/// Convert a direct encoding BDD to a dual encoding BDD.
///
/// This applies the principle: for each state variable, we add constraints
/// (state_var => t_var) & (!state_var => f_var) and then existentially quantify state_var.
///
/// Use [`direct_to_dual_map_function`] to construct the `mapping_function`.
fn direct_to_dual_encoding(function: &Bdd, mapping_function: &Bdd, direct_map: &DirectMap) -> Bdd {
    let direct_vars: Vec<VariableId> = direct_map.mapping.values().copied().collect();
    Bdd::binary_op_with_exists(
        function,
        mapping_function,
        ruddy::boolean_operators::And,
        &direct_vars,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_direct_map_creation() {
        let statements = vec![Statement::from(0), Statement::from(5), Statement::from(10)];
        let map = DirectMap::new(&statements);

        // Check that all statements are present in sorted order
        let result: Vec<_> = map.statements().cloned().collect();
        assert_eq!(
            result,
            vec![Statement::from(0), Statement::from(10), Statement::from(5)]
        );
    }

    #[test]
    fn test_direct_map_get() {
        let statements = vec![Statement::from(0), Statement::from(5)];
        let map = DirectMap::new(&statements);

        // Check that we can retrieve variable IDs
        assert!(map.get(&Statement::from(0)).is_some());
        assert!(map.get(&Statement::from(5)).is_some());
        assert!(map.get(&Statement::from(99)).is_none());

        // Variable IDs should be based on statement indices (shifted by 2)
        let var0 = map.get(&Statement::from(0)).unwrap();
        let var5 = map.get(&Statement::from(5)).unwrap();
        assert_eq!(u64::from(var0), 0 << 2);
        assert_eq!(u64::from(var5), 1 << 2);
    }

    #[test]
    fn test_direct_map_indexing() {
        let statements = vec![Statement::from(0), Statement::from(5)];
        let map = DirectMap::new(&statements);

        // Check indexing with reference
        let var0_ref = map[&Statement::from(0)];
        let var0_get = map.get(&Statement::from(0)).unwrap();
        assert_eq!(var0_ref, var0_get);

        // Check indexing with value
        let var5_val = map[Statement::from(5)];
        let var5_get = map.get(&Statement::from(5)).unwrap();
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

        let positive = map.make_literal(&Statement::from(0), true);
        let negative = map.make_literal(&Statement::from(0), false);

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

        // Check that all statements are present in sorted order
        let result: Vec<_> = map.statements().cloned().collect();
        assert_eq!(
            result,
            vec![Statement::from(0), Statement::from(10), Statement::from(5)]
        );
    }

    #[test]
    fn test_dual_map_get() {
        let statements = vec![Statement::from(0), Statement::from(5)];
        let map = DualMap::new(&statements);

        // Check that we can retrieve variable ID pairs
        assert!(map.get(&Statement::from(0)).is_some());
        assert!(map.get(&Statement::from(5)).is_some());
        assert!(map.get(&Statement::from(99)).is_none());

        // Variable IDs should be consecutive: (index << 2) + 1 and (index << 2) + 2
        let (t0, f0) = map.get(&Statement::from(0)).unwrap();
        let (t5, f5) = map.get(&Statement::from(5)).unwrap();

        assert_eq!(u64::from(t0), (0 << 2) + 1);
        assert_eq!(u64::from(f0), (0 << 2) + 2);
        assert_eq!(u64::from(t5), (1 << 2) + 1);
        assert_eq!(u64::from(f5), (1 << 2) + 2);
    }

    #[test]
    fn test_dual_map_indexing() {
        let statements = vec![Statement::from(0), Statement::from(5)];
        let map = DualMap::new(&statements);

        // Check indexing with reference
        let (t0_ref, f0_ref) = map[&Statement::from(0)];
        let (t0_get, f0_get) = map.get(&Statement::from(0)).unwrap();
        assert_eq!(t0_ref, t0_get);
        assert_eq!(f0_ref, f0_get);

        // Check indexing with value
        let (t5_val, f5_val) = map[Statement::from(5)];
        let (t5_get, f5_get) = map.get(&Statement::from(5)).unwrap();
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

        let (t_lit, f_lit) = map.make_literals(&Statement::from(0));

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

        let t_lit = map.make_positive_literal(&Statement::from(0));
        let f_lit = map.make_negative_literal(&Statement::from(0));
        let (t_both, f_both) = map.make_literals(&Statement::from(0));

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
        let expected = map.make_literal(&Statement::from(0), true);
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
        let expected = map.make_literal(&Statement::from(0), false);
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
        assert!(direct.get_condition(&Statement::from(0)).is_some());
        assert!(direct.get_condition(&Statement::from(1)).is_some());

        // Check dual encoding
        let dual = symbolic_adf.dual_encoding();
        assert_eq!(dual.conditional_statements().count(), 2);
        assert!(dual.get_condition(&Statement::from(0)).is_some());
        assert!(dual.get_condition(&Statement::from(1)).is_some());
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
        assert!(var_map.get(&Statement::from(0)).is_some());

        // Test get_condition
        let condition = direct.get_condition(&Statement::from(0));
        assert!(condition.is_some());
        assert!(condition.unwrap().is_true());

        // Test conditional_statements (should be in sorted order)
        let statements: Vec<_> = direct.conditional_statements().collect();
        assert_eq!(
            statements.into_iter().cloned().collect::<Vec<_>>(),
            vec![Statement::from(0)]
        );
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
        assert!(var_map.get(&Statement::from(0)).is_some());

        // Test get_condition
        let condition = dual.get_condition(&Statement::from(0));
        assert!(condition.is_some());
        let (can_be_true, can_be_false) = condition.unwrap();

        // Both BDDs should exist (we don't make assumptions about their exact values
        // as they depend on the dual encoding transformation)
        assert!(can_be_true.node_count() > 0);
        assert!(can_be_false.node_count() > 0);

        // Test conditional_statements (should be in sorted order)
        let statements: Vec<_> = dual.conditional_statements().cloned().collect();
        assert_eq!(statements, vec![Statement::from(0)]);
    }

    // Test for From<AdfExpressions> implementation
    #[test]
    fn test_from_adf_expressions_owned() {
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, 1).
            ac(1, c(v)).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        // Test the `From` implementation which takes ownership
        let symbolic_adf = AdfBdds::from(expr_adf);

        // Verify that the conversion worked correctly
        let direct = symbolic_adf.direct_encoding();
        assert_eq!(direct.conditional_statements().count(), 2);
        assert!(direct.get_condition(&Statement::from(0)).is_some());
        assert!(direct.get_condition(&Statement::from(1)).is_some());

        let dual = symbolic_adf.dual_encoding();
        assert_eq!(dual.conditional_statements().count(), 2);
    }

    // Comprehensive tests for expression_to_bdd function

    #[test]
    fn test_expression_to_bdd_and() {
        let statements = vec![Statement::from(0), Statement::from(1)];
        let map = DirectMap::new(&statements);

        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(Statement::from(0)),
            ConditionExpression::statement(Statement::from(1)),
        ]);
        let bdd = expression_to_bdd(&expr, &map).unwrap();

        // Should not be a constant
        assert!(!bdd.is_true());
        assert!(!bdd.is_false());

        // Verify the BDD represents AND correctly by checking its true only when both are true
        let s0_lit = map.make_literal(&Statement::from(0), true);
        let s1_lit = map.make_literal(&Statement::from(1), true);
        let expected = s0_lit.and(&s1_lit);
        assert!(bdd.structural_eq(&expected));
    }

    #[test]
    fn test_expression_to_bdd_or() {
        let statements = vec![Statement::from(0), Statement::from(1)];
        let map = DirectMap::new(&statements);

        let expr = ConditionExpression::or(&[
            ConditionExpression::statement(Statement::from(0)),
            ConditionExpression::statement(Statement::from(1)),
        ]);
        let bdd = expression_to_bdd(&expr, &map).unwrap();

        // Should not be a constant
        assert!(!bdd.is_true());
        assert!(!bdd.is_false());

        // Verify the BDD represents OR correctly
        let s0_lit = map.make_literal(&Statement::from(0), true);
        let s1_lit = map.make_literal(&Statement::from(1), true);
        let expected = s0_lit.or(&s1_lit);
        assert!(bdd.structural_eq(&expected));
    }

    #[test]
    fn test_expression_to_bdd_implication() {
        let statements = vec![Statement::from(0), Statement::from(1)];
        let map = DirectMap::new(&statements);

        let expr = ConditionExpression::implication(
            ConditionExpression::statement(Statement::from(0)),
            ConditionExpression::statement(Statement::from(1)),
        );
        let bdd = expression_to_bdd(&expr, &map).unwrap();

        // Should not be a constant
        assert!(!bdd.is_true());
        assert!(!bdd.is_false());

        // Implication: (s0 -> s1) is equivalent to (!s0 | s1)
        let s0_lit = map.make_literal(&Statement::from(0), true);
        let s1_lit = map.make_literal(&Statement::from(1), true);
        let expected = s0_lit.not().or(&s1_lit);
        assert!(bdd.structural_eq(&expected));
    }

    #[test]
    fn test_expression_to_bdd_equivalence() {
        let statements = vec![Statement::from(0), Statement::from(1)];
        let map = DirectMap::new(&statements);

        let expr = ConditionExpression::equivalence(
            ConditionExpression::statement(Statement::from(0)),
            ConditionExpression::statement(Statement::from(1)),
        );
        let bdd = expression_to_bdd(&expr, &map).unwrap();

        // Should not be a constant
        assert!(!bdd.is_true());
        assert!(!bdd.is_false());

        // Verify the BDD represents equivalence correctly
        let s0_lit = map.make_literal(&Statement::from(0), true);
        let s1_lit = map.make_literal(&Statement::from(1), true);
        let expected = s0_lit.iff(&s1_lit);
        assert!(bdd.structural_eq(&expected));
    }

    #[test]
    fn test_expression_to_bdd_exclusive_or() {
        let statements = vec![Statement::from(0), Statement::from(1)];
        let map = DirectMap::new(&statements);

        let expr = ConditionExpression::exclusive_or(
            ConditionExpression::statement(Statement::from(0)),
            ConditionExpression::statement(Statement::from(1)),
        );
        let bdd = expression_to_bdd(&expr, &map).unwrap();

        // Should not be a constant
        assert!(!bdd.is_true());
        assert!(!bdd.is_false());

        // Verify the BDD represents XOR correctly
        let s0_lit = map.make_literal(&Statement::from(0), true);
        let s1_lit = map.make_literal(&Statement::from(1), true);
        let expected = s0_lit.xor(&s1_lit);
        assert!(bdd.structural_eq(&expected));
    }

    #[test]
    fn test_expression_to_bdd_complex_nested() {
        let statements = vec![Statement::from(0), Statement::from(1), Statement::from(2)];
        let map = DirectMap::new(&statements);

        // Build: (s0 AND s1) OR s2
        let expr = ConditionExpression::or(&[
            ConditionExpression::and(&[
                ConditionExpression::statement(Statement::from(0)),
                ConditionExpression::statement(Statement::from(1)),
            ]),
            ConditionExpression::statement(Statement::from(2)),
        ]);
        let bdd = expression_to_bdd(&expr, &map).unwrap();

        // Should not be a constant
        assert!(!bdd.is_true());
        assert!(!bdd.is_false());

        // Build the same BDD manually to verify
        let s0_lit = map.make_literal(&Statement::from(0), true);
        let s1_lit = map.make_literal(&Statement::from(1), true);
        let s2_lit = map.make_literal(&Statement::from(2), true);
        let expected = s0_lit.and(&s1_lit).or(&s2_lit);
        assert!(bdd.structural_eq(&expected));
    }

    #[test]
    fn test_expression_to_bdd_and_multiple_operands() {
        let statements = vec![
            Statement::from(0),
            Statement::from(1),
            Statement::from(2),
            Statement::from(3),
        ];
        let map = DirectMap::new(&statements);

        // AND with 4 operands
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(Statement::from(0)),
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
            ConditionExpression::statement(Statement::from(3)),
        ]);
        let bdd = expression_to_bdd(&expr, &map).unwrap();

        // Build the same BDD manually
        let s0_lit = map.make_literal(&Statement::from(0), true);
        let s1_lit = map.make_literal(&Statement::from(1), true);
        let s2_lit = map.make_literal(&Statement::from(2), true);
        let s3_lit = map.make_literal(&Statement::from(3), true);
        let expected = s0_lit.and(&s1_lit).and(&s2_lit).and(&s3_lit);
        assert!(bdd.structural_eq(&expected));
    }

    #[test]
    fn test_expression_to_bdd_or_multiple_operands() {
        let statements = vec![
            Statement::from(0),
            Statement::from(1),
            Statement::from(2),
            Statement::from(3),
        ];
        let map = DirectMap::new(&statements);

        // OR with 4 operands
        let expr = ConditionExpression::or(&[
            ConditionExpression::statement(Statement::from(0)),
            ConditionExpression::statement(Statement::from(1)),
            ConditionExpression::statement(Statement::from(2)),
            ConditionExpression::statement(Statement::from(3)),
        ]);
        let bdd = expression_to_bdd(&expr, &map).unwrap();

        // Build the same BDD manually
        let s0_lit = map.make_literal(&Statement::from(0), true);
        let s1_lit = map.make_literal(&Statement::from(1), true);
        let s2_lit = map.make_literal(&Statement::from(2), true);
        let s3_lit = map.make_literal(&Statement::from(3), true);
        let expected = s0_lit.or(&s1_lit).or(&s2_lit).or(&s3_lit);
        assert!(bdd.structural_eq(&expected));
    }

    #[test]
    fn test_expression_to_bdd_deeply_nested() {
        let statements = vec![Statement::from(0), Statement::from(1), Statement::from(2)];
        let map = DirectMap::new(&statements);

        // Build: neg(s0 -> (s1 XOR s2))
        let expr = ConditionExpression::negation(ConditionExpression::implication(
            ConditionExpression::statement(Statement::from(0)),
            ConditionExpression::exclusive_or(
                ConditionExpression::statement(Statement::from(1)),
                ConditionExpression::statement(Statement::from(2)),
            ),
        ));
        let bdd = expression_to_bdd(&expr, &map).unwrap();

        // Should not be a constant
        assert!(!bdd.is_true());
        assert!(!bdd.is_false());

        // Build the same BDD manually to verify
        let s0_lit = map.make_literal(&Statement::from(0), true);
        let s1_lit = map.make_literal(&Statement::from(1), true);
        let s2_lit = map.make_literal(&Statement::from(2), true);
        let xor_part = s1_lit.xor(&s2_lit);
        let implication = s0_lit.not().or(&xor_part);
        let expected = implication.not();
        assert!(bdd.structural_eq(&expected));
    }

    // Tests for valid BDD in DualEncoding

    #[test]
    fn test_dual_encoding_valid_accessor() {
        let adf_str = r#"
            s(0).
            ac(0, c(v)).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        let dual = symbolic_adf.dual_encoding();
        let valid = dual.valid();

        // Valid BDD should exist and not be a constant
        assert!(!valid.is_true());
        assert!(!valid.is_false());
        assert!(valid.node_count() > 0);
    }

    #[test]
    fn test_dual_encoding_valid_single_statement() {
        let adf_str = r#"
            s(0).
            ac(0, c(v)).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        let dual = symbolic_adf.dual_encoding();
        let valid = dual.valid();
        let var_map = dual.var_map();

        // For a single statement, valid should be: t_var OR f_var
        let (t_lit, f_lit) = var_map.make_literals(&Statement::from(0));
        let expected = t_lit.or(&f_lit);

        assert!(valid.structural_eq(&expected));
    }

    #[test]
    fn test_dual_encoding_valid_multiple_statements() {
        let adf_str = r#"
            s(0).
            s(1).
            s(2).
            ac(0, 1).
            ac(1, 2).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        let dual = symbolic_adf.dual_encoding();
        let valid = dual.valid();
        let var_map = dual.var_map();

        // For multiple statements, valid should be the conjunction of all (t_i OR f_i)
        let (t0_lit, f0_lit) = var_map.make_literals(&Statement::from(0));
        let (t1_lit, f1_lit) = var_map.make_literals(&Statement::from(1));
        let (t2_lit, f2_lit) = var_map.make_literals(&Statement::from(2));

        let expected = t0_lit
            .or(&f0_lit)
            .and(&t1_lit.or(&f1_lit))
            .and(&t2_lit.or(&f2_lit));

        assert!(valid.structural_eq(&expected));
    }

    #[test]
    fn test_dual_encoding_valid_excludes_invalid_valuations() {
        let adf_str = r#"
            s(0).
            ac(0, c(v)).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        let dual = symbolic_adf.dual_encoding();
        let valid = dual.valid();
        let var_map = dual.var_map();

        // Get the dual variables
        let (t_lit, f_lit) = var_map.make_literals(&Statement::from(0));

        // The invalid case: both t_var and f_var are false
        let both_false = t_lit.not().and(&f_lit.not());

        // Valid AND both_false should be false (no satisfying assignment)
        let intersection = valid.and(&both_false);
        assert!(intersection.is_false());
    }

    #[test]
    fn test_dual_encoding_valid_allows_valid_valuations() {
        let adf_str = r#"
            s(0).
            ac(0, c(v)).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        let dual = symbolic_adf.dual_encoding();
        let valid = dual.valid();
        let var_map = dual.var_map();

        // Get the dual variables
        let (t_lit, f_lit) = var_map.make_literals(&Statement::from(0));

        // Test all three valid cases:
        // 1. Both true (statement can be both true and false - truly "free")
        let both_true = t_lit.and(&f_lit);
        let case1 = valid.and(&both_true);
        assert!(!case1.is_false()); // Should have satisfying assignments

        // 2. Only t_var true (statement can only be true)
        let only_t = t_lit.and(&f_lit.not());
        let case2 = valid.and(&only_t);
        assert!(!case2.is_false()); // Should have satisfying assignments

        // 3. Only f_var true (statement can only be false)
        let only_f = t_lit.not().and(&f_lit);
        let case3 = valid.and(&only_f);
        assert!(!case3.is_false()); // Should have satisfying assignments
    }

    #[test]
    fn test_dual_encoding_valid_with_free_statements() {
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, 1).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        let dual = symbolic_adf.dual_encoding();
        let valid = dual.valid();
        let var_map = dual.var_map();

        // Valid should constrain both statement 0 and statement 1 (including free statements)
        let (t0_lit, f0_lit) = var_map.make_literals(&Statement::from(0));
        let (t1_lit, f1_lit) = var_map.make_literals(&Statement::from(1));

        let expected = t0_lit.or(&f0_lit).and(&t1_lit.or(&f1_lit));

        assert!(valid.structural_eq(&expected));

        // Verify that invalid valuations for the free statement are also excluded
        let s1_both_false = t1_lit.not().and(&f1_lit.not());
        let intersection = valid.and(&s1_both_false);
        assert!(intersection.is_false());
    }

    #[test]
    fn test_dual_encoding_valid_complex_adf() {
        let adf_str = r#"
            s(0).
            s(1).
            s(2).
            s(3).
            ac(0, and(1, 2)).
            ac(1, or(2, 3)).
            ac(2, neg(3)).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        let dual = symbolic_adf.dual_encoding();
        let valid = dual.valid();
        let var_map = dual.var_map();

        // Build the expected valid BDD manually
        let mut expected = Bdd::new_true();
        for i in 0..4 {
            let (t_lit, f_lit) = var_map.make_literals(&Statement::from(i));
            expected = expected.and(&t_lit.or(&f_lit));
        }

        assert!(valid.structural_eq(&expected));
    }

    // Test that conversion fails when there are missing statements

    #[test]
    #[should_panic(expected = "ADF contains missing statements.")]
    fn test_conversion_fails_with_missing_statements() {
        // Create an ADF where a condition references a statement that is not declared
        let adf_str = r#"
            s(0).
            ac(0, and(1, 2)).
        "#;

        // Parse without fixing missing statements - statements 1 and 2 are referenced but not declared
        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");

        // This should panic when trying to convert to BDDs because statements 1 and 2 don't exist
        let _symbolic_adf = AdfBdds::from(&expr_adf);
    }

    #[test]
    fn test_conversion_succeeds_with_fixed_missing_statements() {
        // Create an ADF where a condition references statements that are not declared
        let adf_str = r#"
            s(0).
            ac(0, and(1, 2)).
        "#;

        // Parse and fix missing statements
        let mut expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        expr_adf.fix_missing_statements();

        // Now the conversion should succeed because statements 1 and 2 have been added as free statements
        let symbolic_adf = AdfBdds::from(&expr_adf);

        // Verify that all three statements are present in the encoding
        let direct = symbolic_adf.direct_encoding();
        let var_map = direct.var_map();
        let all_statements: Vec<_> = var_map.statements().cloned().collect();
        assert_eq!(
            all_statements,
            vec![Statement::from(0), Statement::from(1), Statement::from(2)]
        );

        // Verify that only statement 0 has a condition
        assert_eq!(direct.conditional_statements().count(), 1);
        assert!(direct.get_condition(&Statement::from(0)).is_some());
        assert!(direct.get_condition(&Statement::from(1)).is_none());
        assert!(direct.get_condition(&Statement::from(2)).is_none());
    }

    // Tests for count_direct_valuations

    #[test]
    fn test_count_direct_valuations_true_bdd() {
        let adf_str = r#"
            s(0).
            s(1).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        let true_bdd = Bdd::new_true();
        let count = symbolic_adf.count_direct_valuations(&true_bdd);

        // True BDD accepts all valuations: 2^2 = 4 (both statements can be T or F)
        // But due to variable spacing, the actual count is 8.0
        assert_eq!(count, 4.0);
    }

    #[test]
    fn test_count_direct_valuations_false_bdd() {
        let adf_str = r#"
            s(0).
            s(1).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        let false_bdd = Bdd::new_false();
        let count = symbolic_adf.count_direct_valuations(&false_bdd);

        // False BDD accepts no valuations
        assert_eq!(count, 0.0);
    }

    #[test]
    fn test_count_direct_valuations_single_literal() {
        let adf_str = r#"
            s(0).
            s(1).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        // BDD representing s(0) = true
        let var_map = symbolic_adf.direct_encoding().var_map();
        let s0_true = var_map.make_literal(&Statement::from(0), true);
        let count = symbolic_adf.count_direct_valuations(&s0_true);

        // Accepts 2 valuations: s(0)=T, s(1)=T and s(0)=T, s(1)=F
        assert_eq!(count, 2.0);
    }

    #[test]
    fn test_count_direct_valuations_and() {
        let adf_str = r#"
            s(0).
            s(1).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        // BDD representing s(0) AND s(1)
        let var_map = symbolic_adf.direct_encoding().var_map();
        let s0 = var_map.make_literal(&Statement::from(0), true);
        let s1 = var_map.make_literal(&Statement::from(1), true);
        let and_bdd = s0.and(&s1);
        let count = symbolic_adf.count_direct_valuations(&and_bdd);

        // Accepts only 1 valuation: s(0)=T, s(1)=T
        assert_eq!(count, 1.0);
    }

    #[test]
    fn test_count_direct_valuations_three_statements() {
        let adf_str = r#"
            s(0).
            s(1).
            s(2).
        "#;

        let expr_adf = AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let symbolic_adf = AdfBdds::from(&expr_adf);

        // BDD representing (s(0) AND s(1)) OR s(2)
        let var_map = symbolic_adf.direct_encoding().var_map();
        let s0 = var_map.make_literal(&Statement::from(0), true);
        let s1 = var_map.make_literal(&Statement::from(1), true);
        let s2 = var_map.make_literal(&Statement::from(2), true);
        let bdd = s0.and(&s1).or(&s2);
        let count = symbolic_adf.count_direct_valuations(&bdd);

        // Accepts valuations:
        // s(2)=T: (T,T,T), (T,F,T), (F,T,T), (F,F,T) = 4
        // s(2)=F: (T,T,F) = 1
        assert_eq!(count, 5.0);
    }
}
