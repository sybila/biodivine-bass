use crate::{AdfExpressions, ConditionExpression, Statement};
use biodivine_lib_param_bn::{BinaryOp, BooleanNetwork, FnUpdate, Regulation, RegulatoryGraph};
use std::collections::HashMap;

impl From<BooleanNetwork> for AdfExpressions {
    fn from(value: BooleanNetwork) -> Self {
        (&value).into()
    }
}

impl From<&BooleanNetwork> for AdfExpressions {
    fn from(value: &BooleanNetwork) -> Self {
        bn_to_adf(value)
    }
}

impl From<&AdfExpressions> for BooleanNetwork {
    fn from(value: &AdfExpressions) -> Self {
        adf_to_bn(value)
    }
}

impl From<AdfExpressions> for BooleanNetwork {
    fn from(value: AdfExpressions) -> Self {
        (&value).into()
    }
}

/// Convert a `BooleanNetwork` to `AdfExpressions`.
///
/// # Requirements
/// - The network must not have explicit or implicit parameters (panics if it does).
/// - Input variables will be set to identity (self-reference).
///
/// # Arguments
/// - `bn`: The Boolean network to convert.
///
/// # Panics
/// - If the network contains explicit or implicit parameters.
fn bn_to_adf(bn: &BooleanNetwork) -> AdfExpressions {
    let mut bn = bn.clone();

    // Make all inputs use the identity function convention.
    for var in bn.inputs(true) {
        // Ensure there is a regulation
        if bn.as_graph().find_regulation(var, var).is_none() {
            bn.as_graph_mut()
                .add_raw_regulation(Regulation {
                    regulator: var,
                    target: var,
                    observable: false,
                    monotonicity: None,
                })
                .unwrap();
        }
        // Set update function to identity
        bn.set_update_function(var, Some(FnUpdate::Var(var)))
            .unwrap();
    }

    // Check for parameters
    if bn.num_parameters() > 0 {
        let param_names: Vec<String> = bn
            .parameters()
            .map(|p| bn.get_parameter(p).get_name().to_string())
            .collect();
        panic!(
            "Network contains {} explicit parameters: {}",
            param_names.len(),
            param_names.join(", ")
        );
    }

    if bn.num_implicit_parameters() > 0 {
        let param_names: Vec<String> = bn
            .implicit_parameters()
            .into_iter()
            .map(|v| bn.get_variable_name(v).to_string())
            .collect();

        panic!(
            "Network contains {} implicit parameters: {}",
            param_names.len(),
            param_names.join(", ")
        );
    }

    // Start building the new ADF:
    let mut adf = AdfExpressions::new();

    for var_id in bn.variables() {
        let var_name = bn.get_variable_name(var_id);
        let statement = Statement::from(var_name.to_string());

        if let Some(update_fn) = bn.get_update_function(var_id).as_ref() {
            // Convert FnUpdate to ConditionExpression
            let condition = fn_update_to_condition(update_fn, &bn);
            adf.update_condition(statement, condition);
        } else {
            unreachable!("Correctness violation: Implicit parameters not excluded.");
        }
    }

    adf
}

/// Convert `AdfExpressions` to a `BooleanNetwork`.
///
/// # Details
/// - Statement labels that don't start with a letter will be prefixed with "v_".
/// - Statements without conditions become input variables using identity update functions.
///
/// # Arguments
/// - `adf`: The ADF expressions to convert.
///
/// # Panics
/// - If the ADF has missing statements (statements referenced but not declared).
pub fn adf_to_bn(adf: &AdfExpressions) -> BooleanNetwork {
    // Assert that there are no missing statements
    let missing = adf.find_missing_statements();
    assert!(
        missing.is_empty(),
        "ADF has missing statements: {:?}",
        missing.iter().map(|s| s.label()).collect::<Vec<_>>()
    );

    // Build variable names, ensuring they are valid BN identifiers
    let mut var_names = Vec::new();
    let mut statement_to_name = HashMap::new();

    for statement in adf.statements() {
        let var_name = statement.label().to_string();
        // In the future, we need a way to translate invalid names into something else.
        // For now, we'll keep it like this.
        assert!(
            BooleanNetwork::is_valid_name(&var_name),
            "Invalid variable name {var_name}."
        );

        statement_to_name.insert(statement.clone(), var_name.clone());
        var_names.push(var_name);
    }

    // Create regulatory graph
    // We need to infer regulations from the conditions
    let mut rg = RegulatoryGraph::new(var_names.clone());

    // First pass: collect all regulations
    let mut regulations: Vec<(String, String)> = Vec::new();

    for statement in adf.statements() {
        let target_name = statement_to_name.get(statement).unwrap();
        if let Some(condition) = adf.get_condition(statement) {
            let referenced = condition.collect_statements();
            for ref_stmt in referenced {
                let source_name = statement_to_name
                    .get(&ref_stmt)
                    .expect("Correctness violation: statement has no BN variable.");

                regulations.push((source_name.clone(), target_name.clone()));
            }
        } else {
            // For input statements, add self-regulation.
            regulations.push((target_name.clone(), target_name.clone()));
        }
    }

    // Add all regulations to the graph
    for (source, target) in regulations {
        let source_id = rg
            .find_variable(&source)
            .expect("Correctness violation: expected variable to exist.");
        let target_id = rg
            .find_variable(&target)
            .expect("Correctness violation: expected variable to exist.");

        // Skip if regulation already exists
        if rg.find_regulation(source_id, target_id).is_some() {
            continue;
        }

        rg.add_regulation(&source, &target, false, None)
            .expect("Correctness violation: cannot create regulation.");
    }

    // Create the Boolean network
    let mut bn = BooleanNetwork::new(rg);

    // Second pass: set update functions
    for statement in adf.statements() {
        let var_name = statement_to_name.get(statement).unwrap();
        let var_id = bn
            .as_graph()
            .find_variable(var_name)
            .expect("Correctness violation: expected variable to exist.");

        if let Some(condition) = adf.get_condition(statement) {
            // Convert ConditionExpression to FnUpdate
            let update_fn = condition_to_fn_update(condition, &statement_to_name, &bn);

            // Set the update function
            bn.set_update_function(var_id, Some(update_fn))
                .expect("Correctness violation: cannot set update function.");
        } else {
            bn.set_update_function(var_id, Some(FnUpdate::Var(var_id)))
                .expect("Correctness violation: cannot set update function.");
        }
    }

    bn
}

/// Convert an `FnUpdate` to a `ConditionExpression`.
fn fn_update_to_condition(fn_update: &FnUpdate, bn: &BooleanNetwork) -> ConditionExpression {
    match fn_update {
        FnUpdate::Const(value) => ConditionExpression::constant(*value),
        FnUpdate::Var(var_id) => {
            let var_name = bn.get_variable_name(*var_id);
            ConditionExpression::statement(Statement::from(var_name.to_string()))
        }
        FnUpdate::Not(inner) => {
            let inner_cond = fn_update_to_condition(inner, bn);
            ConditionExpression::negation(inner_cond)
        }
        FnUpdate::Binary(op, left, right) => {
            let left_cond = fn_update_to_condition(left, bn);
            let right_cond = fn_update_to_condition(right, bn);

            match op {
                BinaryOp::And => ConditionExpression::and(&[left_cond, right_cond]),
                BinaryOp::Or => ConditionExpression::or(&[left_cond, right_cond]),
                BinaryOp::Xor => ConditionExpression::exclusive_or(left_cond, right_cond),
                BinaryOp::Imp => ConditionExpression::implication(left_cond, right_cond),
                BinaryOp::Iff => ConditionExpression::equivalence(left_cond, right_cond),
            }
        }
        FnUpdate::Param(_, _) => {
            // This should never happen if we checked for parameters first
            panic!("Correctness violation: explicit parameters not supported in conversion.");
        }
    }
}

/// Convert a `ConditionExpression` to an `FnUpdate`.
fn condition_to_fn_update(
    condition: &ConditionExpression,
    statement_to_name: &HashMap<Statement, String>,
    bn: &BooleanNetwork,
) -> FnUpdate {
    use crate::condition_expression::ConditionExpressionNode;

    match &*condition.0 {
        ConditionExpressionNode::Constant(value) => FnUpdate::Const(*value),
        ConditionExpressionNode::Statement(stmt) => {
            let var_name = statement_to_name
                .get(stmt)
                .expect("Correctness violation: statement has no BN variable.");
            let var_id = bn
                .as_graph()
                .find_variable(var_name)
                .expect("Correctness violation: expected variable to exist.");
            FnUpdate::Var(var_id)
        }
        ConditionExpressionNode::Negation(inner) => {
            let inner_fn = condition_to_fn_update(inner, statement_to_name, bn);
            FnUpdate::Not(Box::new(inner_fn))
        }
        ConditionExpressionNode::And(operands) => {
            if operands.is_empty() {
                FnUpdate::Const(true)
            } else if operands.len() == 1 {
                condition_to_fn_update(&operands[0], statement_to_name, bn)
            } else {
                // Convert n-ary AND to nested binary ANDs
                let mut result = condition_to_fn_update(&operands[0], statement_to_name, bn);
                for operand in &operands[1..] {
                    let right = condition_to_fn_update(operand, statement_to_name, bn);
                    result = FnUpdate::Binary(BinaryOp::And, Box::new(result), Box::new(right));
                }
                result
            }
        }
        ConditionExpressionNode::Or(operands) => {
            if operands.is_empty() {
                FnUpdate::Const(false)
            } else if operands.len() == 1 {
                condition_to_fn_update(&operands[0], statement_to_name, bn)
            } else {
                // Convert n-ary OR to nested binary ORs
                let mut result = condition_to_fn_update(&operands[0], statement_to_name, bn);
                for operand in &operands[1..] {
                    let right = condition_to_fn_update(operand, statement_to_name, bn);
                    result = FnUpdate::Binary(BinaryOp::Or, Box::new(result), Box::new(right));
                }
                result
            }
        }
        ConditionExpressionNode::Implication(left, right) => {
            let left_fn = condition_to_fn_update(left, statement_to_name, bn);
            let right_fn = condition_to_fn_update(right, statement_to_name, bn);
            FnUpdate::Binary(BinaryOp::Imp, Box::new(left_fn), Box::new(right_fn))
        }
        ConditionExpressionNode::Equivalence(left, right) => {
            let left_fn = condition_to_fn_update(left, statement_to_name, bn);
            let right_fn = condition_to_fn_update(right, statement_to_name, bn);
            FnUpdate::Binary(BinaryOp::Iff, Box::new(left_fn), Box::new(right_fn))
        }
        ConditionExpressionNode::ExclusiveOr(left, right) => {
            let left_fn = condition_to_fn_update(left, statement_to_name, bn);
            let right_fn = condition_to_fn_update(right, statement_to_name, bn);
            FnUpdate::Binary(BinaryOp::Xor, Box::new(left_fn), Box::new(right_fn))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bn_to_adf_simple() {
        // Create a simple Boolean network: a = b & !c, b = a, c is input
        let bn = BooleanNetwork::try_from_bnet("a, b & !c\nb, a").unwrap();

        let adf = bn_to_adf(&bn);

        // Check that all variables are present
        assert_eq!(adf.len(), 3);
        assert!(adf.has_statement(&Statement::from("a")));
        assert!(adf.has_statement(&Statement::from("b")));
        assert!(adf.has_statement(&Statement::from("c")));

        // Check conditions
        let cond_a = adf.get_condition(&Statement::from("a")).unwrap();
        assert_eq!(
            cond_a,
            &ConditionExpression::parse("and(b,neg(c))").unwrap()
        );

        let cond_b = adf.get_condition(&Statement::from("b")).unwrap();
        assert_eq!(cond_b, &ConditionExpression::parse("a").unwrap());

        // Input c should have identity condition
        let cond_c = adf.get_condition(&Statement::from("c")).unwrap();
        assert_eq!(cond_c, &ConditionExpression::parse("c").unwrap());
    }

    #[test]
    fn test_adf_to_bn_simple() {
        // Create a simple ADF
        let mut adf = AdfExpressions::new();
        let stmt_a = Statement::from("a");
        let stmt_b = Statement::from("b");

        adf.update_condition(
            stmt_a.clone(),
            ConditionExpression::statement(stmt_b.clone()),
        );
        adf.update_condition(
            stmt_b.clone(),
            ConditionExpression::statement(stmt_a.clone()),
        );

        let bn = adf_to_bn(&adf);

        // Check that all variables are present
        assert_eq!(bn.num_vars(), 2);

        // Check update functions
        let var_a = bn.as_graph().find_variable("a").unwrap();
        let var_b = bn.as_graph().find_variable("b").unwrap();

        let update_a = bn.get_update_function(var_a).as_ref().unwrap();
        assert!(matches!(update_a, FnUpdate::Var(_)));

        let update_b = bn.get_update_function(var_b).as_ref().unwrap();
        assert!(matches!(update_b, FnUpdate::Var(_)));
    }

    #[test]
    fn test_roundtrip_conversion() {
        // Create a Boolean network
        let bn1 = BooleanNetwork::try_from_bnet("a, b & c\nb, !a\nc, true").unwrap();

        // Convert to ADF and back
        let adf = bn_to_adf(&bn1);
        let bn2 = adf_to_bn(&adf);

        // Check that the networks are equivalent
        assert_eq!(bn1.num_vars(), bn2.num_vars());

        for var1 in bn1.variables() {
            let name = bn1.get_variable_name(var1);
            let var2 = bn2.as_graph().find_variable(name).unwrap();

            let update1 = bn1.get_update_function(var1);
            let update2 = bn2.get_update_function(var2);

            // Compare string representations (since FnUpdate doesn't implement Eq)
            match (update1, update2) {
                (Some(u1), Some(u2)) => {
                    assert_eq!(u1.to_string(&bn1), u2.to_string(&bn2));
                }
                (None, None) => {}
                _ => panic!("Update functions don't match for variable {}", name),
            }
        }
    }

    #[test]
    fn test_numeric_identifier_conversion() {
        let mut adf = AdfExpressions::new();
        let stmt_1 = Statement::from("1");
        let stmt_2 = Statement::from("2");

        adf.update_condition(
            stmt_1.clone(),
            ConditionExpression::statement(stmt_2.clone()),
        );
        adf.add_statement(stmt_2);

        // Convert to BN - numeric names are actually valid in BooleanNetwork
        let bn = adf_to_bn(&adf);

        assert!(bn.as_graph().find_variable("1").is_some());
        assert!(bn.as_graph().find_variable("2").is_some());
    }

    #[test]
    #[should_panic(expected = "explicit parameters")]
    fn test_network_with_parameters_rejected() {
        // Create a network with a parameter using the API
        let mut rg = RegulatoryGraph::new(vec!["a".to_string(), "b".to_string()]);
        rg.add_regulation("b", "a", true, None).unwrap();

        let mut bn = BooleanNetwork::new(rg);

        // Add a parameter and use it in an update function
        let param = bn.add_parameter("f", 1).unwrap();
        let var_a = bn.as_graph().find_variable("a").unwrap();
        let var_b = bn.as_graph().find_variable("b").unwrap();

        // Create update function that uses the parameter
        let fn_with_param = FnUpdate::Param(param, vec![FnUpdate::Var(var_b)]);
        bn.set_update_function(var_a, Some(fn_with_param)).unwrap();

        // Should panic for networks with parameters
        bn_to_adf(&bn);
    }
}
