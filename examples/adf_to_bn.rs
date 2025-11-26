use ConditionExpressionNode::{
    And, Constant, Equivalence, ExclusiveOr, Implication, Negation, Or, Statement,
};
use biodivine_adf_solver::{AdfExpressions, ConditionExpression, ConditionExpressionNode};
use biodivine_lib_param_bn::BooleanNetwork;
use std::path::PathBuf;

fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    let path = args[1].as_str();
    let mut out_path = PathBuf::from(path);
    out_path.set_extension("bnet");
    let adf = AdfExpressions::parse_file(path).unwrap();

    let mut total_size = 0u64;
    for stmt in adf.statements() {
        if let Some(update) = adf.get_condition(stmt) {
            total_size += expected_size(update);
        }
    }

    if total_size > 10_000_000 {
        println!("Cannot convert {path}. Expected file size >100MB ({total_size})");
        std::fs::write(
            &out_path,
            format!("Conversion failed. File too large: {total_size}"),
        )
        .unwrap();
        out_path.set_extension("sbml");
        std::fs::write(
            &out_path,
            format!("Conversion failed. File too large: {total_size}"),
        )
        .unwrap();
        return;
    }

    let mut bn = BooleanNetwork::from(&adf);

    // Better normalized names for BN formats.
    for (i, var) in bn.variables().enumerate() {
        bn.as_graph_mut()
            .set_variable_name(var, format!("v_{i}").as_str())
            .unwrap();
    }

    std::fs::write(&out_path, bn.to_bnet(true).unwrap()).unwrap();
    out_path.set_extension("sbml");
    std::fs::write(&out_path, bn.to_sbml(None)).unwrap();
}

/// Helper function to estimate the size that the file will eventually have.
/// It's not actual number of bytes, that will likely be several times higher
/// because each variable/constant/operator add more than one byte to the overall file size.
fn expected_size(update: &ConditionExpression) -> u64 {
    match update.node() {
        Statement(_) | Constant(_) => 1,
        Negation(x) => 1 + expected_size(x),
        And(args) | Or(args) => args.iter().map(expected_size).sum::<u64>() + (args.len() as u64),
        Implication(x, y) => expected_size(x) + expected_size(y) + 1,
        Equivalence(x, y) | ExclusiveOr(x, y) => 2 * (expected_size(x) + expected_size(y)) + 3,
    }
}
