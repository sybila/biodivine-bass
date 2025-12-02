use biodivine_bass::{AdfExpressions, Statement};
use std::collections::BTreeMap;
use std::path::PathBuf;

fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    let path = args[1].as_str();
    let mut adf = AdfExpressions::parse_file(path).unwrap();

    let statements = adf.statements().cloned().collect::<Vec<_>>();
    assert!(statements.is_sorted());

    let first_rename_map = statements
        .iter()
        .map(|stmt| {
            let temp_name = Statement::from(format!("v_{}", stmt.label()));
            (stmt.clone(), temp_name)
        })
        .collect::<BTreeMap<_, _>>();

    adf.rename_statements(&first_rename_map).unwrap();

    let second_rename_map = statements
        .iter()
        .enumerate()
        .map(|(i, stmt)| {
            let temp_name = Statement::from(format!("v_{}", stmt.label()));
            let new_name = Statement::from(i);
            (temp_name, new_name)
        })
        .collect::<BTreeMap<_, _>>();

    adf.rename_statements(&second_rename_map).unwrap();

    adf.binarize_operators();

    let mut path = PathBuf::from(path);
    path.set_extension("normal.adf");
    std::fs::write(&path, adf.write()).unwrap();
}
