use biodivine_adf_solver::AdfExpressions;
use biodivine_lib_param_bn::BooleanNetwork;
use std::path::PathBuf;

fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    let path = args[1].as_str();
    let adf = AdfExpressions::parse_file(path).unwrap();
    let bn = BooleanNetwork::from(&adf);

    let mut path = PathBuf::from(path);
    path.set_extension("bnet");
    std::fs::write(&path, bn.to_bnet(true).unwrap()).unwrap();
}
