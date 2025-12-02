use biodivine_bass::AdfExpressions;
use biodivine_lib_param_bn::BooleanNetwork;
use std::path::PathBuf;

fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    let path = args[1].as_str();
    let bn = BooleanNetwork::try_from_file(path).unwrap();
    let adf = AdfExpressions::from(&bn);

    let mut path = PathBuf::from(path);
    path.set_extension("adf");
    std::fs::write(&path, adf.write()).unwrap();
}
