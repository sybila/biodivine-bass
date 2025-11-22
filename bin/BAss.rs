use biodivine_adf_solver::bdd_solver::{
    DynamicBddSolver, NaiveGreedySolver, NaiveGreedySolverShared, QuadraticGreedySolver,
    QuadraticGreedySolverShared,
};
use biodivine_adf_solver::{
    AdfBdds, AdfExpressions, AdfInterpretationSolver, DynamicModelSet, ModelSet,
};
use cancel_this::Cancellable;
use clap::Parser;
use std::process;

#[derive(Parser, Debug)]
#[command(name = "BAss")]
#[command(about = "BDD-based ADF symbolic solver (BAss)", long_about = None)]
struct Args {
    /// Problem type to solve
    #[arg(value_enum)]
    problem_type: ProblemType,

    /// BDD solver backend to use
    #[arg(value_enum)]
    solver: BddSolverType,

    /// Path to the ADF input file
    input_file: String,
}

#[derive(clap::ValueEnum, Clone, Debug)]
enum ProblemType {
    /// Two-valued complete interpretations
    #[value(name = "two-valued-complete", aliases = ["2vc", "two_valued_complete"])]
    TwoValuedComplete,
    /// Three-valued admissible interpretations
    #[value(name = "admissible", aliases = ["adm"])]
    Admissible,
    #[value(name = "complete", aliases = ["com"])]
    Complete,
}

#[derive(clap::ValueEnum, Clone, Debug)]
enum BddSolverType {
    /// Naive greedy solver (split BDD representation)
    #[value(name = "naive-greedy", aliases = ["ng", "naive_greedy"])]
    NaiveGreedy,
    /// Naive greedy solver (shared BDD representation)
    #[value(name = "naive-greedy-shared", aliases = ["ngs", "naive_greedy_shared"])]
    NaiveGreedyShared,
    /// Quadratic greedy solver (split BDD representation)
    #[value(name = "quadratic-greedy", aliases = ["qg", "quadratic_greedy"])]
    QuadraticGreedy,
    /// Quadratic greedy solver (shared BDD representation)
    #[value(
        name = "quadratic-greedy-shared",
        aliases = ["qgs", "quadratic_greedy_shared"]
    )]
    QuadraticGreedyShared,
}

impl From<BddSolverType> for DynamicBddSolver {
    fn from(value: BddSolverType) -> Self {
        match value {
            BddSolverType::NaiveGreedy => Box::new(NaiveGreedySolver),
            BddSolverType::NaiveGreedyShared => Box::new(NaiveGreedySolverShared),
            BddSolverType::QuadraticGreedy => Box::new(QuadraticGreedySolver),
            BddSolverType::QuadraticGreedyShared => Box::new(QuadraticGreedySolverShared),
        }
    }
}

fn main() {
    env_logger::init();

    let args = Args::parse();

    // Load the ADF file
    let mut adf_expressions = match AdfExpressions::parse_file(&args.input_file) {
        Ok(adf) => adf,
        Err(e) => {
            eprintln!("Error parsing ADF file: {}", e);
            process::exit(1);
        }
    };

    // Fix any missing statements
    adf_expressions.fix_missing_statements();

    // Convert AdfExpressions to AdfBdds
    let adf_bdds = match AdfBdds::try_from_expressions(&adf_expressions) {
        Ok(bdds) => bdds,
        Err(_) => {
            eprintln!("Error: Conversion to BDD encoding was cancelled");
            process::exit(1);
        }
    };

    let bdd_solver: DynamicBddSolver = args.solver.into();
    let interpretation_solver = AdfInterpretationSolver::new(bdd_solver);

    // Solve based on problem type
    let model_set = match args.problem_type {
        ProblemType::TwoValuedComplete => {
            process_result(interpretation_solver.solve_complete_two_valued(&adf_bdds))
        }
        ProblemType::Admissible => {
            process_result(interpretation_solver.solve_admissible(&adf_bdds))
        }
        ProblemType::Complete => process_result(interpretation_solver.solve_complete(&adf_bdds)),
    };

    // Output the model count
    let count = model_set.model_count();
    println!("{}", count);
}

fn process_result<T: ModelSet + 'static>(result: Cancellable<T>) -> DynamicModelSet {
    match result {
        Ok(model_set) => Box::new(model_set),
        Err(_) => {
            eprintln!("Error: Solving was cancelled");
            process::exit(1);
        }
    }
}
