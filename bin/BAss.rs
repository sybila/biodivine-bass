use biodivine_bass::bdd_solver::{
    DynamicBddSolver, NaiveGreedySolver, NaiveGreedySolverShared, QuadraticGreedySolver,
    QuadraticGreedySolverShared,
};
use biodivine_bass::{AdfBdds, AdfExpressions, AdfInterpretationSolver, ModelSet, Statement};
use cancel_this::Cancellable;
use clap::Parser;
use log::info;
use std::collections::BTreeMap;
use std::process;

#[derive(Parser, Debug)]
#[command(name = "BAss")]
#[command(about = "BDD-based ADF symbolic solver (BAss)", long_about = None)]
struct Args {
    /// Two-valued complete interpretations (alias: -2v)
    #[arg(long = "two-valued", alias = "2v", group = "problem", action = clap::ArgAction::SetTrue)]
    two_valued: bool,

    /// Stable two-valued interpretations (alias: -stb)
    #[arg(long = "stable", alias = "stb", group = "problem", action = clap::ArgAction::SetTrue)]
    stable: bool,

    /// Three-valued admissible interpretations (alias: -adm)
    #[arg(long = "admissible", alias = "adm", group = "problem", action = clap::ArgAction::SetTrue)]
    admissible: bool,

    /// Three-valued complete interpretations (alias: -com)
    #[arg(long = "complete", alias = "com", group = "problem", action = clap::ArgAction::SetTrue)]
    complete: bool,

    /// Preferred interpretations (alias: -prf)
    #[arg(long = "preferred", alias = "prf", group = "problem", action = clap::ArgAction::SetTrue)]
    preferred: bool,

    /// BDD solver backend to use
    #[arg(
        long,
        value_enum,
        default_value = "quadratic-greedy",
        require_equals = true
    )]
    solver: BddSolverType,

    /// Number of models to enumerate from the result (default: all)
    #[arg(long, short = 'n')]
    solution_count: Option<usize>,

    /// File path to serialize BDD result in ruddy (i.e. biodivine-lib-bdd) string format
    #[arg(long, require_equals = true)]
    output_bdd: Option<String>,

    /// Verbose logging level (flag sets to 'info', or specify: trace, debug, info, warn, error)
    #[arg(long, short, num_args = 0..=1, default_missing_value = "info", require_equals = true)]
    verbose: Option<String>,

    /// Path to the ADF input file (must be last argument)
    #[arg(index = 1)]
    input_file: String,
}

impl Args {
    /// Get the problem type from the flags
    fn problem_type(&self) -> ProblemType {
        if self.two_valued {
            ProblemType::TwoValuedComplete
        } else if self.stable {
            ProblemType::Stable
        } else if self.admissible {
            ProblemType::Admissible
        } else if self.complete {
            ProblemType::Complete
        } else if self.preferred {
            ProblemType::Preferred
        } else {
            // This should never happen if clap validation works correctly
            panic!("No problem type specified")
        }
    }
}

/// Preprocess command line arguments to handle -2v style short options
fn preprocess_args() -> Args {
    let mut args: Vec<String> = std::env::args().collect();

    // Map of short multi-character options to their long forms
    let short_opts = vec![
        ("-2v", "--two-valued"),
        ("-stb", "--stable"),
        ("-adm", "--admissible"),
        ("-com", "--complete"),
        ("-prf", "--preferred"),
    ];

    // Replace -2v style options with --2v style (which clap will recognize via aliases)
    for (short, long) in short_opts {
        for arg in &mut args {
            if arg == short {
                *arg = long.to_string();
            }
        }
    }

    Args::parse_from(args)
}

#[derive(clap::ValueEnum, Clone, Debug)]
enum ProblemType {
    /// Two-valued complete interpretations
    #[value(name = "two-valued", aliases = ["2v"])]
    TwoValuedComplete,
    #[value(name = "stable", aliases = ["stb"])]
    Stable,
    /// Three-valued admissible interpretations
    #[value(name = "admissible", aliases = ["adm"])]
    Admissible,
    #[value(name = "complete", aliases = ["com"])]
    Complete,
    #[value(name = "preferred", aliases = ["prf"])]
    Preferred,
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
    // Preprocess arguments to handle -2v style short options
    let args = preprocess_args();

    // Handle verbose logging - if specified, override env_logger settings
    if let Some(ref log_level) = args.verbose {
        env_logger::Builder::from_default_env()
            .filter_level(match log_level.as_str() {
                "trace" => log::LevelFilter::Trace,
                "debug" => log::LevelFilter::Debug,
                "info" => log::LevelFilter::Info,
                "warn" => log::LevelFilter::Warn,
                "error" => log::LevelFilter::Error,
                _ => log::LevelFilter::Info,
            })
            .init();
    } else {
        env_logger::init();
    }

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

    let bdd_solver: DynamicBddSolver = args.solver.clone().into();
    let interpretation_solver = AdfInterpretationSolver::new(bdd_solver);

    // Solve based on problem type
    match args.problem_type() {
        ProblemType::TwoValuedComplete => process_result(
            interpretation_solver.solve_complete_two_valued(&adf_bdds),
            &args,
        ),
        ProblemType::Stable => process_result(
            interpretation_solver.solve_stable_two_valued(&adf_bdds),
            &args,
        ),
        ProblemType::Admissible => {
            process_result(interpretation_solver.solve_admissible(&adf_bdds), &args)
        }
        ProblemType::Complete => {
            process_result(interpretation_solver.solve_complete(&adf_bdds), &args)
        }
        ProblemType::Preferred => {
            process_result(interpretation_solver.solve_preferred(&adf_bdds), &args)
        }
    };
}

fn process_result<T: ModelSet + 'static>(result: Cancellable<T>, args: &Args) {
    match result {
        Ok(model_set) => {
            let total_count = model_set.model_count();
            info!("Solution count: {}", total_count);

            // Handle output BDD serialization if requested
            if let Some(ref output_path) = args.output_bdd {
                serialize_bdd_output(&model_set, output_path);
            }

            // Enumerate models up to solution_count limit
            let limit = args.solution_count.unwrap_or(usize::MAX);
            let mut count = 0;
            for x in model_set.iter() {
                if count >= limit {
                    break;
                }
                print_model(x);
                count += 1;
            }

            if (count as f64) < total_count {
                println!("... (showing {}/{} models)", count, total_count);
            }
        }
        Err(_) => {
            eprintln!("Error: Solving was cancelled");
            process::exit(1);
        }
    }
}

/// Serialize BDD result to file (stub for future implementation)
fn serialize_bdd_output<T: ModelSet + 'static>(model_set: &T, output_path: &str) {
    std::fs::write(output_path, model_set.symbolic_set().to_serialized_string())
        .expect("BDD serialization failed");
}

fn print_model(model: BTreeMap<Statement, Option<bool>>) {
    let strings = model
        .iter()
        .map(|(k, v)| {
            let v = match v {
                None => "u",
                Some(true) => "t",
                Some(false) => "f",
            };
            format!("{v}({k})")
        })
        .collect::<Vec<String>>();
    println!("{}", strings.join(" "))
}
