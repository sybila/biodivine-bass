use cancel_this::Cancellable;
use ruddy::split::Bdd;

mod naive_greedy;
mod naive_greedy_shared;
mod quadratic_greedy;
mod quadratic_greedy_shared;

pub use naive_greedy::NaiveGreedySolver;
pub use naive_greedy_shared::NaiveGreedySolverShared;

pub use quadratic_greedy::QuadraticGreedySolver;
pub use quadratic_greedy_shared::QuadraticGreedySolverShared;

/// A trait implemented by algorithms which can perform merging of BDDs in some semi-optimized
/// fashion. For all other intents and purposes, this only computes
/// the conjunction of the given constraints.
pub trait BddSolver {
    fn solve_conjunction(constraints: &[Bdd]) -> Cancellable<Bdd>;
}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper function to create simple test BDDs
    fn make_test_bdds() -> Vec<Bdd> {
        // Create a few simple BDDs for testing
        let var0 = ruddy::VariableId::new(0);
        let var1 = ruddy::VariableId::new(1);
        let var2 = ruddy::VariableId::new(2);

        vec![
            Bdd::new_literal(var0, true), // x0
            Bdd::new_literal(var1, true), // x1
            Bdd::new_literal(var2, true), // x2
        ]
    }

    fn make_contradictory_bdds() -> Vec<Bdd> {
        let var0 = ruddy::VariableId::new(0);

        vec![
            Bdd::new_literal(var0, true),  // x0
            Bdd::new_literal(var0, false), // !x0
        ]
    }

    #[test]
    fn test_naive_greedy_solver_empty() {
        let result = NaiveGreedySolver::solve_conjunction(&[]).unwrap();
        assert!(result.is_true());
    }

    #[test]
    fn test_naive_greedy_solver_single() {
        let bdds = vec![Bdd::new_literal(ruddy::VariableId::new(0), true)];
        let result = NaiveGreedySolver::solve_conjunction(&bdds).unwrap();
        assert!(result.structural_eq(&bdds[0]));
    }

    #[test]
    fn test_naive_greedy_solver_simple() {
        let bdds = make_test_bdds();
        let result = NaiveGreedySolver::solve_conjunction(&bdds).unwrap();

        // Result should be conjunction of all three
        let expected = bdds[0].and(&bdds[1]).and(&bdds[2]);
        assert!(result.structural_eq(&expected));
    }

    #[test]
    fn test_naive_greedy_solver_contradiction() {
        let bdds = make_contradictory_bdds();
        let result = NaiveGreedySolver::solve_conjunction(&bdds).unwrap();
        assert!(result.is_false());
    }

    #[test]
    fn test_naive_greedy_solver_with_true() {
        let var0 = ruddy::VariableId::new(0);
        let bdds = vec![Bdd::new_true(), Bdd::new_literal(var0, true)];
        let result = NaiveGreedySolver::solve_conjunction(&bdds).unwrap();

        // True AND x0 = x0
        assert!(result.structural_eq(&bdds[1]));
    }

    #[test]
    fn test_naive_greedy_solver_with_false() {
        let var0 = ruddy::VariableId::new(0);
        let bdds = vec![Bdd::new_false(), Bdd::new_literal(var0, true)];
        let result = NaiveGreedySolver::solve_conjunction(&bdds).unwrap();
        assert!(result.is_false());
    }

    #[test]
    fn test_quadratic_greedy_solver_empty() {
        let result = QuadraticGreedySolver::solve_conjunction(&[]).unwrap();
        assert!(result.is_true());
    }

    #[test]
    fn test_quadratic_greedy_solver_single() {
        let bdds = vec![Bdd::new_literal(ruddy::VariableId::new(0), true)];
        let result = QuadraticGreedySolver::solve_conjunction(&bdds).unwrap();
        assert!(result.structural_eq(&bdds[0]));
    }

    #[test]
    fn test_quadratic_greedy_solver_simple() {
        let bdds = make_test_bdds();
        let result = QuadraticGreedySolver::solve_conjunction(&bdds).unwrap();

        // Result should be conjunction of all three
        let expected = bdds[0].and(&bdds[1]).and(&bdds[2]);
        assert!(result.structural_eq(&expected));
    }

    #[test]
    fn test_quadratic_greedy_solver_contradiction() {
        let bdds = make_contradictory_bdds();
        let result = QuadraticGreedySolver::solve_conjunction(&bdds).unwrap();
        assert!(result.is_false());
    }

    #[test]
    fn test_quadratic_greedy_solver_with_true() {
        let var0 = ruddy::VariableId::new(0);
        let bdds = vec![Bdd::new_true(), Bdd::new_literal(var0, true)];
        let result = QuadraticGreedySolver::solve_conjunction(&bdds).unwrap();
        assert!(result.structural_eq(&bdds[1]));
    }

    #[test]
    fn test_quadratic_greedy_solver_with_false() {
        let var0 = ruddy::VariableId::new(0);
        let bdds = vec![Bdd::new_false(), Bdd::new_literal(var0, true)];
        let result = QuadraticGreedySolver::solve_conjunction(&bdds).unwrap();
        assert!(result.is_false());
    }

    #[test]
    fn test_naive_greedy_solver_shared_empty() {
        let result = NaiveGreedySolverShared::solve_conjunction(&[]).unwrap();
        assert!(result.is_true());
    }

    #[test]
    fn test_naive_greedy_solver_shared_single() {
        let bdds = vec![Bdd::new_literal(ruddy::VariableId::new(0), true)];
        let result = NaiveGreedySolverShared::solve_conjunction(&bdds).unwrap();
        assert!(result.structural_eq(&bdds[0]));
    }

    #[test]
    fn test_naive_greedy_solver_shared_simple() {
        let bdds = make_test_bdds();
        let result = NaiveGreedySolverShared::solve_conjunction(&bdds).unwrap();

        // Result should be conjunction of all three
        let expected = bdds[0].and(&bdds[1]).and(&bdds[2]);
        assert!(result.structural_eq(&expected));
    }

    #[test]
    fn test_naive_greedy_solver_shared_contradiction() {
        let bdds = make_contradictory_bdds();
        let result = NaiveGreedySolverShared::solve_conjunction(&bdds).unwrap();
        assert!(result.is_false());
    }

    #[test]
    fn test_naive_greedy_solver_shared_with_true() {
        let var0 = ruddy::VariableId::new(0);
        let bdds = vec![Bdd::new_true(), Bdd::new_literal(var0, true)];
        let result = NaiveGreedySolverShared::solve_conjunction(&bdds).unwrap();
        assert!(result.structural_eq(&bdds[1]));
    }

    #[test]
    fn test_naive_greedy_solver_shared_with_false() {
        let var0 = ruddy::VariableId::new(0);
        let bdds = vec![Bdd::new_false(), Bdd::new_literal(var0, true)];
        let result = NaiveGreedySolverShared::solve_conjunction(&bdds).unwrap();
        assert!(result.is_false());
    }

    #[test]
    fn test_quadratic_greedy_solver_shared_empty() {
        let result = QuadraticGreedySolverShared::solve_conjunction(&[]).unwrap();
        assert!(result.is_true());
    }

    #[test]
    fn test_quadratic_greedy_solver_shared_single() {
        let bdds = vec![Bdd::new_literal(ruddy::VariableId::new(0), true)];
        let result = QuadraticGreedySolverShared::solve_conjunction(&bdds).unwrap();
        assert!(result.structural_eq(&bdds[0]));
    }

    #[test]
    fn test_quadratic_greedy_solver_shared_simple() {
        let bdds = make_test_bdds();
        let result = QuadraticGreedySolverShared::solve_conjunction(&bdds).unwrap();

        // Result should be conjunction of all three
        let expected = bdds[0].and(&bdds[1]).and(&bdds[2]);
        assert!(result.structural_eq(&expected));
    }

    #[test]
    fn test_quadratic_greedy_solver_shared_contradiction() {
        let bdds = make_contradictory_bdds();
        let result = QuadraticGreedySolverShared::solve_conjunction(&bdds).unwrap();
        assert!(result.is_false());
    }

    #[test]
    fn test_quadratic_greedy_solver_shared_with_true() {
        let var0 = ruddy::VariableId::new(0);
        let bdds = vec![Bdd::new_true(), Bdd::new_literal(var0, true)];
        let result = QuadraticGreedySolverShared::solve_conjunction(&bdds).unwrap();
        assert!(result.structural_eq(&bdds[1]));
    }

    #[test]
    fn test_quadratic_greedy_solver_shared_with_false() {
        let var0 = ruddy::VariableId::new(0);
        let bdds = vec![Bdd::new_false(), Bdd::new_literal(var0, true)];
        let result = QuadraticGreedySolverShared::solve_conjunction(&bdds).unwrap();
        assert!(result.is_false());
    }

    // Test equivalence between solvers
    #[test]
    fn test_solvers_equivalence_simple() {
        let bdds = make_test_bdds();

        let result_naive = NaiveGreedySolver::solve_conjunction(&bdds).unwrap();
        let result_quadratic = QuadraticGreedySolver::solve_conjunction(&bdds).unwrap();
        let result_naive_shared = NaiveGreedySolverShared::solve_conjunction(&bdds).unwrap();
        let result_quadratic_shared =
            QuadraticGreedySolverShared::solve_conjunction(&bdds).unwrap();

        // All solvers should produce structurally equivalent results
        assert!(result_naive.structural_eq(&result_quadratic));
        assert!(result_naive.structural_eq(&result_naive_shared));
        assert!(result_naive.structural_eq(&result_quadratic_shared));
    }

    #[test]
    fn test_solvers_equivalence_complex() {
        // Create a more complex set of BDDs
        let var0 = ruddy::VariableId::new(0);
        let var1 = ruddy::VariableId::new(1);
        let var2 = ruddy::VariableId::new(2);
        let var3 = ruddy::VariableId::new(3);

        let bdds = vec![
            Bdd::new_literal(var0, true).or(&Bdd::new_literal(var1, true)),
            Bdd::new_literal(var1, false).or(&Bdd::new_literal(var2, true)),
            Bdd::new_literal(var2, true).and(&Bdd::new_literal(var3, false)),
        ];

        let result_naive = NaiveGreedySolver::solve_conjunction(&bdds).unwrap();
        let result_quadratic = QuadraticGreedySolver::solve_conjunction(&bdds).unwrap();
        let result_naive_shared = NaiveGreedySolverShared::solve_conjunction(&bdds).unwrap();
        let result_quadratic_shared =
            QuadraticGreedySolverShared::solve_conjunction(&bdds).unwrap();

        // All solvers should produce structurally equivalent results
        assert!(result_naive.structural_eq(&result_quadratic));
        assert!(result_naive.structural_eq(&result_naive_shared));
        assert!(result_naive.structural_eq(&result_quadratic_shared));
    }

    #[test]
    fn test_solvers_with_many_constraints() {
        // Test with more constraints
        let mut bdds = Vec::new();
        for i in 0..10 {
            let var = ruddy::VariableId::new(i);
            bdds.push(Bdd::new_literal(var, true));
        }

        let result_naive = NaiveGreedySolver::solve_conjunction(&bdds).unwrap();
        let result_quadratic = QuadraticGreedySolver::solve_conjunction(&bdds).unwrap();
        let result_naive_shared = NaiveGreedySolverShared::solve_conjunction(&bdds).unwrap();
        let result_quadratic_shared =
            QuadraticGreedySolverShared::solve_conjunction(&bdds).unwrap();

        // All solvers should produce structurally equivalent results
        assert!(result_naive.structural_eq(&result_quadratic));
        assert!(result_naive.structural_eq(&result_naive_shared));
        assert!(result_naive.structural_eq(&result_quadratic_shared));

        // Verify the result is the expected conjunction
        let mut expected = Bdd::new_true();
        for bdd in &bdds {
            expected = expected.and(bdd);
        }
        assert!(result_naive.structural_eq(&expected));
    }

    // Note: Cancellation is tested implicitly through the is_cancelled!() checks
    // in the solver implementations. The solvers will return Err when cancelled.
}
