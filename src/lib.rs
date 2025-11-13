mod adf_bdds;
mod adf_expressions;
mod condition_expression;
mod condition_expression_parser;
mod condition_expression_writer;
mod statement;

pub use adf_bdds::AdfBdds;
pub use adf_expressions::AdfExpressions;
use cancel_this::Cancellable;
pub use condition_expression::ConditionExpression;
use ruddy::split::Bdd;
pub use statement::Statement;

pub trait BddSolver {
    fn solve_conjunction(constraints: &[Bdd]) -> Cancellable<Bdd>;
}

/// A naive greedy solver that repeatedly merges the two smallest BDDs using split BDD representation.
///
/// The algorithm sorts the BDDs by size and always merges the two smallest ones until
/// only one remains. This is a simple greedy approach that doesn't require quadratic
/// comparisons but may not always produce optimal intermediate BDD sizes.
pub struct NaiveGreedySolver;

impl BddSolver for NaiveGreedySolver {
    fn solve_conjunction(constraints: &[Bdd]) -> Cancellable<Bdd> {
        use cancel_this::is_cancelled;

        // Handle edge cases
        if constraints.is_empty() {
            return Ok(Bdd::new_true());
        }
        if constraints.len() == 1 {
            return Ok(constraints[0].clone());
        }

        // Create a working set of BDDs that we'll merge
        let mut to_merge: Vec<Bdd> = constraints.to_vec();

        while to_merge.len() > 1 {
            // Check for cancellation
            is_cancelled!()?;

            // Sort by size (ascending)
            to_merge.sort_by_key(|bdd| bdd.node_count());

            println!(
                "[{} remaining] Largest BDD: {}",
                to_merge.len(),
                to_merge.last().unwrap().node_count()
            );

            // Take the two smallest
            let smallest1 = to_merge.remove(0);
            let smallest2 = to_merge.remove(0);

            // Merge them
            let merged = smallest1.and(&smallest2);

            // Early termination if we reach false
            if merged.is_false() {
                return Ok(Bdd::new_false());
            }

            // Add the result back
            to_merge.push(merged);
        }

        Ok(to_merge.into_iter().next().unwrap())
    }
}

/// A quadratic greedy solver using split BDD representation.
///
/// This solver implements the algorithm from lib-param-bn's `_symbolic_merge`:
/// 1. Start with the smallest BDD as the initial result
/// 2. For each iteration, try merging the result with each remaining constraint
/// 3. Pick the constraint that produces the smallest result
/// 4. Continue until all constraints are merged
///
/// This requires O(n²) merge attempts but often produces smaller intermediate BDDs.
pub struct QuadraticGreedySolver;

impl BddSolver for QuadraticGreedySolver {
    fn solve_conjunction(constraints: &[Bdd]) -> Cancellable<Bdd> {
        use cancel_this::is_cancelled;

        // Handle edge cases
        if constraints.is_empty() {
            return Ok(Bdd::new_true());
        }
        if constraints.len() == 1 {
            return Ok(constraints[0].clone());
        }

        // Find the index of the smallest BDD to use as the initial result
        let mut smallest_idx = 0;
        let mut smallest_size = constraints[0].node_count();
        for (i, bdd) in constraints.iter().enumerate().skip(1) {
            let size = bdd.node_count();
            if size < smallest_size {
                smallest_size = size;
                smallest_idx = i;
            }
        }

        // Start with the smallest BDD as our result
        let mut result = constraints[smallest_idx].clone();

        // Track which constraints we still need to merge
        let mut remaining: Vec<(usize, Bdd)> = constraints
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != smallest_idx)
            .map(|(i, bdd)| (i, bdd.clone()))
            .collect();

        // Iteratively merge constraints
        while !remaining.is_empty() {
            // Check for cancellation
            is_cancelled!()?;

            let mut best_idx = 0;
            let mut best_size = usize::MAX;
            let mut best_result = Bdd::new_false();

            // Try merging with each remaining constraint
            for (i, (_, candidate)) in remaining.iter().enumerate() {
                is_cancelled!()?;

                let merged = result.and(candidate);
                let size = merged.node_count();

                if size < best_size {
                    best_size = size;
                    best_idx = i;
                    best_result = merged;
                }
            }

            // Update result with the best merge
            result = best_result;

            println!(
                "[{} remaining] Result BDD: {}",
                remaining.len(),
                result.node_count()
            );

            // Remove the merged constraint from remaining
            remaining.remove(best_idx);

            // Early termination if we reach false
            if result.is_false() {
                return Ok(Bdd::new_false());
            }
        }

        Ok(result)
    }
}

/// A naive greedy solver using shared BDD representation.
///
/// This is equivalent to `NaiveGreedySolver` but uses a shared BDD manager
/// internally. The input and output are still split BDDs for API consistency.
pub struct NaiveGreedySolverShared;

impl BddSolver for NaiveGreedySolverShared {
    fn solve_conjunction(constraints: &[Bdd]) -> Cancellable<Bdd> {
        use cancel_this::is_cancelled;
        use ruddy::shared::BddManager;

        // Handle edge cases
        if constraints.is_empty() {
            return Ok(Bdd::new_true());
        }
        if constraints.len() == 1 {
            return Ok(constraints[0].clone());
        }

        // Check for any false constraints (early termination)
        if constraints.iter().any(|bdd| bdd.is_false()) {
            return Ok(Bdd::new_false());
        }

        // Filter out true constraints as they don't affect the conjunction
        let filtered_constraints: Vec<&Bdd> =
            constraints.iter().filter(|bdd| !bdd.is_true()).collect();

        // If all constraints were true, return true
        if filtered_constraints.is_empty() {
            return Ok(Bdd::new_true());
        }

        // If only one constraint remains after filtering, return it
        if filtered_constraints.len() == 1 {
            return Ok(filtered_constraints[0].clone());
        }

        // Create a shared BDD manager and import all non-terminal constraints
        let mut manager = BddManager::new();
        let mut to_merge: Vec<ruddy::shared::Bdd> = filtered_constraints
            .iter()
            .map(|bdd| manager.import_split(bdd))
            .collect();

        while to_merge.len() > 1 {
            is_cancelled!()?;

            // Sort by size (ascending)
            to_merge.sort_by_key(|bdd| manager.node_count(bdd));

            // Take the two smallest
            let smallest1 = to_merge.remove(0);
            let smallest2 = to_merge.remove(0);

            // Merge them
            let merged = manager.and(&smallest1, &smallest2);

            // Early termination if we reach false
            if merged.is_false() {
                return Ok(Bdd::new_false());
            }

            // Add the result back
            to_merge.push(merged);
        }

        let result = to_merge.into_iter().next().unwrap();
        Ok(manager.export_split(&result))
    }
}

/// A quadratic greedy solver using shared BDD representation.
///
/// This is equivalent to `QuadraticGreedySolver` but uses a shared BDD manager
/// internally. The input and output are still split BDDs for API consistency.
pub struct QuadraticGreedySolverShared;

impl BddSolver for QuadraticGreedySolverShared {
    fn solve_conjunction(constraints: &[Bdd]) -> Cancellable<Bdd> {
        use cancel_this::is_cancelled;
        use ruddy::shared::BddManager;

        // Handle edge cases
        if constraints.is_empty() {
            return Ok(Bdd::new_true());
        }
        if constraints.len() == 1 {
            return Ok(constraints[0].clone());
        }

        // Check for any false constraints (early termination)
        if constraints.iter().any(|bdd| bdd.is_false()) {
            return Ok(Bdd::new_false());
        }

        // Filter out true constraints as they don't affect the conjunction
        let filtered_constraints: Vec<&Bdd> =
            constraints.iter().filter(|bdd| !bdd.is_true()).collect();

        // If all constraints were true, return true
        if filtered_constraints.is_empty() {
            return Ok(Bdd::new_true());
        }

        // If only one constraint remains after filtering, return it
        if filtered_constraints.len() == 1 {
            return Ok(filtered_constraints[0].clone());
        }

        // Create a shared BDD manager and import all non-terminal constraints
        let mut manager = BddManager::new();
        let shared_bdds: Vec<ruddy::shared::Bdd> = filtered_constraints
            .iter()
            .map(|bdd| manager.import_split(bdd))
            .collect();

        // Find the smallest BDD
        let mut smallest_idx = 0;
        let mut smallest_size = manager.node_count(&shared_bdds[0]);
        for (i, bdd) in shared_bdds.iter().enumerate().skip(1) {
            let size = manager.node_count(bdd);
            if size < smallest_size {
                smallest_size = size;
                smallest_idx = i;
            }
        }

        // Start with the smallest as result
        let mut result = shared_bdds[smallest_idx].clone();

        // Track remaining constraints
        let mut remaining: Vec<(usize, ruddy::shared::Bdd)> = shared_bdds
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != smallest_idx)
            .map(|(i, bdd)| (i, bdd.clone()))
            .collect();

        while !remaining.is_empty() {
            is_cancelled!()?;

            let mut best_idx = 0;
            let mut best_size = usize::MAX;
            let mut best_result = manager.new_bdd_false();

            // Try merging with each remaining constraint
            for (i, (_, candidate)) in remaining.iter().enumerate() {
                is_cancelled!()?;

                let merged = manager.and(&result, candidate);
                let size = manager.node_count(&merged);

                if size < best_size {
                    best_size = size;
                    best_idx = i;
                    best_result = merged;
                }
            }

            // Update result
            result = best_result;

            // Remove the merged constraint
            remaining.remove(best_idx);

            // Early termination
            if result.is_false() {
                return Ok(Bdd::new_false());
            }

            println!(
                "[{} remaining] Largest BDD: {}",
                remaining.len(),
                manager.node_count(&result)
            );
        }

        Ok(manager.export_split(&result))
    }
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
