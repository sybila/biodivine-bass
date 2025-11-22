use crate::bdd_solver::BddSolver;
use cancel_this::Cancellable;
use log::debug;
use ruddy::split::Bdd;

/// A quadratic greedy solver using split BDD representation.
///
/// This solver implements the algorithm from lib-param-bn's `_symbolic_merge`:
/// 1. Start with the smallest BDD as the initial result
/// 2. For each iteration, try merging the result with each remaining constraint
/// 3. Pick the constraint that produces the smallest result
/// 4. Continue until all constraints are merged
///
/// This requires O(n²) merge attempts but often produces smaller intermediate BDDs.
#[derive(Default, Clone, PartialEq, Eq, Hash, Debug)]
pub struct QuadraticGreedySolver;

impl BddSolver for QuadraticGreedySolver {
    fn solve_conjunction(&self, constraints: &[Bdd]) -> Cancellable<Bdd> {
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

            debug!(
                "Merging BDDs: {} constraints remaining, result BDD size: {} nodes",
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
