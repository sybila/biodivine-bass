use crate::bdd_solver::BddSolver;
use cancel_this::Cancellable;
use log::debug;
use ruddy::split::Bdd;

/// A quadratic greedy solver using shared BDD representation.
///
/// This is equivalent to [`crate::bdd_solver::QuadraticGreedySolver`] but uses a shared BDD manager
/// internally. The input and output are still split BDDs for API consistency.
#[derive(Default, Clone, PartialEq, Eq, Hash, Debug)]
pub struct QuadraticGreedySolverShared;

impl BddSolver for QuadraticGreedySolverShared {
    fn solve_conjunction(&self, constraints: &[Bdd]) -> Cancellable<Bdd> {
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

            debug!(
                "Merging BDDs: {} constraints remaining, result BDD size: {} nodes",
                remaining.len(),
                manager.node_count(&result)
            );
        }

        Ok(manager.export_split(&result))
    }
}
