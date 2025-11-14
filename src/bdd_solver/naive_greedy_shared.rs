use crate::bdd_solver::BddSolver;
use cancel_this::Cancellable;
use ruddy::split::Bdd;

/// A naive greedy solver using shared BDD representation.
///
/// This is equivalent to [`crate::bdd_solver::NaiveGreedySolver`] but uses a shared BDD manager
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
