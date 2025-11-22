use crate::bdd_solver::BddSolver;
use cancel_this::Cancellable;
use log::debug;
use ruddy::split::Bdd;

/// A naive greedy solver that repeatedly merges the two smallest BDDs using split BDD representation.
///
/// The algorithm sorts the BDDs by size and always merges the two smallest ones until
/// only one remains. This is a simple greedy approach that doesn't require quadratic
/// comparisons but may not always produce optimal intermediate BDD sizes.
#[derive(Default, Clone, PartialEq, Eq, Hash, Debug)]
pub struct NaiveGreedySolver;

impl BddSolver for NaiveGreedySolver {
    fn solve_conjunction(&self, constraints: &[Bdd]) -> Cancellable<Bdd> {
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

            debug!(
                "Merging BDDs: {} constraints remaining, largest BDD size: {} nodes",
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
