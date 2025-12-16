use crate::bdd_solver::{BddSolver, DynamicBddSolver};
use cancel_this::{Cancellable, is_cancelled};
use log::{debug, info, trace};
use ruddy::split::Bdd;

/// A [`BddSolver`] that delegates to a specific solver instance but first performs unification
/// of constraints that are guaranteed to never increase the size of the initial problem.
///
/// Note that this unification procedure is quadratic, but since the constraints are often
/// initially very small, this is typically an acceptable price to pay for the reduced complexity
/// later on in the computation.
pub struct ConstraintUnificationSolver(DynamicBddSolver);

impl From<DynamicBddSolver> for ConstraintUnificationSolver {
    fn from(value: DynamicBddSolver) -> Self {
        ConstraintUnificationSolver(value)
    }
}

impl BddSolver for ConstraintUnificationSolver {
    fn solve_conjunction(&self, constraints: &[Bdd]) -> Cancellable<Bdd> {
        info!(
            "Starting constraint unification with {} constraints using {} BDD nodes.",
            constraints.len(),
            constraints.iter().map(|it| it.node_count()).sum::<usize>()
        );

        let mut to_unify = constraints.to_vec();
        let mut cannot_unify = Vec::new();

        while !to_unify.is_empty() {
            is_cancelled!()?;

            // This is a bit wasteful but ultimately should be negligible
            // compared to the BDD operations.
            to_unify.sort_by_cached_key(|x| x.node_count());
            to_unify.reverse();

            let try_unify = to_unify
                .pop()
                .expect("Correctness violation: Vector must be non-empty.");

            let mut best_i = 0;
            let mut best_size = usize::MAX;

            for (i, second) in to_unify.iter().enumerate() {
                is_cancelled!()?;

                let unified = try_unify.and(second);
                let is_better = unified.node_count() < best_size;
                let is_acceptable =
                    unified.node_count() - 2 <= try_unify.node_count() + second.node_count() - 4;

                trace!(
                    "Unification with constraint #{i}: {} BDD nodes; is acceptable? {is_acceptable}; is new best? {is_better}.",
                    unified.node_count()
                );

                if is_acceptable && is_better {
                    best_size = unified.node_count();
                    best_i = i;
                }
            }

            debug!(
                "Attempting constraint unification with {} remaining; is unifiable? {}",
                to_unify.len(),
                best_size != usize::MAX,
            );

            if best_size == usize::MAX {
                // cannot unify this constraint
                cannot_unify.push(try_unify);
            } else {
                let second = to_unify.remove(best_i);
                to_unify.push(try_unify.and(&second));
            }
        }

        info!(
            "Finished constraint unification with {} constraints using {} BDD nodes.",
            cannot_unify.len(),
            cannot_unify.iter().map(|it| it.node_count()).sum::<usize>()
        );

        self.0.solve_conjunction(&cannot_unify)
    }
}
