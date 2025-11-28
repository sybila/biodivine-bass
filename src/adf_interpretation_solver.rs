use crate::bdd_solver::{BddSolver, DynamicBddSolver};
use crate::{AdfBdds, ModelSetThreeValued, ModelSetTwoValued, Statement};
use cancel_this::{Cancellable, is_cancelled};
use log::{debug, info};
use ruddy::split::Bdd;
use std::collections::BTreeSet;

pub struct AdfInterpretationSolver {
    solver: DynamicBddSolver,
}

impl<S: BddSolver + 'static> From<S> for AdfInterpretationSolver {
    fn from(value: S) -> Self {
        AdfInterpretationSolver::new(Box::new(value))
    }
}

impl AdfInterpretationSolver {
    /// Create a new `AdfInterpretationSolver` with the given BDD solver.
    pub fn new(solver: DynamicBddSolver) -> Self {
        AdfInterpretationSolver { solver }
    }

    /// Computes the [`ModelSetTwoValued`] of all complete two valued interpretations of this ADF.
    pub fn solve_complete_two_valued(&self, adf: &AdfBdds) -> Cancellable<ModelSetTwoValued> {
        info!("Starting computation of complete two-valued interpretations");

        let direct = adf.direct_encoding();
        let var_map = direct.var_map();

        let mut fixed_point_constraints = Vec::new();
        let total_statements = var_map.statements().count();

        for statement in var_map.statements() {
            is_cancelled!()?;

            // Get the BDD literal for this statement
            let statement_lit = var_map.make_literal(statement, true);

            // If condition does not exist, this is a free statement.
            let Some(condition) = direct.get_condition(statement) else {
                continue;
            };

            // Fixed point constraint: statement <=> condition
            let constraint = statement_lit.iff(condition);

            debug!(
                "Generated constraint of size {} for statement `{}`",
                constraint.node_count(),
                statement
            );

            fixed_point_constraints.push(constraint);
        }

        info!(
            "Generated {} fixed-point constraints from {} statements",
            fixed_point_constraints.len(),
            total_statements
        );

        let result_bdd = self.solver.solve_conjunction(&fixed_point_constraints)?;

        let model_set = adf.mk_two_valued_set(result_bdd);

        info!(
            "Computation complete: resulting BDD has {} nodes",
            model_set.symbolic_set().node_count()
        );

        Ok(model_set)
    }

    pub fn solve_stable_two_valued(&self, adf: &AdfBdds) -> Cancellable<ModelSetTwoValued> {
        // 1. Make a copy without free statements (those can be safely fixed to false
        // for stable models).
        let adf = &adf.fix_free_statements(false);

        info!(
            "Starting computation of stable BDD solver by computing all two-valued interpretations."
        );

        // 2. Compute all two-valued models.
        let mut remaining = self.solve_complete_two_valued(adf)?;

        info!(
            "Starting minimization process with {} BDD nodes.",
            remaining.symbolic_set().node_count()
        );

        let mut result = adf.mk_two_valued_set(Bdd::new_false());

        // 3. Iteratively refine the candidate set using the models with the least
        // number of ones.
        while !remaining.is_empty() {
            is_cancelled!()?;

            let candidate_model = remaining.most_zero_model();

            // Compute the number of ones in the candidate model:
            let mut k_one = 0;
            for var in adf.direct_encoding().var_map().variable_ids() {
                let t_val = candidate_model.get(var).expect(
                    "Correctness violation: Candidate model does not cover all statements.",
                );
                if *t_val {
                    k_one += 1;
                }
            }

            info!("Current best candidate model has {} ones", k_one);

            // For now, the k-sized BDD is only used for small k due to some inefficiencies
            // in ruddy that will eventually be fixed.
            let k_size = if k_one < 10 {
                ModelSetTwoValued::mk_exactly_k_one_statements(k_one, adf)
            } else {
                adf.mk_two_valued_interpretations(candidate_model)
            };

            let k_candidate = remaining.intersect(&k_size);
            assert!(!k_candidate.is_empty());

            result = result.union(&k_candidate);

            let looser_models = k_candidate.extend_with_more_ones();
            remaining = remaining.minus(&looser_models);

            info!(
                "Remaining set nodes: {}; Result set nodes: {}; Result set paths: {}",
                remaining.symbolic_set().node_count(),
                result.symbolic_set().node_count(),
                result.symbolic_set().count_satisfying_paths(),
            );
        }

        info!(
            "Computed stable model candidates: resulting BDD has {} nodes and {} paths",
            result.symbolic_set().node_count(),
            result.symbolic_set().count_satisfying_paths()
        );

        // 4. If the two-valued model has s=0, set the dual variables to zero as well.
        // If it is s=1, set dual variables to free.
        let mut result_bdd = result.symbolic_set().clone();

        for s in adf.statements() {
            is_cancelled!()?;

            let d_var = adf.direct_encoding().var_map()[s];
            let (p_var, n_var) = adf.dual_encoding().var_map()[s];

            let d_lit = Bdd::new_literal(d_var, true);
            let p_lit = Bdd::new_literal(p_var, true);
            let n_lit = Bdd::new_literal(n_var, true);

            // (!s) => (n & !p)
            result_bdd = result_bdd.and(&d_lit.not().implies(&n_lit.and(&p_lit.not())));
            // s => (n & p)
            result_bdd = result_bdd.and(&d_lit.implies(&n_lit.and(&p_lit)));
        }

        info!(
            "Expanded stable model candidates to dual encoding: resulting BDD has {} nodes and {} paths",
            result_bdd.node_count(),
            result_bdd.count_satisfying_paths()
        );

        // 5. Propagate "1" values ("ground") in the 3-valued models encoded in dual encoding.

        let mut changed = true;
        while changed {
            changed = false;

            // A variable that is "free" can be fixed to "1" if it cannot be set to "0"
            // (its negative condition is not satisfied)
            for s in adf.statements() {
                is_cancelled!()?;

                let (p_var, n_var) = adf.dual_encoding().var_map()[s];
                let p_lit = Bdd::new_literal(p_var, true);
                let n_lit = Bdd::new_literal(n_var, true);

                if let Some((_, n_cond)) = adf.dual_encoding().get_condition(s) {
                    let has_s_free = result_bdd.and(&p_lit.and(&n_lit));
                    let cant_go_to_zero = has_s_free.and(&n_cond.not());
                    // These values can be fixed to 1.
                    if !cant_go_to_zero.is_false() {
                        // Subst. s_n=1 for s_n=0
                        let fixed_to_one = cant_go_to_zero.exists(&[n_var]).and(&n_lit.not());
                        // Remove those where the value is zero, substitute the ones where value is one.
                        result_bdd = result_bdd.and(&cant_go_to_zero.not()).or(&fixed_to_one);
                        changed = true;
                    }
                }
                // else: The condition is an identity, meaning the value stays the same
            }
        }

        info!(
            "Computed grounded model candidates: resulting BDD has {} nodes and {} paths",
            result_bdd.node_count(),
            result_bdd.count_satisfying_paths()
        );

        // 6. Enforce that stable models are only those where non-zero variables grounded to 1.

        for s in adf.statements() {
            let d_var = adf.direct_encoding().var_map()[s];
            let (p_var, n_var) = adf.dual_encoding().var_map()[s];

            let d_lit = Bdd::new_literal(d_var, true);
            let p_lit = Bdd::new_literal(p_var, true);
            let n_lit = Bdd::new_literal(n_var, true);

            result_bdd = result_bdd.and(&d_lit.implies(&p_lit.and(&n_lit.not())));
        }

        // Forget about the dual variables
        result_bdd = result_bdd.exists(
            &adf.dual_encoding()
                .var_map()
                .variable_ids()
                .copied()
                .collect::<Vec<_>>(),
        );

        result = adf.mk_two_valued_set(result_bdd);

        // At this point, the BDD is a relation which maps each 2-valued interpretation to its
        // 3-valued counterpart with only zeros fixed.

        info!(
            "Computation complete: resulting BDD has {} nodes and {} paths ",
            result.symbolic_set().node_count(),
            result.symbolic_set().count_satisfying_paths(),
        );

        Ok(result)
    }

    /// Computes the [`ModelSetThreeValued`] of all admissible three valued interpretations of this ADF.
    pub fn solve_admissible(&self, adf: &AdfBdds) -> Cancellable<ModelSetThreeValued> {
        info!("Starting computation of admissible three-valued interpretations");

        let dual = adf.dual_encoding();
        let var_map = dual.var_map();

        let mut trap_constraints = vec![dual.valid().clone()];
        let total_statements = var_map.statements().count();

        for statement in var_map.statements() {
            is_cancelled!()?;

            // If condition does not exist, this is a free statement.
            let Some((p_condition, n_condition)) = dual.get_condition(statement) else {
                continue;
            };

            // Get the BDD literal for this statement
            let p_literal = var_map.make_positive_literal(statement, true);
            let n_literal = var_map.make_negative_literal(statement, true);

            // If the condition can evaluate to true, the corresponding literal must be also set.
            let p_constraint = p_condition.implies(&p_literal);
            let n_constraint = n_condition.implies(&n_literal);

            debug!(
                "Generated constraints of size {}/{} for statement `{}`",
                p_constraint.node_count(),
                n_constraint.node_count(),
                statement
            );

            trap_constraints.push(p_constraint.and(&n_constraint));
        }

        trap_constraints.retain(|it| !it.is_true());

        info!(
            "Generated {} trap constraints from {} statements",
            trap_constraints.len(),
            total_statements
        );

        let result_bdd = self.solver.solve_conjunction(&trap_constraints)?;

        let model_set = adf.mk_three_valued_set(result_bdd);

        info!(
            "Computation complete: resulting BDD has {} nodes",
            model_set.symbolic_set().node_count()
        );

        Ok(model_set)
    }

    /// Computes the [`ModelSetThreeValued`] of all complete three valued interpretations of this ADF.
    pub fn solve_complete(&self, adf: &AdfBdds) -> Cancellable<ModelSetThreeValued> {
        self.solve_complete_internal(adf, &BTreeSet::new())
    }

    /// Internal version of complete model computation which allows to explicitly fix
    /// all input variables. This means the result are not all complete models, just the
    /// ones with fixed inputs, but that's often enough (e.g. if searching for preferred models).
    fn solve_complete_internal(
        &self,
        adf: &AdfBdds,
        fixed_inputs: &BTreeSet<Statement>,
    ) -> Cancellable<ModelSetThreeValued> {
        info!("Starting computation of complete three-valued interpretations");

        let dual = adf.dual_encoding();
        let var_map = dual.var_map();

        let mut initial = dual.valid().clone();
        for s in fixed_inputs {
            let p_literal = var_map.make_positive_literal(s, true);
            let n_literal = var_map.make_negative_literal(s, true);
            initial = initial.and(&p_literal.and(&n_literal).not());
        }

        let mut trap_constraints = vec![initial];
        let total_statements = var_map.statements().count();

        for statement in var_map.statements() {
            if fixed_inputs.contains(statement) {
                // These statements are already explicitly fixed to 0/1 and can't be *.
                continue;
            }

            is_cancelled!()?;

            /*
               Compared to admissible interpretations, in complete interpretations we also
               require each interpretation that contains * actually allows that variable to
               be set to both 0 and 1 in it.
            */

            // If condition does not exist, this is a free statement.
            let Some((p_condition, n_condition)) = dual.get_condition(statement) else {
                continue;
            };

            // Get the BDD literal for this statement
            let p_literal = var_map.make_positive_literal(statement, true);
            let n_literal = var_map.make_negative_literal(statement, true);

            // If the condition can evaluate to true, the corresponding literal must be also set.
            let p_constraint = p_condition.implies(&p_literal);
            let n_constraint = n_condition.implies(&n_literal);

            let not_fixed = p_literal.and(&n_literal);
            let can_be_both = p_condition.and(n_condition);
            let completeness = not_fixed.implies(&can_be_both);

            debug!(
                "Generated constraints of size {}/{}/{} for statement `{}`",
                p_constraint.node_count(),
                n_constraint.node_count(),
                completeness.node_count(),
                statement
            );

            trap_constraints.push(p_constraint.and(&n_constraint).and(&completeness));
        }

        trap_constraints.retain(|it| !it.is_true());

        info!(
            "Generated {} trap constraints from {} statements",
            trap_constraints.len(),
            total_statements
        );

        let result_bdd = self.solver.solve_conjunction(&trap_constraints)?;

        let model_set = adf.mk_three_valued_set(result_bdd);

        info!(
            "Computation complete: resulting BDD has {} nodes",
            model_set.symbolic_set().node_count()
        );

        Ok(model_set)
    }

    pub fn solve_preferred(&self, adf: &AdfBdds) -> Cancellable<ModelSetThreeValued> {
        info!(
            "Starting computation of preferred interpretations by finding complete interpretations"
        );

        let fixed_inputs = adf.free_statements();
        let mut remaining = self.solve_complete_internal(adf, &fixed_inputs)?;

        info!(
            "Starting minimization process with {} BDD nodes.",
            remaining.symbolic_set().node_count()
        );

        let mut result = adf.mk_three_valued_set(Bdd::new_false());

        while !remaining.is_empty() {
            let preferred_model = remaining.most_fixed_model();

            // Compute the number of free statements in the preferred model:
            let mut k_free = 0;
            for (t_var, f_var) in adf.dual_encoding().var_map().variable_id_pairs() {
                let t_val = preferred_model.get(t_var).expect(
                    "Correctness violation: Preferred model does not cover all statements.",
                );
                let f_val = preferred_model.get(f_var).expect(
                    "Correctness violation: Preferred model does not cover all statements.",
                );
                if *t_val && *f_val {
                    k_free += 1;
                }
            }

            info!(
                "Current best preferred model has {} free statements",
                k_free
            );

            let k_size = ModelSetThreeValued::mk_exactly_k_free_statements(k_free, adf);

            let k_preferred = remaining.intersect(&k_size);
            assert!(!k_preferred.is_empty());

            info!(
                "Preferred models of size {} are represented using {} nodes.",
                k_free,
                k_preferred.symbolic_set().node_count(),
            );

            result = result.union(&k_preferred);

            let looser_models = k_preferred.extend_with_looser_models(&fixed_inputs);
            remaining = remaining.minus(&looser_models);

            info!(
                "Remaining nodes: {}; Result nodes: {}",
                remaining.symbolic_set().node_count(),
                result.symbolic_set().node_count(),
            );
        }

        info!(
            "Computation complete: resulting BDD has {} nodes",
            result.symbolic_set().node_count()
        );

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bdd_solver::NaiveGreedySolver;

    fn create_test_solver() -> AdfInterpretationSolver {
        AdfInterpretationSolver::from(NaiveGreedySolver::default())
    }

    #[test]
    fn test_solve_simple_adf_constant_true() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            ac(0, c(v)).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_complete_two_valued(&adf)
            .expect("Solving should not be cancelled");

        // For statement 0 with constant true condition:
        // Fixed point: 0 <=> true, which means 0 must be true
        // So there is exactly 1 interpretation: {0: true}
        assert_eq!(model_set.model_count(), 1.0);
    }

    #[test]
    fn test_solve_two_statements() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, 1).
            ac(1, 0).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_complete_two_valued(&adf)
            .expect("Solving should not be cancelled");

        // For statements with mutual dependencies:
        // Fixed points: 0 <=> 1 and 1 <=> 0
        // This means: 0 <=> 1, so both must be true or both must be false
        // There are 2 interpretations: {0: true, 1: true} and {0: false, 1: false}
        assert_eq!(model_set.model_count(), 2.0);
    }

    #[test]
    fn test_solve_with_free_statement() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, c(v)).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_complete_two_valued(&adf)
            .expect("Solving should not be cancelled");

        // Statement 0 has condition true, so 0 must be true (fixed point: 0 <=> true)
        // Statement 1 has no condition (free), so it can be true or false
        // There are 2 interpretations: {0: true, 1: true} and {0: true, 1: false}
        assert_eq!(model_set.model_count(), 2.0);
    }

    #[test]
    fn test_solve_admissible_simple_constant_true() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            ac(0, c(v)).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_admissible(&adf)
            .expect("Solving should not be cancelled");

        // For statement 0 with constant true condition:
        // Trap constraint: if condition can be true (always), then positive literal must be set
        // This means statement 0 can be true or undefined (both), but not false
        // For one statement: {T}, {U}, or {T,U} are valid three-valued interpretations
        // With the constraint, we must allow T, so we have: {T} and {T,U}
        assert_eq!(model_set.model_count(), 2.0);
    }

    #[test]
    fn test_solve_admissible_two_statements() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, 1).
            ac(1, c(v)).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_admissible(&adf)
            .expect("Solving should not be cancelled");

        // Statement 0 depends on 1, statement 1 has constant true
        // This means both statements can be * or 1, but not 0. Valid statements are: **, *1, 11.
        assert_eq!(model_set.model_count(), 3.0);
    }

    #[test]
    fn test_solve_admissible_with_free_statement() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, c(v)).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_admissible(&adf)
            .expect("Solving should not be cancelled");

        // Statement 0 has constant true condition, statement 1 is free.
        // Free statements don't add constraints, so we just have the constraint from statement 0.
        // Plus the valid constraint requiring at least one dual variable per statement.
        assert_eq!(model_set.model_count(), 6.0);
    }

    #[test]
    fn test_solve_complete_simple_constant_true() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            ac(0, c(v)).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_complete(&adf)
            .expect("Solving should not be cancelled");

        // For statement 0 with constant true condition:
        // Admissible allows: {T} and {T,U} (2 interpretations)
        // Complete requires: if statement is free (both T and F), condition must be able to be both
        // Since condition is constant true (can't be both), statement can't be free
        // So only {T} is allowed = 1 interpretation
        assert_eq!(model_set.model_count(), 1.0);
    }

    #[test]
    fn test_solve_complete_two_statements() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, 1).
            ac(1, c(v)).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_complete(&adf)
            .expect("Solving should not be cancelled");

        // Statement 0 depends on 1, statement 1 has constant true
        // Admissible allows: **, *1, 11 (3 interpretations)
        // Complete: Statement 1 can't be free (constant true), so *1 and ** are excluded
        // Only 11 is allowed = 1 interpretation
        assert_eq!(model_set.model_count(), 1.0);
    }

    #[test]
    fn test_solve_complete_with_free_statement() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, c(v)).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_complete(&adf)
            .expect("Solving should not be cancelled");

        // Statement 0 has constant true condition, statement 1 is free (no condition)
        // Admissible allows: 6 interpretations
        // Complete: Statement 0 can't be free (constant true), so interpretations where 0 is free are excluded
        // Statement 1 is free, so it can be anything valid
        assert_eq!(model_set.model_count(), 3.0);
    }

    #[test]
    fn test_solve_preferred_simple_constant_true() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            ac(0, c(v)).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_preferred(&adf)
            .expect("Solving should not be cancelled");

        // Statement 0 has constant true condition
        // Complete interpretations: only {T} (0 free statements)
        // Preferred: should be 1 interpretation with 0 free statements
        assert_eq!(model_set.model_count(), 1.0);
    }

    #[test]
    fn test_solve_preferred_two_statements_one_free() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, c(v)).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_preferred(&adf)
            .expect("Solving should not be cancelled");

        // Statement 0 has constant true condition (must be fixed), statement 1 is free
        // Complete interpretations: 3 total (0 fixed, 1 can be T/F/*)
        // Preferred: those with 0 free statements (both 0 and 1 fixed)
        // So preferred should be: {T, T} and {T, F} = 2 interpretations
        assert_eq!(model_set.model_count(), 2.0);
    }

    #[test]
    fn test_solve_preferred_mutual_dependency() {
        let solver = create_test_solver();
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, 1).
            ac(1, 0).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        let adf = AdfBdds::from(&expr_adf);

        let model_set = solver
            .solve_preferred(&adf)
            .expect("Solving should not be cancelled");

        // Both statements depend on each other
        // Complete interpretations: must satisfy 0 <=> 1 and 1 <=> 0
        // This means both must be true or both must be false (0 free statements)
        // Preferred: should be 2 interpretations with 0 free statements: {T, T} and {F, F}
        assert_eq!(model_set.model_count(), 2.0);
    }
}
