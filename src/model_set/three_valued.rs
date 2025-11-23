use crate::model_set::ModelSet;
use crate::{AdfBdds, DualEncoding};
use log::trace;
use ruddy::VariableId;
use ruddy::split::Bdd;
use std::collections::BTreeMap;
use std::sync::Arc;

#[derive(Clone)]
pub struct ModelSetThreeValued {
    symbolic_set: Bdd,
    encoding: Arc<DualEncoding>,
}

impl PartialEq for ModelSetThreeValued {
    fn eq(&self, other: &Self) -> bool {
        self.symbolic_set.structural_eq(&other.symbolic_set)
            && Arc::ptr_eq(&self.encoding, &other.encoding)
    }
}

impl Eq for ModelSetThreeValued {}

impl ModelSet for ModelSetThreeValued {
    fn symbolic_set(&self) -> &Bdd {
        ModelSetThreeValued::symbolic_set(self)
    }

    fn model_count(&self) -> f64 {
        ModelSetThreeValued::model_count(self)
    }
}

impl ModelSetThreeValued {
    /// Make a [`ModelSetThreeValued`] from the underlying parts.
    ///
    /// # Panics
    ///
    /// Fails if the `symbolic_set` uses BDD variables that are not used by the given `encoding`.
    pub fn new(symbolic_set: Bdd, encoding: Arc<DualEncoding>) -> Self {
        assert!(encoding.is_dual_encoded(&symbolic_set));
        ModelSetThreeValued {
            symbolic_set,
            encoding,
        }
    }

    /// Get a reference to the underlying [`Bdd`].
    pub fn symbolic_set(&self) -> &Bdd {
        &self.symbolic_set
    }

    /// Get a reference to the underlying [`DualEncoding`].
    pub fn encoding(&self) -> &DualEncoding {
        &self.encoding
    }

    /// Count the models in this set (possibly overflowing to [`f64::INFINITY`]).
    pub fn model_count(&self) -> f64 {
        self.encoding.count_dual_valuations(&self.symbolic_set)
    }

    /// Extract the model with the highest number of fixed variable values (i.e. `1` or `0`
    /// instead of `*`).
    ///
    /// # Panics
    ///
    /// The set must not be empty.
    pub fn most_fixed_model(&self) -> BTreeMap<VariableId, bool> {
        self.encoding.most_fixed_model(&self.symbolic_set)
    }

    /// Returns `true` if this set of models is empty.
    pub fn is_empty(&self) -> bool {
        self.symbolic_set.is_false()
    }

    /// Compute the set of ADF interpretations that have *exactly* `k` free statements.
    ///
    /// Under normal circumstances, this should be a relatively fast operation, where the
    /// resulting BDD is linear in the number of statements. Hence, it is currently
    /// not cancellable.
    pub fn mk_exactly_k_free_statements(
        free_count: usize,
        encoding: &AdfBdds,
    ) -> ModelSetThreeValued {
        let dual = encoding.dual_encoding();
        let direct = encoding.direct_encoding();

        let mut free_var_constraints = BTreeMap::new();
        for s in dual.var_map().statements() {
            let (p_lit, n_lit) = dual.var_map().make_literals(s);
            free_var_constraints.insert(s.clone(), p_lit.and(&n_lit));
        }

        // At the moment, there isn't a method that will do this on BDDs directly, so we first
        // build it on variables, and then use substitution to swap variables for (p_var & n_var)
        // expressions that enforce the variable is free in a subspace.
        let direct_vars = direct.var_map().variable_ids().copied().collect::<Vec<_>>();
        let mut at_most_k_free = Bdd::new_sat_exactly_k(free_count, &direct_vars);
        for s in direct.var_map().statements() {
            let direct_var = direct.var_map()[s];
            let replacement = free_var_constraints
                .get(s)
                .expect("Correctness violation: Statement missing.");
            at_most_k_free = at_most_k_free.safe_substitution(direct_var, replacement);
        }

        encoding.mk_three_valued_set(at_most_k_free.and(dual.valid()))
    }

    /// Compute the intersection of two sets.
    pub fn intersect(&self, other: &ModelSetThreeValued) -> ModelSetThreeValued {
        assert!(Arc::ptr_eq(&self.encoding, &other.encoding));

        ModelSetThreeValued {
            symbolic_set: self.symbolic_set.and(&other.symbolic_set),
            encoding: self.encoding.clone(),
        }
    }

    /// Compute the union of two sets.
    pub fn union(&self, other: &ModelSetThreeValued) -> ModelSetThreeValued {
        assert!(Arc::ptr_eq(&self.encoding, &other.encoding));

        ModelSetThreeValued {
            symbolic_set: self.symbolic_set.or(&other.symbolic_set),
            encoding: self.encoding.clone(),
        }
    }

    /// Compute the difference of two sets.
    pub fn minus(&self, other: &ModelSetThreeValued) -> ModelSetThreeValued {
        assert!(Arc::ptr_eq(&self.encoding, &other.encoding));

        ModelSetThreeValued {
            symbolic_set: self.symbolic_set.and(&other.symbolic_set.not()),
            encoding: self.encoding.clone(),
        }
    }

    /// Extend this set with every "looser" interpretation of the interpretations that are
    /// already in the set. In this context, "looser" means the interpretation has `*` in place
    /// of some `1` or `0`.
    pub fn extend_with_looser_models(&self) -> ModelSetThreeValued {
        let mut result = self.symbolic_set.clone();
        for (i, (p_var, n_var)) in self
            .encoding
            .var_map()
            .variable_id_pairs()
            .copied()
            .rev()
            .enumerate()
        {
            let p_lit = Bdd::new_literal(p_var, true);
            let p_nlit = Bdd::new_literal(p_var, false);
            let n_lit = Bdd::new_literal(n_var, true);
            let n_nlit = Bdd::new_literal(n_var, false);

            // Select every space in which we have `t_var=false`, but there is
            // no equivalent space with `t_var=true`. Flips `t_var` on output,
            // meaning we actually get the set of super spaces where `true` is added.

            let adds_true = result
                // Select every space where p_var=false and eliminate p_var
                .binary_op_with_exists(&p_nlit, ruddy::boolean_operators::And, &[p_var])
                // Reintroduce it with p_var=true
                .and(&p_lit);

            let adds_false = result
                // Select every space where n_var=false
                .binary_op_with_exists(&n_nlit, ruddy::boolean_operators::And, &[n_var])
                // Reintroduce it with n_var=true
                .and(&n_lit);

            let adds = adds_true.or(&adds_false);
            if !adds.is_false() {
                result = result.or(&adds);
                trace!(
                    "Computing super-spaces[{}/{}]: BDD size {}.",
                    i + 1,
                    self.encoding.var_map().size(),
                    result.node_count(),
                );
            }
        }

        ModelSetThreeValued {
            symbolic_set: result,
            encoding: self.encoding.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{AdfBdds, Statement};

    fn create_test_adf_bdds() -> AdfBdds {
        let adf_str = r#"
            s(0).
            s(1).
            ac(0, 1).
            ac(1, c(v)).
        "#;
        let expr_adf = crate::AdfExpressions::parse(adf_str).expect("Failed to parse ADF");
        AdfBdds::from(&expr_adf)
    }

    #[test]
    fn test_symbolic_set_accessor() {
        let adf = create_test_adf_bdds();
        // Use the valid BDD which represents all valid three-valued interpretations
        let valid_bdd = adf.dual_encoding().valid().clone();
        let model_set = adf.mk_three_valued_set(valid_bdd.clone());

        let retrieved_bdd = model_set.symbolic_set();
        assert!(retrieved_bdd.structural_eq(&valid_bdd));
    }

    #[test]
    fn test_encoding_accessor() {
        let adf = create_test_adf_bdds();
        let valid_bdd = adf.dual_encoding().valid().clone();
        let model_set1 = adf.mk_three_valued_set(valid_bdd.clone());
        let model_set2 = adf.mk_three_valued_set(valid_bdd);

        let encoding1 = model_set1.encoding();
        let encoding2 = model_set2.encoding();
        assert_eq!(encoding1.var_map(), encoding2.var_map());
    }

    #[test]
    fn test_model_count_valid() {
        let adf = create_test_adf_bdds();
        // The valid BDD represents all valid three-valued interpretations
        let valid_bdd = adf.dual_encoding().valid().clone();
        let model_set = adf.mk_three_valued_set(valid_bdd);

        // For 2 statements, each can be: undefined (UU), true (TU), false (UF), or both (TT)
        // But valid requires at least one dual variable to be true, so we exclude UU
        // That gives us 3^2 = 9 interpretations total (excluding invalid UU cases)
        assert_eq!(model_set.model_count(), 9.0);
    }

    #[test]
    fn test_model_count_false() {
        let adf = create_test_adf_bdds();
        let false_bdd = ruddy::split::Bdd::new_false();
        let model_set = adf.mk_three_valued_set(false_bdd);

        // False BDD accepts no valuations
        assert_eq!(model_set.model_count(), 0.0);
    }

    #[test]
    fn test_model_count_single_positive_literal() {
        let adf = create_test_adf_bdds();
        let var_map = adf.dual_encoding().var_map();
        // Statement 0 can be true (positive literal set)
        let s0_positive = var_map.make_positive_literal(&Statement::from(0), true);
        // Must combine with valid to ensure other constraints are satisfied
        let valid_bdd = adf.dual_encoding().valid();
        let constraint_bdd = s0_positive.and(valid_bdd);
        let model_set = adf.mk_three_valued_set(constraint_bdd);

        // Statement 0 must have positive variable true, and all must be valid.
        // That leaves 6/9 models. Invalid are 0*, 00, and 01.
        assert_eq!(model_set.model_count(), 6.0);
    }

    #[test]
    fn test_clone() {
        let adf = create_test_adf_bdds();
        let valid_bdd = adf.dual_encoding().valid().clone();
        let model_set1 = adf.mk_three_valued_set(valid_bdd);
        let model_set2 = model_set1.clone();

        // Both should have the same model count
        assert_eq!(model_set1.model_count(), model_set2.model_count());
        assert_eq!(model_set1.model_count(), 9.0);

        // Both should be equal
        assert!(model_set1 == model_set2);
    }

    #[test]
    fn test_partial_eq_equal() {
        let adf = create_test_adf_bdds();
        let valid_bdd = adf.dual_encoding().valid().clone();
        let model_set1 = adf.mk_three_valued_set(valid_bdd.clone());
        let model_set2 = adf.mk_three_valued_set(valid_bdd);

        // Both use the same BDD and encoding, so they should be equal
        assert!(model_set1 == model_set2);
    }

    #[test]
    fn test_partial_eq_different_bdd() {
        let adf = create_test_adf_bdds();
        let valid_bdd = adf.dual_encoding().valid().clone();
        let false_bdd = ruddy::split::Bdd::new_false();
        let model_set1 = adf.mk_three_valued_set(valid_bdd);
        let model_set2 = adf.mk_three_valued_set(false_bdd);

        // Different BDDs should not be equal
        assert!(model_set1 != model_set2);
    }

    #[test]
    fn test_model_count_both_literals() {
        let adf = create_test_adf_bdds();
        let var_map = adf.dual_encoding().var_map();
        let s0_positive = var_map.make_positive_literal(&Statement::from(0), true);
        let s0_negative = var_map.make_negative_literal(&Statement::from(0), true);

        // Both dual variables true means the statement can be both true and false
        let both_true = s0_positive.and(&s0_negative);
        let valid_bdd = adf.dual_encoding().valid();
        let constraint_bdd = both_true.and(valid_bdd);
        let model_set = adf.mk_three_valued_set(constraint_bdd);

        // Statement 0 can be both true and false, statement 1 can be anything valid
        let count = model_set.model_count();
        assert!(count > 0.0);
        assert!(count.is_finite());
    }
}
