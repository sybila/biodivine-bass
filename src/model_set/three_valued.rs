use crate::DualEncoding;
use crate::model_set::ModelSet;
use ruddy::split::Bdd;
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
        crate::ModelSetThreeValued {
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
