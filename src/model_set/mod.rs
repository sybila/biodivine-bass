use crate::Statement;
use ruddy::split::Bdd;
use std::collections::BTreeMap;

pub mod three_valued;
pub mod two_valued;

pub trait ModelSet {
    /// Get a reference to the underlying [`Bdd`].
    fn symbolic_set(&self) -> &Bdd;

    /// Count the models in this set (possibly overflowing to [`f64::INFINITY`]).
    fn model_count(&self) -> f64;

    /// Iterate over all models stored in the set. For two-valued models,
    /// the values cannot be `None`.
    fn iter(&self) -> impl Iterator<Item = BTreeMap<Statement, Option<bool>>>;
}
