/// An integer identifier of an ADF statement.
#[derive(Clone, PartialOrd, PartialEq, Eq, Ord, Debug, Hash)]
pub struct Statement(String);

impl Statement {
    /// Get the label of this statement
    pub fn label(&self) -> &str {
        &self.0
    }
}

impl From<usize> for Statement {
    fn from(value: usize) -> Self {
        Statement(value.to_string())
    }
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
