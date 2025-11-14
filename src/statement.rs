/// An identifier of an ADF statement. Can be a numeric ID or an arbitrary string label.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
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

impl From<String> for Statement {
    fn from(value: String) -> Self {
        Statement(value)
    }
}

impl From<&str> for Statement {
    fn from(value: &str) -> Self {
        Statement(value.to_string())
    }
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
