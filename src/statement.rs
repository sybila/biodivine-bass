/// An integer identifier of an ADF statement.
#[derive(Copy, Clone, PartialOrd, PartialEq, Eq, Ord, Debug, Hash)]
pub struct Statement(usize);

impl From<usize> for Statement {
    fn from(value: usize) -> Self {
        Statement(value)
    }
}

impl From<Statement> for usize {
    fn from(value: Statement) -> Self {
        value.0
    }
}

impl Statement {
    pub fn into_index(self) -> usize {
        self.into()
    }
}
