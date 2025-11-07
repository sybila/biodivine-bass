use crate::ConditionExpression;
use crate::statement::Statement;
use std::collections::BTreeMap;

/// Represents an abstract dialectical framework based on expressions
/// (typically loaded from a file).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AdfExpressions {
    conditions: BTreeMap<Statement, Option<ConditionExpression>>,
}

impl AdfExpressions {
    /// Create a new empty ADF.
    pub fn new() -> Self {
        AdfExpressions {
            conditions: BTreeMap::new(),
        }
    }

    /// Get the acceptance condition for a statement.
    /// Returns `None` if the statement doesn't exist or has no condition.
    pub fn get_condition(&self, statement: Statement) -> Option<&ConditionExpression> {
        self.conditions.get(&statement).and_then(|opt| opt.as_ref())
    }

    /// Check if a statement exists in the ADF (with or without a condition).
    pub fn has_statement(&self, statement: Statement) -> bool {
        self.conditions.contains_key(&statement)
    }

    /// Get all statements in the ADF.
    ///
    /// The statements are returned in sorted order (by their index) because they are
    /// stored in a [`BTreeMap`].
    pub fn statements(&self) -> impl Iterator<Item = Statement> {
        self.conditions.keys().copied()
    }

    /// Get the number of statements in the ADF.
    pub fn len(&self) -> usize {
        self.conditions.len()
    }

    /// Check if the ADF is empty.
    pub fn is_empty(&self) -> bool {
        self.conditions.is_empty()
    }

    /// Parse an ADF from a string in the `.adf` file format.
    ///
    /// The format consists of lines with:
    /// - `s(number).` to declare a statement
    /// - `ac(number, expression).` to declare an acceptance condition
    ///
    /// Empty lines and lines starting with `#` are ignored as comments.
    /// Statements can be declared without conditions, and conditions can reference
    /// statements that are not explicitly declared.
    pub fn parse(input: &str) -> Result<Self, String> {
        let mut adf = AdfExpressions::new();

        for (line_num, line) in input.lines().enumerate() {
            let line = line.trim();

            // Skip empty lines and comments
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            // Parse statement declaration: s(number).
            if line.starts_with("s(") && line.ends_with(").") {
                let number_str = &line[2..line.len() - 2];
                let number = number_str.parse::<usize>().map_err(|_| {
                    format!(
                        "Line {}: Invalid statement number: {}",
                        line_num + 1,
                        number_str
                    )
                })?;
                let statement = Statement::from(number);

                // Insert statement with no condition if not already present
                adf.conditions.entry(statement).or_insert(None);
                continue;
            }

            // Parse acceptance condition: ac(number, expression).
            if line.starts_with("ac(") && line.ends_with(").") {
                // Find the comma that separates the statement number from the expression
                let content = &line[3..line.len() - 2];
                let comma_pos = content.find(',').ok_or_else(|| {
                    format!(
                        "Line {}: Missing comma in acceptance condition",
                        line_num + 1
                    )
                })?;

                let number_str = content[..comma_pos].trim();
                let expr_str = content[comma_pos + 1..].trim();

                let number = number_str.parse::<usize>().map_err(|_| {
                    format!(
                        "Line {}: Invalid statement number: {}",
                        line_num + 1,
                        number_str
                    )
                })?;
                let statement = Statement::from(number);

                // Parse the condition expression
                let condition = ConditionExpression::parse(expr_str).map_err(|e| {
                    format!(
                        "Line {}: Failed to parse condition expression: {}",
                        line_num + 1,
                        e
                    )
                })?;

                // Check if this statement already has a condition
                if let Some(Some(_)) = adf.conditions.get(&statement) {
                    return Err(format!(
                        "Line {}: Statement {} already has a condition declared",
                        line_num + 1,
                        number
                    ));
                }

                // Insert the condition
                adf.conditions.insert(statement, Some(condition));
                continue;
            }

            // If we get here, the line format is not recognized
            return Err(format!(
                "Line {}: Unrecognized line format: {}",
                line_num + 1,
                line
            ));
        }

        Ok(adf)
    }

    /// Parse an ADF from a string and automatically fix missing statements.
    /// This is equivalent to calling `parse()` followed by `fix_missing_statements()`.
    pub fn parse_and_fix(input: &str) -> Result<Self, String> {
        let mut adf = Self::parse(input)?;
        adf.fix_missing_statements();
        Ok(adf)
    }

    /// Parse an ADF from a file.
    pub fn parse_file(path: impl AsRef<std::path::Path>) -> Result<Self, String> {
        let content = std::fs::read_to_string(path.as_ref())
            .map_err(|e| format!("Failed to read file: {}", e))?;
        Self::parse(&content)
    }

    /// Parse an ADF from a file and automatically fix missing statements.
    /// This is equivalent to calling `parse_file()` followed by `fix_missing_statements()`.
    pub fn parse_and_fix_file(path: impl AsRef<std::path::Path>) -> Result<Self, String> {
        let mut adf = Self::parse_file(path)?;
        adf.fix_missing_statements();
        Ok(adf)
    }

    /// Add a statement without a condition.
    /// If the statement already exists, this does nothing.
    pub fn add_statement(&mut self, statement: Statement) {
        self.conditions.entry(statement).or_insert(None);
    }

    /// Add a condition for a statement.
    /// Returns an error if the statement already has a condition.
    pub fn add_condition(
        &mut self,
        statement: Statement,
        condition: ConditionExpression,
    ) -> Result<(), String> {
        if let Some(Some(_)) = self.conditions.get(&statement) {
            return Err(format!(
                "Statement {} already has a condition",
                statement.into_index()
            ));
        }
        self.conditions.insert(statement, Some(condition));
        Ok(())
    }

    /// Remove a statement and its condition entirely from the ADF.
    pub fn remove_statement(&mut self, statement: Statement) {
        self.conditions.remove(&statement);
    }

    /// Remove the condition for a statement, but keep the statement.
    /// If the statement doesn't exist, this does nothing.
    pub fn remove_condition(&mut self, statement: Statement) {
        if let Some(cond) = self.conditions.get_mut(&statement) {
            *cond = None;
        }
    }

    /// Update or set the condition for a statement.
    /// If the statement doesn't exist, it will be created.
    /// If it already has a condition, it will be replaced.
    pub fn update_condition(&mut self, statement: Statement, condition: ConditionExpression) {
        self.conditions.insert(statement, Some(condition));
    }

    /// Get an iterator over all statements that have conditions.
    /// Returns pairs of (statement, condition).
    ///
    /// The statements are returned in sorted order (by their index) because they are
    /// stored in a [`BTreeMap`].
    pub fn conditions(&self) -> impl Iterator<Item = (Statement, &ConditionExpression)> {
        self.conditions
            .iter()
            .filter_map(|(stmt, cond)| cond.as_ref().map(|c| (*stmt, c)))
    }

    /// Get an iterator over all statements that have no condition.
    ///
    /// The statements are returned in sorted order (by their index) because they are
    /// stored in a [`BTreeMap`].
    pub fn free_statements(&self) -> impl Iterator<Item = Statement> {
        self.conditions.iter().filter_map(
            |(stmt, cond)| {
                if cond.is_none() { Some(*stmt) } else { None }
            },
        )
    }

    /// Find all statements that appear in some condition expression but are not declared.
    /// Returns a sorted vector of missing statements.
    pub fn find_missing_statements(&self) -> Vec<Statement> {
        use std::collections::BTreeSet;

        let mut referenced = BTreeSet::new();

        // Collect all statements referenced in conditions
        for (_, condition) in self.conditions() {
            let statements = condition.collect_statements();
            referenced.extend(statements);
        }

        // Find statements that are referenced but not declared
        referenced
            .into_iter()
            .filter(|stmt| !self.conditions.contains_key(stmt))
            .collect()
    }

    /// Add all missing statements (those referenced in conditions but not declared) as free statements.
    pub fn fix_missing_statements(&mut self) {
        let missing = self.find_missing_statements();
        for statement in missing {
            self.add_statement(statement);
        }
    }

    /// Write the ADF to a string in the `.adf` file format.
    ///
    /// The format consists of:
    /// - `s(number).` for each statement
    /// - `ac(number, expression).` for statements with conditions
    ///
    /// Statements are written in sorted order by their number.
    /// This matches the format used in test files where both s(N) and ac(N, ...)
    /// can appear for the same statement.
    pub fn write(&self) -> String {
        let mut output = String::new();

        // First pass: write all s(N) declarations
        for statement in self.conditions.keys() {
            output.push_str(&format!("s({}).\n", statement.into_index()));
        }

        // Second pass: write all ac(N, expr) declarations
        for (statement, condition) in &self.conditions {
            if let Some(expr) = condition {
                output.push_str(&format!("ac({},{}).\n", statement.into_index(), expr));
            }
        }

        output
    }

    /// Write the ADF to a file in the `.adf` file format.
    pub fn write_file(&self, path: impl AsRef<std::path::Path>) -> Result<(), String> {
        let content = self.write();
        std::fs::write(path.as_ref(), content).map_err(|e| format!("Failed to write file: {}", e))
    }
}

impl Default for AdfExpressions {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_adf() {
        let input = r#"
s(1).
s(2).
ac(1, c(v)).
ac(2, neg(1)).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 2);

        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        assert!(adf.has_statement(s1));
        assert!(adf.has_statement(s2));
        assert!(adf.get_condition(s1).is_some());
        assert!(adf.get_condition(s2).is_some());
    }

    #[test]
    fn test_parse_statement_without_condition() {
        let input = r#"
s(1).
s(2).
ac(1, c(v)).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 2);

        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        assert!(adf.get_condition(s1).is_some());
        assert!(adf.get_condition(s2).is_none());
    }

    #[test]
    fn test_parse_condition_without_declaration() {
        let input = r#"
ac(1, and(2, 3)).
ac(2, c(v)).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 2);

        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        assert!(adf.get_condition(s1).is_some());
        assert!(adf.get_condition(s2).is_some());
    }

    #[test]
    fn test_parse_complex_expressions() {
        let input = r#"
s(1).
s(2).
s(3).
ac(1, and(or(2, neg(3)), 2)).
ac(2, or(neg(1), 3)).
ac(3, and(neg(2), 3)).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 3);
    }

    #[test]
    fn test_parse_unordered_declarations() {
        let input = r#"
ac(2, neg(1)).
s(1).
ac(1, c(v)).
s(2).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 2);

        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        assert!(adf.get_condition(s1).is_some());
        assert!(adf.get_condition(s2).is_some());
    }

    #[test]
    fn test_parse_with_comments_and_empty_lines() {
        let input = r#"
# This is a comment
s(1).

# Another comment
s(2).

ac(1, c(v)).
ac(2, neg(1)).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 2);
    }

    #[test]
    fn test_parse_real_example() {
        let input = r#"
s(7).
s(4).
s(8).
s(3).
s(5).
s(9).
s(10).
s(1).
s(6).
s(2).
ac(7,c(v)).
ac(4,6).
ac(8,or(neg(1),7)).
ac(3,and(or(7,neg(6)),2)).
ac(5,4).
ac(9,neg(7)).
ac(10,and(neg(2),6)).
ac(1,and(neg(7),2)).
ac(6,neg(7)).
ac(2,and(neg(9),neg(6))).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 10);

        // Check that all statements have conditions
        for i in 1..=10 {
            let stmt = Statement::from(i);
            assert!(adf.get_condition(stmt).is_some());
        }
    }

    #[test]
    fn test_parse_all_test_instances() {
        use std::fs;
        use std::path::Path;

        let test_dir = Path::new("test_instances");
        if !test_dir.exists() {
            // Skip test if directory doesn't exist
            return;
        }

        let entries = fs::read_dir(test_dir).unwrap();
        let mut count = 0;
        let mut errors = Vec::new();

        for entry in entries {
            let entry = entry.unwrap();
            let path = entry.path();

            if path.extension().and_then(|s| s.to_str()) == Some("adf") {
                count += 1;
                let content = fs::read_to_string(&path).unwrap();

                match AdfExpressions::parse(&content) {
                    Ok(adf) => {
                        // Basic sanity check
                        assert!(!adf.is_empty(), "ADF from {:?} is empty", path);
                    }
                    Err(e) => {
                        errors.push((path.clone(), e));
                    }
                }
            }
        }

        if !errors.is_empty() {
            eprintln!("Failed to parse {} out of {} files:", errors.len(), count);
            for (path, error) in &errors {
                eprintln!("  {:?}: {}", path, error);
            }
            panic!("Some test instances failed to parse");
        }

        println!("Successfully parsed {} test instance files", count);
    }

    #[test]
    fn test_parse_invalid_statement_number() {
        let input = "s(abc).";
        assert!(AdfExpressions::parse(input).is_err());
    }

    #[test]
    fn test_parse_invalid_condition_number() {
        let input = "ac(xyz, c(v)).";
        assert!(AdfExpressions::parse(input).is_err());
    }

    #[test]
    fn test_parse_invalid_expression() {
        let input = "ac(1, invalid_expr).";
        assert!(AdfExpressions::parse(input).is_err());
    }

    #[test]
    fn test_parse_malformed_line() {
        let input = "this is not a valid line";
        assert!(AdfExpressions::parse(input).is_err());
    }

    #[test]
    fn test_parse_missing_comma_in_ac() {
        // Test the error condition when ac() line is missing comma
        let input = "ac(1 c(v)).";
        let result = AdfExpressions::parse(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.contains("Missing comma in acceptance condition"));
        assert!(err.contains("Line 1"));
    }

    #[test]
    fn test_parse_missing_comma_in_ac_multiline() {
        let input = r#"
s(1).
s(2).
ac(1, c(v)).
ac(2 neg(1)).
"#;
        let result = AdfExpressions::parse(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.contains("Missing comma in acceptance condition"));
        assert!(err.contains("Line 5")); // Should be line 5
    }

    #[test]
    fn test_parse_duplicate_condition_simple() {
        let input = r#"
s(1).
ac(1, c(v)).
ac(1, c(f)).
"#;
        let result = AdfExpressions::parse(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.contains("already has a condition declared"));
        assert!(err.contains("Statement 1"));
    }

    #[test]
    fn test_parse_duplicate_condition_without_declaration() {
        let input = r#"
ac(1, c(v)).
ac(1, neg(2)).
"#;
        let result = AdfExpressions::parse(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.contains("already has a condition declared"));
        assert!(err.contains("Statement 1"));
    }

    #[test]
    fn test_parse_duplicate_condition_mixed_order() {
        let input = r#"
ac(1, c(v)).
s(2).
ac(2, neg(1)).
s(1).
ac(1, c(f)).
"#;
        let result = AdfExpressions::parse(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.contains("already has a condition declared"));
        assert!(err.contains("Statement 1"));
    }

    #[test]
    fn test_parse_duplicate_condition_complex() {
        let input = r#"
s(1).
s(2).
s(3).
ac(1, c(v)).
ac(2, neg(1)).
ac(3, and(1, 2)).
ac(2, or(1, 3)).
"#;
        let result = AdfExpressions::parse(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.contains("already has a condition declared"));
        assert!(err.contains("Statement 2"));
    }

    #[test]
    fn test_parse_statement_redeclaration_is_ok() {
        // Multiple s(N) declarations for the same statement should be OK
        // (it's redundant but not an error)
        let input = r#"
s(1).
s(1).
s(1).
ac(1, c(v)).
"#;
        let result = AdfExpressions::parse(input);
        assert!(result.is_ok());
        let adf = result.unwrap();
        assert_eq!(adf.len(), 1);
        assert!(adf.get_condition(Statement::from(1)).is_some());
    }

    #[test]
    fn test_parse_different_statements_ok() {
        // Multiple conditions for different statements should be fine
        let input = r#"
ac(1, c(v)).
ac(2, neg(1)).
ac(3, and(1, 2)).
"#;
        let result = AdfExpressions::parse(input);
        assert!(result.is_ok());
        let adf = result.unwrap();
        assert_eq!(adf.len(), 3);
    }

    // Tests for add_statement
    #[test]
    fn test_add_statement_new() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        adf.add_statement(s1);
        assert_eq!(adf.len(), 1);
        assert!(adf.has_statement(s1));
        assert!(adf.get_condition(s1).is_none());
    }

    #[test]
    fn test_add_statement_existing() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        adf.add_statement(s1);
        adf.add_statement(s1); // Should not error, just do nothing
        assert_eq!(adf.len(), 1);
    }

    #[test]
    fn test_add_statement_with_existing_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.add_condition(s1, cond.clone()).unwrap();
        adf.add_statement(s1); // Should not change existing condition
        assert_eq!(adf.len(), 1);
        assert!(adf.get_condition(s1).is_some());
    }

    // Tests for add_condition
    #[test]
    fn test_add_condition_new_statement() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        let result = adf.add_condition(s1, cond);
        assert!(result.is_ok());
        assert_eq!(adf.len(), 1);
        assert!(adf.get_condition(s1).is_some());
    }

    #[test]
    fn test_add_condition_existing_statement_no_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.add_statement(s1);
        let result = adf.add_condition(s1, cond);
        assert!(result.is_ok());
        assert!(adf.get_condition(s1).is_some());
    }

    #[test]
    fn test_add_condition_duplicate_fails() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond1 = ConditionExpression::constant(true);
        let cond2 = ConditionExpression::constant(false);

        adf.add_condition(s1, cond1).unwrap();
        let result = adf.add_condition(s1, cond2);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("already has a condition"));
    }

    // Tests for remove_statement
    #[test]
    fn test_remove_statement_existing() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_statement(s1);
        adf.add_statement(s2);
        assert_eq!(adf.len(), 2);

        adf.remove_statement(s1);
        assert_eq!(adf.len(), 1);
        assert!(!adf.has_statement(s1));
        assert!(adf.has_statement(s2));
    }

    #[test]
    fn test_remove_statement_nonexistent() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        adf.remove_statement(s1); // Should not panic
        assert_eq!(adf.len(), 0);
    }

    #[test]
    fn test_remove_statement_with_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.add_condition(s1, cond).unwrap();
        adf.remove_statement(s1);
        assert_eq!(adf.len(), 0);
    }

    // Tests for remove_condition
    #[test]
    fn test_remove_condition_existing() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.add_condition(s1, cond).unwrap();
        assert!(adf.get_condition(s1).is_some());

        adf.remove_condition(s1);
        assert_eq!(adf.len(), 1); // Statement still exists
        assert!(adf.get_condition(s1).is_none());
    }

    #[test]
    fn test_remove_condition_nonexistent_statement() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        adf.remove_condition(s1); // Should not panic
        assert_eq!(adf.len(), 0);
    }

    #[test]
    fn test_remove_condition_already_none() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        adf.add_statement(s1);
        adf.remove_condition(s1); // Should not panic
        assert!(adf.get_condition(s1).is_none());
    }

    // Tests for update_condition
    #[test]
    fn test_update_condition_new_statement() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.update_condition(s1, cond);
        assert_eq!(adf.len(), 1);
        assert!(adf.get_condition(s1).is_some());
    }

    #[test]
    fn test_update_condition_existing_no_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.add_statement(s1);
        adf.update_condition(s1, cond);
        assert!(adf.get_condition(s1).is_some());
    }

    #[test]
    fn test_update_condition_existing_with_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond1 = ConditionExpression::constant(true);
        let cond2 = ConditionExpression::constant(false);

        adf.add_condition(s1, cond1).unwrap();
        adf.update_condition(s1, cond2.clone());

        let retrieved = adf.get_condition(s1).unwrap();
        assert_eq!(retrieved, &cond2);
    }

    // Tests for conditions iterator
    #[test]
    fn test_conditions_empty() {
        let adf = AdfExpressions::new();
        assert_eq!(adf.conditions().count(), 0);
    }

    #[test]
    fn test_conditions_only_free_statements() {
        let mut adf = AdfExpressions::new();
        adf.add_statement(Statement::from(1));
        adf.add_statement(Statement::from(2));

        assert_eq!(adf.conditions().count(), 0);
    }

    #[test]
    fn test_conditions_mixed() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        adf.add_statement(s1);
        adf.add_condition(s2, ConditionExpression::constant(true))
            .unwrap();
        adf.add_condition(s3, ConditionExpression::constant(false))
            .unwrap();

        let conditions: Vec<_> = adf.conditions().collect();
        assert_eq!(conditions.len(), 2);
    }

    // Tests for free_statements iterator
    #[test]
    fn test_free_statements_empty() {
        let adf = AdfExpressions::new();
        assert_eq!(adf.free_statements().count(), 0);
    }

    #[test]
    fn test_free_statements_all_have_conditions() {
        let mut adf = AdfExpressions::new();
        adf.add_condition(Statement::from(1), ConditionExpression::constant(true))
            .unwrap();
        adf.add_condition(Statement::from(2), ConditionExpression::constant(false))
            .unwrap();

        assert_eq!(adf.free_statements().count(), 0);
    }

    #[test]
    fn test_free_statements_mixed() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        adf.add_statement(s1);
        adf.add_condition(s2, ConditionExpression::constant(true))
            .unwrap();
        adf.add_statement(s3);

        let free: Vec<_> = adf.free_statements().collect();
        assert_eq!(free.len(), 2);
        assert!(free.contains(&&s1));
        assert!(free.contains(&&s3));
    }

    // Tests for find_missing_statements
    #[test]
    fn test_find_missing_statements_none() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_statement(s1);
        adf.add_statement(s2);
        adf.add_condition(s1, ConditionExpression::statement(s2))
            .unwrap();

        let missing = adf.find_missing_statements();
        assert!(missing.is_empty());
    }

    #[test]
    fn test_find_missing_statements_simple() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_condition(s1, ConditionExpression::statement(s2))
            .unwrap();

        let missing = adf.find_missing_statements();
        assert_eq!(missing.len(), 1);
        assert!(missing.contains(&s2));
    }

    #[test]
    fn test_find_missing_statements_nested() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        let cond = ConditionExpression::and(&[
            ConditionExpression::statement(s2),
            ConditionExpression::negation(ConditionExpression::statement(s3)),
        ]);
        adf.add_condition(s1, cond).unwrap();

        let missing = adf.find_missing_statements();
        assert_eq!(missing.len(), 2);
        assert!(missing.contains(&s2));
        assert!(missing.contains(&s3));
    }

    #[test]
    fn test_find_missing_statements_complex() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let s4 = Statement::from(4);
        let _s5 = Statement::from(5);

        // s1 depends on s2 and s3
        adf.add_condition(
            s1,
            ConditionExpression::or(&[
                ConditionExpression::statement(s2),
                ConditionExpression::statement(s3),
            ]),
        )
        .unwrap();

        // s2 exists and depends on s4
        adf.add_statement(s2);
        adf.add_condition(s2, ConditionExpression::statement(s4))
            .unwrap();

        // s3 is missing and references s5 (also missing)
        // But s3 is already marked as missing from s1's condition

        let missing = adf.find_missing_statements();
        // Should find s3 (referenced by s1) and s4 (referenced by s2)
        // s5 is not referenced since s3 doesn't have a condition
        assert_eq!(missing.len(), 2);
        assert!(missing.contains(&s3));
        assert!(missing.contains(&s4));
    }

    #[test]
    fn test_find_missing_statements_implication() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        adf.add_condition(
            s1,
            ConditionExpression::implication(
                ConditionExpression::statement(s2),
                ConditionExpression::statement(s3),
            ),
        )
        .unwrap();

        let missing = adf.find_missing_statements();
        assert_eq!(missing.len(), 2);
        assert!(missing.contains(&s2));
        assert!(missing.contains(&s3));
    }

    #[test]
    fn test_find_missing_statements_equivalence() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        adf.add_condition(
            s1,
            ConditionExpression::equivalence(
                ConditionExpression::statement(s2),
                ConditionExpression::statement(s3),
            ),
        )
        .unwrap();

        let missing = adf.find_missing_statements();
        assert_eq!(missing.len(), 2);
        assert!(missing.contains(&s2));
        assert!(missing.contains(&s3));
    }

    #[test]
    fn test_find_missing_statements_xor() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        adf.add_condition(
            s1,
            ConditionExpression::exclusive_or(
                ConditionExpression::statement(s2),
                ConditionExpression::statement(s3),
            ),
        )
        .unwrap();

        let missing = adf.find_missing_statements();
        assert_eq!(missing.len(), 2);
        assert!(missing.contains(&s2));
        assert!(missing.contains(&s3));
    }

    // Tests for fix_missing_statements
    #[test]
    fn test_fix_missing_statements_none() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        adf.add_condition(s1, ConditionExpression::constant(true))
            .unwrap();
        let len_before = adf.len();

        adf.fix_missing_statements();
        assert_eq!(adf.len(), len_before);
    }

    #[test]
    fn test_fix_missing_statements_simple() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_condition(s1, ConditionExpression::statement(s2))
            .unwrap();
        assert_eq!(adf.len(), 1);

        adf.fix_missing_statements();
        assert_eq!(adf.len(), 2);
        assert!(adf.has_statement(s2));
        assert!(adf.get_condition(s2).is_none());
    }

    #[test]
    fn test_fix_missing_statements_complex() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let s4 = Statement::from(4);

        adf.add_condition(
            s1,
            ConditionExpression::and(&[
                ConditionExpression::statement(s2),
                ConditionExpression::or(&[
                    ConditionExpression::statement(s3),
                    ConditionExpression::statement(s4),
                ]),
            ]),
        )
        .unwrap();
        assert_eq!(adf.len(), 1);

        adf.fix_missing_statements();
        assert_eq!(adf.len(), 4);

        // All missing statements should now exist without conditions
        assert!(adf.get_condition(s2).is_none());
        assert!(adf.get_condition(s3).is_none());
        assert!(adf.get_condition(s4).is_none());
    }

    #[test]
    fn test_fix_missing_statements_idempotent() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_condition(s1, ConditionExpression::statement(s2))
            .unwrap();

        adf.fix_missing_statements();
        let len_after_first = adf.len();

        adf.fix_missing_statements();
        assert_eq!(adf.len(), len_after_first);
    }

    // Tests for statements iterator
    #[test]
    fn test_statements_empty() {
        let adf = AdfExpressions::new();
        assert_eq!(adf.statements().count(), 0);
    }

    #[test]
    fn test_statements_single() {
        let mut adf = AdfExpressions::new();
        adf.add_statement(Statement::from(5));
        let stmts: Vec<_> = adf.statements().collect();
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0], Statement::from(5));
    }

    #[test]
    fn test_statements_multiple() {
        let mut adf = AdfExpressions::new();
        adf.add_statement(Statement::from(3));
        adf.add_statement(Statement::from(1));
        adf.add_statement(Statement::from(2));

        // Should be sorted (BTreeMap)
        let stmts: Vec<_> = adf.statements().collect();
        assert_eq!(
            stmts,
            vec![Statement::from(1), Statement::from(2), Statement::from(3)]
        );
    }

    #[test]
    fn test_statements_with_and_without_conditions() {
        let mut adf = AdfExpressions::new();
        adf.add_statement(Statement::from(1));
        adf.add_condition(Statement::from(2), ConditionExpression::constant(true))
            .unwrap();
        adf.add_statement(Statement::from(3));

        // All statements should be present in sorted order
        let stmts: Vec<_> = adf.statements().collect();
        assert_eq!(
            stmts,
            vec![Statement::from(1), Statement::from(2), Statement::from(3)]
        );
    }

    // Tests for Default implementation
    #[test]
    fn test_default_creates_empty_adf() {
        let adf = AdfExpressions::default();
        assert!(adf.is_empty());
        assert_eq!(adf.len(), 0);
    }

    #[test]
    fn test_default_equivalent_to_new() {
        let adf1 = AdfExpressions::new();
        let adf2 = AdfExpressions::default();
        assert_eq!(adf1, adf2);
    }

    // Tests for has_statement
    #[test]
    fn test_has_statement_exists() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        adf.add_statement(s1);
        assert!(adf.has_statement(s1));
    }

    #[test]
    fn test_has_statement_does_not_exist() {
        let adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        assert!(!adf.has_statement(s1));
    }

    #[test]
    fn test_has_statement_with_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        adf.add_condition(s1, ConditionExpression::constant(true))
            .unwrap();
        assert!(adf.has_statement(s1));
    }

    // Tests for parse_and_fix
    #[test]
    fn test_parse_and_fix_no_missing() {
        let input = r#"
s(1).
s(2).
ac(1, c(v)).
ac(2, neg(1)).
"#;
        let adf = AdfExpressions::parse_and_fix(input).unwrap();
        assert_eq!(adf.len(), 2);
    }

    #[test]
    fn test_parse_and_fix_with_missing() {
        let input = r#"
s(1).
ac(1, and(2, 3)).
"#;
        let adf = AdfExpressions::parse_and_fix(input).unwrap();
        assert_eq!(adf.len(), 3);
        assert!(adf.has_statement(Statement::from(1)));
        assert!(adf.has_statement(Statement::from(2)));
        assert!(adf.has_statement(Statement::from(3)));
        // s1 should have a condition
        assert!(adf.get_condition(Statement::from(1)).is_some());
        // s2 and s3 should not have conditions
        assert!(adf.get_condition(Statement::from(2)).is_none());
        assert!(adf.get_condition(Statement::from(3)).is_none());
    }

    // Tests for parse_file
    #[test]
    fn test_parse_file_success() {
        use std::path::Path;

        let test_dir = Path::new("test_instances");
        if !test_dir.exists() {
            // Skip test if directory doesn't exist
            return;
        }

        let test_file = test_dir.join(
            "adfgen_acyc_a_02_s_02_b_02_t_02_x_02_c_sXOR_ABA2AF_afinput_exp_acyclic_depvary_step1_batch_yyy03_10_21.apx.adf",
        );

        let adf = AdfExpressions::parse_file(&test_file).unwrap();
        assert_eq!(adf.len(), 10);
    }

    #[test]
    fn test_parse_file_nonexistent() {
        let result = AdfExpressions::parse_file("nonexistent_file.adf");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Failed to read file"));
    }

    // Tests for parse_and_fix_file
    #[test]
    fn test_parse_and_fix_file_success() {
        use std::fs;
        use std::io::Write;

        // Create a temporary file with missing statements
        let temp_file = "test_temp_missing.adf";
        {
            let mut file = fs::File::create(temp_file).unwrap();
            writeln!(file, "s(1).").unwrap();
            writeln!(file, "ac(1, and(2, 3)).").unwrap();
        }

        let adf = AdfExpressions::parse_and_fix_file(temp_file).unwrap();
        assert_eq!(adf.len(), 3);
        assert!(adf.has_statement(Statement::from(2)));
        assert!(adf.has_statement(Statement::from(3)));

        // Clean up
        fs::remove_file(temp_file).unwrap();
    }

    // Tests for write
    #[test]
    fn test_write_empty() {
        let adf = AdfExpressions::new();
        let output = adf.write();
        assert_eq!(output, "");
    }

    #[test]
    fn test_write_statement_without_condition() {
        let mut adf = AdfExpressions::new();
        adf.add_statement(Statement::from(1));
        let output = adf.write();
        assert_eq!(output, "s(1).\n");
    }

    #[test]
    fn test_write_statement_with_condition() {
        let mut adf = AdfExpressions::new();
        adf.add_condition(Statement::from(1), ConditionExpression::constant(true))
            .unwrap();
        let output = adf.write();
        assert_eq!(output, "s(1).\nac(1,c(v)).\n");
    }

    #[test]
    fn test_write_mixed_statements() {
        let mut adf = AdfExpressions::new();
        adf.add_statement(Statement::from(1));
        adf.add_condition(Statement::from(2), ConditionExpression::constant(false))
            .unwrap();
        adf.add_statement(Statement::from(3));
        let output = adf.write();
        let expected = "s(1).\ns(2).\ns(3).\nac(2,c(f)).\n";
        assert_eq!(output, expected);
    }

    #[test]
    fn test_write_complex_expression() {
        let mut adf = AdfExpressions::new();
        let expr = ConditionExpression::and(&[
            ConditionExpression::statement(Statement::from(2)),
            ConditionExpression::negation(ConditionExpression::statement(Statement::from(3))),
        ]);
        adf.add_condition(Statement::from(1), expr).unwrap();
        let output = adf.write();
        assert_eq!(output, "s(1).\nac(1,and(2,neg(3))).\n");
    }

    #[test]
    fn test_write_sorted_order() {
        let mut adf = AdfExpressions::new();
        // Add in random order
        adf.add_statement(Statement::from(5));
        adf.add_statement(Statement::from(1));
        adf.add_statement(Statement::from(3));
        let output = adf.write();
        // Should be written in sorted order
        let expected = "s(1).\ns(3).\ns(5).\n";
        assert_eq!(output, expected);
    }

    #[test]
    fn test_write_parse_roundtrip() {
        let input = "s(1).\ns(2).\nac(1,c(v)).\nac(2,neg(1)).\n";
        let adf = AdfExpressions::parse(input).unwrap();
        let output = adf.write();

        // Parse the output and compare
        let adf2 = AdfExpressions::parse(&output).unwrap();
        assert_eq!(adf, adf2);
    }

    #[test]
    fn test_write_real_example() {
        let input = r#"
s(7).
s(4).
s(8).
s(3).
s(5).
s(9).
s(10).
s(1).
s(6).
s(2).
ac(7,c(v)).
ac(4,6).
ac(8,or(neg(1),7)).
ac(3,and(or(7,neg(6)),2)).
ac(5,4).
ac(9,neg(7)).
ac(10,and(neg(2),6)).
ac(1,and(neg(7),2)).
ac(6,neg(7)).
ac(2,and(neg(9),neg(6))).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        let output = adf.write();

        // Parse the output
        let adf2 = AdfExpressions::parse(&output).unwrap();

        // Should be equal
        assert_eq!(adf, adf2);

        // Check that all statements are declared and have conditions
        for i in 1..=10 {
            assert!(output.contains(&format!("s({}).", i)));
            assert!(output.contains(&format!("ac({},", i)));
        }
    }

    // Tests for write_file
    #[test]
    fn test_write_file_success() {
        use std::fs;

        let mut adf = AdfExpressions::new();
        adf.add_statement(Statement::from(1));
        adf.add_condition(Statement::from(2), ConditionExpression::constant(true))
            .unwrap();

        let temp_file = "test_temp_write.adf";
        adf.write_file(temp_file).unwrap();

        // Read back and verify
        let content = fs::read_to_string(temp_file).unwrap();
        assert_eq!(content, "s(1).\ns(2).\nac(2,c(v)).\n");

        // Clean up
        fs::remove_file(temp_file).unwrap();
    }

    #[test]
    fn test_write_file_roundtrip() {
        use std::fs;

        let mut adf = AdfExpressions::new();
        adf.add_condition(
            Statement::from(1),
            ConditionExpression::or(&[
                ConditionExpression::statement(Statement::from(2)),
                ConditionExpression::statement(Statement::from(3)),
            ]),
        )
        .unwrap();
        adf.add_statement(Statement::from(2));
        adf.add_statement(Statement::from(3));

        let temp_file = "test_temp_roundtrip.adf";
        adf.write_file(temp_file).unwrap();

        // Read back and parse
        let adf2 = AdfExpressions::parse_file(temp_file).unwrap();
        assert_eq!(adf, adf2);

        // Clean up
        fs::remove_file(temp_file).unwrap();
    }

    // Comprehensive test: parse and write all test instances
    #[test]
    fn test_parse_write_all_test_instances() {
        use std::collections::HashSet;
        use std::fs;
        use std::path::Path;

        let test_dir = Path::new("test_instances");
        if !test_dir.exists() {
            // Skip test if directory doesn't exist
            return;
        }

        let entries = fs::read_dir(test_dir).unwrap();
        let mut count = 0;
        let mut errors = Vec::new();

        for entry in entries {
            let entry = entry.unwrap();
            let path = entry.path();

            if path.extension().and_then(|s| s.to_str()) == Some("adf") {
                count += 1;
                let original_content = fs::read_to_string(&path).unwrap();

                match AdfExpressions::parse(&original_content) {
                    Ok(adf) => {
                        // Write it back
                        let written_content = adf.write();

                        // Parse the written content
                        match AdfExpressions::parse(&written_content) {
                            Ok(adf2) => {
                                // The ADFs should be equal
                                if adf != adf2 {
                                    errors.push((
                                        path.clone(),
                                        "ADF changed after parse-write-parse roundtrip".to_string(),
                                    ));
                                    continue;
                                }

                                // Compare line sets (order may differ)
                                let original_lines: HashSet<&str> = original_content
                                    .lines()
                                    .map(|l| l.trim())
                                    .filter(|l| !l.is_empty() && !l.starts_with('#'))
                                    .collect();

                                let written_lines: HashSet<&str> = written_content
                                    .lines()
                                    .map(|l| l.trim())
                                    .filter(|l| !l.is_empty())
                                    .collect();

                                if original_lines != written_lines {
                                    errors.push((
                                        path.clone(),
                                        format!(
                                            "Line sets differ. Original: {}, Written: {}",
                                            original_lines.len(),
                                            written_lines.len()
                                        ),
                                    ));
                                }
                            }
                            Err(e) => {
                                errors.push((
                                    path.clone(),
                                    format!("Failed to parse written content: {}", e),
                                ));
                            }
                        }
                    }
                    Err(e) => {
                        errors.push((path.clone(), format!("Failed to parse original: {}", e)));
                    }
                }
            }
        }

        if !errors.is_empty() {
            eprintln!(
                "Failed roundtrip test on {} out of {} files:",
                errors.len(),
                count
            );
            for (path, error) in &errors {
                eprintln!("  {:?}: {}", path, error);
            }
            panic!("Some test instances failed roundtrip test");
        }

        println!(
            "Successfully roundtrip tested {} test instance files",
            count
        );
    }
}
