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
    pub fn get_condition(&self, statement: &Statement) -> Option<&ConditionExpression> {
        self.conditions.get(statement).and_then(|opt| opt.as_ref())
    }

    /// Check if a statement exists in the ADF (with or without a condition).
    pub fn has_statement(&self, statement: &Statement) -> bool {
        self.conditions.contains_key(statement)
    }

    /// Get all statements in the ADF.
    ///
    /// The statements are returned in sorted order (by their index) because they are
    /// stored in a [`BTreeMap`].
    pub fn statements(&self) -> impl Iterator<Item = &Statement> {
        self.conditions.keys()
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
    /// - `s(label).` or `statement(label).` to declare a statement
    /// - `ac(label, expression).` to declare an acceptance condition
    ///
    /// Labels can be numeric (e.g., `1`, `42`) or string identifiers (e.g., `foo`, `bar`).
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

            // Parse statement declaration: s(label). or statement(label).
            let is_short_form = line.starts_with("s(") && line.ends_with(").");
            let is_long_form = line.starts_with("statement(") && line.ends_with(").");

            if is_short_form || is_long_form {
                let label_str = if is_short_form {
                    &line[2..line.len() - 2]
                } else {
                    &line[10..line.len() - 2]
                };

                let label_str = label_str.trim();

                // Try to parse as number first, otherwise use as string label
                let statement = Statement::from(label_str);

                // Insert statement with no condition if not already present
                adf.conditions.entry(statement).or_insert(None);
                continue;
            }

            // Parse acceptance condition: ac(label, expression).
            if line.starts_with("ac(") && line.ends_with(").") {
                // Find the comma that separates the statement label from the expression
                let content = &line[3..line.len() - 2];
                let comma_pos = content.find(',').ok_or_else(|| {
                    format!(
                        "Line {}: Missing comma in acceptance condition",
                        line_num + 1
                    )
                })?;

                let label_str = content[..comma_pos].trim();
                let expr_str = content[comma_pos + 1..].trim();

                // Try to parse as number first, otherwise use as string label
                let statement = Statement::from(label_str);

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
                        statement
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
            return Err(format!("Statement {} already has a condition", statement));
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
            .filter_map(|(stmt, cond)| cond.as_ref().map(|c| (stmt.clone(), c)))
    }

    /// Get an iterator over all statements that have no condition.
    ///
    /// The statements are returned in sorted order (by their index) because they are
    /// stored in a [`BTreeMap`].
    pub fn free_statements(&self) -> impl Iterator<Item = Statement> {
        self.conditions.iter().filter_map(|(stmt, cond)| {
            if cond.is_none() {
                Some(stmt.clone())
            } else {
                None
            }
        })
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
            output.push_str(&format!("s({}).\n", statement));
        }

        // Second pass: write all ac(N, expr) declarations
        for (statement, condition) in &self.conditions {
            if let Some(expr) = condition {
                output.push_str(&format!("ac({},{}).\n", statement, expr));
            }
        }

        output
    }

    /// Write the ADF to a file in the `.adf` file format.
    pub fn write_file(&self, path: impl AsRef<std::path::Path>) -> Result<(), String> {
        let content = self.write();
        std::fs::write(path.as_ref(), content).map_err(|e| format!("Failed to write file: {}", e))
    }

    /// Substitute all occurrences of a statement with a condition expression in all conditions.
    ///
    /// This method applies the substitution to all conditions in the ADF. The statement
    /// being replaced can still exist in the ADF as a declared statement; only its
    /// occurrences within conditions are replaced.
    ///
    /// # Arguments
    ///
    /// * `statement` - The statement to replace in all conditions
    /// * `replacement` - The expression to substitute in place of the statement
    ///
    /// # Example
    ///
    /// ```
    /// # use biodivine_bass::{AdfExpressions, ConditionExpression, Statement};
    /// let mut adf = AdfExpressions::new();
    /// let s1 = Statement::from(1);
    /// let s2 = Statement::from(2);
    /// let s3 = Statement::from(3);
    ///
    /// // Add condition: ac(1, and(2, 3))
    /// adf.add_condition(s1.clone(), ConditionExpression::and(&[
    ///     ConditionExpression::statement(s2.clone()),
    ///     ConditionExpression::statement(s3.clone()),
    /// ])).unwrap();
    ///
    /// // Substitute s2 with neg(s3)
    /// adf.substitute_statement(&s2, &ConditionExpression::negation(
    ///     ConditionExpression::statement(s3.clone())
    /// ));
    ///
    /// // Now s1's condition is: and(neg(3), 3)
    /// assert_eq!(adf.get_condition(&s1).unwrap().to_string(), "and(neg(3),3)");
    /// ```
    pub fn substitute_statement(
        &mut self,
        statement: &Statement,
        replacement: &ConditionExpression,
    ) {
        for (_, condition) in self.conditions.iter_mut() {
            if let Some(cond) = condition {
                *cond = cond.substitute(statement, replacement);
            }
        }
    }

    /// Convert all n-ary AND and OR operators to binary operators in all conditions.
    ///
    /// This method applies the binarization transformation to every condition in the ADF.
    /// N-ary AND and OR operations are converted to left-associative binary operations:
    /// - `and(a, b, c)` becomes `and(and(a, b), c)`
    /// - `or(a, b, c, d)` becomes `or(or(or(a, b), c), d)`
    ///
    /// See [`ConditionExpression::binarize`] for details on the transformation.
    ///
    /// # Example
    ///
    /// ```
    /// # use biodivine_bass::{AdfExpressions, ConditionExpression, Statement};
    /// let mut adf = AdfExpressions::new();
    /// let s1 = Statement::from(1);
    /// let s2 = Statement::from(2);
    /// let s3 = Statement::from(3);
    ///
    /// // Add condition: ac(1, and(2, 3, 1))
    /// adf.add_condition(s1.clone(), ConditionExpression::and(&[
    ///     ConditionExpression::statement(s2),
    ///     ConditionExpression::statement(s3),
    ///     ConditionExpression::statement(s1.clone()),
    /// ])).unwrap();
    ///
    /// adf.binarize_operators();
    ///
    /// // Now the condition is: ac(1, and(and(2, 3), 1))
    /// assert_eq!(adf.get_condition(&s1).unwrap().to_string(), "and(and(2,3),1)");
    /// ```
    pub fn binarize_operators(&mut self) {
        for (_, condition) in self.conditions.iter_mut() {
            if let Some(cond) = condition {
                // Optimization: only binarize if expression has non-binary operators
                if cond.has_non_binary_operators() {
                    *cond = cond.binarize();
                }
            }
        }
    }

    /// Build a dependency map showing which statements are referenced in each condition.
    ///
    /// Returns a map where the key is a statement that has a condition, and the value
    /// is a set of statements that appear in that condition.
    ///
    /// This is useful for optimizing operations that need to know which conditions
    /// reference which statements.
    ///
    /// # Example
    ///
    /// ```
    /// # use biodivine_bass::{AdfExpressions, ConditionExpression, Statement};
    /// let mut adf = AdfExpressions::new();
    /// let s1 = Statement::from(1);
    /// let s2 = Statement::from(2);
    /// let s3 = Statement::from(3);
    ///
    /// // ac(1, and(2, 3))
    /// adf.add_condition(s1.clone(), ConditionExpression::and(&[
    ///     ConditionExpression::statement(s2.clone()),
    ///     ConditionExpression::statement(s3.clone()),
    /// ])).unwrap();
    ///
    /// let deps = adf.build_dependency_map();
    /// let s1_deps = deps.get(&s1).unwrap();
    /// assert!(s1_deps.contains(&s2));
    /// assert!(s1_deps.contains(&s3));
    /// ```
    pub fn build_dependency_map(
        &self,
    ) -> BTreeMap<Statement, std::collections::BTreeSet<Statement>> {
        let mut dep_map = BTreeMap::new();

        for (statement, condition) in &self.conditions {
            if let Some(cond) = condition {
                let statements = cond.collect_statements();
                dep_map.insert(statement.clone(), statements.into_iter().collect());
            }
        }

        dep_map
    }

    /// Rename multiple statements throughout the entire ADF using a map.
    ///
    /// This method renames multiple statements both in the statement list and in all conditions
    /// in a single pass. This is more efficient than calling `rename_statement` multiple times.
    ///
    /// For each entry in the map:
    /// - The old statement is removed from the statement list
    /// - The new statement is added to the statement list  
    /// - If the old statement had a condition, it's moved to the new statement
    /// - All occurrences of old statements in conditions are replaced with new statements
    ///
    /// # Arguments
    ///
    /// * `renamings` - A map from old statement names to new statement names
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` on success, or an error if:
    /// - Any old statement doesn't exist in the ADF
    /// - Any new statement already exists in the ADF (and is not being renamed)
    /// - The renaming would create conflicts (e.g., swapping two statements)
    ///
    /// # Example
    ///
    /// ```
    /// # use biodivine_bass::{AdfExpressions, ConditionExpression, Statement};
    /// # use std::collections::BTreeMap;
    /// let mut adf = AdfExpressions::new();
    /// let s1 = Statement::from(1);
    /// let s2 = Statement::from(2);
    /// let s3 = Statement::from(3);
    ///
    /// // Add conditions
    /// adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone())).unwrap();
    /// adf.add_condition(s2.clone(), ConditionExpression::statement(s3.clone())).unwrap();
    /// adf.add_statement(s3.clone());
    ///
    /// // Rename: 1->10, 2->20, 3->30
    /// let mut renamings = BTreeMap::new();
    /// renamings.insert(s1.clone(), Statement::from(10));
    /// renamings.insert(s2.clone(), Statement::from(20));
    /// renamings.insert(s3.clone(), Statement::from(30));
    /// adf.rename_statements(&renamings).unwrap();
    ///
    /// // Original statements are gone, new ones exist
    /// assert!(!adf.has_statement(&s1));
    /// assert!(adf.has_statement(&Statement::from(10)));
    /// assert_eq!(adf.get_condition(&Statement::from(10)).unwrap().to_string(), "20");
    /// assert_eq!(adf.get_condition(&Statement::from(20)).unwrap().to_string(), "30");
    /// ```
    pub fn rename_statements(
        &mut self,
        renamings: &BTreeMap<Statement, Statement>,
    ) -> Result<(), String> {
        // Optimization: if map is empty, do nothing
        if renamings.is_empty() {
            return Ok(());
        }

        // Validation: check that all old statements exist
        for old_stmt in renamings.keys() {
            if !self.conditions.contains_key(old_stmt) {
                return Err(format!("Statement {} does not exist in the ADF", old_stmt));
            }
        }

        // Validation: check that new statements don't conflict with existing ones
        // (unless they're being renamed themselves)
        for new_stmt in renamings.values() {
            if self.conditions.contains_key(new_stmt) && !renamings.contains_key(new_stmt) {
                return Err(format!(
                    "Statement {} already exists in the ADF and is not being renamed",
                    new_stmt
                ));
            }
        }

        // Build substitution map for conditions
        let mut substitutions = BTreeMap::new();
        for (old_stmt, new_stmt) in renamings {
            substitutions.insert(
                old_stmt.clone(),
                ConditionExpression::statement(new_stmt.clone()),
            );
        }

        // Apply substitutions to all conditions
        for (_, condition) in self.conditions.iter_mut() {
            if let Some(cond) = condition {
                *cond = cond.substitute_many(&substitutions);
            }
        }

        // Rename statements in the statement list
        // Collect old conditions first to avoid borrowing issues
        let old_conditions: Vec<_> = renamings
            .keys()
            .map(|old_stmt| (old_stmt.clone(), self.conditions.remove(old_stmt)))
            .collect();

        // Insert with new names
        for (old_stmt, old_condition) in old_conditions {
            if let Some(new_stmt) = renamings.get(&old_stmt) {
                self.conditions
                    .insert(new_stmt.clone(), old_condition.flatten());
            }
        }

        Ok(())
    }

    /// Rename a statement throughout the entire ADF.
    ///
    /// This method renames a statement both in the statement list and in all conditions.
    /// If the old statement has a condition, it will be moved to the new statement.
    /// All occurrences of the old statement in conditions will be replaced with the new statement.
    ///
    /// If the new statement already exists, this method will fail and return an error.
    /// After renaming, the old statement will no longer exist in the ADF.
    ///
    /// # Arguments
    ///
    /// * `old_statement` - The statement to rename
    /// * `new_statement` - The new statement name
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` on success, or an error if:
    /// - The old statement doesn't exist in the ADF
    /// - The new statement already exists in the ADF
    ///
    /// # Example
    ///
    /// ```
    /// # use biodivine_bass::{AdfExpressions, ConditionExpression, Statement};
    /// let mut adf = AdfExpressions::new();
    /// let s1 = Statement::from(1);
    /// let s2 = Statement::from(2);
    ///
    /// // Add conditions: ac(1, 2), ac(2, 1)
    /// adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone())).unwrap();
    /// adf.add_condition(s2.clone(), ConditionExpression::statement(s1.clone())).unwrap();
    ///
    /// // Rename s1 to s99
    /// adf.rename_statement(&s1, &Statement::from(99)).unwrap();
    ///
    /// // Now s1 is gone, s99 exists
    /// assert!(!adf.has_statement(&s1));
    /// assert!(adf.has_statement(&Statement::from(99)));
    /// // ac(99, 2) and ac(2, 99)
    /// assert_eq!(adf.get_condition(&Statement::from(99)).unwrap().to_string(), "2");
    /// assert_eq!(adf.get_condition(&s2).unwrap().to_string(), "99");
    /// ```
    pub fn rename_statement(
        &mut self,
        old_statement: &Statement,
        new_statement: &Statement,
    ) -> Result<(), String> {
        // Check if old statement exists
        if !self.conditions.contains_key(old_statement) {
            return Err(format!(
                "Statement {} does not exist in the ADF",
                old_statement
            ));
        }

        // Check if new statement already exists
        if self.conditions.contains_key(new_statement) {
            return Err(format!(
                "Statement {} already exists in the ADF",
                new_statement
            ));
        }

        // Remove the old statement and get its condition
        let old_condition = self.conditions.remove(old_statement);

        // Substitute old statement with new statement in all conditions
        let replacement = ConditionExpression::statement(new_statement.clone());
        for (_, condition) in self.conditions.iter_mut() {
            if let Some(cond) = condition
                && cond.collect_statements().contains(old_statement)
            {
                *cond = cond.substitute(old_statement, &replacement);
            }
        }

        // Also substitute in the condition we just removed (if it exists)
        let new_condition = old_condition
            .map(|opt_cond| opt_cond.map(|cond| cond.substitute(old_statement, &replacement)));

        // Insert the new statement with the (possibly modified) condition
        self.conditions
            .insert(new_statement.clone(), new_condition.flatten());

        Ok(())
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
    use rstest::rstest;

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

        assert!(adf.has_statement(&s1));
        assert!(adf.has_statement(&s2));
        assert!(adf.get_condition(&s1).is_some());
        assert!(adf.get_condition(&s2).is_some());
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

        assert!(adf.get_condition(&s1).is_some());
        assert!(adf.get_condition(&s2).is_none());
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

        assert!(adf.get_condition(&s1).is_some());
        assert!(adf.get_condition(&s2).is_some());
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

        assert!(adf.get_condition(&s1).is_some());
        assert!(adf.get_condition(&s2).is_some());
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
            assert!(adf.get_condition(&stmt).is_some());
        }
    }

    #[rstest]
    #[case("A-")]
    #[case("B-")]
    #[case("C-")]
    #[case("T-")]
    #[case("adfgen_acyc")]
    #[case("adfgen_nacyc")]
    #[case("comma")]
    #[case("metro")]
    #[case("Small")]
    #[case("Medium")]
    fn test_parse_all_test_instances(#[case] prefix: &str) {
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

            if !entry.file_name().to_str().unwrap().starts_with(prefix) {
                // Skip file names that don't match the desired prefix.
                continue;
            }

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

        // Each filter should match at least one test file.
        assert!(count > 0);

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
    fn test_parse_statement_string_label() {
        // String labels are now valid
        let input = "s(abc).";
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 1);
        assert!(adf.has_statement(&Statement::from("abc")));
    }

    #[test]
    fn test_parse_condition_string_label() {
        // String labels are now valid in conditions
        let input = "ac(xyz, c(v)).";
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 1);
        assert!(adf.has_statement(&Statement::from("xyz")));
    }

    #[test]
    fn test_parse_invalid_expression() {
        // Unknown identifiers are now treated as statement labels, not invalid
        // Let's test an actually invalid expression syntax instead
        let input = "ac(1, and(,)).";
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
        assert!(adf.get_condition(&Statement::from(1)).is_some());
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

        adf.add_statement(s1.clone());
        assert_eq!(adf.len(), 1);
        assert!(adf.has_statement(&s1));
        assert!(adf.get_condition(&s1).is_none());
    }

    #[test]
    fn test_add_statement_existing() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        adf.add_statement(s1.clone());
        adf.add_statement(s1.clone()); // Should not error, just do nothing
        assert_eq!(adf.len(), 1);
    }

    #[test]
    fn test_add_statement_with_existing_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.add_condition(s1.clone(), cond.clone()).unwrap();
        adf.add_statement(s1.clone()); // Should not change existing condition
        assert_eq!(adf.len(), 1);
        assert!(adf.get_condition(&s1).is_some());
    }

    // Tests for add_condition
    #[test]
    fn test_add_condition_new_statement() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        let result = adf.add_condition(s1.clone(), cond);
        assert!(result.is_ok());
        assert_eq!(adf.len(), 1);
        assert!(adf.get_condition(&s1).is_some());
    }

    #[test]
    fn test_add_condition_existing_statement_no_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.add_statement(s1.clone());
        let result = adf.add_condition(s1.clone(), cond);
        assert!(result.is_ok());
        assert!(adf.get_condition(&s1).is_some());
    }

    #[test]
    fn test_add_condition_duplicate_fails() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond1 = ConditionExpression::constant(true);
        let cond2 = ConditionExpression::constant(false);

        adf.add_condition(s1.clone(), cond1).unwrap();
        let result = adf.add_condition(s1.clone(), cond2);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("already has a condition"));
    }

    // Tests for remove_statement
    #[test]
    fn test_remove_statement_existing() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_statement(s1.clone());
        adf.add_statement(s2.clone());
        assert_eq!(adf.len(), 2);

        adf.remove_statement(s1.clone());
        assert_eq!(adf.len(), 1);
        assert!(!adf.has_statement(&s1));
        assert!(adf.has_statement(&s2));
    }

    #[test]
    fn test_remove_statement_nonexistent() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        adf.remove_statement(s1.clone()); // Should not panic
        assert_eq!(adf.len(), 0);
    }

    #[test]
    fn test_remove_statement_with_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.add_condition(s1.clone(), cond).unwrap();
        adf.remove_statement(s1.clone());
        assert_eq!(adf.len(), 0);
    }

    // Tests for remove_condition
    #[test]
    fn test_remove_condition_existing() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.add_condition(s1.clone(), cond).unwrap();
        assert!(adf.get_condition(&s1).is_some());

        adf.remove_condition(s1.clone());
        assert_eq!(adf.len(), 1); // Statement still exists
        assert!(adf.get_condition(&s1).is_none());
    }

    #[test]
    fn test_remove_condition_nonexistent_statement() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        adf.remove_condition(s1.clone()); // Should not panic
        assert_eq!(adf.len(), 0);
    }

    #[test]
    fn test_remove_condition_already_none() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        adf.add_statement(s1.clone());
        adf.remove_condition(s1.clone()); // Should not panic
        assert!(adf.get_condition(&s1).is_none());
    }

    // Tests for update_condition
    #[test]
    fn test_update_condition_new_statement() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.update_condition(s1.clone(), cond);
        assert_eq!(adf.len(), 1);
        assert!(adf.get_condition(&s1).is_some());
    }

    #[test]
    fn test_update_condition_existing_no_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond = ConditionExpression::constant(true);

        adf.add_statement(s1.clone());
        adf.update_condition(s1.clone(), cond);
        assert!(adf.get_condition(&s1).is_some());
    }

    #[test]
    fn test_update_condition_existing_with_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let cond1 = ConditionExpression::constant(true);
        let cond2 = ConditionExpression::constant(false);

        adf.add_condition(s1.clone(), cond1).unwrap();
        adf.update_condition(s1.clone(), cond2.clone());

        let retrieved = adf.get_condition(&s1).unwrap();
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

        adf.add_statement(s1.clone());
        adf.add_condition(s2.clone(), ConditionExpression::constant(true))
            .unwrap();
        adf.add_statement(s3.clone());

        let free: Vec<_> = adf.free_statements().collect();
        assert_eq!(free.len(), 2);
        assert!(free.contains(&s1));
        assert!(free.contains(&s3));
    }

    // Tests for find_missing_statements
    #[test]
    fn test_find_missing_statements_none() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_statement(s1.clone());
        adf.add_statement(s2.clone());
        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();

        let missing = adf.find_missing_statements();
        assert!(missing.is_empty());
    }

    #[test]
    fn test_find_missing_statements_simple() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
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
            ConditionExpression::statement(s2.clone()),
            ConditionExpression::negation(ConditionExpression::statement(s3.clone())),
        ]);
        adf.add_condition(s1.clone(), cond).unwrap();

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
            s1.clone(),
            ConditionExpression::or(&[
                ConditionExpression::statement(s2.clone()),
                ConditionExpression::statement(s3.clone()),
            ]),
        )
        .unwrap();

        // s2 exists and depends on s4
        adf.add_statement(s2.clone());
        adf.add_condition(s2.clone(), ConditionExpression::statement(s4.clone()))
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
            s1.clone(),
            ConditionExpression::implication(
                ConditionExpression::statement(s2.clone()),
                ConditionExpression::statement(s3.clone()),
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
            s1.clone(),
            ConditionExpression::equivalence(
                ConditionExpression::statement(s2.clone()),
                ConditionExpression::statement(s3.clone()),
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
            s1.clone(),
            ConditionExpression::exclusive_or(
                ConditionExpression::statement(s2.clone()),
                ConditionExpression::statement(s3.clone()),
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

        adf.add_condition(s1.clone(), ConditionExpression::constant(true))
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

        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();
        assert_eq!(adf.len(), 1);

        adf.fix_missing_statements();
        assert_eq!(adf.len(), 2);
        assert!(adf.has_statement(&s2));
        assert!(adf.get_condition(&s2).is_none());
    }

    #[test]
    fn test_fix_missing_statements_complex() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let s4 = Statement::from(4);

        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::statement(s2.clone()),
                ConditionExpression::or(&[
                    ConditionExpression::statement(s3.clone()),
                    ConditionExpression::statement(s4.clone()),
                ]),
            ]),
        )
        .unwrap();
        assert_eq!(adf.len(), 1);

        adf.fix_missing_statements();
        assert_eq!(adf.len(), 4);

        // All missing statements should now exist without conditions
        assert!(adf.get_condition(&s2).is_none());
        assert!(adf.get_condition(&s3).is_none());
        assert!(adf.get_condition(&s4).is_none());
    }

    #[test]
    fn test_fix_missing_statements_idempotent() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
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
        assert_eq!(*stmts[0], Statement::from(5));
    }

    #[test]
    fn test_statements_multiple() {
        let mut adf = AdfExpressions::new();
        adf.add_statement(Statement::from(3));
        adf.add_statement(Statement::from(1));
        adf.add_statement(Statement::from(2));

        // Should be sorted (BTreeMap)
        let stmts: Vec<_> = adf.statements().cloned().collect();
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
        let stmts: Vec<_> = adf.statements().cloned().collect();
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
        adf.add_statement(s1.clone());
        assert!(adf.has_statement(&s1));
    }

    #[test]
    fn test_has_statement_does_not_exist() {
        let adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        assert!(!adf.has_statement(&s1));
    }

    #[test]
    fn test_has_statement_with_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        adf.add_condition(s1.clone(), ConditionExpression::constant(true))
            .unwrap();
        assert!(adf.has_statement(&s1));
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
        assert!(adf.has_statement(&Statement::from(1)));
        assert!(adf.has_statement(&Statement::from(2)));
        assert!(adf.has_statement(&Statement::from(3)));
        // s1 should have a condition
        assert!(adf.get_condition(&Statement::from(1)).is_some());
        // s2 and s3 should not have conditions
        assert!(adf.get_condition(&Statement::from(2)).is_none());
        assert!(adf.get_condition(&Statement::from(3)).is_none());
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
        assert!(adf.has_statement(&Statement::from(2)));
        assert!(adf.has_statement(&Statement::from(3)));

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

    // Tests for statement(X) syntax
    #[test]
    fn test_parse_statement_long_form() {
        let input = r#"
statement(1).
statement(2).
ac(1, c(v)).
ac(2, neg(1)).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 2);

        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        assert!(adf.has_statement(&s1));
        assert!(adf.has_statement(&s2));
        assert!(adf.get_condition(&s1).is_some());
        assert!(adf.get_condition(&s2).is_some());
    }

    #[test]
    fn test_parse_statement_mixed_forms() {
        let input = r#"
s(1).
statement(2).
ac(1, c(v)).
ac(2, neg(1)).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 2);

        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        assert!(adf.has_statement(&s1));
        assert!(adf.has_statement(&s2));
        assert!(adf.get_condition(&s1).is_some());
        assert!(adf.get_condition(&s2).is_some());
    }

    #[test]
    fn test_parse_string_labels() {
        let input = r#"
s(foo).
s(bar).
ac(foo, c(v)).
ac(bar, neg(foo)).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 2);

        let s_foo = Statement::from("foo");
        let s_bar = Statement::from("bar");

        assert!(adf.has_statement(&s_foo));
        assert!(adf.has_statement(&s_bar));
        assert!(adf.get_condition(&s_foo).is_some());
        assert!(adf.get_condition(&s_bar).is_some());
    }

    #[test]
    fn test_parse_string_labels_long_form() {
        let input = r#"
statement(alice).
statement(bob).
ac(alice, c(v)).
ac(bob, neg(alice)).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 2);

        let s_alice = Statement::from("alice");
        let s_bob = Statement::from("bob");

        assert!(adf.has_statement(&s_alice));
        assert!(adf.has_statement(&s_bob));
        assert!(adf.get_condition(&s_alice).is_some());
        assert!(adf.get_condition(&s_bob).is_some());
    }

    #[test]
    fn test_parse_mixed_numeric_and_string_labels() {
        let input = r#"
s(1).
s(foo).
ac(1, foo).
ac(foo, neg(1)).
"#;
        let adf = AdfExpressions::parse(input).unwrap();
        assert_eq!(adf.len(), 2);

        let s1 = Statement::from(1);
        let s_foo = Statement::from("foo");

        assert!(adf.has_statement(&s1));
        assert!(adf.has_statement(&s_foo));
        assert!(adf.get_condition(&s1).is_some());
        assert!(adf.get_condition(&s_foo).is_some());
    }

    // Tests for substitute_statement

    #[test]
    fn test_substitute_statement_simple() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();

        let replacement = ConditionExpression::constant(true);
        adf.substitute_statement(&s2, &replacement);

        let cond = adf.get_condition(&s1).unwrap();
        assert!(cond.is_constant());
        assert_eq!(cond.as_constant(), Some(true));
    }

    #[test]
    fn test_substitute_statement_multiple_conditions() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // ac(1, 2)
        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();
        // ac(2, and(3, 3))
        adf.add_condition(
            s2.clone(),
            ConditionExpression::and(&[
                ConditionExpression::statement(s3.clone()),
                ConditionExpression::statement(s3.clone()),
            ]),
        )
        .unwrap();

        let replacement = ConditionExpression::constant(false);
        adf.substitute_statement(&s3, &replacement);

        // s1's condition should be unchanged
        assert_eq!(adf.get_condition(&s1).unwrap().to_string(), "2");
        // s2's condition should have both s3 replaced
        assert_eq!(
            adf.get_condition(&s2).unwrap().to_string(),
            "and(c(f),c(f))"
        );
    }

    #[test]
    fn test_substitute_statement_no_occurrences() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();

        let original = adf.get_condition(&s1).unwrap().clone();
        let replacement = ConditionExpression::constant(true);
        adf.substitute_statement(&s3, &replacement);

        // Condition should be unchanged
        assert_eq!(adf.get_condition(&s1).unwrap(), &original);
    }

    #[test]
    fn test_substitute_statement_complex_expression() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // ac(1, and(or(2, 3), neg(2)))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::or(&[
                    ConditionExpression::statement(s2.clone()),
                    ConditionExpression::statement(s3.clone()),
                ]),
                ConditionExpression::negation(ConditionExpression::statement(s2.clone())),
            ]),
        )
        .unwrap();

        let replacement = ConditionExpression::constant(true);
        adf.substitute_statement(&s2, &replacement);

        // Result should be: and(or(c(v), 3), neg(c(v)))
        assert_eq!(
            adf.get_condition(&s1).unwrap().to_string(),
            "and(or(c(v),3),neg(c(v)))"
        );
    }

    #[test]
    fn test_substitute_statement_with_complex_replacement() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // ac(1, and(2, 3))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::statement(s2.clone()),
                ConditionExpression::statement(s3.clone()),
            ]),
        )
        .unwrap();

        // Replace s2 with "or(3, s3)"
        let replacement = ConditionExpression::or(&[
            ConditionExpression::statement(s3.clone()),
            ConditionExpression::statement(s3.clone()),
        ]);
        adf.substitute_statement(&s2, &replacement);

        // Result should be: and(or(3, 3), 3)
        assert_eq!(
            adf.get_condition(&s1).unwrap().to_string(),
            "and(or(3,3),3)"
        );
    }

    #[test]
    fn test_substitute_statement_free_statements_unchanged() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        // s1 has no condition
        adf.add_statement(s1.clone());
        // s2 has a condition
        adf.add_condition(s2.clone(), ConditionExpression::statement(s1.clone()))
            .unwrap();

        let replacement = ConditionExpression::constant(false);
        adf.substitute_statement(&s1, &replacement);

        // s1 should still be free (no condition)
        assert!(adf.get_condition(&s1).is_none());
        // s2's condition should be updated
        assert_eq!(adf.get_condition(&s2).unwrap().to_string(), "c(f)");
    }

    #[test]
    fn test_substitute_statement_chain() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // ac(1, 2)
        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();

        // First substitution: 2 -> 3
        adf.substitute_statement(&s2, &ConditionExpression::statement(s3.clone()));
        assert_eq!(adf.get_condition(&s1).unwrap().to_string(), "3");

        // Second substitution: 3 -> c(v)
        adf.substitute_statement(&s3, &ConditionExpression::constant(true));
        assert_eq!(adf.get_condition(&s1).unwrap().to_string(), "c(v)");
    }

    #[test]
    fn test_substitute_statement_self_reference() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        // ac(1, 1) - self-referential
        adf.add_condition(s1.clone(), ConditionExpression::statement(s1.clone()))
            .unwrap();

        let replacement = ConditionExpression::constant(false);
        adf.substitute_statement(&s1, &replacement);

        // The self-reference should be replaced
        assert_eq!(adf.get_condition(&s1).unwrap().to_string(), "c(f)");
    }

    #[test]
    fn test_substitute_statement_all_operators() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s_target = Statement::from(99);

        // Test with implication
        adf.add_condition(
            Statement::from(10),
            ConditionExpression::implication(
                ConditionExpression::statement(s_target.clone()),
                ConditionExpression::statement(s1.clone()),
            ),
        )
        .unwrap();

        // Test with equivalence
        adf.add_condition(
            Statement::from(11),
            ConditionExpression::equivalence(
                ConditionExpression::statement(s_target.clone()),
                ConditionExpression::statement(s1.clone()),
            ),
        )
        .unwrap();

        // Test with xor
        adf.add_condition(
            Statement::from(12),
            ConditionExpression::exclusive_or(
                ConditionExpression::statement(s_target.clone()),
                ConditionExpression::statement(s2.clone()),
            ),
        )
        .unwrap();

        let replacement = ConditionExpression::constant(true);
        adf.substitute_statement(&s_target, &replacement);

        // Check all conditions have been updated
        assert_eq!(
            adf.get_condition(&Statement::from(10)).unwrap().to_string(),
            "imp(c(v),1)"
        );
        assert_eq!(
            adf.get_condition(&Statement::from(11)).unwrap().to_string(),
            "iff(c(v),1)"
        );
        assert_eq!(
            adf.get_condition(&Statement::from(12)).unwrap().to_string(),
            "xor(c(v),2)"
        );
    }

    #[test]
    fn test_substitute_statement_empty_adf() {
        let mut adf = AdfExpressions::new();

        // Should not panic on empty ADF
        adf.substitute_statement(&Statement::from(1), &ConditionExpression::constant(true));

        assert!(adf.is_empty());
    }

    #[test]
    fn test_substitute_statement_preserves_statements() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();
        adf.add_statement(s2.clone());
        adf.add_statement(s3.clone());

        let replacement = ConditionExpression::constant(true);
        adf.substitute_statement(&s2, &replacement);

        // All statements should still exist (substitution doesn't remove statements)
        assert_eq!(adf.len(), 3);
        assert!(adf.has_statement(&s1));
        assert!(adf.has_statement(&s2));
        assert!(adf.has_statement(&s3));
    }

    #[test]
    fn test_substitute_statement_parse_roundtrip() {
        let input = r#"
s(1).
s(2).
s(3).
ac(1, and(2, 3)).
ac(2, or(1, 3)).
"#;
        let mut adf = AdfExpressions::parse(input).unwrap();

        // Substitute s3 with neg(s1)
        adf.substitute_statement(
            &Statement::from(3),
            &ConditionExpression::negation(ConditionExpression::statement(Statement::from(1))),
        );

        // Write and reparse
        let output = adf.write();
        let adf2 = AdfExpressions::parse(&output).unwrap();

        // Should be equal
        assert_eq!(adf, adf2);

        // Verify the substitution took effect
        assert_eq!(
            adf2.get_condition(&Statement::from(1)).unwrap().to_string(),
            "and(2,neg(1))"
        );
        assert_eq!(
            adf2.get_condition(&Statement::from(2)).unwrap().to_string(),
            "or(1,neg(1))"
        );
    }

    // Tests for build_dependency_map

    #[test]
    fn test_build_dependency_map_empty() {
        let adf = AdfExpressions::new();
        let deps = adf.build_dependency_map();
        assert!(deps.is_empty());
    }

    #[test]
    fn test_build_dependency_map_simple() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // ac(1, and(2, 3))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::statement(s2.clone()),
                ConditionExpression::statement(s3.clone()),
            ]),
        )
        .unwrap();

        let deps = adf.build_dependency_map();
        assert_eq!(deps.len(), 1);

        let s1_deps = deps.get(&s1).unwrap();
        assert_eq!(s1_deps.len(), 2);
        assert!(s1_deps.contains(&s2));
        assert!(s1_deps.contains(&s3));
    }

    #[test]
    fn test_build_dependency_map_no_dependencies() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        // ac(1, c(v))
        adf.add_condition(s1.clone(), ConditionExpression::constant(true))
            .unwrap();

        let deps = adf.build_dependency_map();
        let s1_deps = deps.get(&s1).unwrap();
        assert!(s1_deps.is_empty());
    }

    #[test]
    fn test_build_dependency_map_self_reference() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        // ac(1, neg(1))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::negation(ConditionExpression::statement(s1.clone())),
        )
        .unwrap();

        let deps = adf.build_dependency_map();
        let s1_deps = deps.get(&s1).unwrap();
        assert_eq!(s1_deps.len(), 1);
        assert!(s1_deps.contains(&s1));
    }

    #[test]
    fn test_build_dependency_map_multiple_conditions() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // ac(1, 2)
        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();
        // ac(2, or(1, 3))
        adf.add_condition(
            s2.clone(),
            ConditionExpression::or(&[
                ConditionExpression::statement(s1.clone()),
                ConditionExpression::statement(s3.clone()),
            ]),
        )
        .unwrap();

        let deps = adf.build_dependency_map();
        assert_eq!(deps.len(), 2);

        let s1_deps = deps.get(&s1).unwrap();
        assert_eq!(s1_deps.len(), 1);
        assert!(s1_deps.contains(&s2));

        let s2_deps = deps.get(&s2).unwrap();
        assert_eq!(s2_deps.len(), 2);
        assert!(s2_deps.contains(&s1));
        assert!(s2_deps.contains(&s3));
    }

    #[test]
    fn test_build_dependency_map_free_statements_excluded() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        adf.add_statement(s1.clone());
        adf.add_condition(s2.clone(), ConditionExpression::statement(s3.clone()))
            .unwrap();

        let deps = adf.build_dependency_map();
        // s1 has no condition, so it shouldn't be in the map
        assert!(!deps.contains_key(&s1));
        assert!(deps.contains_key(&s2));
    }

    #[test]
    fn test_build_dependency_map_complex_nested() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        // ac(1, imp(and(2, 3), or(4, 5)))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::implication(
                ConditionExpression::and(&[
                    ConditionExpression::statement(Statement::from(2)),
                    ConditionExpression::statement(Statement::from(3)),
                ]),
                ConditionExpression::or(&[
                    ConditionExpression::statement(Statement::from(4)),
                    ConditionExpression::statement(Statement::from(5)),
                ]),
            ),
        )
        .unwrap();

        let deps = adf.build_dependency_map();
        let s1_deps = deps.get(&s1).unwrap();
        assert_eq!(s1_deps.len(), 4);
        assert!(s1_deps.contains(&Statement::from(2)));
        assert!(s1_deps.contains(&Statement::from(3)));
        assert!(s1_deps.contains(&Statement::from(4)));
        assert!(s1_deps.contains(&Statement::from(5)));
    }

    #[test]
    fn test_build_dependency_map_duplicates_removed() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        // ac(1, or(2, 2, 2))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::or(&[
                ConditionExpression::statement(s2.clone()),
                ConditionExpression::statement(s2.clone()),
                ConditionExpression::statement(s2.clone()),
            ]),
        )
        .unwrap();

        let deps = adf.build_dependency_map();
        let s1_deps = deps.get(&s1).unwrap();
        // Duplicates should be removed (BTreeSet)
        assert_eq!(s1_deps.len(), 1);
        assert!(s1_deps.contains(&s2));
    }

    // Tests for binarize_operators

    #[test]
    fn test_binarize_operators_empty_adf() {
        let mut adf = AdfExpressions::new();
        adf.binarize_operators();
        assert!(adf.is_empty());
    }

    #[test]
    fn test_binarize_operators_simple() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // ac(1, and(2, 3))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::statement(s2),
                ConditionExpression::statement(s3),
            ]),
        )
        .unwrap();

        adf.binarize_operators();

        // Should remain and(2, 3) - already binary
        assert_eq!(adf.get_condition(&s1).unwrap().to_string(), "and(2,3)");
    }

    #[test]
    fn test_binarize_operators_ternary_and() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        // ac(1, and(2, 3, 4))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::statement(Statement::from(2)),
                ConditionExpression::statement(Statement::from(3)),
                ConditionExpression::statement(Statement::from(4)),
            ]),
        )
        .unwrap();

        adf.binarize_operators();

        // Should become and(and(2, 3), 4)
        assert_eq!(
            adf.get_condition(&s1).unwrap().to_string(),
            "and(and(2,3),4)"
        );
    }

    #[test]
    fn test_binarize_operators_ternary_or() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        // ac(1, or(2, 3, 4))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::or(&[
                ConditionExpression::statement(Statement::from(2)),
                ConditionExpression::statement(Statement::from(3)),
                ConditionExpression::statement(Statement::from(4)),
            ]),
        )
        .unwrap();

        adf.binarize_operators();

        // Should become or(or(2, 3), 4)
        assert_eq!(adf.get_condition(&s1).unwrap().to_string(), "or(or(2,3),4)");
    }

    #[test]
    fn test_binarize_operators_multiple_conditions() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        // ac(1, and(2, 3, 4))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::statement(Statement::from(2)),
                ConditionExpression::statement(Statement::from(3)),
                ConditionExpression::statement(Statement::from(4)),
            ]),
        )
        .unwrap();

        // ac(2, or(1, 3, 4, 5))
        adf.add_condition(
            s2.clone(),
            ConditionExpression::or(&[
                ConditionExpression::statement(s1.clone()),
                ConditionExpression::statement(Statement::from(3)),
                ConditionExpression::statement(Statement::from(4)),
                ConditionExpression::statement(Statement::from(5)),
            ]),
        )
        .unwrap();

        adf.binarize_operators();

        assert_eq!(
            adf.get_condition(&s1).unwrap().to_string(),
            "and(and(2,3),4)"
        );
        assert_eq!(
            adf.get_condition(&s2).unwrap().to_string(),
            "or(or(or(1,3),4),5)"
        );
    }

    #[test]
    fn test_binarize_operators_nested() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        // ac(1, and(or(2, 3, 4), 5))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::or(&[
                    ConditionExpression::statement(Statement::from(2)),
                    ConditionExpression::statement(Statement::from(3)),
                    ConditionExpression::statement(Statement::from(4)),
                ]),
                ConditionExpression::statement(Statement::from(5)),
            ]),
        )
        .unwrap();

        adf.binarize_operators();

        // Should become and(or(or(2, 3), 4), 5)
        assert_eq!(
            adf.get_condition(&s1).unwrap().to_string(),
            "and(or(or(2,3),4),5)"
        );
    }

    #[test]
    fn test_binarize_operators_free_statements_unchanged() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_statement(s1.clone());
        adf.add_condition(
            s2.clone(),
            ConditionExpression::and(&[
                ConditionExpression::statement(Statement::from(1)),
                ConditionExpression::statement(Statement::from(2)),
                ConditionExpression::statement(Statement::from(3)),
            ]),
        )
        .unwrap();

        adf.binarize_operators();

        // s1 should still be free
        assert!(adf.get_condition(&s1).is_none());
        // s2's condition should be binarized
        assert_eq!(
            adf.get_condition(&s2).unwrap().to_string(),
            "and(and(1,2),3)"
        );
    }

    #[test]
    fn test_binarize_operators_complex_expression() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        // ac(1, imp(and(2, 3, 4), or(5, 6, 7)))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::implication(
                ConditionExpression::and(&[
                    ConditionExpression::statement(Statement::from(2)),
                    ConditionExpression::statement(Statement::from(3)),
                    ConditionExpression::statement(Statement::from(4)),
                ]),
                ConditionExpression::or(&[
                    ConditionExpression::statement(Statement::from(5)),
                    ConditionExpression::statement(Statement::from(6)),
                    ConditionExpression::statement(Statement::from(7)),
                ]),
            ),
        )
        .unwrap();

        adf.binarize_operators();

        // Should become imp(and(and(2, 3), 4), or(or(5, 6), 7))
        assert_eq!(
            adf.get_condition(&s1).unwrap().to_string(),
            "imp(and(and(2,3),4),or(or(5,6),7))"
        );
    }

    #[test]
    fn test_binarize_operators_with_constants() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        // ac(1, and(c(v), 2, 3))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::constant(true),
                ConditionExpression::statement(Statement::from(2)),
                ConditionExpression::statement(Statement::from(3)),
            ]),
        )
        .unwrap();

        adf.binarize_operators();

        // Should become and(and(c(v), 2), 3)
        assert_eq!(
            adf.get_condition(&s1).unwrap().to_string(),
            "and(and(c(v),2),3)"
        );
    }

    #[test]
    fn test_binarize_operators_idempotent() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        // ac(1, and(2, 3, 4))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::statement(Statement::from(2)),
                ConditionExpression::statement(Statement::from(3)),
                ConditionExpression::statement(Statement::from(4)),
            ]),
        )
        .unwrap();

        adf.binarize_operators();
        let first_result = adf.get_condition(&s1).unwrap().to_string();

        adf.binarize_operators();
        let second_result = adf.get_condition(&s1).unwrap().to_string();

        // Binarizing twice should produce the same result
        assert_eq!(first_result, second_result);
    }

    #[test]
    fn test_binarize_operators_parse_roundtrip() {
        let input = r#"
s(1).
s(2).
ac(1, and(2, 3, 4)).
ac(2, or(1, 3, 4, 5)).
"#;
        let mut adf = AdfExpressions::parse(input).unwrap();

        adf.binarize_operators();

        // Write and reparse
        let output = adf.write();
        let adf2 = AdfExpressions::parse(&output).unwrap();

        // Should be equal
        assert_eq!(adf, adf2);

        // Verify binarization
        assert_eq!(
            adf2.get_condition(&Statement::from(1)).unwrap().to_string(),
            "and(and(2,3),4)"
        );
        assert_eq!(
            adf2.get_condition(&Statement::from(2)).unwrap().to_string(),
            "or(or(or(1,3),4),5)"
        );
    }

    // Tests for rename_statements

    #[test]
    fn test_rename_statements_empty_map() {
        let mut adf = AdfExpressions::new();
        adf.add_statement(Statement::from(1));

        let renamings = BTreeMap::new();
        let result = adf.rename_statements(&renamings);
        assert!(result.is_ok());
        assert!(adf.has_statement(&Statement::from(1)));
    }

    #[test]
    fn test_rename_statements_single() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        adf.add_statement(s1.clone());

        let mut renamings = BTreeMap::new();
        renamings.insert(s1.clone(), Statement::from(10));

        let result = adf.rename_statements(&renamings);
        assert!(result.is_ok());
        assert!(!adf.has_statement(&s1));
        assert!(adf.has_statement(&Statement::from(10)));
    }

    #[test]
    fn test_rename_statements_multiple() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();
        adf.add_condition(s2.clone(), ConditionExpression::statement(s3.clone()))
            .unwrap();
        adf.add_statement(s3.clone());

        let mut renamings = BTreeMap::new();
        renamings.insert(s1.clone(), Statement::from(10));
        renamings.insert(s2.clone(), Statement::from(20));
        renamings.insert(s3.clone(), Statement::from(30));

        let result = adf.rename_statements(&renamings);
        assert!(result.is_ok());

        // Old statements should be gone
        assert!(!adf.has_statement(&s1));
        assert!(!adf.has_statement(&s2));
        assert!(!adf.has_statement(&s3));

        // New statements should exist
        assert!(adf.has_statement(&Statement::from(10)));
        assert!(adf.has_statement(&Statement::from(20)));
        assert!(adf.has_statement(&Statement::from(30)));

        // Conditions should be updated
        assert_eq!(
            adf.get_condition(&Statement::from(10)).unwrap().to_string(),
            "20"
        );
        assert_eq!(
            adf.get_condition(&Statement::from(20)).unwrap().to_string(),
            "30"
        );
    }

    #[test]
    fn test_rename_statements_complex_conditions() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        // ac(1, and(2, 3, 2))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::statement(s2.clone()),
                ConditionExpression::statement(s3.clone()),
                ConditionExpression::statement(s2.clone()),
            ]),
        )
        .unwrap();
        // Add s2 and s3 as free statements
        adf.add_statement(s2.clone());
        adf.add_statement(s3.clone());

        let mut renamings = BTreeMap::new();
        renamings.insert(s2.clone(), Statement::from(20));
        renamings.insert(s3.clone(), Statement::from(30));

        let result = adf.rename_statements(&renamings);
        assert!(result.is_ok());

        // All occurrences should be replaced
        assert_eq!(adf.get_condition(&s1).unwrap().to_string(), "and(20,30,20)");
    }

    #[test]
    fn test_rename_statements_nonexistent_fails() {
        let mut adf = AdfExpressions::new();
        adf.add_statement(Statement::from(1));

        let mut renamings = BTreeMap::new();
        renamings.insert(Statement::from(99), Statement::from(100));

        let result = adf.rename_statements(&renamings);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("does not exist"));
    }

    #[test]
    fn test_rename_statements_conflict_fails() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_statement(s1.clone());
        adf.add_statement(s2.clone());

        // Try to rename s1 to s2 (which already exists)
        let mut renamings = BTreeMap::new();
        renamings.insert(s1, s2);

        let result = adf.rename_statements(&renamings);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("already exists"));
    }

    #[test]
    fn test_rename_statements_swap_allowed() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();
        adf.add_condition(s2.clone(), ConditionExpression::statement(s1.clone()))
            .unwrap();

        // Swap: 1->2, 2->1
        let mut renamings = BTreeMap::new();
        renamings.insert(s1.clone(), s2.clone());
        renamings.insert(s2.clone(), s1.clone());

        let result = adf.rename_statements(&renamings);
        // This should be allowed since both are being renamed
        assert!(result.is_ok());
    }

    #[test]
    fn test_rename_statements_preserves_free_statements() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_statement(s1.clone());
        adf.add_statement(s2.clone());

        let mut renamings = BTreeMap::new();
        renamings.insert(s1, Statement::from(10));

        let result = adf.rename_statements(&renamings);
        assert!(result.is_ok());

        // s10 should be free
        assert!(adf.get_condition(&Statement::from(10)).is_none());
        // s2 should still exist
        assert!(adf.has_statement(&s2));
    }

    #[test]
    fn test_rename_statements_with_self_reference() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);

        // ac(1, neg(1))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::negation(ConditionExpression::statement(s1.clone())),
        )
        .unwrap();

        let mut renamings = BTreeMap::new();
        renamings.insert(s1, Statement::from(10));

        let result = adf.rename_statements(&renamings);
        assert!(result.is_ok());

        // ac(10, neg(10))
        assert_eq!(
            adf.get_condition(&Statement::from(10)).unwrap().to_string(),
            "neg(10)"
        );
    }

    #[test]
    fn test_rename_statements_parse_roundtrip() {
        let input = r#"
s(1).
s(2).
s(3).
ac(1, and(2, 3)).
ac(2, or(1, 3)).
"#;
        let mut adf = AdfExpressions::parse(input).unwrap();

        let mut renamings = BTreeMap::new();
        renamings.insert(Statement::from(1), Statement::from(10));
        renamings.insert(Statement::from(2), Statement::from(20));
        renamings.insert(Statement::from(3), Statement::from(30));

        let result = adf.rename_statements(&renamings);
        assert!(result.is_ok());

        // Write and reparse
        let output = adf.write();
        let adf2 = AdfExpressions::parse(&output).unwrap();

        // Should be equal
        assert_eq!(adf, adf2);

        // Verify the renaming
        assert_eq!(
            adf2.get_condition(&Statement::from(10))
                .unwrap()
                .to_string(),
            "and(20,30)"
        );
        assert_eq!(
            adf2.get_condition(&Statement::from(20))
                .unwrap()
                .to_string(),
            "or(10,30)"
        );
    }

    // Tests for rename_statement

    #[test]
    fn test_rename_statement_simple() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s99 = Statement::from(99);

        adf.add_statement(s1.clone());

        let result = adf.rename_statement(&s1, &s99);
        assert!(result.is_ok());

        // Old statement should not exist
        assert!(!adf.has_statement(&s1));
        // New statement should exist
        assert!(adf.has_statement(&s99));
        assert_eq!(adf.len(), 1);
    }

    #[test]
    fn test_rename_statement_with_condition() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s99 = Statement::from(99);

        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();

        let result = adf.rename_statement(&s1, &s99);
        assert!(result.is_ok());

        // s99 should have the condition that s1 had
        assert!(adf.get_condition(&s99).is_some());
        assert_eq!(adf.get_condition(&s99).unwrap().to_string(), "2");
        // s1 should not exist
        assert!(!adf.has_statement(&s1));
    }

    #[test]
    fn test_rename_statement_referenced_in_conditions() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s99 = Statement::from(99);

        // ac(1, 2)
        adf.add_condition(s1.clone(), ConditionExpression::statement(s2.clone()))
            .unwrap();
        // ac(2, 1)
        adf.add_condition(s2.clone(), ConditionExpression::statement(s1.clone()))
            .unwrap();

        let result = adf.rename_statement(&s1, &s99);
        assert!(result.is_ok());

        // ac(99, 2) - the renamed statement's condition
        assert_eq!(adf.get_condition(&s99).unwrap().to_string(), "2");
        // ac(2, 99) - s1 replaced with s99 in s2's condition
        assert_eq!(adf.get_condition(&s2).unwrap().to_string(), "99");
    }

    #[test]
    fn test_rename_statement_self_referential() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s99 = Statement::from(99);

        // ac(1, neg(1))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::negation(ConditionExpression::statement(s1.clone())),
        )
        .unwrap();

        let result = adf.rename_statement(&s1, &s99);
        assert!(result.is_ok());

        // ac(99, neg(99))
        assert_eq!(adf.get_condition(&s99).unwrap().to_string(), "neg(99)");
    }

    #[test]
    fn test_rename_statement_complex_expression() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let s99 = Statement::from(99);

        // ac(1, and(or(2, 1), neg(1)))
        adf.add_condition(
            s1.clone(),
            ConditionExpression::and(&[
                ConditionExpression::or(&[
                    ConditionExpression::statement(s2.clone()),
                    ConditionExpression::statement(s1.clone()),
                ]),
                ConditionExpression::negation(ConditionExpression::statement(s1.clone())),
            ]),
        )
        .unwrap();
        // ac(3, 1)
        adf.add_condition(s3.clone(), ConditionExpression::statement(s1.clone()))
            .unwrap();

        let result = adf.rename_statement(&s1, &s99);
        assert!(result.is_ok());

        // ac(99, and(or(2, 99), neg(99)))
        assert_eq!(
            adf.get_condition(&s99).unwrap().to_string(),
            "and(or(2,99),neg(99))"
        );
        // ac(3, 99)
        assert_eq!(adf.get_condition(&s3).unwrap().to_string(), "99");
    }

    #[test]
    fn test_rename_statement_multiple_occurrences() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s99 = Statement::from(99);

        // Add s1 as a statement
        adf.add_statement(s1.clone());
        // ac(2, or(1, and(1, 1)))
        adf.add_condition(
            s2.clone(),
            ConditionExpression::or(&[
                ConditionExpression::statement(s1.clone()),
                ConditionExpression::and(&[
                    ConditionExpression::statement(s1.clone()),
                    ConditionExpression::statement(s1.clone()),
                ]),
            ]),
        )
        .unwrap();

        let result = adf.rename_statement(&s1, &s99);
        assert!(result.is_ok());

        // All occurrences should be renamed
        assert_eq!(
            adf.get_condition(&s2).unwrap().to_string(),
            "or(99,and(99,99))"
        );
    }

    #[test]
    fn test_rename_statement_nonexistent_fails() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s99 = Statement::from(99);

        adf.add_statement(s1.clone());

        let result = adf.rename_statement(&s99, &s2);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("does not exist"));
    }

    #[test]
    fn test_rename_statement_target_exists_fails() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);

        adf.add_statement(s1.clone());
        adf.add_statement(s2.clone());

        let result = adf.rename_statement(&s1, &s2);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("already exists"));
    }

    #[test]
    fn test_rename_statement_preserves_other_statements() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);
        let s99 = Statement::from(99);

        adf.add_statement(s1.clone());
        adf.add_statement(s2.clone());
        adf.add_statement(s3.clone());

        let result = adf.rename_statement(&s1, &s99);
        assert!(result.is_ok());

        // s2 and s3 should still exist
        assert!(adf.has_statement(&s2));
        assert!(adf.has_statement(&s3));
        assert!(adf.has_statement(&s99));
        assert!(!adf.has_statement(&s1));
        assert_eq!(adf.len(), 3);
    }

    #[test]
    fn test_rename_statement_with_free_statement() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s99 = Statement::from(99);

        // s1 has no condition (free statement)
        adf.add_statement(s1.clone());

        let result = adf.rename_statement(&s1, &s99);
        assert!(result.is_ok());

        // s99 should be free as well
        assert!(adf.has_statement(&s99));
        assert!(adf.get_condition(&s99).is_none());
    }

    #[test]
    fn test_rename_statement_chain() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s2 = Statement::from(2);
        let s3 = Statement::from(3);

        adf.add_condition(s1.clone(), ConditionExpression::constant(true))
            .unwrap();

        // Rename 1 -> 2
        let result = adf.rename_statement(&s1, &s2);
        assert!(result.is_ok());
        assert!(adf.has_statement(&s2));
        assert!(!adf.has_statement(&s1));

        // Rename 2 -> 3
        let result = adf.rename_statement(&s2, &s3);
        assert!(result.is_ok());
        assert!(adf.has_statement(&s3));
        assert!(!adf.has_statement(&s2));
        assert_eq!(adf.get_condition(&s3).unwrap().to_string(), "c(v)");
    }

    #[test]
    fn test_rename_statement_all_operators() {
        let mut adf = AdfExpressions::new();
        let s1 = Statement::from(1);
        let s_target = Statement::from(99);
        let s_new = Statement::from(100);

        // Add the target statement that we'll rename
        adf.add_statement(s_target.clone());

        // Test with various operators
        adf.add_condition(
            Statement::from(10),
            ConditionExpression::implication(
                ConditionExpression::statement(s_target.clone()),
                ConditionExpression::statement(s1.clone()),
            ),
        )
        .unwrap();

        adf.add_condition(
            Statement::from(11),
            ConditionExpression::equivalence(
                ConditionExpression::statement(s_target.clone()),
                ConditionExpression::statement(s1.clone()),
            ),
        )
        .unwrap();

        adf.add_condition(
            Statement::from(12),
            ConditionExpression::exclusive_or(
                ConditionExpression::statement(s_target.clone()),
                ConditionExpression::statement(s1.clone()),
            ),
        )
        .unwrap();

        let result = adf.rename_statement(&s_target, &s_new);
        assert!(result.is_ok());

        assert_eq!(
            adf.get_condition(&Statement::from(10)).unwrap().to_string(),
            "imp(100,1)"
        );
        assert_eq!(
            adf.get_condition(&Statement::from(11)).unwrap().to_string(),
            "iff(100,1)"
        );
        assert_eq!(
            adf.get_condition(&Statement::from(12)).unwrap().to_string(),
            "xor(100,1)"
        );
        assert!(!adf.has_statement(&s_target));
        assert!(adf.has_statement(&s_new));
    }

    #[test]
    fn test_rename_statement_parse_roundtrip() {
        let input = r#"
s(1).
s(2).
s(3).
ac(1, and(2, 3)).
ac(2, or(1, 3)).
ac(3, neg(1)).
"#;
        let mut adf = AdfExpressions::parse(input).unwrap();

        // Rename s1 to s99
        let result = adf.rename_statement(&Statement::from(1), &Statement::from(99));
        assert!(result.is_ok());

        // Write and reparse
        let output = adf.write();
        let adf2 = AdfExpressions::parse(&output).unwrap();

        // Should be equal
        assert_eq!(adf, adf2);

        // Verify the rename took effect
        assert!(!adf2.has_statement(&Statement::from(1)));
        assert!(adf2.has_statement(&Statement::from(99)));
        assert_eq!(
            adf2.get_condition(&Statement::from(99))
                .unwrap()
                .to_string(),
            "and(2,3)"
        );
        assert_eq!(
            adf2.get_condition(&Statement::from(2)).unwrap().to_string(),
            "or(99,3)"
        );
        assert_eq!(
            adf2.get_condition(&Statement::from(3)).unwrap().to_string(),
            "neg(99)"
        );
    }

    #[test]
    fn test_rename_statement_string_labels() {
        let mut adf = AdfExpressions::new();
        let s_foo = Statement::from("foo");
        let s_bar = Statement::from("bar");
        let s_baz = Statement::from("baz");

        // ac(foo, bar)
        adf.add_condition(s_foo.clone(), ConditionExpression::statement(s_bar.clone()))
            .unwrap();
        // ac(bar, foo)
        adf.add_condition(s_bar.clone(), ConditionExpression::statement(s_foo.clone()))
            .unwrap();

        let result = adf.rename_statement(&s_foo, &s_baz);
        assert!(result.is_ok());

        assert!(!adf.has_statement(&s_foo));
        assert!(adf.has_statement(&s_baz));
        assert_eq!(adf.get_condition(&s_baz).unwrap().to_string(), "bar");
        assert_eq!(adf.get_condition(&s_bar).unwrap().to_string(), "baz");
    }

    // Comprehensive test: parse and write all test instances
    #[rstest]
    #[case("A-")]
    #[case("B-")]
    #[case("C-")]
    #[case("T-")]
    #[case("adfgen_acyc")]
    #[case("adfgen_nacyc")]
    #[case("comma")]
    #[case("metro")]
    #[case("Small")]
    #[case("Medium")]
    fn test_parse_write_all_test_instances(#[case] prefix: &str) {
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

            if !entry.file_name().to_str().unwrap().starts_with(prefix) {
                // Skip file names that don't match the desired prefix.
                continue;
            }

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
                                let original_lines: HashSet<String> = original_content
                                    .lines()
                                    .map(|l| l.trim())
                                    .map(|l| {
                                        // If the line is a "long" statement declaration, shorten it.
                                        if l.starts_with("statement") {
                                            l.replace("statement", "s")
                                        } else {
                                            l.to_string()
                                        }
                                    })
                                    .filter(|l| !l.is_empty() && !l.starts_with('#'))
                                    .collect();

                                let written_lines: HashSet<String> = written_content
                                    .lines()
                                    .map(|l| l.trim().to_string())
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

        // Each filter should match at least one test file.
        assert!(count > 0);

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
