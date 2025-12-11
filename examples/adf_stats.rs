use biodivine_bass::AdfExpressions;
use std::fs;
use std::path::Path;

fn main() {
    let test_dir = Path::new("test_instances");
    if !test_dir.exists() {
        // Skip test if directory doesn't exist
        return;
    }

    let entries = fs::read_dir(test_dir).unwrap();
    let mut stm_counts = vec![];
    let mut link_counts = vec![];

    for entry in entries {
        let entry = entry.unwrap();

        let path = entry.path();

        if path.extension().and_then(|s| s.to_str()) == Some("adf") {
            println!("Processing {}", path.display());
            let original_content = fs::read_to_string(&path).unwrap();
            let adf = AdfExpressions::parse(&original_content).unwrap();

            stm_counts.push(adf.statements().count());
            link_counts.push(
                adf.conditions()
                    .map(|(_, c)| c.collect_statements().len())
                    .sum::<usize>(),
            );
        }
    }

    stm_counts.sort();
    link_counts.sort();

    let total_statements = stm_counts.iter().sum::<usize>();
    println!("Total statements: {}", total_statements);
    println!("Avr. statements: {}", total_statements / stm_counts.len());
    println!("Max. statements: {}", stm_counts.iter().max().unwrap());
    println!("Median statements: {}", stm_counts[stm_counts.len() / 2]);

    let total_links = link_counts.iter().sum::<usize>();
    println!("Total links: {}", total_links);
    println!("Avr. links: {}", total_links / link_counts.len());
    println!("Max. links: {}", link_counts.iter().max().unwrap());
    println!("Median links: {}", link_counts[link_counts.len() / 2]);
}
