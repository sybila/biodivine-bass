#!/usr/bin/env python3
"""
Process benchmark result tables and generate summary statistics.

Usage:
    python process_results.py <results_folder> <exclude_file> [output_file]

Arguments:
    results_folder: Path to folder containing CSV result tables
    exclude_file: Path to file containing instance names to exclude (one per line)
    output_file: Optional path for output summary CSV (default: summary.csv)
"""

import sys
import os
import pandas as pd
from pathlib import Path


def load_exclude_list(exclude_file):
    """Load the list of instances to exclude."""
    with open(exclude_file, 'r') as f:
        exclude_set = {line.strip() for line in f if line.strip()}
    return exclude_set


def load_result_tables(results_folder):
    """Load all CSV files from the results folder."""
    folder_path = Path(results_folder)
    csv_files = list(folder_path.glob('*.csv'))
    
    if not csv_files:
        raise ValueError(f"No CSV files found in {results_folder}")
    
    tables = {}
    for csv_file in csv_files:
        # Use filename without extension as the table name
        table_name = csv_file.stem
        df = pd.read_csv(csv_file)
        
        # Sort by first column (Instance)
        first_col = df.columns[0]
        df = df.sort_values(by=first_col).reset_index(drop=True)
        
        tables[table_name] = df
    
    return tables


def normalize_instance_name(instance_name):
    """Normalize instance name by removing .normal.adf or .normal.sbml extension."""
    # Remove common extensions to match instances across different formats
    for ext in ['.normal.adf', '.normal.sbml', '.normal.bnet']:
        if instance_name.endswith(ext):
            return instance_name[:-len(ext)]
    return instance_name


def process_tables(tables, exclude_set):
    """Process tables: remove excluded rows and ensure same rows."""
    # Get the instance column name (first column)
    instance_col = None
    processed_tables = {}
    
    # Normalize exclude set
    normalized_exclude_set = {normalize_instance_name(inst) for inst in exclude_set}
    
    for table_name, df in tables.items():
        instance_col = df.columns[0]
        
        # Create normalized instance column for matching
        df = df.copy()
        df['_normalized_instance'] = df[instance_col].apply(normalize_instance_name)
        
        # Remove excluded instances (using normalized names)
        df_filtered = df[~df['_normalized_instance'].isin(normalized_exclude_set)].copy()
        
        # Sort by normalized instance
        df_filtered = df_filtered.sort_values(by='_normalized_instance').reset_index(drop=True)
        
        processed_tables[table_name] = df_filtered
    
    # Find common normalized instances across all tables
    if not processed_tables:
        raise ValueError("No tables to process")
    
    common_normalized_instances = set(processed_tables[list(processed_tables.keys())[0]]['_normalized_instance'])
    for df in processed_tables.values():
        common_normalized_instances &= set(df['_normalized_instance'])
    
    # Filter all tables to only include common normalized instances
    for table_name in processed_tables:
        processed_tables[table_name] = processed_tables[table_name][
            processed_tables[table_name]['_normalized_instance'].isin(common_normalized_instances)
        ].sort_values(by='_normalized_instance').reset_index(drop=True)
    
    return processed_tables, instance_col


def join_tables(tables, instance_col):
    """Join all tables together with renamed columns."""
    # Start with the first table's normalized instance column
    first_table = tables[list(tables.keys())[0]]
    result = pd.DataFrame({
        instance_col: first_table[instance_col],
        '_normalized_instance': first_table['_normalized_instance']
    })
    
    # For each table, add Status, Runtime_sec, and Memory_KB columns with table name prefix
    for table_name, df in tables.items():
        # Check which columns exist
        status_col = 'Status' if 'Status' in df.columns else None
        runtime_col = 'Runtime_sec' if 'Runtime_sec' in df.columns else None
        memory_col = 'Memory_KB' if 'Memory_KB' in df.columns else None
        
        # Merge on normalized instance column
        merge_cols = ['_normalized_instance']
        if status_col:
            merge_cols.append(status_col)
        if runtime_col:
            merge_cols.append(runtime_col)
        if memory_col:
            merge_cols.append(memory_col)
        
        df_to_merge = df[merge_cols].copy()
        
        # Rename columns
        rename_dict = {}
        if status_col:
            rename_dict[status_col] = f'{table_name}_Status'
        if runtime_col:
            rename_dict[runtime_col] = f'{table_name}_Runtime_sec'
        if memory_col:
            rename_dict[memory_col] = f'{table_name}_Memory_KB'
        
        df_to_merge = df_to_merge.rename(columns=rename_dict)
        
        result = result.merge(df_to_merge, on='_normalized_instance', how='inner')
    
    # Drop the normalized instance column before returning
    result = result.drop(columns=['_normalized_instance'])
    
    return result


def compute_statistics(tables, instance_col):
    """Compute statistics for each table."""
    stats = {}
    unique_solved = [] # List of (instance, tool_name)
    
    for table_name, df in tables.items():
        status_col = 'Status' if 'Status' in df.columns else None
        runtime_col = 'Runtime_sec' if 'Runtime_sec' in df.columns else None
        
        if not status_col:
            stats[table_name] = {
                'ok_count': 0,
                'unique_ok_count': 0,
                'penalised_avg_runtime': 0.0
            }
            continue
        
        # Count OK statuses
        ok_count = (df[status_col] == 'OK').sum()
        
        # Count instances that are OK only in this table
        unique_ok_count = 0
        for idx, row in df.iterrows():
            normalized_instance = row['_normalized_instance']
            if row[status_col] == 'OK':
                # Check if all other tables have non-OK status for this normalized instance
                is_unique = True
                for other_name, other_df in tables.items():
                    if other_name == table_name:
                        continue
                    other_status_col = 'Status' if 'Status' in other_df.columns else None
                    if other_status_col:
                        other_row = other_df[other_df['_normalized_instance'] == normalized_instance]
                        if not other_row.empty and other_row.iloc[0][other_status_col] == 'OK':
                            is_unique = False
                            break
                if is_unique:
                    unique_ok_count += 1
                    unique_solved.append((row[instance_col], table_name))
        
        # Compute penalised average runtime
        if runtime_col:
            time_limit = 1200.0
            penalised_runtimes = []
            for idx, row in df.iterrows():
                if row[status_col] == 'OK':
                    penalised_runtimes.append(row[runtime_col])
                else:
                    penalised_runtimes.append(2 * time_limit)
            penalised_avg_runtime = sum(penalised_runtimes) / len(penalised_runtimes) if penalised_runtimes else 0.0
        else:
            penalised_avg_runtime = 0.0
        
        stats[table_name] = {
            'ok_count': ok_count,
            'unique_ok_count': unique_ok_count,
            'penalised_avg_runtime': penalised_avg_runtime
        }
    
    return stats, unique_solved


def main():
    if len(sys.argv) < 3:
        print("Usage: python process_results.py <results_folder> <exclude_file> [output_file]")
        sys.exit(1)
    
    results_folder = sys.argv[1]
    exclude_file = sys.argv[2]
    output_file = sys.argv[3] if len(sys.argv) > 3 else 'summary.csv'
    
    # Load exclude list
    print(f"Loading exclude list from {exclude_file}...")
    exclude_set = load_exclude_list(exclude_file)
    print(f"  Found {len(exclude_set)} instances to exclude")
    
    # Load result tables
    print(f"\nLoading result tables from {results_folder}...")
    tables = load_result_tables(results_folder)
    print(f"  Found {len(tables)} result tables: {', '.join(tables.keys())}")
    
    # Process tables
    print("\nProcessing tables...")
    processed_tables, instance_col = process_tables(tables, exclude_set)
    
    # Check row counts
    row_counts = {name: len(df) for name, df in processed_tables.items()}
    print(f"  Row counts after processing: {row_counts}")
    
    if len(set(row_counts.values())) > 1:
        print("  WARNING: Tables have different row counts after processing!")
    
    # Join tables
    print("\nJoining tables...")
    joined_df = join_tables(processed_tables, instance_col)
    print(f"  Joined table has {len(joined_df)} rows and {len(joined_df.columns)} columns")
    
    # Save summary CSV
    print(f"\nSaving summary to {output_file}...")
    joined_df.to_csv(output_file, index=False)
    print(f"  Summary saved successfully")
    
    # Compute statistics
    print("\nComputing statistics...")
    stats, unique_solved = compute_statistics(processed_tables, instance_col)
    
    # Save unique solved instances
    unique_output_file = output_file.replace('.csv', '_unique.csv') if output_file.endswith('.csv') else output_file + '_unique.csv'
    print(f"Saving unique solved instances to {unique_output_file}...")
    unique_df = pd.DataFrame(unique_solved, columns=[instance_col, 'Tool'])
    unique_df.to_csv(unique_output_file, index=False)
    
    # Print statistics
    print("\n" + "="*80)
    print("STATISTICS")
    print("="*80)
    for table_name, stat in stats.items():
        print(f"\n{table_name}:")
        print(f"  OK count: {stat['ok_count']}")
        print(f"  Unique OK count (OK only in this table): {stat['unique_ok_count']}")
        print(f"  Penalised Average Runtime × 2: {stat['penalised_avg_runtime']:.2f} seconds")
    print("="*80)


if __name__ == '__main__':
    main()

