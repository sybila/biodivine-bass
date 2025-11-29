#!/usr/bin/env python3
"""
Fix status errors in CSV result tables by checking log files for OSError.

Usage:
    python fix_file_errors.py <csv_file> <log_folder> [output_file]

Arguments:
    csv_file: Path to CSV result table to fix
    log_folder: Path to folder containing .log files
    output_file: Optional path for output CSV (default: overwrites input file)
"""

import sys
import os
import pandas as pd
from pathlib import Path


def check_log_for_oserror(log_file_path):
    """Check if a log file contains 'OSError'."""
    try:
        with open(log_file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
            return 'OSError' in content
    except FileNotFoundError:
        return False
    except Exception as e:
        print(f"  Warning: Could not read {log_file_path}: {e}")
        return False


def fix_csv_errors(csv_file, log_folder, output_file=None):
    """Fix status errors in CSV by checking log files."""
    # Load CSV
    print(f"Loading CSV file: {csv_file}")
    df = pd.read_csv(csv_file)
    
    # Get instance column (first column)
    instance_col = df.columns[0]
    
    if 'Status' not in df.columns:
        raise ValueError(f"CSV file does not have a 'Status' column. Columns found: {df.columns.tolist()}")
    
    log_folder_path = Path(log_folder)
    if not log_folder_path.exists():
        raise ValueError(f"Log folder does not exist: {log_folder}")
    
    # Track changes
    changes_made = 0
    
    print(f"\nChecking {len(df)} instances for OSError in log files...")
    
    # For each instance, check the corresponding log file
    for idx, row in df.iterrows():
        instance = row[instance_col]
        current_status = row['Status']
        
        # Construct log file path
        log_file_path = log_folder_path / f"{instance}.log"
        
        # Check if log file exists and contains OSError
        if log_file_path.exists():
            if check_log_for_oserror(log_file_path):
                if current_status != 'ERROR':
                    df.at[idx, 'Status'] = 'ERROR'
                    changes_made += 1
                    print(f"  Fixed: {instance} (was {current_status}, now ERROR)")
        else:
            # Log file doesn't exist - this is okay, just skip
            pass
    
    # Save the updated CSV
    if output_file is None:
        output_file = csv_file
    
    print(f"\nSaving updated CSV to: {output_file}")
    df.to_csv(output_file, index=False)
    
    print(f"\nSummary:")
    print(f"  Total instances checked: {len(df)}")
    print(f"  Status changes made: {changes_made}")
    print(f"  Updated CSV saved to: {output_file}")


def main():
    if len(sys.argv) < 3:
        print("Usage: python fix_file_errors.py <csv_file> <log_folder> [output_file]")
        print("\nArguments:")
        print("  csv_file: Path to CSV result table to fix")
        print("  log_folder: Path to folder containing .log files")
        print("  output_file: Optional path for output CSV (default: overwrites input file)")
        sys.exit(1)
    
    csv_file = sys.argv[1]
    log_folder = sys.argv[2]
    output_file = sys.argv[3] if len(sys.argv) > 3 else None
    
    if not os.path.exists(csv_file):
        print(f"Error: CSV file does not exist: {csv_file}")
        sys.exit(1)
    
    try:
        fix_csv_errors(csv_file, log_folder, output_file)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()

