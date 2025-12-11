#!/usr/bin/env python3
"""
Find problem instances that were finished in less than 10 seconds by all tools.

This script reads all CSV result files from subdirectories (2v, adm, com, prf, stm)
and identifies instances where every tool completed successfully in under 10 seconds.
Outputs separate files for each problem type (e.g., 2v_fast.txt, adm_fast.txt).

Usage:
    python find_fast_instances.py [output_dir]

Arguments:
    output_dir: Optional output directory (default: current directory)
"""

import sys
import os
import csv
from pathlib import Path


def normalize_instance_name(instance_name):
    """Normalize instance name by removing format-specific extensions."""
    for ext in ['.normal.adf', '.normal.sbml', '.normal.bnet']:
        if instance_name.endswith(ext):
            return instance_name[:-len(ext)]
    return instance_name


def load_results_from_directory(directory_path):
    """Load all CSV files from a directory and return a dictionary mapping tool names to data."""
    csv_files = list(directory_path.glob('*.csv'))
    
    if not csv_files:
        return {}
    
    tables = {}
    for csv_file in csv_files:
        # Use filename without extension as the tool name
        tool_name = csv_file.stem
        try:
            with open(csv_file, 'r') as f:
                reader = csv.DictReader(f)
                rows = list(reader)
            
            # Create a dictionary mapping normalized instance names to row data
            instance_data = {}
            instance_col = None
            
            for row in rows:
                # Get the instance column (first column)
                if instance_col is None:
                    instance_col = list(row.keys())[0]
                
                instance_name = row[instance_col]
                normalized = normalize_instance_name(instance_name)
                instance_data[normalized] = row
            
            tables[tool_name] = {
                'instance_col': instance_col,
                'data': instance_data
            }
        except Exception as e:
            print(f"Warning: Could not read {csv_file}: {e}", file=sys.stderr)
    
    return tables


def find_fast_instances(results_dir, time_threshold=10.0):
    """
    Find instances that were completed in less than time_threshold seconds by all tools.
    
    Returns a dictionary mapping subdirectory names to sets of normalized instance names.
    """
    results_path = Path(results_dir)
    fast_instances_by_dir = {}
    
    # Subdirectories to check
    subdirs = ['2v', 'adm', 'com', 'prf', 'stm']
    
    for subdir in subdirs:
        subdir_path = results_path / subdir
        if not subdir_path.exists():
            print(f"Warning: Directory {subdir_path} does not exist, skipping...", file=sys.stderr)
            continue
        
        print(f"Processing {subdir}...", file=sys.stderr)
        tables = load_results_from_directory(subdir_path)
        
        if not tables:
            print(f"  No CSV files found in {subdir}", file=sys.stderr)
            continue
        
        print(f"  Found {len(tables)} tools: {', '.join(tables.keys())}", file=sys.stderr)
        
        # Get all normalized instances that appear in at least one tool's results
        all_instances = set()
        for tool_data in tables.values():
            all_instances.update(tool_data['data'].keys())
        
        # For each instance, check if all tools completed it in < time_threshold seconds
        fast_instances = set()
        
        for instance in all_instances:
            all_tools_fast = True
            
            for tool_name, tool_data in tables.items():
                # Find the row for this instance
                instance_data = tool_data['data'].get(instance)
                
                if instance_data is None:
                    # Instance not found in this tool's results - skip this instance
                    all_tools_fast = False
                    break
                
                # Check if Status is OK and Runtime_sec < time_threshold
                status = instance_data.get('Status', '')
                runtime_str = instance_data.get('Runtime_sec', '')
                
                try:
                    runtime = float(runtime_str) if runtime_str else float('inf')
                except (ValueError, TypeError):
                    runtime = float('inf')
                
                if status != 'OK' or runtime >= time_threshold:
                    all_tools_fast = False
                    break
            
            if all_tools_fast:
                fast_instances.add(instance)
        
        fast_instances_by_dir[subdir] = fast_instances
        print(f"  Found {len(fast_instances)} instances completed in < {time_threshold}s by all tools", file=sys.stderr)
    
    return fast_instances_by_dir


def main():
    # Determine script location and results directory
    script_dir = Path(__file__).parent
    results_dir = script_dir  # Results are in the same directory as the script
    
    # Optional output directory argument
    output_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else script_dir
    
    print(f"Searching for instances completed in < 10 seconds by all tools...", file=sys.stderr)
    print(f"Results directory: {results_dir}", file=sys.stderr)
    print(f"Output directory: {output_dir}", file=sys.stderr)
    print("", file=sys.stderr)
    
    # Find fast instances
    fast_instances_by_dir = find_fast_instances(results_dir, time_threshold=10.0)
    
    # Write separate files for each problem type
    print("", file=sys.stderr)
    print("Writing output files...", file=sys.stderr)
    
    for subdir in ['2v', 'adm', 'com', 'prf', 'stm']:
        fast_instances = fast_instances_by_dir.get(subdir, set())
        output_file = output_dir / f"{subdir}_fast.txt"
        
        with open(output_file, 'w') as f:
            # Write one normalized instance name per line, sorted
            for instance in sorted(fast_instances):
                f.write(f"{instance}\n")
        
        print(f"  {output_file}: {len(fast_instances)} instances", file=sys.stderr)
    
    # Print summary by subdirectory
    print("\nSummary by subdirectory:", file=sys.stderr)
    total_unique = set()
    for subdir in ['2v', 'adm', 'com', 'prf', 'stm']:
        instances = fast_instances_by_dir.get(subdir, set())
        total_unique.update(instances)
        count = len(instances)
        print(f"  {subdir}: {count} instances", file=sys.stderr)
    
    print(f"\nTotal unique instances across all problem types: {len(total_unique)}", file=sys.stderr)


if __name__ == '__main__':
    main()
