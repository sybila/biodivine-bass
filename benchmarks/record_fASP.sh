#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

BENCHMARKS='./test_instances/_normalized'
RESULTS_DIR='./benchmarks/results'
OUTPUT_DIR='./benchmarks/results/recorded'

mkdir -p "$OUTPUT_DIR"

# fASP supports: two-valued
# Mapping: two-valued -> 2v

fast_file="${RESULTS_DIR}/2v_fast.txt"
output_file="${OUTPUT_DIR}/fasp_2v.txt"

if [ ! -f "$fast_file" ]; then
    echo "Error: $fast_file not found"
    exit 1
fi

echo "Recording fASP results for two-valued..."
echo "=== fASP two-valued ===" > "$output_file"

while IFS= read -r instance; do
    if [ -z "$instance" ]; then
        continue
    fi
    
    # Find the .normal.bnet file
    instance_file=$(find "$BENCHMARKS" -name "${instance}.normal.bnet" -type f | head -n 1)
    
    if [ -z "$instance_file" ]; then
        echo "Warning: Instance $instance not found, skipping" >> "$output_file"
        continue
    fi
    
    echo "" >> "$output_file"
    echo "--- Instance: $instance ---" >> "$output_file"
    
    # Run the tool WITHOUT --count-only
    ./benchmarks/run_fASP.sh "$instance_file" >> "$output_file" 2>&1 || echo "Error running $instance" >> "$output_file"
    
done < "$fast_file"

echo "fASP recordings completed!"
