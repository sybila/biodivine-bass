#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

BENCHMARKS='./test_instances/_normalized'
RESULTS_DIR='./benchmarks/results'
OUTPUT_DIR='./benchmarks/results/recorded'

mkdir -p "$OUTPUT_DIR"

# aeon-py supports: two-valued, complete, preferred
# Mapping: two-valued -> 2v, complete -> com, preferred -> prf

declare -A PROBLEM_MAP=(
    ["two-valued"]="2v"
    ["complete"]="com"
    ["preferred"]="prf"
)

declare -A ARG_MAP=(
    ["two-valued"]="/sw/adf_two_valued.py"
    ["complete"]="/sw/adf_complete.py"
    ["preferred"]="/sw/adf_preferred.py"
)

for problem in "two-valued" complete preferred; do
    problem_short="${PROBLEM_MAP[$problem]}"
    fast_file="${RESULTS_DIR}/${problem_short}_fast.txt"
    output_file="${OUTPUT_DIR}/aeon_${problem_short}.txt"
    
    if [ ! -f "$fast_file" ]; then
        echo "Warning: $fast_file not found, skipping $problem"
        continue
    fi
    
    echo "Recording aeon-py results for $problem..."
    echo "=== aeon-py $problem ===" > "$output_file"
    
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
        
        # Run the tool using a very large enumeration limit
        ./benchmarks/run_aeon-py.sh ${ARG_MAP[$problem]} "$instance_file" 1000000000 >> "$output_file" 2>&1 || echo "Error running $instance" >> "$output_file"
        
    done < "$fast_file"
    
    echo "Completed recording for $problem"
done

echo "All aeon-py recordings completed!"
