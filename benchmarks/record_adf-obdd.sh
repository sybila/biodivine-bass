#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

BENCHMARKS='./test_instances/_normalized'
RESULTS_DIR='./benchmarks/results'
OUTPUT_DIR='./benchmarks/results/recorded'

mkdir -p "$OUTPUT_DIR"

# adf-obdd supports: complete, two-valued, stable
# Mapping: complete -> com, two-valued -> 2v, stable -> stm
# Note: bench script uses --count-only, but we want actual results

declare -A PROBLEM_MAP=(
    ["complete"]="com"
    ["two-valued"]="2v"
    ["stable"]="stm"
)

declare -A ARG_MAP=(
    ["complete"]="--com"
    ["two-valued"]="--twoval"
    ["stable"]="--stm"
)

for problem in complete "two-valued" stable; do
    problem_short="${PROBLEM_MAP[$problem]}"
    fast_file="${RESULTS_DIR}/${problem_short}_fast.txt"
    output_file="${OUTPUT_DIR}/adf_obdd_${problem_short}.txt"
    
    if [ ! -f "$fast_file" ]; then
        echo "Warning: $fast_file not found, skipping $problem"
        continue
    fi
    
    echo "Recording adf-obdd results for $problem..."
    echo "=== adf-obdd $problem ===" > "$output_file"
    
    while IFS= read -r instance; do
        if [ -z "$instance" ]; then
            continue
        fi
        
        # Find the .normal.adf file
        instance_file=$(find "$BENCHMARKS" -name "${instance}.normal.adf" -type f | head -n 1)
        
        if [ -z "$instance_file" ]; then
            echo "Warning: Instance $instance not found, skipping" >> "$output_file"
            continue
        fi
        
        echo "" >> "$output_file"
        echo "--- Instance: $instance ---" >> "$output_file"
        
        # Run the tool WITHOUT --count-only
        ./benchmarks/run_adf-obdd.sh ${ARG_MAP[$problem]} "$instance_file" >> "$output_file" 2>&1 || echo "Error running $instance" >> "$output_file"
        
    done < "$fast_file"
    
    echo "Completed recording for $problem"
done

echo "All adf-obdd recordings completed!"
