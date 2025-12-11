#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

BENCHMARKS='./test_instances/_normalized'
RESULTS_DIR='./benchmarks/results'
OUTPUT_DIR='./benchmarks/results/recorded'

mkdir -p "$OUTPUT_DIR"

# mpbn supports: two-valued (fixedpoints), preferred (attractors)
# Mapping: two-valued -> 2v, preferred -> prf

declare -A PROBLEM_MAP=(
    ["two-valued"]="2v"
    ["preferred"]="prf"
)

declare -A ARG_MAP=(
    ["two-valued"]="fixedpoints"
    ["preferred"]="attractors"
)

for problem in "two-valued" preferred; do
    problem_short="${PROBLEM_MAP[$problem]}"
    fast_file="${RESULTS_DIR}/${problem_short}_fast.txt"
    output_file="${OUTPUT_DIR}/mpbn_${problem_short}.txt"
    
    if [ ! -f "$fast_file" ]; then
        echo "Warning: $fast_file not found, skipping $problem"
        continue
    fi
    
    echo "Recording mpbn results for $problem..."
    echo "=== mpbn $problem ===" > "$output_file"
    
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
        
        # Run the tool without --count-only
        # run_mpbn.sh will swap the arguments as needed
        ./benchmarks/run_mpbn.sh ${ARG_MAP[$problem]} "$instance_file" >> "$output_file" 2>&1 || echo "Error running $instance" >> "$output_file"
        
    done < "$fast_file"
    
    echo "Completed recording for $problem"
done

echo "All mpbn recordings completed!"
