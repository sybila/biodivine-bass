#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

BENCHMARKS='./test_instances/_normalized'
RESULTS_DIR='./benchmarks/results'
OUTPUT_DIR='./benchmarks/results/recorded'

mkdir -p "$OUTPUT_DIR"

# tsconj supports: fix (2v), min (prf)
# Mapping: fix -> 2v, min -> prf

declare -A PROBLEM_MAP=(
    ["fix"]="2v"
    ["min"]="prf"
)

declare -A ARG_MAP=(
    ["fix"]="/sw/run.py fix 0"
    ["min"]="/sw/run.py min 0"
)

for problem in fix min; do
    problem_short="${PROBLEM_MAP[$problem]}"
    fast_file="${RESULTS_DIR}/${problem_short}_fast.txt"
    output_file="${OUTPUT_DIR}/tsconj_${problem_short}.txt"
    
    if [ ! -f "$fast_file" ]; then
        echo "Warning: $fast_file not found, skipping $problem"
        continue
    fi
    
    echo "Recording tsconj results for $problem..."
    echo "=== tsconj $problem ===" > "$output_file"
    
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
        ./benchmarks/run_tsconj.sh ${ARG_MAP[$problem]} "$instance_file" >> "$output_file" 2>&1 || echo "Error running $instance" >> "$output_file"
        
    done < "$fast_file"
    
    echo "Completed recording for $problem"
done

echo "All tsconj recordings completed!"
