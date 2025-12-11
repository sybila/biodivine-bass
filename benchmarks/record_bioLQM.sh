#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

BENCHMARKS='./test_instances/_normalized'
RESULTS_DIR='./benchmarks/results'
OUTPUT_DIR='./benchmarks/results/recorded'

mkdir -p "$OUTPUT_DIR"

# bioLQM supports: stable (2v), trapspace terminal (prf), trapspace tree (com), trapspace all (adm)
# Mapping: stable -> 2v, trapspace terminal -> prf, trapspace tree -> com, trapspace all -> adm

declare -A PROBLEM_MAP=(
    ["stable"]="2v"
    ["trapspace-terminal"]="prf"
    ["trapspace-tree"]="com"
    ["trapspace-all"]="adm"
)

declare -A ARG_MAP=(
    ["stable"]="-r stable BDD"
    ["trapspace-terminal"]="-r trapspace terminal BDD"
    ["trapspace-tree"]="-r trapspace tree BDD"
    ["trapspace-all"]="-r trapspace all BDD"
)

for problem in stable "trapspace-terminal" "trapspace-tree" "trapspace-all"; do
    problem_short="${PROBLEM_MAP[$problem]}"
    fast_file="${RESULTS_DIR}/${problem_short}_fast.txt"
    output_file="${OUTPUT_DIR}/biolqm_${problem_short}.txt"
    
    if [ ! -f "$fast_file" ]; then
        echo "Warning: $fast_file not found, skipping $problem"
        continue
    fi
    
    echo "Recording bioLQM results for $problem..."
    echo "=== bioLQM $problem ===" > "$output_file"
    
    while IFS= read -r instance; do
        if [ -z "$instance" ]; then
            continue
        fi
        
        # Find the .normal.sbml file
        instance_file=$(find "$BENCHMARKS" -name "${instance}.normal.sbml" -type f | head -n 1)
        
        if [ -z "$instance_file" ]; then
            echo "Warning: Instance $instance not found, skipping" >> "$output_file"
            continue
        fi
        
        echo "" >> "$output_file"
        echo "--- Instance: $instance ---" >> "$output_file"
        
        # Run the tool WITHOUT --count-only
        ./benchmarks/run_bioLQM.sh ${ARG_MAP[$problem]} "$instance_file" >> "$output_file" 2>&1 || echo "Error running $instance" >> "$output_file"
        
    done < "$fast_file"
    
    echo "Completed recording for $problem"
done

echo "All bioLQM recordings completed!"
