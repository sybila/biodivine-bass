#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

BENCHMARKS='./test_instances/_normalized'
RESULTS_DIR='./benchmarks/results'
OUTPUT_DIR='./benchmarks/results/recorded'

mkdir -p "$OUTPUT_DIR"

# yadf supports: admissible, complete, preferred, stable
# Mapping: admissible -> adm, complete -> com, preferred -> prf, stable -> stm

declare -A PROBLEM_MAP=(
    ["admissible"]="adm"
    ["complete"]="com"
    ["preferred"]="prf"
    ["stable"]="stm"
)

declare -A ARG_MAP=(
    ["admissible"]="-adm 0"
    ["complete"]="-com 0"
    ["preferred"]="-prf 0"
    ["stable"]="-stb 0"
)

for problem in admissible complete preferred stable; do
    problem_short="${PROBLEM_MAP[$problem]}"
    fast_file="${RESULTS_DIR}/${problem_short}_fast.txt"
    output_file="${OUTPUT_DIR}/yadf_${problem_short}.txt"
    
    if [ ! -f "$fast_file" ]; then
        echo "Warning: $fast_file not found, skipping $problem"
        continue
    fi
    
    echo "Recording yadf results for $problem..."
    echo "=== yadf $problem ===" > "$output_file"
    
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
        ./benchmarks/run_yadf.sh ${ARG_MAP[$problem]} "$instance_file" >> "$output_file" 2>&1 || echo "Error running $instance" >> "$output_file"
        
    done < "$fast_file"
    
    echo "Completed recording for $problem"
done

echo "All yadf recordings completed!"
