#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

BENCHMARKS='./test_instances/_normalized'
RESULTS_DIR='./benchmarks/results'
OUTPUT_DIR='./benchmarks/results/recorded'

mkdir -p "$OUTPUT_DIR"

# k++ADF supports: mod (2v), adm, com, prf, stb
# Mapping: mod -> 2v, adm -> adm, com -> com, prf -> prf, stb -> stm

declare -A PROBLEM_MAP=(
    ["mod"]="2v"
    ["adm"]="adm"
    ["com"]="com"
    ["prf"]="prf"
    ["stb"]="stm"
)

declare -A ARG_MAP=(
    ["mod"]="mod"
    ["adm"]="adm"
    ["com"]="com"
    ["prf"]="prf"
    ["stb"]="stb"
)

for problem in mod adm com prf stb; do
    problem_short="${PROBLEM_MAP[$problem]}"
    fast_file="${RESULTS_DIR}/${problem_short}_fast.txt"
    output_file="${OUTPUT_DIR}/k_adf_${problem_short}.txt"
    
    if [ ! -f "$fast_file" ]; then
        echo "Warning: $fast_file not found, skipping $problem"
        continue
    fi
    
    echo "Recording k++ADF results for $problem..."
    echo "=== k++ADF $problem ===" > "$output_file"
    
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
        ./benchmarks/run_k++ADF.sh ${ARG_MAP[$problem]} "$instance_file" >> "$output_file" 2>&1 || echo "Error running $instance" >> "$output_file"
        
    done < "$fast_file"
    
    echo "Completed recording for $problem"
done

echo "All k++ADF recordings completed!"
