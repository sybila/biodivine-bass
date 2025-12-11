#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e
set -x

mkdir -p ./results

TOOL='sybila/tool-bass'
BENCHMARKS='./test_instances/_normalized'
TIMEOUT=${TIMEOUT:-'10s'}
PARALLEL=${PARALLEL:-'1'}

# Time to one solution across various semantics.
python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- -v -n 0 -stb
for d in run_*/; do mv -- "$d" "results/bass_stb_${d#./}"; done

python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- -v -n 0 -2v
for d in run_*/; do mv -- "$d" "results/bass_2v_${d#./}"; done

python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- -v -n 0 -prf
for d in run_*/; do mv -- "$d" "results/bass_prf_${d#./}"; done

python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- -v -n 0 -com
for d in run_*/; do mv -- "$d" "results/bass_com_${d#./}"; done

python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- -v -n 0 -adm
for d in run_*/; do mv -- "$d" "results/bass_adm_${d#./}"; done
