#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e
set -x

mkdir -p ./results

TOOL='sybila/tool-mpbn'
BENCHMARKS='./test_instances/_normalized'
TIMEOUT=${TIMEOUT:-'10s'}
PARALLEL=${PARALLEL:-'1'}

python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.bnet' --parallel $PARALLEL -- --count-only fixedpoints
for d in run_*/; do mv -- "$d" "results/mpbn_2v_${d#./}"; done

python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.bnet' --parallel $PARALLEL -- --count-only attractors
for d in run_*/; do mv -- "$d" "results/mpbn_prf_${d#./}"; done
