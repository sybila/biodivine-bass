#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e
set -x

mkdir -p ./results

TIMEOUT='10s'
TOOL='sybila/tool-k-adf'
BENCHMARKS='./test_instances/_normalized'

# Time to one solution across various semantics.
python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' -- adm
for d in run_*/; do mv -- "$d" "results/yadf_1_adm_${d#./}"; done
python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' -- com
for d in run_*/; do mv -- "$d" "results/yadf_1_com_${d#./}"; done
python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' -- prf
for d in run_*/; do mv -- "$d" "results/yadf_1_prf_${d#./}"; done
python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' -- stb
for d in run_*/; do mv -- "$d" "results/yadf_1_stb_${d#./}"; done