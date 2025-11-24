#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e
set -x

mkdir -p ./results

TOOL='sybila/tool-go-diamond'
BENCHMARKS='./test_instances/_normalized'
TIMEOUT=${TIMEOUT:-'10s'}
PARALLEL=${PARALLEL:-'1'}

# Time to one solution across various semantics.
python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- --count-only -mod
for d in run_*/; do mv -- "$d" "results/go_diamond_2v_${d#./}"; done

python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- --count-only -adm
for d in run_*/; do mv -- "$d" "results/go_diamond_adm_${d#./}"; done

python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- --count-only -com
for d in run_*/; do mv -- "$d" "results/go_diamond_com_${d#./}"; done

python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- --count-only -prf
for d in run_*/; do mv -- "$d" "results/go_diamond_prf_${d#./}"; done

python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- --count-only -stm
for d in run_*/; do mv -- "$d" "results/go_diamond_stb_${d#./}"; done
