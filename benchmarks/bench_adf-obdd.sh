#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -e
set -x

mkdir -p ./results

TOOL='sybila/tool-adf-obdd'
BENCHMARKS='./test_instances/_normalized'
TIMEOUT=${TIMEOUT:-'10s'}
PARALLEL=${PARALLEL:-'1'}

# Time to one solution across various semantics.
# python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- adm
# for d in run_*/; do mv -- "$d" "results/adf_obdd_adm_${d#./}"; done
python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- --com
for d in run_*/; do mv -- "$d" "results/adf_obdd_com_${d#./}"; done
#python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- prf
#for d in run_*/; do mv -- "$d" "results/adf_obdd_prf_${d#./}"; done
python3 ./benchmarks/bench_docker.py --docker-image $TOOL --timeout $TIMEOUT --folder $BENCHMARKS --match '.*.adf' --parallel $PARALLEL -- --stm
for d in run_*/; do mv -- "$d" "results/adf_obdd_stb_${d#./}"; done

