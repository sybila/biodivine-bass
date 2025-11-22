#!/bin/bash

# Arguments: semantics, number of solutions, input file name.

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x

set -e
java -jar /sw/yadf_0.1.1.jar $1 $3 > /tmp/problem.lp 
/sw/lpopt-2.2-x86_64/lpopt < /tmp/problem.lp > /tmp/translated.lp 

# Regarding exit codes: https://github.com/potassco/clasp/issues/42#issuecomment-459981038
set +e
if [ "$2" = "0" ]; then
    clingo -n $2 /tmp/translated.lp 2>&1 | wc -l
    exit_code=${PIPESTATUS[0]}
else
    clingo -n $2 /tmp/translated.lp
    exit_code=$?
fi
case $exit_code in (10|20|30) exit 0;; (*) exit 1;; esac

# 10 - SAT and not done
# 20 - UNSAT
# 30 - SAT and done