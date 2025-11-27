#!/bin/bash

# Arguments: semantics, number of solutions, input file name.
# If first argument is --count-only, output is piped to wc -l

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x

set -e

# Check if first argument is --count-only
if [ "$1" = "--count-only" ]; then
    shift  # Remove --count-only, so $1 becomes semantics, $2 becomes number of solutions, $3 becomes input file
    java -jar /sw/yadf_0.1.1.jar $1 $3 > /tmp/problem.lp 
    /sw/lpopt-2.2-x86_64/lpopt < /tmp/problem.lp > /tmp/translated.lp 
    
    # Regarding exit codes: https://github.com/potassco/clasp/issues/42#issuecomment-459981038
    set +e
    clingo -n $2 /tmp/translated.lp 2>&1 | wc -l
    exit_code=${PIPESTATUS[0]}
    echo "Exit code of yadf/clingo: $exit_code"
    case $exit_code in (10|20|30) exit 0;; (*) exit 1;; esac
else
    java -jar /sw/yadf_0.1.1.jar $1 $3 > /tmp/problem.lp 
    /sw/lpopt-2.2-x86_64/lpopt < /tmp/problem.lp > /tmp/translated.lp 
    
    set +e
    clingo -n $2 /tmp/translated.lp 2>&1
    exit_code=$?
    echo "Exit code of yadf/clingo: $exit_code"
    case $exit_code in (10|20|30) exit 0;; (*) exit 1;; esac
fi

# 10 - SAT and not done
# 20 - UNSAT
# 30 - SAT and done