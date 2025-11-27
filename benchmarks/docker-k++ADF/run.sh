#!/bin/bash

# All arguments are passed on to k++ADF
# If first argument is --count-only, output is piped to wc -l

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x
set -e

if [ "$1" = "--count-only" ]; then
    /sw/andreasniskanen-k-adf-637c31f2fd4f/k++adf "${@:2}" | wc -l
    exit_code=${PIPESTATUS[0]}
    echo "Exit code of k++ADF: $exit_code"
    exit $exit_code
else
    /sw/andreasniskanen-k-adf-637c31f2fd4f/k++adf "$@"
fi