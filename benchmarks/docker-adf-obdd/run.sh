#!/bin/bash

# All arguments are passed on to adf-obdd
# If first argument is --count-only, output is piped to wc -l

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x
set -e

if [ "$1" = "--count-only" ]; then
    /sw/adf-obdd-main/target/release/adf-bdd "${@:2}" | wc -l
    exit_code=${PIPESTATUS[0]}
    echo "Exit code of ADF-OBDD: $exit_code"
    exit $exit_code
else
    /sw/adf-obdd-main/target/release/adf-bdd "$@"
fi