#!/bin/bash

# All arguments are passed on to goDiamond
# If first argument is --count-only, output is piped to wc -l

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x
set -e

if [ "$1" = "--count-only" ]; then
    python3 /sw/diamond/diamond.py "${@:2}" | wc -l
    exit_code=${PIPESTATUS[0]}
    echo "Exit code of goDiamond: $exit_code"
    exit $exit_code
else
    python3 /sw/diamond/diamond.py "$@"
fi