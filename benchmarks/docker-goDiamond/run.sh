#!/bin/bash

# All arguments are passed on to goDiamond
# If first argument is --count-only, output is piped to wc -l

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x
set -e

if [ "$1" = "--count-only" ]; then
    python3 /sw/diamond/diamond.py "${@:2}" | wc -l
else
    python3 /sw/diamond/diamond.py "$@"
fi