#!/bin/bash

# Expects only one argument: file name.

# If first argument is --count-only, output is piped to wc -l

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x

set -e

# Check if first argument is --count-only
# The special arguments magic ensures the last argument is first (i.e. model name), and then
# the rest follows as normal.
if [ "$1" = "--count-only" ]; then
    /app/solve-bmsa.sh 64g 1g h3 $2 | wc -l
    exit_code=${PIPESTATUS[0]}
    echo "Exit code of bsaf: $exit_code"
    exit $exit_code
else
    /app/solve-bmsa.sh 64g 1g h3 $1
fi
