#!/bin/bash

# Arguments are passed directly to bioLQM, except for the file name, which is expected
# to be the last argument and is instead passed as first.

# If first argument is --count-only, output is piped to wc -l

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x

set -e

# Check if first argument is --count-only
# The special arguments magic ensures the last argument is first (i.e. model name), and then
# the rest follows as normal.
if [ "$1" = "--count-only" ]; then
    java -jar /sw/bioLQM-0.6.1.jar "${@: -1}" "${@:2:$#-1}" | wc -l
    exit_code=${PIPESTATUS[0]}
    echo "Exit code of bioLQM: $exit_code"
    exit $exit_code
else
    java -jar /sw/bioLQM-0.6.1.jar "${@: -1}" "${@:1:$#-1}"
fi
