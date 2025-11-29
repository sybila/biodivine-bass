#!/bin/bash

# All arguments are passed on to goDiamond
# If first argument is --count-only, output is piped to wc -l

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x
set -e

# Note that goDiamond heavily relies on tempfiles, which can cause exhaust
# the available drive space. To mitigate this, we only allow each invocation
# to create files that have 4GB.

if [ "$1" = "--count-only" ]; then
    (ulimit -f 4194304; python3 /sw/diamond/diamond.py "${@:2}") | wc -l
    exit_code=${PIPESTATUS[0]}
    echo "Exit code of goDiamond: $exit_code"
    exit $exit_code
else
    (ulimit -f 4194304; python3 /sw/diamond/diamond.py "$@")
fi