#!/bin/bash

# All arguments are passed on to fASP

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x
set -e

if [ "$1" = "--count-only" ]; then
    /sw/venv/bin/fASP "${@:2}" | wc -l
    exit_code=${PIPESTATUS[0]}
    echo "Exit code of fASP: $exit_code"
    exit $exit_code
else    
    /sw/venv/bin/fASP "$@"
fi