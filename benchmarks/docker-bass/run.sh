#!/bin/bash

# All arguments are passed on to adf-obdd
# If first argument is --count-only, output is piped to wc -l

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x
set -e

if [ "$1" = "--count-only" ]; then
    RUST_LOG=debug /sw/BAss "${@:2}" | wc -l
    exit_code=${PIPESTATUS[0]}
    echo "Exit code of BAss: $exit_code"
    exit $exit_code
else
    RUST_LOG=debug /sw/BAss "$@"
fi