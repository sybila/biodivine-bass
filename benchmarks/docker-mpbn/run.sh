#!/bin/bash

# All arguments are passed on to mpbn

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x
set -e

# We need to swap the last two arguments, because mpbn expects the arguments to end 
# with .bnet file and problem type.

if [ "$1" = "--count-only" ]; then
    args=("${@:2}")          # drop $1
    last=${#args[@]}        # index of last element

    # swap last two
    if (( last >= 2 )); then
        last=${args[-1]}
        prev=${args[-2]}
        args[-1]=$prev
        args[-2]=$last
    fi

    /sw/venv/bin/mpbn "${args[@]}" | wc -l
    exit_code=${PIPESTATUS[0]}
    echo "Exit code of mpbn: $exit_code"
    exit $exit_code
else
    args=("$@")
    last=${#args[@]}        # index of last element

    # swap last two
    if (( last >= 2 )); then
        last=${args[-1]}
        prev=${args[-2]}
        args[-1]=$prev
        args[-2]=$last
    fi

    /sw/venv/bin/mpbn "${args[@]}"
fi