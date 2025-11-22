#!/bin/bash

# All arguments are passed on to adf-obdd

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x
set -e

/sw/adf-obdd-main/target/release/adf-bdd "$@"