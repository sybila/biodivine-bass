#!/bin/bash

# All arguments are passed on to k++ADF

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

set -x
set -e

/sw/andreasniskanen-k-adf-637c31f2fd4f/k++adf "$@"