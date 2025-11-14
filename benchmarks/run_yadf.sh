#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

CONTAINER_WORKDIR='/root'
HOST_WORKDIR=`pwd`
DOCKER_IMAGE='sybila/tool-yadf'

# Read semantics, model count, and input path from command line.
SEMANTICS=-adm
MODEL_COUNT=1
while [[ $# -gt 1 ]]; do
    case "$1" in
        -adm|-com|-prf|-stb) SEMANTICS=$1; shift ;;
        -n) MODEL_COUNT=$2; shift 2 ;;
        *) shift ;;
    esac
done
INPUT=$1

echo "Starting '$DOCKER_IMAGE' in '$HOST_WORKDIR'."
echo "Will execute 'java -jar yadf_0.1.1.jar' with semantics '$SEMANTICS', model count '$MODEL_COUNT' and input file '$INPUT'."

# Run the command inside the docker container
# --rm : Remove the container automatically when it exits
# --init : Hopefully this means internal processes are terminated when this script exits
# -v   : Mount the host directory containing the file(s) into the container
# -w   : Set the working directory inside the container
docker run --rm --init \
  -v "${HOST_WORKDIR}:${CONTAINER_WORKDIR}" \
  -w "${CONTAINER_WORKDIR}" \
  "${DOCKER_IMAGE}" \
  "/run.sh" $SEMANTICS $MODEL_COUNT $INPUT