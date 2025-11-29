#!/bin/bash

trap 'echo "Received signal, exiting..."; exit 0' SIGINT SIGTERM

CONTAINER_WORKDIR='/root'
HOST_WORKDIR=`pwd`
DOCKER_IMAGE='sybila/tool-yadf'

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
  "/run.sh" "$@"