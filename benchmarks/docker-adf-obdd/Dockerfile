# Stage 1: Build adf-obdd
FROM rust:slim-trixie AS build-stage

WORKDIR /sw

# Basic dependencies for building adf-obdd:
RUN apt-get update && apt install -y --no-install-recommends unzip && rm -rf /var/lib/apt/lists/*

# Sources are originally downloaded from https://github.com/ellmau/adf-obdd/tree/main/bin (ff12d4fede6197d3f24dba52650f5492bb7cc04c)
COPY ./adf-obdd-main.zip ./adf-obdd-main.zip
RUN unzip ./adf-obdd-main.zip
RUN cd ./adf-obdd-main/bin; cargo build --release

# Stage 2: Actual environment to run adf-obdd
FROM debian:trixie AS run-stage

COPY --from=build-stage /sw /sw

# Core dependencies needed for benchmarking:
RUN apt-get update && apt install -y --no-install-recommends coreutils time && rm -rf /var/lib/apt/lists/*

# A designated file that benchmark scripts will consider as entry point.
COPY ./run.sh /run.sh
RUN chmod +x /run.sh

WORKDIR /root

CMD ["/bin/bash"]