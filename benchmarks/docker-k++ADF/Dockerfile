# Stage 1: Build k++-ADF
FROM debian:trixie AS build-stage

WORKDIR /sw

# Basic dependencies for building a C++ project and k++ADF specifically:
RUN apt-get update && apt install -y --no-install-recommends build-essential unzip zlib1g-dev && rm -rf /var/lib/apt/lists/*

# Sources are originally downloaded from https://bitbucket.org/andreasniskanen/k-adf/src/master/ (637c31f)
COPY ./andreasniskanen-k-adf-637c31f2fd4f.zip ./andreasniskanen-k-adf-637c31f2fd4f.zip 
RUN unzip ./andreasniskanen-k-adf-637c31f2fd4f.zip 
RUN cd ./andreasniskanen-k-adf-637c31f2fd4f; make

# Stage 2: Actual environment to run k++-ADF
FROM debian:trixie AS run-stage

COPY --from=build-stage /sw /sw

# Core dependencies needed for benchmarking:
RUN apt-get update && apt install -y --no-install-recommends coreutils time && rm -rf /var/lib/apt/lists/*

# A designated file that benchmark scripts will consider as entry point.
COPY ./run.sh /run.sh
RUN chmod +x /run.sh

WORKDIR /root

CMD ["/bin/bash"]