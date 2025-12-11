FROM debian:trixie

WORKDIR /sw

# Core dependencies needed for benchmarking:
RUN apt-get update && apt install -y --no-install-recommends coreutils time && rm -rf /var/lib/apt/lists/*

# Tool-specific dependencies:
RUN apt-get update && apt install -y --no-install-recommends gringo python3 bzip2 && rm -rf /var/lib/apt/lists/*

# Downloaded from https://sourceforge.net/projects/diamond-adf/
COPY ./diamond-2.0.2.tar.bz2 /sw/diamond-2.0.2.tar.bz2
RUN tar -xf /sw/diamond-2.0.2.tar.bz2

# A designated file that benchmark scripts will consider as entry point.
COPY ./run.sh /run.sh
RUN chmod +x /run.sh

# Make a link to the python interpreter
RUN ln -s $(which python3) /usr/bin/python

WORKDIR /root

CMD ["/bin/bash"]