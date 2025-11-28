# For some reason, PyEDA does not like newer Python and/or Debian versions.
FROM python:3.11-bookworm

WORKDIR /sw

# Core dependencies needed for benchmarking:
RUN apt-get update && apt install -y --no-install-recommends coreutils time && rm -rf /var/lib/apt/lists/*

# Tool-specific dependencies:
RUN apt-get update && apt install -y --no-install-recommends build-essential gringo unzip && rm -rf /var/lib/apt/lists/*

# See also https://github.com/bnediction/mpbn/
RUN python3 -m venv ./venv
RUN /sw/venv/bin/pip install mpbn==4.1

# A designated file that benchmark scripts will consider as entry point.
COPY ./run.sh /run.sh
RUN chmod +x /run.sh

WORKDIR /root

CMD ["/bin/bash"]