# Formal-source checks only. Numerical experiments have separate dependencies.
# docker build -t unified-theory . && docker run --rm unified-theory
FROM ubuntu:22.04

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git python3 && rm -rf /var/lib/apt/lists/*
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    -o /tmp/elan-init.sh && sh /tmp/elan-init.sh -y --default-toolchain none \
    && rm /tmp/elan-init.sh

ENV PATH="/root/.elan/bin:${PATH}"
COPY . /unified-theory
WORKDIR /unified-theory

# Keep failures visible; piping through tail previously hid Lake's exit status.
RUN lake exe cache get && lake build
CMD ["python3", "scripts/check_yang_mills_requirements.py"]
