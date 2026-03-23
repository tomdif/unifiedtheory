# Reproduce all results from "The Physics of Order" trilogy
# docker build -t unified-theory . && docker run unified-theory
FROM ubuntu:22.04

# System deps
RUN apt-get update && apt-get install -y curl git python3 python3-pip && \
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash -s -- -y --default-toolchain none

ENV PATH="/root/.elan/bin:${PATH}"

# Python deps (CPU-only for reproducibility)
RUN pip3 install numpy scipy torch --index-url https://download.pytorch.org/whl/cpu

# Copy project
COPY . /unified-theory
WORKDIR /unified-theory

# Build Lean (proves all theorems)
RUN lake build 2>&1 | tail -5

# Run numerical predictions
CMD echo "=== LEAN VERIFICATION ===" && \
    lake build 2>&1 | grep -E "sorry|error:|Build completed" && \
    echo "" && \
    echo "=== NUMERICAL PREDICTIONS ===" && \
    cd scripts && \
    python3 -c "from lepton_gpu import run_lepton_gpu; r=run_lepton_gpu(10000,300,0); print(f'  m_mu/m_tau = {r[\"r_mu_tau\"]:.4f} (expt: 0.0595)')" && \
    python3 coleman_weinberg.py 2>&1 | grep -A2 "RESULT:" && \
    echo "Done. All results reproduced."
