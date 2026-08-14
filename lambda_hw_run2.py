#!/usr/bin/env python3
"""LAMBDA-OBSERVABLE HARDWARE RUN v2: MATCHED-DURATION PROTOCOL.

Run 1 (lambda_hw_run.py, ibm_marrakesh job d9vnulob1g9c73a8u8ag)
fired reading (ii) at records 0,1 (+5.3, +6.7 sigma) - but analysis
identified a CONFOUND the original protocol note underestimated:
in the naive prefix comparison the shallow circuit measures the
ancilla right after writing while the deep circuit lets it idle
through the remaining stages, so one-signed positive regression is
exactly the T1-relaxation signature (P ~ 0.87, idle ~ several us,
T1 ~ 200 us -> ~2%, the observed order).  Registered correction.

V2 PROTOCOL (T1-matched): the depth-d circuit runs ALL T stages of
system-qubit unitaries; only the CNOTs of the first d stages are
included.  Every circuit has identical duration, identical system
1q-gate sequence, and ancilla k idles identically in every circuit
that contains it.  The ONLY difference between P_k(d) and P_k(T) is
the presence of later record-writing CNOTs - which is precisely the
lambda-observable question (does writing further records regress
earlier ones?), now with T1 cancelling in delta_k at first order.
Residual systematics: crosstalk from the extra CNOTs and their gate
error on the system qubit (order 1e-3 per 2q gate).

Estimators and REGISTERED READINGS identical to run 1:
  delta_k = P_k(k+1) - P_k(T);  sigma_k binomial.
  (i)   NULL (all |delta| < 3 sigma): report one-sided 95% CL bound
        epsilon_RR <= max_k(delta_k + 1.645 sigma_k).  With T1
        cancelled the expected floor is the crosstalk scale ~1e-2/2q
        ... realistically a few x 1e-3.
  (ii)  ONE-SIGNED EXCESS beyond 3 sigma: flagged for replication
        only (crosstalk asymmetry must first be excluded with
        interleaved repeats and dynamical decoupling).
  (iii) both signs / negative: decoherence-consistent.
"""
import json, math, time
from datetime import datetime, timezone

from qiskit import QuantumCircuit
from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2, Batch

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

T = 5
SHOTS = 20000
THETAS = [0.9, 1.3, 0.7, 1.1, 0.5]
PHIS = [0.4, 1.0, 0.6, 1.2, 0.8]

def circuit_matched(d):
    """All T stages of system gates; CNOT records only for k < d.
    Ancillas: T of them always present (idling identically)."""
    qc = QuantumCircuit(1 + T, d)
    qc.h(0)
    for k in range(T):
        qc.ry(THETAS[k], 0)
        qc.rz(PHIS[k], 0)
        if k < d:
            qc.cx(0, 1 + k)
    for k in range(d):
        qc.measure(1 + k, k)
    return qc

log("connecting to IBM Quantum Platform")
svc = QiskitRuntimeService()
backend = svc.backend("ibm_marrakesh")
log(f"backend: {backend.name} ({backend.num_qubits}q), "
    f"pending jobs: {backend.status().pending_jobs}")

circs = [circuit_matched(d) for d in range(1, T + 1)]
pm = generate_preset_pass_manager(backend=backend, optimization_level=1)
isa = [pm.run(c) for c in circs]
log(f"transpiled {len(isa)} circuits; 2q-gate counts: "
    f"{[c.count_ops().get('cz', 0) + c.count_ops().get('ecr', 0) for c in isa]}")

log(f"submitting batch ({SHOTS} shots per circuit)")
with Batch(backend=backend) as batch:
    sampler = SamplerV2(mode=batch)
    job = sampler.run(isa, shots=SHOTS)
    log(f"job id: {job.job_id()}")
    result = job.result()
log("results received")

P = {}
counts_log = {}
for i, d in enumerate(range(1, T + 1)):
    counts = result[i].data.c.get_counts()
    counts_log[d] = counts
    tot = sum(counts.values())
    for k in range(d):
        ones = sum(v for bits, v in counts.items()
                   if bits[::-1][k] == "1")
        P[(k, d)] = (ones / tot, tot)

log("--- record probabilities P_k(depth), T1-matched ---")
for k in range(T):
    row = "  ".join(f"d={d}: {P[(k,d)][0]:.4f}"
                    for d in range(k + 1, T + 1))
    log(f"  ancilla {k}: {row}")

log("--- regression estimators delta_k = P_k(k+1) - P_k(T) ---")
deltas = []
for k in range(T - 1):
    p1, n1 = P[(k, k + 1)]
    p2, n2 = P[(k, T)]
    d_ = p1 - p2
    se = math.sqrt(p1 * (1 - p1) / n1 + p2 * (1 - p2) / n2)
    deltas.append((k, d_, se))
    log(f"  record {k}: delta = {d_:+.4f} ± {se:.4f} "
        f"({d_/se:+.1f} sigma)")

eps_bound = max(0.0, max(d_ + 1.645 * se for _, d_, se in deltas))
sig_pos = [k for k, d_, se in deltas if d_ > 3 * se]
sig_neg = [k for k, d_, se in deltas if d_ < -3 * se]

log("--- VERDICT (registered readings, v2 matched) ---")
if not sig_pos and not sig_neg:
    log("  reading (i) NULL: all |delta| < 3 sigma.")
    log(f"  epsilon_RR <= {eps_bound:.4f}  (95% CL, one-sided, T1-matched)")
elif sig_pos and not sig_neg:
    log(f"  reading (ii) ONE-SIGNED EXCESS at records {sig_pos}: "
        "FLAGGED FOR REPLICATION - no claim.")
    log(f"  bound if systematic: {eps_bound:.4f}")
else:
    log(f"  reading (iii) MIXED/NEGATIVE (pos {sig_pos}, neg {sig_neg}): "
        "decoherence/crosstalk-consistent.")
    log(f"  positive-side bound: epsilon_RR <= {eps_bound:.4f}")

meta = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "protocol": "v2-matched-duration",
    "backend": backend.name,
    "job_id": job.job_id(),
    "shots": SHOTS,
    "thetas": THETAS,
    "phis": PHIS,
    "counts": {str(d): c for d, c in counts_log.items()},
    "deltas": [(k, d_, se) for k, d_, se in deltas],
    "eps_RR_95CL": eps_bound,
}
out = (f"logs_lambda_hw_v2_{backend.name}_"
       f"{meta['utc'][:19].replace(':','')}.json")
with open(out, "w") as f:
    json.dump(meta, f, indent=1)
log(f"raw counts + analysis saved to {out}")
log("DONE")
