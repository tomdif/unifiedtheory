#!/usr/bin/env python3
"""THE LAMBDA-OBSERVABLE HARDWARE RUN (first execution).

Companion to lambda_hw_protocol.py (protocol + simulator validation,
2026-08-13).  This script runs the record-regression suite on a real
IBM Quantum backend, producing - to our knowledge - the first
experimental bound on the record-regression parameter epsilon_RR.

PHYSICS.  Standard QM: once a record ancilla is written, the
probability of the recorded event is a MARTINGALE under subsequent
unitary evolution + further records - exactly zero regression at
every horizon, for every record.  The bi-normalized theory's
lambda-observable permits one-signed monotone-record regression
bounded by (1-lambda)(|I_T| + |I_{T+1}|).  A null hardware result
bounds epsilon_RR (and thereby the lambda-family); a one-signed
excess beyond the decoherence-symmetric noise floor would be
new physics (and would first demand replication).

CIRCUITS.  For depth d = 1..T (T = 5): system qubit in |+>, then per
stage k <= d: RY(theta_k), RZ(phi_k) on the system, CNOT(system ->
ancilla_k); measure all d ancillas.  Angles fixed (calibrated,
generic).  P_k(d) := P(ancilla_k = 1) estimated from the depth-d
circuit.  Regression estimator per record k: delta_k := P_k(k) -
P_k(T) (probability at write time minus probability at final
horizon).  QM: delta_k = 0 identically.  epsilon_RR := max(0,
max_k delta_k).

REGISTERED READINGS (binomial SEs; sigma_k = SE of delta_k):
  (i)   NULL: every |delta_k| < 3 sigma_k  ->  report the 95% CL
        upper bound  epsilon_RR <= max_k (delta_k + 1.645 sigma_k)
        (one-sided), plus the symmetric-drift diagnostic.  Expected:
        bound at the 1e-2 scale set by hardware readout/gate error.
  (ii)  ONE-SIGNED EXCESS: some delta_k > 3 sigma_k AND the excess
        set is one-signed (all significant delta_k > 0).  FLAGGED
        FOR REPLICATION ONLY - no claim; hardware drift between the
        d=k and d=T jobs can mimic this; a claim would need
        interleaved repetition and error mitigation.
  (iii) SYMMETRIC/NEGATIVE DRIFT: significant delta_k of both signs
        or predominantly negative (noise writes records) -
        decoherence-consistent; still yields the reading-(i) bound
        on the positive side.

BUDGET.  6 jobs (depths 1..5 hardware + the analysis uses depth-k
prefixes), 20000 shots each, single Batch on the least-busy Heron r2
backend; estimated QPU time well under one minute of the 10-minute
open-plan cycle.

Everything (backend, calibration timestamp, raw counts) is logged;
the analysis is deterministic from the log.
"""
import json, math, sys, time
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

def circuit(depth):
    qc = QuantumCircuit(1 + depth, depth)
    qc.h(0)
    for k in range(depth):
        qc.ry(THETAS[k], 0)
        qc.rz(PHIS[k], 0)
        qc.cx(0, 1 + k)
    for k in range(depth):
        qc.measure(1 + k, k)
    return qc

log("connecting to IBM Quantum Platform")
svc = QiskitRuntimeService()
backend = svc.least_busy(operational=True, simulator=False)
log(f"backend: {backend.name} ({backend.num_qubits}q), "
    f"pending jobs: {backend.status().pending_jobs}")

circs = [circuit(d) for d in range(1, T + 1)]
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

# per-depth ancilla-1 marginals
P = {}   # P[(k, d)] = P(ancilla_k = 1 | depth-d circuit)
counts_log = {}
for i, d in enumerate(range(1, T + 1)):
    counts = result[i].data.c.get_counts()
    counts_log[d] = counts
    tot = sum(counts.values())
    for k in range(d):
        ones = sum(v for bits, v in counts.items()
                   if bits[::-1][k] == "1")
        P[(k, d)] = (ones / tot, tot)

log("--- record probabilities P_k(depth) ---")
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

log("--- VERDICT (registered readings) ---")
if not sig_pos and not sig_neg:
    log(f"  reading (i) NULL: all |delta| < 3 sigma.")
    log(f"  epsilon_RR <= {eps_bound:.4f}  (95% CL, one-sided)")
elif sig_pos and not sig_neg:
    log(f"  reading (ii) ONE-SIGNED EXCESS at records {sig_pos}: "
        f"FLAGGED FOR REPLICATION - no claim.")
    log(f"  epsilon_RR bound (if drift): {eps_bound:.4f}")
else:
    log(f"  reading (iii) SYMMETRIC/NEGATIVE DRIFT "
        f"(pos {sig_pos}, neg {sig_neg}): decoherence-consistent.")
    log(f"  positive-side bound: epsilon_RR <= {eps_bound:.4f}")

meta = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "backend": backend.name,
    "job_id": job.job_id(),
    "shots": SHOTS,
    "thetas": THETAS,
    "phis": PHIS,
    "counts": {str(d): c for d, c in counts_log.items()},
    "deltas": [(k, d_, se) for k, d_, se in deltas],
    "eps_RR_95CL": eps_bound,
}
out = f"logs_lambda_hw_{backend.name}_{meta['utc'][:19].replace(':','')}.json"
with open(out, "w") as f:
    json.dump(meta, f, indent=1)
log(f"raw counts + analysis saved to {out}")
log("DONE")
