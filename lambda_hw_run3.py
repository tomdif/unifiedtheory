#!/usr/bin/env python3
"""LAMBDA-OBSERVABLE HARDWARE RUN v3: LINE-WALK, FULLY MATCHED.

Run 1 confound: T1 idle mismatch (shallow circuits measured early).
Run 2 (matched duration) confound: transpiler ROUTING - one system
qubit recording to 5 ancillas needs SWAP chains on the heavy-hex
lattice; 2q-gate counts jumped [1,2,3,10,11], so depth >= 4 circuits
carry ~3x the gate error, producing one-signed deltas from routing
alone.  Within run 2's routing-free window (d <= 3) the result was
NULL: record 0 +1.9 sigma, record 1 +1.4 sigma.

V3 PROTOCOL (T1-matched AND routing-matched): six circuit wires
mapped to a physical PATH p0..p5 on the device (found from the
coupling map).  The system walks the line: at stage k it sits on
wire k, applies RY/RZ, SWAPs forward to wire k+1, and (iff the
record is included) applies one CNOT back to the vacated wire k,
whose qubit then holds the record and is never touched again.
Every circuit contains the identical RY/RZ/SWAP skeleton; circuits
differ ONLY by which single back-CNOTs are present (one 2q gate
per record, ~1e-3 error each - the residual mismatch, quantified).
All 2q gates are nearest-neighbor on the path by construction, so
the transpiler adds no routing (verified by printed gate counts).
Ancillas are measured at the end in every circuit (identical idle).

Estimators and registered readings as in runs 1-2:
  delta_k = P_k(k+1) - P_k(T), binomial sigma_k.
  (i) NULL: all |delta| < 3 sigma -> one-sided 95% CL bound
      epsilon_RR <= max_k(delta_k + 1.645 sigma_k).
  (ii) one-signed excess > 3 sigma -> flagged for replication only.
  (iii) mixed/negative -> decoherence-consistent.
Residual systematic floor: (T-d) extra CZs' worth of error
difference (~ few x 1e-3) + crosstalk; anything at or below that
scale is NOT attributable to record physics.
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

def circuit_line(d):
    """System walks wires 0..T; ancilla for stage k lives on wire k.
    Identical skeleton for every d; only back-CNOTs differ."""
    qc = QuantumCircuit(T + 1, d)
    qc.h(0)
    for k in range(T):
        qc.ry(THETAS[k], k)
        qc.rz(PHIS[k], k)
        qc.swap(k, k + 1)
        if k < d:
            qc.cx(k + 1, k)
    for k in range(d):
        qc.measure(k, k)
    return qc

def find_path(cmap, length):
    """simple DFS for a path of `length` distinct qubits."""
    adj = {}
    for a, b in cmap:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    def dfs(path):
        if len(path) == length:
            return path
        for nxt in sorted(adj.get(path[-1], ())):
            if nxt not in path:
                r = dfs(path + [nxt])
                if r:
                    return r
        return None
    for start in sorted(adj):
        r = dfs([start])
        if r:
            return r
    raise RuntimeError("no path found")

log("connecting to IBM Quantum Platform")
svc = QiskitRuntimeService()
backend = svc.backend("ibm_marrakesh")
log(f"backend: {backend.name}, pending: {backend.status().pending_jobs}")

cmap = [tuple(e) for e in backend.configuration().coupling_map]
path = find_path(cmap, T + 1)
log(f"physical path: {path}")

circs = [circuit_line(d) for d in range(1, T + 1)]
pm = generate_preset_pass_manager(backend=backend, optimization_level=1,
                                  initial_layout=path)
isa = [pm.run(c) for c in circs]
counts2q = [c.count_ops().get("cz", 0) + c.count_ops().get("ecr", 0)
            for c in isa]
log(f"transpiled 2q-gate counts (should rise by 1 per depth): {counts2q}")

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

log("--- record probabilities P_k(depth), fully matched ---")
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

log("--- VERDICT (registered readings, v3 line-walk) ---")
if not sig_pos and not sig_neg:
    log("  reading (i) NULL: all |delta| < 3 sigma.")
    log(f"  epsilon_RR <= {eps_bound:.4f}  (95% CL, one-sided, "
        "T1- and routing-matched)")
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
    "protocol": "v3-line-walk-matched",
    "backend": backend.name,
    "physical_path": path,
    "counts2q": counts2q,
    "job_id": job.job_id(),
    "shots": SHOTS,
    "thetas": THETAS,
    "phis": PHIS,
    "counts": {str(d): c for d, c in counts_log.items()},
    "deltas": [(k, d_, se) for k, d_, se in deltas],
    "eps_RR_95CL": eps_bound,
}
out = (f"logs_lambda_hw_v3_{backend.name}_"
       f"{meta['utc'][:19].replace(':','')}.json")
with open(out, "w") as f:
    json.dump(meta, f, indent=1)
log(f"raw counts + analysis saved to {out}")
log("DONE")
