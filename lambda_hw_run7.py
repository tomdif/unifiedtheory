#!/usr/bin/env python3
"""LAMBDA-OBSERVABLE v7: RECORD-0 EXCESS DISCRIMINATORS.

v6 (pooled, readout-matched) left ONE reproducible signal: record 0
delta = +0.0118 +- 0.0016 (+7.5 sigma), chi2-consistent across
interleaved repeats, while records 1-3 are dead null at +-0.002.
Two discriminators, same protocol, R = 3 repeats each:

  v7a  ibm_marrakesh, physical path REVERSED [5,4,3,2,1,0]:
       if the excess follows PHYSICAL qubit 0 it vanishes from
       record 0 (whose ancilla now lives on qubit 5); if it follows
       the LOGICAL record-0 position it persists.
  v7b  ibm_fez (different device), path [0..5]:
       device-specificity test.

REGISTERED READINGS (for the record-0 delta, sigma ~ 0.0023):
  (A) excess ABSENT (< 3 sigma) on both  ->  marrakesh-qubit-0
      hardware artifact; the clean-null bound stands on records 1-3
      and the record-0 line is excluded as device-specific.
  (B) excess PERSISTS (> 3 sigma, same sign, comparable size) on
      the reversed path AND on fez  ->  protocol-position-linked;
      escalate: this is what record physics would look like -
      requires angle-family variation + mitigation studies before
      any claim.
  (C) mixed  ->  partial hardware attribution; iterate.

Usage: lambda_hw_run7.py <backend> <reverse:0|1> <R>
"""
import json, math, random, sys, time
from datetime import datetime, timezone

from qiskit import QuantumCircuit
from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2, Batch

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

BACKEND = sys.argv[1] if len(sys.argv) > 1 else "ibm_marrakesh"
REVERSE = bool(int(sys.argv[2])) if len(sys.argv) > 2 else False
R = int(sys.argv[3]) if len(sys.argv) > 3 else 3
AVOID = set(int(x) for x in sys.argv[4].split(",")) if len(sys.argv) > 4 else set()
T = 5
SHOTS = 20000
THETAS = [0.9, 1.3, 0.7, 1.1, 0.5]
PHIS = [0.4, 1.0, 0.6, 1.2, 0.8]

def circuit_line(d):
    qc = QuantumCircuit(T + 1, T)
    qc.h(0)
    for k in range(T):
        qc.ry(THETAS[k], k)
        qc.rz(PHIS[k], k)
        qc.swap(k, k + 1)
        if k < d:
            qc.cx(k + 1, k)
    for k in range(T):
        qc.measure(k, k)
    return qc

def find_path(cmap, length):
    adj = {}
    for a, b in cmap:
        if a in AVOID or b in AVOID:
            continue
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
    raise RuntimeError("no path")

log(f"config: backend={BACKEND} reverse={REVERSE} R={R}")
svc = QiskitRuntimeService()
backend = svc.backend(BACKEND)
log(f"backend: {backend.name}, pending: {backend.status().pending_jobs}")

cmap = [tuple(e) for e in backend.configuration().coupling_map]
path = find_path(cmap, T + 1)
if REVERSE:
    path = path[::-1]
log(f"physical path: {path}")

pm = generate_preset_pass_manager(backend=backend, optimization_level=1,
                                  initial_layout=path)
isa = {d: pm.run(circuit_line(d)) for d in range(1, T + 1)}
counts2q = {d: isa[d].count_ops().get("cz", 0)
            + isa[d].count_ops().get("ecr", 0) for d in isa}
log(f"2q-gate counts: {counts2q}")

order = [(r, d) for r in range(R) for d in range(1, T + 1)]
random.Random(20260814).shuffle(order)
pubs = [isa[d] for _, d in order]

log(f"submitting batch: {len(pubs)} pubs x {SHOTS} shots")
with Batch(backend=backend) as batch:
    sampler = SamplerV2(mode=batch)
    job = sampler.run(pubs, shots=SHOTS)
    log(f"job id: {job.job_id()}")
    result = job.result()
log("results received")

ones, tot, counts_log = {}, {}, {}
for i, (r, d) in enumerate(order):
    counts = result[i].data.c.get_counts()
    counts_log[f"{r}:{d}"] = counts
    tt = sum(counts.values())
    tot[(d, r)] = tt
    for k in range(d):
        ones[(k, d, r)] = sum(v for bits, v in counts.items()
                              if bits[::-1][k] == "1")

def P_pool(k, d):
    o = sum(ones[(k, d, r)] for r in range(R))
    n = sum(tot[(d, r)] for r in range(R))
    return o / n, n

log("--- pooled record probabilities ---")
for k in range(T):
    row = "  ".join(f"d={d}: {P_pool(k,d)[0]:.4f}"
                    for d in range(k + 1, T + 1))
    log(f"  ancilla {k}: {row}")

log("--- pooled regression estimators ---")
deltas = []
for k in range(T - 1):
    p1, n1 = P_pool(k, k + 1)
    p2, n2 = P_pool(k, T)
    d_ = p1 - p2
    se = math.sqrt(p1 * (1 - p1) / n1 + p2 * (1 - p2) / n2)
    deltas.append((k, d_, se))
    log(f"  record {k}: delta = {d_:+.4f} ± {se:.4f} "
        f"({d_/se:+.1f} sigma)")

k0, d0, s0 = deltas[0]
log("--- record-0 discriminator verdict ---")
if d0 > 3 * s0:
    log(f"  record-0 excess PERSISTS here: {d0:+.4f} ({d0/s0:+.1f} "
        "sigma)")
else:
    log(f"  record-0 excess ABSENT here: {d0:+.4f} ({d0/s0:+.1f} "
        "sigma)")

meta = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "protocol": f"v7-{'reversed' if REVERSE else 'forward'}-avoid{sorted(AVOID)}",
    "backend": backend.name,
    "physical_path": path,
    "repeats": R,
    "counts2q": counts2q,
    "job_id": job.job_id(),
    "shots": SHOTS,
    "counts": counts_log,
    "deltas": deltas,
}
out = (f"logs_lambda_hw_v7_{backend.name}_"
       f"{'rev' if REVERSE else 'fwd'}_"
       f"{meta['utc'][:19].replace(':','')}.json")
with open(out, "w") as f:
    json.dump(meta, f, indent=1)
log(f"saved {out}")
log("DONE")
