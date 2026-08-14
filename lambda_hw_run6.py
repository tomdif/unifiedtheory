#!/usr/bin/env python3
"""LAMBDA-OBSERVABLE HARDWARE RUN v6: POOLED STATISTICS
(registered follow-up: push the bound toward 1e-2).

Protocol identical to v5 (line-walk, T1- routing- and readout-
matched) - the five depth circuits are submitted R = 6 times each,
interleaved in one Batch in a seeded-shuffled order (drift
decorrelation), 20000 shots per pub (2.4e5 total per depth).

Analysis: pooled P_k(d) across repeats; per-repeat deltas give a
drift diagnostic chi^2_k = sum_r (delta_r - mean)^2 / sigma_r^2
~ chi^2(R-1).

REGISTERED READINGS (pooled sigma ~ 0.002):
  (i)   NULL: all pooled |delta_k| < 3 sigma  ->  bound
        eps_RR <= max_k(delta_k + 1.645 sigma_k); expected scale
        ~1e-2 or below.
  (ii)  ONE-SIGNED EXCESS > 3 sigma with chi^2 CONSISTENT across
        repeats (p > 0.01): reproducible systematic or physics -
        flagged for cross-backend replication.
  (iii) excess with chi^2 INCONSISTENT (p < 0.01): drift-dominated,
        inconclusive at this depth of averaging.
Also registered: v5's +1.9 sigma (record 0) and +2.6 sigma
(record 3) should regress toward 0 if they were fluctuations.
Final line combines the pooled bound with the theory-side envelope
sums S_k (lambda_theory_I.py) into the conditional (1-lambda) bound.
"""
import json, math, random, time
from datetime import datetime, timezone

from qiskit import QuantumCircuit
from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2, Batch

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

T = 5
R = 6
SHOTS = 20000
THETAS = [0.9, 1.3, 0.7, 1.1, 0.5]
PHIS = [0.4, 1.0, 0.6, 1.2, 0.8]
S_ENV = {0: 3.3814, 1: 2.1627, 2: 0.5542, 3: 0.5393}  # lambda_theory_I

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

log("connecting to IBM Quantum Platform")
svc = QiskitRuntimeService()
backend = svc.backend("ibm_marrakesh")
log(f"backend: {backend.name}, pending: {backend.status().pending_jobs}")

cmap = [tuple(e) for e in backend.configuration().coupling_map]
path = [0, 1, 2, 3, 4, 5]
pm = generate_preset_pass_manager(backend=backend, optimization_level=1,
                                  initial_layout=path)
isa = {d: pm.run(circuit_line(d)) for d in range(1, T + 1)}
counts2q = {d: isa[d].count_ops().get("cz", 0)
            + isa[d].count_ops().get("ecr", 0) for d in isa}
log(f"2q-gate counts: {counts2q}")

order = [(r, d) for r in range(R) for d in range(1, T + 1)]
random.Random(20260814).shuffle(order)
pubs = [isa[d] for _, d in order]

log(f"submitting batch: {len(pubs)} pubs x {SHOTS} shots "
    f"(seeded-shuffled interleaving)")
with Batch(backend=backend) as batch:
    sampler = SamplerV2(mode=batch)
    job = sampler.run(pubs, shots=SHOTS)
    log(f"job id: {job.job_id()}")
    result = job.result()
log("results received")

# per-repeat and pooled marginals
ones = {}   # (k, d, r) -> ones count
tot = {}    # (d, r) -> shots
counts_log = {}
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

log("--- pooled regression estimators + drift chi^2 ---")
deltas = []
for k in range(T - 1):
    p1, n1 = P_pool(k, k + 1)
    p2, n2 = P_pool(k, T)
    d_ = p1 - p2
    se = math.sqrt(p1 * (1 - p1) / n1 + p2 * (1 - p2) / n2)
    # per-repeat deltas
    reps = []
    for r in range(R):
        q1 = ones[(k, k + 1, r)] / tot[(k + 1, r)]
        q2 = ones[(k, T, r)] / tot[(T, r)]
        s = math.sqrt(q1 * (1 - q1) / tot[(k + 1, r)]
                      + q2 * (1 - q2) / tot[(T, r)])
        reps.append((q1 - q2, s))
    mean = sum(x for x, _ in reps) / R
    chi2 = sum((x - mean) ** 2 / s ** 2 for x, s in reps)
    deltas.append((k, d_, se, chi2))
    log(f"  record {k}: delta = {d_:+.4f} ± {se:.4f} "
        f"({d_/se:+.1f} sigma)   chi2({R-1}) = {chi2:.1f}")

eps_bound = max(0.0, max(d_ + 1.645 * se for _, d_, se, _ in deltas))
sig_pos = [k for k, d_, se, _ in deltas if d_ > 3 * se]
sig_neg = [k for k, d_, se, _ in deltas if d_ < -3 * se]
CHI2_CRIT = 15.09  # chi2(5), p = 0.01

log("--- VERDICT (registered readings, v6 pooled) ---")
if not sig_pos and not sig_neg:
    log("  reading (i) NULL: all pooled |delta| < 3 sigma.")
    log(f"  eps_RR <= {eps_bound:.4f}  (95% CL, one-sided, pooled "
        f"{R}x{SHOTS} shots)")
elif sig_pos and not sig_neg:
    drifty = [k for k, _, _, c in deltas if k in sig_pos
              and c > CHI2_CRIT]
    if drifty == sig_pos:
        log(f"  reading (iii) drift-dominated excess at {sig_pos} "
            "(chi2 inconsistent): inconclusive.")
    else:
        log(f"  reading (ii) REPRODUCIBLE ONE-SIGNED EXCESS at "
            f"{[k for k in sig_pos if k not in drifty]}: flagged "
            "for cross-backend replication.")
    log(f"  bound if systematic: {eps_bound:.4f}")
else:
    log(f"  reading (iii) MIXED (pos {sig_pos}, neg {sig_neg}).")
    log(f"  positive-side bound: eps_RR <= {eps_bound:.4f}")

log("--- conditional (1-lambda) conversion (envelope sums from "
    "lambda_theory_I.py; assumption f = envelope fraction) ---")
best = None
for k, d_, se, _ in deltas:
    if k in S_ENV and S_ENV[k] >= 0.02:
        b = (d_ + 1.645 * se) / S_ENV[k]
        best = b if best is None else min(best, b)
        log(f"  record {k}: (1-lambda) <= {b:.4f}  [f=1]")
if best is not None:
    log(f"  HEADLINE: (1-lambda) <= {best:.4f} [f=1]   "
        f"<= {best/0.83:.4f} [f=0.83]   <= {best/0.5:.4f} [f=0.5]")

meta = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "protocol": "v6-pooled-interleaved",
    "backend": backend.name,
    "physical_path": path,
    "repeats": R,
    "order": order,
    "counts2q": counts2q,
    "job_id": job.job_id(),
    "shots": SHOTS,
    "thetas": THETAS,
    "phis": PHIS,
    "counts": counts_log,
    "deltas": [(k, d_, se, chi2) for k, d_, se, chi2 in deltas],
    "eps_RR_95CL": eps_bound,
    "one_minus_lambda_f1": best,
}
out = (f"logs_lambda_hw_v6_{backend.name}_"
       f"{meta['utc'][:19].replace(':','')}.json")
with open(out, "w") as f:
    json.dump(meta, f, indent=1)
log(f"raw counts + analysis saved to {out}")
log("DONE")
